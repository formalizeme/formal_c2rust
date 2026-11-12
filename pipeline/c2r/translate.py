"""Dependency-ordered translation, reversible integration and compiler repair."""

from __future__ import annotations

import json
import copy
from collections import Counter
import os
import shlex
import signal
import subprocess
import time
from dataclasses import asdict
from pathlib import Path

from .config import Config, PromptBudgetError, experiment_hash, to_dict
from .llm import ModelClient, ModelError, OpenRouterClient
from .runtime import InfrastructureError, compiler_environment, storage_error, storage_preflight
from .rust_edits import (apply_response, begin_transaction, finish_transaction, parse_response,
                         response_schema, source_files)
from .rust_project import RustProject, _atomic_json, _sha
from .tools import run as run_command
from .translation_units import read_translation_plan, render_messages


def _cargo(cfg: Config) -> list[str]:
    return [cfg.tools.cargo, *([f"+{cfg.tools.rust_toolchain}"] if cfg.tools.rust_toolchain else [])]


def cargo_check(run: RustProject, cfg: Config, directory: Path) -> dict:
    try:
        with compiler_environment(run.root) as env:
            return _cargo_check(run, cfg, directory, env)
    except InfrastructureError as exc:
        directory.mkdir(parents=True, exist_ok=True)
        result = {"command": [], "exit_code": None, "success": False, "timeout": False,
                  "environment_error": True, "stage": "environment", "diagnostics": str(exc)}
        (directory / "cargo.txt").write_text(str(exc))
        _atomic_json(directory / "cargo.json", result)
        return result


def _cargo_check(run: RustProject, cfg: Config, directory: Path, env: dict) -> dict:
    directory.mkdir(parents=True, exist_ok=True)
    command = [*_cargo(cfg), "check", "--lib", "--color=never", "--message-format=json",
               "--jobs", str(cfg.runner.cargo_jobs)]
    if cfg.runner.offline:
        command.append("--offline")
    if (run.root / "Cargo.lock").is_file():
        command.append("--locked")
    flags = (env["CARGO_ENCODED_RUSTFLAGS"].split("\x1f") if "CARGO_ENCODED_RUSTFLAGS" in env
             else shlex.split(env.get("RUSTFLAGS", "")))
    env["CARGO_ENCODED_RUSTFLAGS"] = "\x1f".join([*flags, "-F", "unsafe_code"])
    env["SOURCE_DATE_EPOCH"] = "0"
    started = time.monotonic()
    timeout = False
    try:
        process = subprocess.Popen(command, cwd=run.root, env=env, stdin=subprocess.DEVNULL,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                   errors="replace", start_new_session=True)
        try:
            output, _ = process.communicate(timeout=cfg.runner.compile_timeout)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            output, _ = process.communicate()
            timeout = True
        except BaseException:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.communicate()
            raise
        code = process.returncode
    except FileNotFoundError:
        code, output = 127, f"Cargo executable not found: {cfg.tools.cargo}"
    diagnostics = []
    for line in output.splitlines():
        try:
            message = json.loads(line)
        except ValueError:
            diagnostics.append(line)
            continue
        if message.get("reason") == "compiler-message":
            diagnostics.append(message["message"].get("rendered") or message["message"]["message"])
    if timeout:
        diagnostics.append(f"cargo check timed out after {cfg.runner.compile_timeout} seconds")
    result = {"command": command, "exit_code": code, "success": code == 0 and not timeout,
              "environment_error": storage_error(output),
              "timeout": timeout, "elapsed_seconds": time.monotonic() - started,
              "diagnostics": "\n".join(diagnostics),
              "cargo_lock_sha256": _sha((run.root / "Cargo.lock").read_bytes()) if (run.root / "Cargo.lock").is_file() else None}
    (directory / "cargo.txt").write_text(output)
    _atomic_json(directory / "cargo.json", result)
    return result


def _protocol(plan, cfg: Config) -> str:
    if cfg.runner.output_protocol != "auto":
        return cfg.runner.output_protocol
    return "fixed_functions" if plan.interface_mode == "fixed" else "edits"


def _messages(plan, unit, working: RustProject, cfg: Config, feedback: dict | None = None,
              previous: str | None = None) -> list[dict]:
    from .interfaces import definitions
    from .translation_units import RustArtifact
    artifacts = working.rust_artifacts()
    state = working.status()
    failed = {item for job in state["jobs"].values() if job["status"] == "failed" for item in job["item_ids"]}
    if state.get("allow_failed_prerequisites"):
        for key in failed:
            artifacts.setdefault(key, RustArtifact(
                "// Dependency translation failed. Its fixed API body remains unimplemented!(). "
                "Use the fixed signature if present, or absorb the C helper locally; this is not a translated implementation."))
    messages = render_messages(plan, unit, rust_artifacts=artifacts, require_ready=True,
                               include_interfaces=False, include_rust=False)
    protocol = _protocol(plan, cfg)
    if protocol == "fixed_functions":
        from .fixed_output import GUIDE
        messages[0]["content"] += " " + GUIDE
    else:
        messages[0]["content"] += (
            " Return JSON with edits, items and notes using the supplied schema. "
            "Edits change only src/*.rs: replace.old must match once; append/create use old=''. "
            "Account for every source item with installed code and rust_targets. "
            "Keep completed definitions unchanged. Do not leave todo!()/unimplemented!() in completed items.")
    messages[0]["content"] += " Do not use unsafe Rust."
    current = source_files(working)
    paths = {state["placements"][key]["path"] for key in unit.item_ids if state["placements"][key]["path"]}
    if not paths:
        paths = set(current)  # Ambiguous file placement remains visible, not guessed.
    data = {"placements": {key: state["placements"][key] for key in unit.item_ids},
            "failed_dependency_ids": sorted(failed & set(unit.rust_dependency_ids))}
    if plan.interface_mode == "fixed":
        # Once per prompt: exact target bodies, available API signatures and
        # declarations. Omit doc comments and unrelated implementation bodies.
        context = {}
        selected = {target for key in unit.item_ids for target in state["placements"][key]["rust_targets"]}
        from .interfaces import destination_path, match_item
        api_targets = {}
        for interface in plan.interfaces:
            destination = destination_path(interface.path, cfg.rust_project)
            api_targets[destination] = {d.target for d in definitions(interface.code, interface.path)}
        dependency_targets = {target for key in unit.dependency_ids if key in state["placements"]
                              for target in state["placements"][key]["rust_targets"]}
        for path in sorted(paths):
            entries = []
            from .rust_edits import _parse
            raw, root = _parse(current.get(path, ""), path)
            entries += [raw[n.start_byte:n.end_byte].decode() for n in root.named_children
                        if n.type in {"use_declaration", "extern_crate_declaration"}]
            inventory = definitions(current.get(path, ""), path)
            for key in unit.item_ids:
                if not state["placements"][key]["rust_targets"] and key in plan.graph.items:
                    matched = match_item(plan.graph.items[key], inventory)
                    if matched is not None:
                        selected.add(matched.target)
            relevant = selected | dependency_targets | api_targets.get(path, set())
            for definition in inventory:
                if definition.target not in relevant:
                    continue
                if definition.kind == "function_item":
                    if definition.target in selected:
                        text = definition.code
                    else:
                        raw = definition.code.encode()
                        text = raw[:definition.body_start - definition.start].decode().rstrip() + ";"
                    if definition.container:
                        text = definition.container + " {\n" + text + "\n}"
                    entries.append(text)
                else:
                    entries.append(definition.code)
            context[path] = "\n".join(entries)
        data["rust_api_and_current_targets"] = context
    if protocol == "edits":
        data["current_rust_files"] = {path: current[path] for path in sorted(paths) if path in current}
        # Exact-edit mode needs file text; avoid a duplicate contract listing.
        data.pop("rust_api_and_current_targets", None)
    dependencies = []
    seen = set()
    for key in unit.rust_dependency_ids + unit.dependency_ids:
        if key in artifacts:
            artifact = artifacts[key]
            if artifact.code not in seen:
                dependencies.append({"item_id": key, "path": artifact.path, "code": artifact.code})
                seen.add(artifact.code)
    if dependencies:
        if (cfg.translation.max_prompt_chars is not None and
                sum(len(d["code"]) for d in dependencies) > cfg.translation.max_prompt_chars // 4):
            from .interfaces import declaration_context
            for dependency in dependencies:
                dependency["code"] = "// Dependency signatures only: bodies omitted for prompt budget.\n" + declaration_context(
                    dependency["code"], dependency["path"] or "Rust dependency")
        data["rust_dependencies"] = dependencies
    if previous and previous.strip():
        messages.append({"role": "assistant", "content": previous})
    if feedback:
        data["last_attempt_feedback"] = feedback
    from .translation_units import _fence
    rust_context = data.pop("rust_api_and_current_targets", {})
    current_context = data.pop("current_rust_files", {})
    dependency_context = data.pop("rust_dependencies", [])
    sections = [json.dumps(data, indent=2)]
    for path, code in {**rust_context, **current_context}.items():
        sections += [f"## Current Rust: {path}", _fence(code, "rust")]
    for dependency in dependency_context:
        if any(dependency["code"] in code for code in [*rust_context.values(), *current_context.values()]):
            continue
        sections += [f"## Rust dependency: {dependency['item_id']} ({dependency['path']})",
                     _fence(dependency["code"], "rust")]
    messages.append({"role": "user", "content": "\n\n".join(sections)})
    length = sum(len(m["content"]) for m in messages)
    if cfg.translation.max_prompt_chars is not None and length > cfg.translation.max_prompt_chars:
        raise PromptBudgetError(length, cfg.translation.max_prompt_chars)
    return messages


def _settings(cfg: Config, client: ModelClient, interface_mode: str | None = None) -> dict:
    translation_cfg = copy.deepcopy(cfg)
    translation_cfg.idiomatic_stage = False
    return {"client": client.identity(), "model": to_dict(cfg)["model"], "repair": asdict(cfg.repair),
            "resolved_output_protocol": (cfg.runner.output_protocol if cfg.runner.output_protocol != "auto" else
                "fixed_functions" if interface_mode == "fixed" else "edits"),
            "runner": asdict(cfg.runner), "cargo": _cargo(cfg), "experiment_hash": experiment_hash(translation_cfg),
            "rustflags": os.environ.get("RUSTFLAGS"),
            "encoded_rustflags": os.environ.get("CARGO_ENCODED_RUSTFLAGS")}


def _job(plan, unit, working: RustProject, cfg: Config, client: ModelClient, *, progress=print) -> bool:
    working.start_job(unit.id)
    feedback = None
    previous = None
    last_error = "translation did not finish"
    details = {}
    try:
        begin_transaction(working, unit.id)
        request, retained = unit, {}
        if unit.kind == "interface_completion":
            from .interface_completion import pending_completion
            request, retained = pending_completion(plan, unit, working)
            if not request.item_ids:
                details = cargo_check(working, cfg, working.root / ".c2r/completion" / unit.id)
                if details.get("environment_error"):
                    raise InfrastructureError(details["diagnostics"])
                if details["success"]:
                    working.complete_job(unit.id, retained, validation={"cargo_check": details,
                        "already_implemented": len(retained), "model_calls": 0})
                    finish_transaction(working, unit.id, commit=True)
                    working.write_artifact_context()
                    return True
                raise ValueError("existing completed interface code failed cargo check")
        while True:
            storage_preflight(working.root)
            messages = _messages(plan, request, working, cfg, feedback, previous)
            number = working.reserve_model_call(unit.id, job_limit=1 + cfg.repair.max_retries,
                                                 total_limit=cfg.runner.max_model_calls)
            directory = working.root / ".c2r/calls" / f"call-{number:06}"
            if client.identity().get("transport") == "openrouter":
                progress(f"[request] {unit.id}: call {number}, wall-clock deadline {cfg.model.timeout}s")
            try:
                schema = None if _protocol(plan, cfg) == "fixed_functions" else response_schema(request.item_ids)
                completion = client.complete(messages, schema, seed=working.status()["seed"],
                                             directory=directory, job_id=unit.id, call_number=number)
            except ModelError as exc:
                working.record_model_call(number, exc.record())
                details = {"stage": "provider", "error": str(exc), "provider_error": exc.details}
                last_error = f"model request failed: {exc}"
                progress(f"[provider] {unit.id}: {exc}")
                break  # No hidden transport retries or repeat charges.
            working.record_model_call(number, {"status": "responded", "model": completion.model,
                                      "usage": completion.usage, "cost": completion.cost,
                                      "response_id": completion.response_id, "finish_reason": completion.finish_reason,
                                      "elapsed_seconds": completion.elapsed_seconds})
            previous = completion.text
            try:
                if completion.finish_reason not in {"stop", None}:
                    raise ValueError(f"completion ended with finish_reason={completion.finish_reason}")
                legacy_replay = (client.identity().get("transport") == "replay"
                                 and completion.text.lstrip().startswith(("{", "```json")))
                if _protocol(plan, cfg) == "fixed_functions" and not legacy_replay:
                    from .fixed_output import parse_fixed_response
                    from .interfaces import definitions
                    current = source_files(working)
                    public = {d.target for path, code in current.items() for d in definitions(code, path)
                              if d.kind == "function_item" and "pub" in d.signature}
                    expected = {key: [target for target in request.rust_targets.get(key, [])
                                     if target in public or unit.kind == "interface_completion"]
                                for key in request.item_ids}
                    placements = working.status()["placements"]
                    response = parse_fixed_response(completion.text, request.item_ids, current, expected,
                        {key: placements[key]["path"] for key in request.item_ids})
                else:
                    response = parse_response(completion.text, request.item_ids)
                candidate = apply_response(working, unit.id, response, max_files=cfg.runner.max_edit_files)
                if unit.kind == "interface_completion":
                    remaining, _ = pending_completion(plan, unit, working)
                    if remaining.item_ids:
                        raise ValueError("completion response left required interface functions unimplemented")
                _atomic_json(directory / "candidate.json", candidate)
                details = cargo_check(working, cfg, directory)
                details["stage"] = "environment" if details.get("environment_error") else "compiler"
                if details.get("environment_error"):
                    raise InfrastructureError(details["diagnostics"])
                if details["success"]:
                    working.record_model_call(number, {"acceptance_stage": "compiler", "accepted": True})
                    artifacts = {**retained, **response.artifacts}
                    for key, artifact in artifacts.items():
                        working.set_placement(key, artifact["path"], rust_targets=artifact["rust_targets"])
                    working.complete_job(unit.id, artifacts, validation={"cargo_check": details,
                                         "call_number": number, "semantic_validation": "not performed"})
                    finish_transaction(working, unit.id, commit=True)
                    working.write_artifact_context()
                    return True
                last_error = "cargo check failed"
                feedback = {"stage": "compiler", "success": False}
                if "compiler" in cfg.repair.feedback:
                    feedback["diagnostics"] = details["diagnostics"]
            except ValueError as exc:
                if working.status()["jobs"][unit.id]["status"] == "completed":
                    raise
                last_error = str(exc)
                feedback = {"stage": "integration", "error": last_error}
                details = feedback
            _atomic_json(directory / "feedback.json", feedback)
            working.record_model_call(number, {"acceptance_stage": feedback["stage"], "accepted": False})
            execution = working.status()["execution"]
            used = execution["job_calls"][unit.id] - execution.get("job_call_offsets", {}).get(unit.id, 0)
            if used >= 1 + cfg.repair.max_retries:
                break
            if cfg.runner.max_model_calls is not None and execution["model_calls"] >= cfg.runner.max_model_calls:
                last_error += "; runner.max_model_calls reached"
                break
    except KeyboardInterrupt:
        complete = working.status()["jobs"][unit.id]["status"] == "completed"
        finish_transaction(working, unit.id, commit=complete)
        if not complete:
            working.interrupt_job(unit.id)
        raise
    except (OSError, RuntimeError, ValueError) as exc:
        if working.status()["jobs"][unit.id]["status"] == "completed":
            raise
        last_error = str(exc)
        if isinstance(exc, PromptBudgetError):
            details = {"stage": "prompt_budget", "characters": exc.actual, "limit": exc.limit}
        elif isinstance(exc, InfrastructureError) or storage_error(str(exc)):
            details = {"stage": "environment", "environment_error": True, "error": str(exc)}
    finish_transaction(working, unit.id, commit=False)
    working.fail_job(unit.id, last_error, details=details)
    return False


def _summary(working: RustProject, processed: int, limited: bool, plan=None) -> dict:
    state = working.status()
    execution = state.get("execution", {})
    calls = list(execution.get("calls", {}).values())
    summary = {**working.summary(), "completed": all(j["status"] == "completed" for j in state["jobs"].values()),
               "environment_error": any(j["status"] == "failed" and
                   j.get("validation", {}).get("stage") == "environment" for j in state["jobs"].values()),
               "processed_jobs": processed, "stopped_by_limit": limited,
               "model_calls": execution.get("model_calls", 0),
               "transport": execution.get("settings", {}).get("client", {}).get("transport"),
               "output_protocol": execution.get("settings", {}).get("resolved_output_protocol"),
               "reported_cost": sum(c["cost"] for c in calls if isinstance(c.get("cost"), (int, float))),
               "calls_missing_cost": sum(not isinstance(c.get("cost"), (int, float)) for c in calls),
               "reported_tokens": {name: sum(c.get("usage", {}).get(name, 0) or 0 for c in calls)
                                   for name in ("prompt_tokens", "completion_tokens", "total_tokens")},
               "calls_missing_usage": sum(not c.get("usage") for c in calls),
               "execution_settings_sha256": execution.get("settings_sha256"),
               "failure_stages": dict(Counter(job.get("validation", {}).get("stage", "runner")
                   for job in state["jobs"].values() if job["status"] == "failed")),
               "recovered_jobs": {key: job["recovery"] for key, job in state["jobs"].items()
                                  if job["status"] == "completed" and job.get("recovery")},
               "jobs_by_kind": {kind: dict(Counter(j["status"] for j in state["jobs"].values()
                                                  if j.get("kind", "source") == kind))
                                for kind in {j.get("kind", "source") for j in state["jobs"].values()}},
               "model_calls_by_kind": dict(Counter(state["jobs"][call["job_id"]].get("kind", "source")
                                                   for call in calls)),
               "semantic_validation": "not performed"}
    if plan is not None and plan.interface_mode == "fixed":
        from .interface_completion import coverage_report
        coverage = coverage_report(plan, working)
        _atomic_json(working.root / ".c2r/interface_coverage.json", coverage)
        summary["interface_coverage"] = {k: coverage[k] for k in
            ("initial_placeholders", "unmatched_placeholders", "remaining_placeholders", "interface_complete")}
        summary["completed"] = summary["completed"] and coverage["interface_complete"]
    _atomic_json(working.root / ".c2r/translation_summary.json", summary)
    return summary


def translate_run(directory: Path, *, config: Config | None = None, client: ModelClient | None = None,
                  max_jobs: int | None = None, dry_run: bool = False, retry_failed: bool = False,
                  idiomatic_client: ModelClient | None = None, progress=print,
                  allow_token_limit_increase: bool = False,
                  allow_request_limit_decrease: bool = False) -> dict:
    working = RustProject(directory)
    if working.status().get("kind") == "idiomatic":
        raise ValueError("this is a v2 checkpoint; resume it with idiomatize on the original v1 crate")
    plan = read_translation_plan(working.root / ".c2r/contexts")
    cfg = config or plan.config
    if plan.interface_mode != "fixed" and cfg.runner.output_protocol == "fixed_functions":
        raise ValueError("runner.output_protocol=fixed_functions requires fixed interfaces")
    if "tests" in cfg.repair.feedback:
        raise ValueError("test feedback is not implemented in this stage; use repair.feedback=[compiler]")
    if cfg.idiomatic_stage and working.status()["interface_mode"] != "fixed":
        raise ValueError("idiomatic_stage currently requires fixed-interface benchmark validation")
    if (cfg.idiomatic_stage and client is not None and client.identity().get("transport") == "replay"
            and idiomatic_client is None and not dry_run):
        raise ValueError("automatic idiomatic replay needs a separate idiomatic response file/client")
    if max_jobs is not None and max_jobs < 1:
        raise ValueError("max_jobs must be positive")
    def finish(summary):
        if cfg.idiomatic_stage and summary["completed"]:
            from .idiomatic import idiomatize_run
            summary["idiomatic"] = idiomatize_run(working.root, config=cfg, client=idiomatic_client, progress=progress)
            _atomic_json(working.root / ".c2r/translation_summary.json", summary)
        return summary
    if dry_run:
        previews = []
        by_id = {unit.id: unit for unit in plan.units}
        for key in working.ready_jobs()[:max_jobs]:
            request = by_id[key]
            if request.kind == "interface_completion":
                from .interface_completion import pending_completion
                request, _ = pending_completion(plan, request, working)
            path = working.root / ".c2r/preview" / f"{key}.json"
            _atomic_json(path, {"job_id": key, "messages": _messages(plan, request, working, cfg),
                               "schema": None if _protocol(plan, cfg) == "fixed_functions" else response_schema(request.item_ids)})
            previews.append(str(path))
        return {**working.summary(), "dry_run": True, "previews": previews}
    working.resume()
    if any(j["status"] == "in_progress" for j in working.status()["jobs"].values()):
        raise ValueError("a translator already owns this crate")
    from .interface_completion import reconcile_source_jobs
    def reconcile():
        reconcile_source_jobs(plan, working, lambda path: cargo_check(working, cfg, path), progress=progress)
    # Also reconcile old checkpoints before constructing a live model client.
    reconcile()
    if not working.ready_jobs() and not retry_failed:
        return finish(_summary(working, 0, False, plan))
    storage_preflight(working.root)
    code, version = run_command([*_cargo(cfg), "--version"], timeout=cfg.runner.compile_timeout)
    if code:
        raise ValueError(f"configured Cargo/toolchain is unavailable: {version}")
    own_client = client is None
    client = client or OpenRouterClient(cfg.model)
    processed = 0
    limited = False
    try:
        working.configure_execution(_settings(cfg, client, plan.interface_mode),
                                    allow_token_limit_increase=allow_token_limit_increase,
                                    allow_request_limit_decrease=allow_request_limit_decrease)
        if retry_failed:
            for key, job in working.status()["jobs"].items():
                if job["status"] == "failed":
                    working.retry_job(key)
        by_id = {unit.id: unit for unit in plan.units}
        while max_jobs is None or processed < max_jobs:
            ready = working.ready_jobs()
            if not ready:
                break
            execution = working.status()["execution"]
            key = ready[0]
            if cfg.runner.max_model_calls is not None and execution["model_calls"] >= cfg.runner.max_model_calls:
                no_call_completion = False
                if by_id[key].kind == "interface_completion":
                    from .interface_completion import pending_completion
                    pending, _ = pending_completion(plan, by_id[key], working)
                    no_call_completion = not pending.item_ids
                if not no_call_completion:
                    limited = True
                    progress(f"[translate] request cap reached: {execution['model_calls']}/{cfg.runner.max_model_calls}; preserving remaining jobs")
                    break
            progress(f"[translate] {working.status()['project']}: {key}")
            success = _job(plan, by_id[key], working, cfg, client, progress=progress)
            processed += 1
            progress(f"[{'completed' if success else 'failed'}] {key}")
            if working.status()["jobs"][key].get("validation", {}).get("stage") == "environment":
                progress("[translate] infrastructure failure; stopping before further model calls")
                break
            if not success and not cfg.runner.continue_on_failure:
                break
        limited |= max_jobs is not None and processed >= max_jobs and bool(working.ready_jobs())
        reconcile()
        return finish(_summary(working, processed, limited, plan))
    finally:
        if own_client:
            client.close()
