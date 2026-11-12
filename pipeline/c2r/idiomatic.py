"""Optional Rust-to-Rust refactoring, isolated from the faithful translation.

One whole-crate job uses the existing edit journal, model accounting, compiler
gate and RBench validator. The original translation remains the v1 artifact.
"""

from __future__ import annotations

import copy
import difflib
import fcntl
import json
import os
import shutil
import tempfile
from contextlib import contextmanager
from dataclasses import asdict
from pathlib import Path

from .config import Config, config_from_dict, to_dict
from .llm import ModelClient, ModelError, OpenRouterClient
from .runtime import InfrastructureError, storage_error, storage_preflight
from .rust_edits import (apply_response, begin_transaction, finish_transaction, parse_response,
                         public_contract, response_schema, source_files, validate_rust)
from .rust_project import RustProject, _atomic_json, _fingerprint, _inside, _sha
from .translate import cargo_check
from .validation import (VALIDATION_POLICY_VERSION, _benchmark, _candidate_files,
                         candidate_fingerprint, validate_run)


JOB = "idiomatic"
PROMPT_VERSION = 1


def _schema() -> dict:
    schema = response_schema([])
    del schema["properties"]["items"]
    schema["required"].remove("items")
    return schema


def _parse(text: str):
    # Use the same strict edit parser without requiring fresh C-item mappings.
    from .rust_edits import _unique_object
    text = text.strip()
    if text.startswith("```") and text.endswith("```"):
        text = text.split("\n", 1)[1].rsplit("```", 1)[0]
    data = json.loads(text, object_pairs_hook=_unique_object)
    if not isinstance(data, dict) or set(data) != {"edits", "notes"}:
        raise ValueError("idiomatic response must contain exactly edits and notes")
    return parse_response(json.dumps({**data, "items": []}), [])


def _settings(cfg: Config) -> dict:
    settings = {"prompt_version": PROMPT_VERSION, "model": to_dict(cfg)["model"],
            "validation_policy_version": VALIDATION_POLICY_VERSION,
            "repair": asdict(cfg.repair), "runner": asdict(cfg.runner),
            "validation": asdict(cfg.validation), "benchmark_rust_dir": cfg.benchmark.rust_dir,
            "cargo": cfg.tools.cargo, "rust_toolchain": cfg.tools.rust_toolchain,
            "max_prompt_chars": cfg.translation.max_prompt_chars,
            "rustflags": os.environ.get("RUSTFLAGS"),
            "encoded_rustflags": os.environ.get("CARGO_ENCODED_RUSTFLAGS")}
    if cfg.benchmark.rust_project is not None:
        settings["benchmark_rust_project"] = cfg.benchmark.rust_project
    return settings


@contextmanager
def _stage_lock(root: Path):
    root.mkdir(parents=True, exist_ok=True)
    with (root / "stage.lock").open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError("another process owns this idiomatic stage") from None
        yield


def _clone(source: RustProject, destination: Path, files: dict[str, bytes], state: dict,
           *, candidate: bool) -> None:
    destination.mkdir()
    for name, content in files.items():
        path = _inside(destination, name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    shutil.copytree(source.root / ".c2r/contexts", destination / ".c2r/contexts")
    shutil.copyfile(source.root / ".c2r/interfaces.json", destination / ".c2r/interfaces.json")
    state = copy.deepcopy(state)
    # Translation accounting belongs to v1; stage calls have their own budgets.
    for key in ("execution", "validations", "idiomatic_runs"):
        state.pop(key, None)
    if candidate:
        state.update(kind="idiomatic", artifacts={}, supplied_artifacts={}, placements={},
                     require_rust_context=False, jobs={JOB: {
                         "order": 0, "item_ids": [], "prerequisite_units": [], "rust_dependency_ids": [],
                         "status": "pending", "attempts": 0, "blocked_reasons": [], "last_error": None,
                         "owner": None, "validation": {}, "completed_at": None}})
    _atomic_json(destination / ".c2r/state.json", state)


def _prepare(source: RustProject, root: Path, cfg: Config) -> dict:
    with source._locked() as state:
        if state.get("kind") == "idiomatic":
            raise ValueError("start an idiomatic stage from the faithful v1 crate, not from v2")
        if state["interface_mode"] != "fixed":
            raise ValueError("idiomatic refactoring currently requires fixed-interface validation")
        if not state["jobs"] or any(j["status"] != "completed" for j in state["jobs"].values()):
            raise ValueError("finish every translation job before idiomatic refactoring")
        if (source.root / ".c2r/active_edit.json").exists():
            raise ValueError("recover the translation's active edit transaction before refactoring")
        files = _candidate_files(source)
        fingerprint = _fingerprint({p: _sha(c) for p, c in files.items()})
        for artifact in state["artifacts"].values():
            if artifact["code"] not in files.get(artifact["path"], b"").decode():
                raise ValueError("v1 artifacts changed; resume and complete its translation first")
        for path, content in files.items():
            if path.endswith(".rs"):
                validate_rust(content.decode(), path, artifact=True)
        settings = _settings(cfg)
        metadata = {"schema_version": 1, "project": state["project"], "seed": state["seed"],
                    "source": str(source.root), "source_sha256": fingerprint, "settings": settings}
        marker = root / "stage.json"
        if marker.exists():
            if json.loads(marker.read_text()) != metadata:
                raise ValueError("v1 or idiomatic settings changed; choose a fresh stage output directory")
            return metadata
        if any(p.name != "stage.lock" for p in root.iterdir()):
            raise ValueError("refusing to overwrite an unrecognized idiomatic output directory")
        # Publish both snapshots and their lineage together, under the stage lock.
        with tempfile.TemporaryDirectory(prefix=".prepare-", dir=root) as tmp:
            stage = Path(tmp)
            _clone(source, stage / "baseline", files, state, candidate=False)
            _clone(source, stage / "rust-v2", files, state, candidate=True)
            (stage / "baseline").rename(root / "baseline")
            (stage / "rust-v2").rename(root / "rust-v2")
        _atomic_json(marker, metadata)
        return metadata


def _messages(candidate: RustProject, cfg: Config, feedback: dict | None = None,
              previous: str | None = None) -> list[dict]:
    messages = [{"role": "system", "content": (
        "Refactor the supplied completed Rust library into clearer, idiomatic safe Rust. "
        "Preserve all observable behavior and the fixed public API: names, visibility, types, fields, "
        "signatures, errors, side effects and output. Improve ownership, borrowing, iterators, pattern "
        "matching, naming of local variables and control flow where useful. Keep representation changes "
        "inside function bodies or private helpers when the public API requires the current representation. "
        "Do not replace real implementations with placeholders, remove checks, add dependencies, "
        "introduce unsafe Rust, change tests, or change cfg/attributes to evade validation. "
        "Return only JSON with edits and notes, using the supplied schema. Edit only src/*.rs files. "
        "A replace old string must match exactly once; append/create require old=''. "
        "If no useful improvement is justified, return edits=[].") }]
    if previous and previous.strip():
        messages.append({"role": "assistant", "content": previous})
    data = {"current_rust_files": source_files(candidate),
            "cargo_manifest": (candidate.root / "Cargo.toml").read_text(), "output_schema": _schema()}
    if feedback:
        data["last_attempt_feedback"] = feedback
    messages.append({"role": "user", "content": "Edit these CURRENT files:\n" + json.dumps(data, indent=2)})
    length = sum(len(message["content"]) for message in messages)
    if cfg.translation.max_prompt_chars is not None and length > cfg.translation.max_prompt_chars:
        raise ValueError(f"idiomatic prompt has {length} characters; limit is {cfg.translation.max_prompt_chars}; no source was truncated")
    return messages


def _same_suite(baseline: dict, result: dict) -> bool:
    def cases(report):
        return [(t["name"], t["path"], t["harness"], t["counts"],
                 t["programs_passed"], t["programs_failed"]) for t in report["targets"]]
    return (result["outcome"] == "passed"
            and result.get("suite", {}).get("suite_sha256") == baseline["suite"]["suite_sha256"]
            and cases(result) == cases(baseline))


def _report(source: RustProject, candidate: RustProject, root: Path, metadata: dict,
            outcome: str, **details) -> dict:
    state = candidate.status()
    execution = state.get("execution", {})
    calls = list(execution.get("calls", {}).values())
    baseline = source_files(RustProject(root / "baseline"))
    current = source_files(candidate)
    diff_path = root / "changes.diff"
    diff_path.write_text("".join(line for path in sorted(baseline.keys() | current.keys())
        for line in difflib.unified_diff(baseline.get(path, "").splitlines(keepends=True),
                                        current.get(path, "").splitlines(keepends=True),
                                        fromfile=f"v1/{path}", tofile=f"v2/{path}")))
    report = {"schema_version": 1, "stage": "idiomatic", "project": state["project"],
              "seed": state["seed"], "outcome": outcome, "accepted": state["jobs"][JOB]["status"] == "completed",
              "source": str(source.root), "source_sha256": metadata["source_sha256"],
              "candidate": str(candidate.root), "candidate_sha256": candidate_fingerprint(candidate),
              "baseline": str(root / "baseline"), "report_path": str(root / "report.json"),
              "diff_path": str(diff_path),
              "changed_files": sorted(p for p in baseline.keys() | current.keys() if baseline.get(p) != current.get(p)),
              "model_calls": execution.get("model_calls", 0), "settings": metadata["settings"],
              "reported_cost": sum(c["cost"] for c in calls if isinstance(c.get("cost"), (int, float))),
              "calls_missing_cost": sum(not isinstance(c.get("cost"), (int, float)) for c in calls),
              "reported_tokens": {name: sum(c.get("usage", {}).get(name, 0) or 0 for c in calls)
                                  for name in ("prompt_tokens", "completion_tokens", "total_tokens")},
              "calls_missing_usage": sum(not c.get("usage") for c in calls),
              "execution_settings_sha256": execution.get("settings_sha256"), **details}
    _atomic_json(root / "report.json", report)
    (root / "report.md").write_text(
        f"# Idiomatic refactoring: {state['project']}\n\nOutcome: **{outcome}**.\n\n"
        f"Accepted: {report['accepted']}. Model calls: {report['model_calls']}.\n\n"
        f"Changed files: {', '.join(report['changed_files']) or 'none'}.\n\n"
        "Acceptance uses compilation and existing benchmark tests; it is not an equivalence proof.\n")
    with source._locked() as original:
        entry = {k: report[k] for k in ("outcome", "accepted", "source_sha256", "candidate",
                                      "candidate_sha256", "report_path", "model_calls", "reported_cost")}
        records = original.setdefault("idiomatic_runs", [])
        records[:] = [r for r in records if r["report_path"] != report["report_path"]]
        records.append(entry)
        source._save(original, "idiomatic_recorded", **entry)
    return report


def idiomatize_run(directory: Path, *, config: Config | None = None, client: ModelClient | None = None,
                   output: Path | None = None, dry_run: bool = False, progress=print) -> dict:
    """Refactor a completed fixed-interface translation, with resumable call limits."""
    source = RustProject(directory)
    archived = json.loads((source.root / ".c2r/contexts/manifest.json").read_text())["config"]
    cfg = config or config_from_dict(archived)
    if "tests" in cfg.repair.feedback:
        raise ValueError("idiomatic repair currently supports compiler feedback only; benchmark diagnostics stay held out")
    identity = _fingerprint({"source": candidate_fingerprint(source), "settings": _settings(cfg)})[:16]
    root = (output or source.root / ".c2r/idiomatic" / identity).resolve()
    if root == source.root or root.is_relative_to(source.root / "src") or source.root.is_relative_to(root):
        raise ValueError("idiomatic output must be separate from the v1 crate and its src/")
    if root.is_relative_to(_benchmark(cfg, source.status()["project"])):
        raise ValueError("idiomatic output cannot be inside the benchmark source tree")
    with _stage_lock(root):
        metadata = _prepare(source, root, cfg)
        baseline, candidate = RustProject(root / "baseline"), RustProject(root / "rust-v2")
        if candidate_fingerprint(baseline) != metadata["source_sha256"]:
            raise ValueError("the saved v1 baseline changed; refusing to use it")
        candidate.resume()
        job = candidate.status()["jobs"][JOB]
        if job["status"] == "completed":
            validation = job["validation"]
            if candidate_fingerprint(candidate) != validation["candidate_sha256"]:
                raise ValueError("accepted v2 source changed outside the stage; use a fresh output directory")
            return _report(source, candidate, root, metadata, validation["outcome"], **validation["reports"])
        if job["status"] == "in_progress":
            raise ValueError("the v2 checkpoint is owned by another process")
        if source_files(candidate) != source_files(baseline):
            raise ValueError("uncommitted v2 source differs from the baseline after recovery")
        if dry_run:
            path = root / "preview.json"
            _atomic_json(path, {"job_id": JOB, "messages": _messages(candidate, cfg), "schema": _schema()})
            return {"outcome": "prepared", "accepted": False, "preview": str(path), "candidate": str(candidate.root)}
        baseline_path = root / "baseline-validation.json"
        reference = json.loads(baseline_path.read_text()) if baseline_path.is_file() else None
        if (reference and reference["outcome"] == "passed"
                and reference.get("validation_policy_version") == VALIDATION_POLICY_VERSION):
            current_suite = validate_run(baseline.root, config=cfg, prepare_only=True)
            if current_suite.get("suite") != reference.get("suite"):
                raise ValueError("benchmark suite changed; use a fresh idiomatic output directory")
        else:
            progress("[idiomatic] validating v1 baseline")
            reference = validate_run(baseline.root, config=cfg)
            _atomic_json(baseline_path, reference)
        reports = {"baseline_validation": reference["report_path"]}
        if reference["outcome"] != "passed":
            return _report(source, candidate, root, metadata, "baseline_failed", **reports,
                           environment_error=reference["outcome"] == "environment_error",
                           baseline_outcome=reference["outcome"])
        # Check prompt size before initializing a paid transport.
        _messages(candidate, cfg)
        storage_preflight(candidate.root)
        own_client = client is None
        client = client or OpenRouterClient(cfg.model)
        try:
            candidate.configure_execution({**_settings(cfg), "client": client.identity()})
            state = candidate.status()
            used = state["execution"]["model_calls"]
            if used >= 1 + cfg.repair.max_retries or (cfg.runner.max_model_calls is not None and used >= cfg.runner.max_model_calls):
                return _report(source, candidate, root, metadata, "budget_exhausted", **reports)
            if state["jobs"][JOB]["status"] == "failed":
                candidate.retry_job(JOB)
            candidate.start_job(JOB)
            feedback = previous = None
            last_error = "no candidate accepted"
            environment_failure = False
            try:
                begin_transaction(candidate, JOB)
                while True:
                    storage_preflight(candidate.root)
                    messages = _messages(candidate, cfg, feedback, previous)
                    number = candidate.reserve_model_call(JOB, job_limit=1 + cfg.repair.max_retries,
                                                          total_limit=cfg.runner.max_model_calls)
                    call = candidate.root / ".c2r/calls" / f"call-{number:06}"
                    progress(f"[idiomatic] model call {number}, request deadline {cfg.model.timeout}s")
                    try:
                        completion = client.complete(messages, _schema(), seed=state["seed"], directory=call,
                                                     job_id=JOB, call_number=number)
                    except ModelError as exc:
                        candidate.record_model_call(number, exc.record())
                        last_error = f"model request failed: {exc}"
                        progress(f"[provider] idiomatic: {exc}")
                        break
                    candidate.record_model_call(number, {"status": "responded", "model": completion.model,
                        "usage": completion.usage, "cost": completion.cost, "response_id": completion.response_id,
                        "finish_reason": completion.finish_reason, "elapsed_seconds": completion.elapsed_seconds})
                    previous = completion.text
                    try:
                        if completion.finish_reason not in {"stop", None}:
                            raise ValueError(f"completion ended with finish_reason={completion.finish_reason}")
                        response = _parse(previous)
                        files = apply_response(candidate, JOB, response, max_files=cfg.runner.max_edit_files)
                        originals = source_files(baseline)
                        for path, code in files.items():
                            validate_rust(code, path, artifact=True)
                            if public_contract(code, path) != public_contract(originals.get(path, ""), path):
                                raise ValueError(f"{path}: v1 public declarations or trait implementations changed")
                        _atomic_json(call / "candidate.json", files)
                        check = cargo_check(candidate, cfg, call)
                        if check.get("environment_error"):
                            raise InfrastructureError(check["diagnostics"])
                        if check["success"]:
                            progress("[idiomatic] validating v2 candidate")
                            result = validate_run(candidate.root, config=cfg, active_job=JOB)
                            _atomic_json(call / "validation.json", result)
                            reports["candidate_validation"] = result["report_path"]
                            if _same_suite(reference, result):
                                unchanged = source_files(candidate) == source_files(baseline)
                                outcome = "unchanged" if unchanged else "accepted"
                                candidate.complete_job(JOB, {}, validation={"cargo_check": check,
                                    "candidate_sha256": candidate_fingerprint(candidate), "call_number": number,
                                    "outcome": outcome, "reports": reports})
                                finish_transaction(candidate, JOB, commit=True)
                                return _report(source, candidate, root, metadata, outcome, **reports)
                            last_error = "candidate did not pass the unchanged benchmark suite"
                            feedback = {"stage": "acceptance", "error": last_error}
                            if result["outcome"] in {"setup_error", "environment_error", "interrupted"}:
                                environment_failure = result["outcome"] == "environment_error"
                                break
                        else:
                            last_error = "cargo check failed"
                            feedback = {"stage": "compiler", "success": False}
                            if "compiler" in cfg.repair.feedback:
                                feedback["diagnostics"] = check["diagnostics"]
                    except ValueError as exc:
                        if candidate.status()["jobs"][JOB]["status"] == "completed":
                            raise
                        last_error = str(exc)
                        feedback = {"stage": "integration", "error": last_error}
                    _atomic_json(call / "feedback.json", feedback)
                    used = candidate.status()["execution"]["model_calls"]
                    if used >= 1 + cfg.repair.max_retries or (cfg.runner.max_model_calls is not None and used >= cfg.runner.max_model_calls):
                        break
            except KeyboardInterrupt:
                complete = candidate.status()["jobs"][JOB]["status"] == "completed"
                finish_transaction(candidate, JOB, commit=complete)
                if not complete:
                    candidate.interrupt_job(JOB)
                _report(source, candidate, root, metadata, "interrupted", **reports)
                raise
            except (OSError, RuntimeError, ValueError) as exc:
                if candidate.status()["jobs"][JOB]["status"] == "completed":
                    raise
                last_error = str(exc)
                environment_failure = isinstance(exc, InfrastructureError) or storage_error(last_error)
            finish_transaction(candidate, JOB, commit=False)
            candidate.fail_job(JOB, last_error, details={"stage": "environment"} if environment_failure else None)
            return _report(source, candidate, root, metadata,
                           "environment_error" if environment_failure else "rejected", **reports,
                           environment_error=environment_failure, error=last_error)
        finally:
            if own_client:
                client.close()
