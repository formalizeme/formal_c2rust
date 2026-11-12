"""Run one original C project through preparation, translation and evaluation.

Original C supplies graph identities. Per-unit stage-1 outcomes choose the C
representation in prompts. Pipeline records never substitute for job journals.
"""

from __future__ import annotations

import copy
import fcntl
import json
import os
import tempfile
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from uuid import uuid4

from .benchmark import Project, find_rust_project
from .c_analysis import _parse_arguments, compilation_commands, preprocessor_flags
from .config import Config, config_from_dict, experiment_hash, resolve, resume_budget_changes, to_dict
from .dependencies import GRAPH_PARSER_VERSION
from .idiomatic import idiomatize_run
from .llm import ModelClient
from .refactor import COPY_IGNORE, run_project, write_view
from .rust_project import RustProject, _atomic_json, _fingerprint, _sha, initialize_project
from .translate import translate_run
from .translation_units import (build_translation_plan, read_stage1_record, read_translation_plan,
                                write_stage1_record, write_translation_plan)
from .validation import VALIDATION_POLICY_VERSION, candidate_fingerprint, validate_run
from .runtime import InfrastructureError, storage_error


def _tree(path: Path, *, crate: bool = False) -> dict[str, str]:
    """Hash inputs, excluding the same C artifacts as the preparation copy."""
    files = {}
    for directory, dirs, names in os.walk(path):
        ignored = COPY_IGNORE(directory, [*dirs, *names])
        if crate:
            ignored |= {"target"}
        dirs[:] = sorted(d for d in dirs if d not in ignored)
        for name in dirs:
            if (Path(directory) / name).is_symlink():
                raise ValueError(f"directory symlinks are unsupported for pipeline input snapshots: {Path(directory) / name}")
        for name in sorted(set(names) - ignored):
            file = Path(directory) / name
            files[file.relative_to(path).as_posix()] = _sha(file.read_bytes())
    return files


def _absolute_options(args: list[str], directory: Path) -> list[str]:
    """Make relative include/file options independent of tool working dirs."""
    paths = ("-I", "-isystem", "-iquote", "-include", "-imacros", "-idirafter",
             "-isysroot", "-resource-dir", "--sysroot")
    result = []
    index = 0
    while index < len(args):
        arg = args[index]
        index += 1
        if arg in paths:
            if index == len(args):
                raise ValueError(f"missing path after {arg}")
            value = Path(args[index])
            index += 1
            result += [arg, str(value if value.is_absolute() else (directory / value).resolve())]
        elif prefix := next((p for p in paths if arg.startswith(p + "=") or
                             (p in {"-I", "-isystem", "-iquote", "-idirafter", "-isysroot", "-imacros"}
                              and arg.startswith(p) and arg != p)), None):
            tail = arg[len(prefix):]
            separator = "=" if tail.startswith("=") else ""
            value = Path(tail.removeprefix("="))
            result.append(prefix + separator + str(value if value.is_absolute() else (directory / value).resolve()))
        elif arg in {"-D", "-U"}:
            if index == len(args):
                raise ValueError(f"missing value after {arg}")
            result += [arg, args[index]]
            index += 1
        else:
            result.append(arg)
    return result


def _unit_flags(project: Project, database: Path | None, clang_args: list[str]) -> dict[str, list[str]]:
    commands = compilation_commands(database) if database else None
    flags = {}
    for path in sorted(set(project.units) | set(project.c_units)):
        args = []
        if commands is not None:
            entries = commands.get(path.resolve(), [])
            if len(entries) > 1:
                raise ValueError(f"expected one compilation command for {path}, found {len(entries)}")
            if entries:
                directory, argv = entries[0]
                args = _absolute_options(_parse_arguments(argv, path.resolve(), directory), directory)
            # Databases often omit tests/examples. Still attempt those using
            # stage-1 defaults; graph parsing rejects missing selected builds.
        # CompCert chooses its own C dialect. Forward preprocessing options,
        # not Clang code-generation, warning, optimization or target switches.
        selected = [f for f in preprocessor_flags([*args, *clang_args]) if not f.startswith("-std=")]
        flags[path.relative_to(project.c_dir).as_posix()] = selected
    return flags


@contextmanager
def _lock(root: Path):
    root.mkdir(parents=True, exist_ok=True)
    with (root / "pipeline.lock").open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError("another process owns this pipeline run") from None
        yield


def _save(root: Path, report: dict, outcome: str, **details) -> dict:
    report.update(outcome=outcome, **details)
    _atomic_json(root / "pipeline.json", report)
    (root / "pipeline.md").write_text(
        f"# Pipeline: {report['project']}\n\nOutcome: **{outcome}**.\n\n"
        f"Rust v1: `{report['rust']}`.\n\n"
        "Graph identities come from original C. Prompt source choices are recorded in "
        "`source_selection.json` and the exported contexts.\n")
    return report


def run_pipeline(directory: Path, *, config: Config, output: Path | None = None, seed: int = 0,
                 compile_commands: Path | None = None, clang_args: list[str] | tuple[str, ...] = (),
                 prepare_only: bool = False, dry_run: bool = False, max_jobs: int | None = None,
                 retry_failed: bool = False, skip_validation: bool = False,
                 client: ModelClient | None = None, idiomatic_client: ModelClient | None = None,
                 progress=print) -> dict:
    """Run/resume a single project and seed without modifying its C sources."""
    cfg = copy.deepcopy(config)
    source = directory.resolve()
    if not source.is_dir():
        raise ValueError(f"C project directory does not exist: {source}")
    if max_jobs is not None and max_jobs < 1:
        raise ValueError("max_jobs must be positive")
    cfg.seeds = [seed]
    cfg.projects = [source.name]
    # Only rejected units may fall back; successful-but-unmatched symbols are
    # preparation errors rather than a hidden change of experimental input.
    cfg.translation.missing_representation = "failed_units"
    cfg.translation.require_rust_context = cfg.context != "none"
    cfg = config_from_dict(to_dict(cfg))
    crate = find_rust_project(resolve(cfg.benchmark.rust_dir), source.name,
                              resolve(cfg.benchmark.rust_project) if cfg.benchmark.rust_project else None)
    if crate:
        cfg.benchmark.rust_project = str(crate)
    mode = cfg.translation.interface_mode
    mode = ("fixed" if cfg.experiment == "E2" else "free") if mode == "auto" else mode
    if not skip_validation and mode == "free" and not (prepare_only or dry_run):
        raise ValueError("free-interface behavioral validation is unavailable; use fixed interfaces/RBench or explicitly --skip-validation")
    if cfg.idiomatic_stage and (skip_validation or mode != "fixed"):
        raise ValueError("idiomatic_stage requires fixed-interface benchmark validation")
    if mode == "fixed" and not crate and not cfg.translation.interface_files:
        raise ValueError("fixed-interface mode needs a matching RBench crate or interface_files; use --rbench PATH")
    if not skip_validation and mode == "fixed" and crate is None and not (prepare_only or dry_run):
        raise ValueError("benchmark validation needs an RBench crate; use --rbench PATH or --skip-validation")
    project = Project(source.name, source, crate)
    if (cfg.idiomatic_stage and client is not None and client.identity().get("transport") == "replay"
            and idiomatic_client is None and not (prepare_only or dry_run)):
        raise ValueError("two-stage replay needs --idiomatic-responses as well as --responses")
    database = compile_commands.resolve() if compile_commands else source / "compile_commands.json"
    if database.is_dir():
        database = database / "compile_commands.json"
    database = database if database.is_file() else None
    if compile_commands and database is None:
        raise ValueError(f"compilation database does not exist: {compile_commands}")
    arguments = _absolute_options(list(clang_args), source)
    files = _tree(source)
    if not project.units and not project.headers:
        raise ValueError("the project contains no C compilation units or headers")
    extra = {}
    for name in (cfg.translation.item_map, cfg.translation.rust_artifacts, *cfg.translation.interface_files):
        if name:
            path = resolve(name.replace("{project}", project.name))
            extra[str(path)] = _sha(path.read_bytes())
    inputs = {"source": str(source), "files": files, "config": to_dict(cfg), "seed": seed,
              "compile_commands": str(database) if database else None,
              "compile_commands_sha256": _sha(database.read_bytes()) if database else None,
              "clang_args": arguments, "external_inputs": extra,
              "benchmark_files": _tree(crate, crate=True) if crate else None,
              "skip_validation": skip_validation}
    identity = _fingerprint(inputs)
    root = (output or resolve(cfg.output.runs_dir) / project.name /
            f"{experiment_hash(cfg)}-{identity[:12]}" / f"seed-{seed}").resolve()
    if root.is_relative_to(source) or source.is_relative_to(root):
        raise ValueError("pipeline output must be outside the C project directory")
    if crate and (root.is_relative_to(crate) or crate.is_relative_to(root)):
        raise ValueError("pipeline output must be separate from the benchmark crate")
    scratch = resolve(cfg.output.work_dir).resolve()
    if scratch.is_relative_to(source) or (crate and scratch.is_relative_to(crate)):
        raise ValueError("output.work_dir must be outside C/benchmark input directories")
    with _lock(root):
        state_path = root / "pipeline.json"
        if state_path.is_file():
            report = json.loads(state_path.read_text())
            if report.get("input_sha256") != identity:
                previous = report.get("inputs", {})
                changes = resume_budget_changes(previous.get("config", {}), inputs["config"])
                if (changes is None or {**inputs, "config": previous.get("config")} != previous
                        or _fingerprint(previous) != report.get("input_sha256")):
                    raise ValueError("project inputs or pipeline settings changed; choose a fresh --output directory")
                if report.get("outcome") == "completed":
                    stages = report.get("stages", {})
                    validation = stages.get("validation", {})
                    current = candidate_fingerprint(RustProject(root / "rust"))
                    unchanged = validation.get("outcome") == "passed" and validation.get("candidate_sha256") == current
                    if cfg.idiomatic_stage:
                        idiomatic = stages.get("idiomatic", {})
                        unchanged = (unchanged and idiomatic.get("accepted")
                                     and idiomatic.get("source_sha256") == current
                                     and idiomatic.get("candidate_sha256") == candidate_fingerprint(
                                         RustProject(Path(idiomatic["candidate"]))))
                    if unchanged:
                        progress("[pipeline] already complete; retaining its saved request settings")
                        return report
                report.setdefault("input_history", []).append({
                    "at": datetime.now(timezone.utc).isoformat(), "reason": "request_budgets_changed",
                    "previous_input_sha256": report["input_sha256"], "previous_inputs": previous,
                    "changes": changes})
                report.update(inputs=inputs, input_sha256=identity)
                _atomic_json(state_path, report)
                for change in changes:
                    progress(f"[pipeline] {change['setting']}: {change['old']} -> {change['new']}; preserving jobs and call counts")
        else:
            if any(path.name != "pipeline.lock" for path in root.iterdir()):
                raise ValueError("refusing to overwrite a nonempty output directory without pipeline.json")
            report = {"schema_version": 1, "project": project.name, "seed": seed,
                      "input_sha256": identity, "inputs": inputs, "rust": str(root / "rust"),
                      "report_path": str(state_path), "stages": {}}
        stage = "preparation"
        try:
            report["capabilities"] = {"validation": "RBench tests" if mode == "fixed" and not skip_validation else "none",
                "pointer_hints": False, "meaningful_renaming": False, "full_source_name_restoration": False,
                "ffi_differential": False, "kani": False, "unsafe_code": "forbidden by compiler",
                "output_protocol": cfg.runner.output_protocol}
            for key in ("errors", "error", "failed_stage", "interrupted_stage", "jobs", "semantic_validation"):
                report.pop(key, None)
            _save(root, report, "preparing")
            record = None
            if cfg.input.representation == "original_c":
                progress("[pipeline] using original C; skipping C refactoring")
                paths = sorted(set(project.units) | set(project.c_units)) or project.headers
                selection = [{"path": path.relative_to(source).as_posix(),
                              "kind": "header" if path.suffix == ".h" else project.kind(path),
                              "accepted": None, "representation": "original_c",
                              "original_sha256": _sha(path.read_bytes()),
                              "refactored_sha256": None, "attempts": [], "flags": None}
                             for path in paths]
                report["stages"]["refactor"] = {"status": "skipped", "reason": "original_c input",
                    "accepted": 0, "original": len(selection)}
            else:
                record_path = root / "stage1.json"
                if record_path.is_file():
                    saved = report["stages"].get("refactor", {}).get("snapshot_sha256")
                    if saved and saved != _sha(record_path.read_bytes()):
                        raise ValueError("saved stage-1 record changed; use a fresh pipeline workspace")
                    progress("[pipeline] reusing stage-1 record")
                    record = read_stage1_record(record_path, project, cfg=cfg)
                else:
                    progress("[pipeline] attempting C refactoring per compilation unit")
                    record = run_project(cfg, project, unit_flags=_unit_flags(project, database, arguments),
                                         include_library_units=True)
                    with tempfile.TemporaryDirectory(prefix=".stage1-", dir=root) as tmp:
                        path = write_stage1_record(record, Path(tmp) / "record.json", cfg=cfg)
                        path.replace(record_path)
                report["stages"]["refactor"] = {"status": record.status, "record": str(record_path),
                    "snapshot_sha256": _sha(record_path.read_bytes()),
                    "accepted": sum(u.accepted for u in record.units),
                    "original": sum(not u.accepted for u in record.units)}
                selection = [{"path": u.path, "kind": u.kind, "accepted": u.accepted,
                              "representation": (cfg.input.representation if u.accepted else "original_c"),
                              "original_sha256": _sha(u.source.encode()),
                              "refactored_sha256": _sha(u.refactored.encode()) if u.refactored is not None else None,
                              "attempts": u.errors, "flags": u.flags} for u in record.units]
                view_cfg = copy.deepcopy(cfg)
                view_cfg.output.refactored_dir = str(root / "c-view")
                write_view(view_cfg, [record])
            _atomic_json(root / "source_selection.json", {"units": selection, "graph_representation": "original_c",
                                                         "requested_representation": cfg.input.representation})
            contexts = root / "contexts"
            refresh_contexts = False
            if (contexts / "manifest.json").is_file():
                saved = report["stages"].get("contexts", {}).get("snapshot_sha256")
                if saved and saved != _fingerprint(_tree(contexts)):
                    raise ValueError("saved context export changed; use a fresh pipeline workspace")
                cached = json.loads((contexts / "manifest.json").read_text())
                graph_path = contexts / "dependencies.json"
                parser_version = (json.loads(graph_path.read_text()).get("parser_version", 1)
                                  if graph_path.is_file() else 1)
                refresh_contexts = (not cached.get("graph_complete", False)
                                    and parser_version < GRAPH_PARSER_VERSION
                                    and not (root / "rust" / ".c2r" / "state.json").exists())
                if refresh_contexts:
                    progress("[pipeline] refreshing blocked graph with updated Clang compatibility")
                elif not cached.get("jobs"):
                    report["stages"]["contexts"] = {"manifest": str(contexts / "manifest.json"),
                        "snapshot_sha256": _fingerprint(_tree(contexts)), "jobs": 0,
                        "source_ready": False, "graph_complete": cached.get("graph_complete", False)}
                    return _save(root, report, "blocked", errors=cached.get("issues", []))
                else:
                    plan = read_translation_plan(contexts)
            if refresh_contexts or not (contexts / "manifest.json").is_file():
                progress("[pipeline] building original-C graph and selecting prompt sources")
                plan = build_translation_plan(cfg, project, record=record, compile_commands=database,
                                              clang_args=arguments)
                with tempfile.TemporaryDirectory(prefix=".contexts-", dir=root) as tmp:
                    export = Path(tmp) / "contexts"
                    write_translation_plan(plan, export)
                    archive = None
                    if refresh_contexts:
                        history = root / "context-history"
                        history.mkdir(exist_ok=True)
                        archive = history / f"parser-v{parser_version}-{uuid4().hex[:12]}"
                        contexts.replace(archive)
                    try:
                        export.replace(contexts)
                    except BaseException:
                        if archive is not None:
                            archive.replace(contexts)
                        raise
            if (_tree(source) != files or (crate and _tree(crate, crate=True) != inputs["benchmark_files"])
                    or (database and _sha(database.read_bytes()) != inputs["compile_commands_sha256"])):
                raise ValueError("project or benchmark inputs changed during preparation; use a fresh run")
            report["stages"]["contexts"] = {"manifest": str(contexts / "manifest.json"),
                "snapshot_sha256": _fingerprint(_tree(contexts)),
                "graph_complete": plan.graph.complete, "source_ready": plan.complete, "jobs": len(plan.units),
                "completion_jobs": sum(u.kind == "interface_completion" for u in plan.units),
                "expansion_fallback_items": len({i.item_id for u in plan.units for i in u.issues
                    if i.code == "lowering_expansion_fallback" and i.item_id is not None}),
                "interface_coverage": str(contexts / "interface_coverage.json"),
                "initial_placeholders": plan.interface_coverage.get("initial_placeholders", 0),
                "unmatched_placeholders": plan.interface_coverage.get("unmatched_placeholders", 0)}
            if not plan.complete:
                errors = [i.__dict__ for i in plan.issues if i.severity == "error"]
                errors += [i.__dict__ for unit in plan.units for i in unit.issues if i.severity == "error"]
                return _save(root, report, "blocked", errors=errors)
            run = initialize_project(contexts, root / "rust", seed=seed, options=cfg.rust_project)
            if prepare_only:
                return _save(root, report, "prepared", jobs=run.summary()["jobs"])
            stage = "translation"
            translation_cfg = copy.deepcopy(cfg)
            translation_cfg.idiomatic_stage = False  # orchestration validates v1 first
            progress("[pipeline] translating dependency-first jobs")
            translated = translate_run(run.root, config=translation_cfg, client=client, max_jobs=max_jobs,
                                       dry_run=dry_run, retry_failed=retry_failed, progress=progress,
                                       allow_token_limit_increase=True, allow_request_limit_decrease=True)
            report["stages"]["translation"] = translated
            if dry_run:
                return _save(root, report, "previewed")
            if translated.get("environment_error"):
                return _save(root, report, "environment_error", failed_stage="translation",
                             error="Compiler infrastructure failed; repair storage before resuming")
            if cfg.metrics.enabled:
                from .metrics import collect_metrics
                report["stages"]["metrics"] = collect_metrics(run.root, cfg, root / "metrics-v1.json")
            if not translated["completed"]:
                report["stages"].pop("idiomatic", None)
                if mode == "fixed" and not skip_validation:
                    progress("[pipeline] evaluating E2 translation with unresolved source jobs")
                    report["stages"]["validation"] = validate_run(run.root, config=cfg)
                    if report["stages"]["validation"]["outcome"] == "environment_error":
                        return _save(root, report, "environment_error", failed_stage="validation")
                else:
                    report["stages"]["validation"] = {"outcome": "skipped", "reason": "partial translation without fixed-interface evaluation"}
                return _save(root, report, "incomplete", jobs=translated["jobs"])
            if skip_validation:
                report["stages"]["validation"] = {"outcome": "skipped", "explicit": True}
                return _save(root, report, "compiled_only", semantic_validation="not performed")
            stage = "validation"
            current = candidate_fingerprint(run)
            saved = report["stages"].get("validation", {})
            if (saved.get("outcome") == "passed" and saved.get("candidate_sha256") == current
                    and saved.get("validation_policy_version") == VALIDATION_POLICY_VERSION):
                validation = saved
            else:
                progress("[pipeline] evaluating Rust v1 with existing benchmark tests")
                validation = validate_run(run.root, config=cfg)
                report["stages"]["validation"] = validation
            if validation["outcome"] != "passed":
                return _save(root, report, "environment_error" if validation["outcome"] == "environment_error"
                             else "validation_failed")
            _save(root, report, "validated")
            if cfg.idiomatic_stage:
                stage = "idiomatic"
                progress("[pipeline] running optional Rust v2 refactoring")
                result = idiomatize_run(run.root, config=cfg, client=idiomatic_client, progress=progress)
                report["stages"]["idiomatic"] = result
                if not result["accepted"]:
                    return _save(root, report, "environment_error" if result.get("environment_error")
                                 else "idiomatic_failed")
                if cfg.metrics.enabled:
                    report["stages"]["metrics_v2"] = collect_metrics(Path(result["candidate"]), cfg, root / "metrics-v2.json")
            return _save(root, report, "completed")
        except KeyboardInterrupt:
            _save(root, report, "interrupted", interrupted_stage=stage)
            raise
        except (OSError, ValueError, RuntimeError, ImportError, KeyError) as exc:
            _save(root, report, "environment_error" if isinstance(exc, InfrastructureError) or storage_error(str(exc))
                  else "error", failed_stage=stage, error=str(exc))
            raise
