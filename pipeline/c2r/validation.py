"""Evaluate generated fixed-interface Rust with existing benchmark tests.

Validation uses a separate crate. Benchmark tests, fixtures and reports are
never added to translation prompts or to the generated crate's source tree.
"""

from __future__ import annotations

import json
import os
import re
import shlex
import shutil
import signal
import subprocess
import time
import tomllib
import uuid
from collections import Counter
from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path

from .benchmark import find_rust_project
from .config import Config, config_from_dict, resolve
from .rust_edits import _parse, source_files
from .rust_project import RustProject, _atomic_json, _fingerprint, _inside, _relative, _sha, _toml_value
from .runtime import InfrastructureError, compiler_environment, storage_error


_RESULT = re.compile(r"test result: (?:ok|FAILED)\. (\d+) passed; (\d+) failed; (\d+) ignored; "
                     r"(\d+) measured; (\d+) filtered out")
_CASE_RESULT = re.compile(r"^test .+ \.\.\. (ok|FAILED|ignored)\s*$", re.M)
VALIDATION_POLICY_VERSION = 2


def _candidate_files(run: RustProject) -> dict[str, bytes]:
    result = {name: code.encode() for name, code in source_files(run).items()}
    for name in ("Cargo.toml", "Cargo.lock"):
        path = run.root / name
        if path.is_file():
            result[name] = path.read_bytes()
    return result


def candidate_fingerprint(run: RustProject) -> str:
    return _fingerprint({name: _sha(data) for name, data in _candidate_files(run).items()})


def _benchmark(cfg: Config, project: str) -> Path:
    path = find_rust_project(resolve(cfg.benchmark.rust_dir), project,
                             resolve(cfg.benchmark.rust_project) if cfg.benchmark.rust_project else None)
    if path is None:
        raise ValueError(f"no Rust benchmark for {project}; supply benchmark.rust_project")
    return path


def _harness(source: str) -> bool:
    """Unlisted src/bin programs use libtest only when test attributes exist."""
    try:
        data, tree = _parse(source, "benchmark test")
    except ValueError:
        return True  # Compilation will report the actual syntax problem.
    pending = [tree]
    while pending:
        node = pending.pop()
        if node.type == "attribute_item":
            text = data[node.start_byte:node.end_byte].decode()
            if re.search(r"\btest\b", text):
                return True
        pending.extend(node.named_children)
    return not any(n.type == "function_item" and n.child_by_field_name("name") is not None
                   and data[n.child_by_field_name("name").start_byte:n.child_by_field_name("name").end_byte] == b"main"
                   for n in tree.named_children)


def _targets(root: Path, manifest: dict) -> list[dict]:
    selected, paths, names = [], set(), set()
    def add(name, path, harness=True, features=()):
        path = _relative(path)
        _inside(root, path)
        if path in paths:
            return
        if name in names:
            raise ValueError(f"benchmark test target name is ambiguous: {name}")
        names.add(name)
        paths.add(path)
        selected.append({"name": name, "path": path, "harness": bool(harness),
                         "required-features": list(features)})
    for target in manifest.get("test", []):
        name = target["name"]
        add(name, target.get("path", f"tests/{name}.rs"), target.get("harness", True),
            target.get("required-features", []))
    # CRUST-Bench stores most tests in src/bin, including crates with no [[test]].
    for path in sorted((root / "src/bin").glob("*.rs")):
        add(path.stem, path.relative_to(root).as_posix(), _harness(path.read_text()))
    if manifest.get("package", {}).get("autotests", True):
        for path in sorted((root / "tests").glob("*.rs")):
            add(path.stem, path.relative_to(root).as_posix())
        for path in sorted((root / "tests").glob("*/main.rs")):
            add(path.parent.name, path.relative_to(root).as_posix())
    return selected


def _cargo_manifest(data: dict) -> str:
    lines = ["# Isolated benchmark validation manifest.\n"]
    for section, value in data.items():
        if isinstance(value, dict):
            lines.append(f"[{section}]")
            lines += [f"{json.dumps(k)} = {_toml_value(v)}" for k, v in value.items()]
        elif section == "test":
            for target in value:
                lines.append("[[test]]")
                lines += [f"{json.dumps(k)} = {_toml_value(v)}" for k, v in target.items()]
        else:
            lines.append(f"{json.dumps(section)} = {_toml_value(value)}")
        lines.append("")
    text = "\n".join(lines)
    tomllib.loads(text)
    return text


def _prepare(workspace: Path, files: dict[str, bytes], benchmark: Path, cfg: Config) -> tuple[list[dict], dict]:
    original = tomllib.loads((benchmark / "Cargo.toml").read_text())
    targets = _targets(benchmark, original)
    if cfg.validation.targets:
        missing = set(cfg.validation.targets) - {t["name"] for t in targets}
        if missing:
            raise ValueError(f"unknown benchmark targets: {sorted(missing)}")
        targets = [t for t in targets if t["name"] in cfg.validation.targets]
    # Apply the compiler-enforced policy to the generated library only. The
    # isolated benchmark executables and dependencies may use their own unsafe.
    manifest = tomllib.loads(files["Cargo.toml"].decode())
    library = manifest.get("lib", {}).get("path", "src/lib.rs")
    library = _relative(library)
    if library not in files:
        raise ValueError(f"generated library root is missing: {library}")
    files = dict(files)
    root = files[library].decode("utf-8-sig")
    # A Unix shebang must remain the first line, if the supplied root has one.
    prefix = ""
    if root.startswith("#!") and not root.startswith("#!["):
        prefix, _, root = root.partition("\n")
        prefix += "\n"
    files[library] = (prefix + "#![forbid(unsafe_code)]\n" + root).encode()
    workspace.mkdir()
    for name, content in files.items():
        path = _inside(workspace, name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    copied = {}
    def copy(path: Path):
        if not path.is_file():
            raise ValueError(f"benchmark support/test file is missing: {path}")
        if not path.resolve().is_relative_to(benchmark):
            raise ValueError(f"benchmark file leaves its source tree: {path}")
        relative = path.relative_to(benchmark).as_posix()
        if relative in {"Cargo.toml", "Cargo.lock"}:
            raise ValueError("support files cannot replace Cargo manifests or lockfiles")
        dest = _inside(workspace, relative)
        content = path.read_bytes()
        if dest.exists():
            if relative in copied and copied[relative] == _sha(content):
                return
            raise ValueError(f"benchmark file would overwrite generated source: {relative}")
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(content)
        copied[relative] = _sha(content)
    for target in targets:
        copy(_inside(benchmark, target["path"]))
    for name in cfg.validation.support_files:
        path = _inside(benchmark, _relative(name))
        if path.is_dir():
            for child in sorted(path.rglob("*")):
                if child.is_file():
                    copy(child)
        else:
            copy(path)
    cargo = tomllib.loads(files["Cargo.toml"].decode())
    cargo["package"].update(autobins=False, autotests=False, autoexamples=False, autobenches=False, build=False)
    cargo["lib"].update(test=False, doctest=False)
    expected_lib = original.get("lib", {}).get("name") or original["package"]["name"].replace("-", "_")
    cargo["lib"]["name"] = expected_lib
    cargo["test"] = targets
    dependencies = {**original.get("dev-dependencies", {}), **cfg.validation.dependencies}
    for name, value in dependencies.items():
        if isinstance(value, dict) and ("path" in value or "workspace" in value):
            raise ValueError(f"validation dependency {name} requires an explicit registry override")
    if dependencies:
        cargo["dev-dependencies"] = dependencies
    for target, settings in original.get("target", {}).items():
        dev = settings.get("dev-dependencies", {})
        if dev:
            dev = {k: cfg.validation.dependencies.get(k, v) for k, v in dev.items()}
            if any(isinstance(v, dict) and ("path" in v or "workspace" in v) for v in dev.values()):
                raise ValueError("platform-specific validation dependencies cannot inherit paths/workspaces")
            cargo.setdefault("target", {}).setdefault(target, {})["dev-dependencies"] = dev
    (workspace / "Cargo.toml").write_text(_cargo_manifest(cargo))
    # Validation may add dev dependencies; only the isolated lockfile may change.
    return targets, {"files": copied, "cargo_manifest_sha256": _sha((benchmark / "Cargo.toml").read_bytes()),
                     "suite_sha256": _fingerprint({"files": copied, "targets": targets,
                         "manifest": _sha((benchmark / "Cargo.toml").read_bytes())}),
                     "library_crate_name": expected_lib,
                     "generated_library_guard": {"path": library, "attribute": "#![forbid(unsafe_code)]"}}


def _execute(command: list[str], cwd: Path, timeout: int, log: Path, env: dict) -> tuple[dict, str]:
    try:
        with compiler_environment(cwd, env) as compiler_env:
            return _execute_with_environment(command, cwd, timeout, log, compiler_env)
    except InfrastructureError as exc:
        output = str(exc)
        log.write_text(output)
        return {"command": command, "timeout": False, "exit_code": None,
                "error": output, "elapsed_seconds": 0}, output


def _execute_with_environment(command: list[str], cwd: Path, timeout: int, log: Path,
                              env: dict) -> tuple[dict, str]:
    started = time.monotonic()
    result = {"command": command, "timeout": False, "error": None}
    try:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                   errors="replace", start_new_session=True)
        try:
            output, _ = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            result["timeout"] = True
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            output, _ = process.communicate()
        except BaseException:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            output, _ = process.communicate()
            log.write_text(output)
            raise
        result["exit_code"] = process.returncode
    except OSError as exc:
        output = str(exc)
        result.update(exit_code=None, error=output)
    result["elapsed_seconds"] = time.monotonic() - started
    log.write_text(output)
    return result, output


def _environment_error(result: dict, output: str) -> bool:
    if result["error"] or storage_error(output):
        return True
    plain = "\n".join(line for line in output.splitlines() if not line.startswith("{"))
    return bool(re.search(r"no matching package named|failed to download|failed to get .+ as a dependency|"
                          r"toolchain .+ is not installed|could not execute process|"
                          r"attempting to make an HTTP request|linker .+ not found", plain, re.I))


def _run_target(target: dict, workspace: Path, destination: Path, cfg: Config, env: dict) -> dict:
    destination.mkdir()
    command = [cfg.tools.cargo, *([f"+{cfg.tools.rust_toolchain}"] if cfg.tools.rust_toolchain else []),
               "test", "--test", target["name"], "--no-run", "--message-format=json", "--color=never",
               "--jobs", str(cfg.validation.cargo_jobs)]
    if cfg.validation.offline:
        command.append("--offline")
    if target["required-features"]:
        command += ["--features", ",".join(target["required-features"])]
    build, output = _execute(command, workspace, cfg.validation.build_timeout, destination / "build.txt", env)
    result = {**target, "build": build, "counts": {"passed": 0, "failed": 0, "ignored": 0, "measured": 0, "filtered": 0},
              "programs_passed": 0, "programs_failed": 0}
    if build["timeout"]:
        return {**result, "outcome": "timeout", "stage": "build"}
    if _environment_error(build, output):
        return {**result, "outcome": "environment_error", "stage": "build"}
    if build["exit_code"] != 0:
        return {**result, "outcome": "compile_failed", "stage": "build"}
    executable = None
    for line in output.splitlines():
        try:
            message = json.loads(line)
        except ValueError:
            continue
        if (message.get("reason") == "compiler-artifact" and message.get("target", {}).get("name") == target["name"]
                and "test" in message["target"].get("kind", []) and message.get("executable")):
            executable = Path(message["executable"])
    if executable is None or not executable.is_file() or not executable.resolve().is_relative_to(workspace.resolve()):
        return {**result, "outcome": "environment_error", "stage": "build", "detail": "Cargo did not produce the expected test executable"}
    command = [str(executable)]
    if target["harness"]:
        command += [f"--test-threads={cfg.validation.test_threads}", "--color=never"]
        if cfg.validation.include_ignored:
            command.append("--include-ignored")
    execution, output = _execute(command, workspace, cfg.validation.test_timeout, destination / "run.txt", env)
    result["execution"] = execution
    summaries = _RESULT.findall(output) if target["harness"] else []
    if summaries:
        result["counts"] = dict(zip(result["counts"], map(int, summaries[-1])))
    elif target["harness"]:
        # Generated code can exit the whole test process, even with exit(0).
        # Preserve observed case results, but never accept a truncated harness
        # run or count unreported cases as passing. This is a candidate failure,
        # not evidence that compiler storage/the batch environment is broken.
        observed = Counter(_CASE_RESULT.findall(output))
        result["counts"].update(passed=observed["ok"], failed=observed["FAILED"], ignored=observed["ignored"])
        result.update(incomplete_test_output=True,
                      detail="test process ended without the final libtest result summary; reported counts are partial")
    if execution["timeout"]:
        return {**result, "outcome": "timeout", "stage": "execution"}
    if execution["error"]:
        return {**result, "outcome": "environment_error", "stage": "execution"}
    if not target["harness"]:
        result["programs_passed" if execution["exit_code"] == 0 else "programs_failed"] = 1
    if execution["exit_code"] != 0 or result["counts"]["failed"]:
        return {**result, "outcome": "test_failed", "stage": "execution"}
    if target["harness"] and not summaries:
        return {**result, "outcome": "test_failed", "stage": "execution"}
    if target["harness"] and result["counts"]["passed"] == 0:
        return {**result, "outcome": "no_tests", "stage": "execution"}
    return {**result, "outcome": "passed", "stage": "execution"}


def validate_run(directory: Path, *, config: Config | None = None, output: Path | None = None,
                 prepare_only: bool = False, active_job: str | None = None) -> dict:
    run = RustProject(directory)
    manifest = json.loads((run.root / ".c2r/contexts/manifest.json").read_text())
    cfg = config or config_from_dict(manifest["config"])
    with run._locked() as state:
        active = [key for key, job in state["jobs"].items() if job["status"] == "in_progress"]
        if active:
            if active != [active_job]:
                raise ValueError("validate a quiescent crate; a translator currently owns this run")
            # An orchestrator may evaluate its own uncommitted candidate. Other
            # processes still cannot validate a partially edited translation.
            run._running_job(state, active_job)
        files = _candidate_files(run)
        snapshot = {"revision": state["revision"], "jobs": {key: j["status"] for key, j in state["jobs"].items()},
                    "kind": state.get("kind", "translation"),
                    "complete": all(j["status"] == "completed" for j in state["jobs"].values())}
        project, seed, mode = state["project"], state["seed"], state["interface_mode"]
    base = (output or run.root / ".c2r/validation").resolve()
    if base.is_relative_to((run.root / "src").resolve()):
        raise ValueError("validation output cannot be inside generated src/")
    if mode == "fixed":
        try:
            benchmark_root = _benchmark(cfg, project)
        except ValueError:
            benchmark_root = None
        if benchmark_root and base.is_relative_to(benchmark_root):
            raise ValueError("validation output cannot be inside the benchmark source tree")
    identifier = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S") + "-" + uuid.uuid4().hex[:10]
    destination = base / identifier
    destination.mkdir(parents=True)
    workspace = destination / "crate"
    report = {"schema_version": 1, "id": identifier, "project": project, "seed": seed, "interface_mode": mode,
              "validation_policy_version": VALIDATION_POLICY_VERSION,
              "source_snapshot": snapshot, "candidate_sha256": _fingerprint({p: _sha(c) for p, c in files.items()}),
              "candidate_files": {p: _sha(c) for p, c in files.items()}, "settings": asdict(cfg.validation),
              "tools": {"cargo": cfg.tools.cargo, "rust_toolchain": cfg.tools.rust_toolchain},
              "started_at": datetime.now(timezone.utc).isoformat(), "targets": [], "outcome": "setup_error",
              "report_path": str(destination / "report.json"), "workspace": str(workspace),
              "feedback_to_model": False}
    started = time.monotonic()
    interrupted = False
    try:
        if mode != "fixed":
            report.update(outcome="unsupported_mode", detail="E1/free-interface validation needs adapters and is not implemented")
        else:
            benchmark = _benchmark(cfg, project)
            if destination.is_relative_to(benchmark):
                raise ValueError("validation output cannot be inside the benchmark source tree")
            targets, provenance = _prepare(workspace, files, benchmark, cfg)
            report.update(benchmark=str(benchmark), suite=provenance)
            env = dict(os.environ)
            for key in ("CARGO_TARGET_DIR", "CARGO_BUILD_TARGET_DIR", "RUST_TEST_THREADS", "RUST_TEST_NOCAPTURE", "RUST_TEST_FILTER"):
                env.pop(key, None)
            flags = env.get("CARGO_ENCODED_RUSTFLAGS")
            parsed_flags = flags.split("\x1f") if flags else shlex.split(env.get("RUSTFLAGS", ""))
            env.update(CARGO_ENCODED_RUSTFLAGS="\x1f".join(parsed_flags), SOURCE_DATE_EPOCH="0")
            report["compiler_flags"] = parsed_flags
            report["unsafe_policy"] = "forbid unsafe in generated library; benchmark tests may use unsafe"
            if prepare_only:
                report.update(outcome="prepared", selected_targets=targets)
            elif not targets:
                report["outcome"] = "no_tests"
            else:
                for index, target in enumerate(targets):
                    result = _run_target(target, workspace, destination / f"target-{index:03}", cfg, env)
                    report["targets"].append(result)
                    if result["outcome"] == "environment_error":
                        break  # Another test target cannot repair unavailable storage.
                outcomes = {t["outcome"] for t in report["targets"]}
                report["outcome"] = next((o for o in ("environment_error", "timeout", "compile_failed", "test_failed")
                                          if o in outcomes), "passed" if "passed" in outcomes else "no_tests")
    except KeyboardInterrupt:
        interrupted = True
        report["outcome"] = "interrupted"
    except (OSError, ValueError, KeyError, InfrastructureError) as exc:
        report.update(outcome="environment_error" if isinstance(exc, InfrastructureError) or storage_error(str(exc))
                      else "setup_error", detail=str(exc))
    finally:
        report["counts"] = {key: sum(t["counts"][key] for t in report["targets"])
                            for key in ("passed", "failed", "ignored", "measured", "filtered")}
        report["programs_passed"] = sum(t["programs_passed"] for t in report["targets"])
        report["programs_failed"] = sum(t["programs_failed"] for t in report["targets"])
        report["elapsed_seconds"] = time.monotonic() - started
        report["finished_at"] = datetime.now(timezone.utc).isoformat()
        if not cfg.validation.keep_workspace and workspace.exists():
            shutil.rmtree(workspace)
            report["workspace_retained"] = False
        else:
            report["workspace_retained"] = workspace.exists()
        _atomic_json(destination / "report.json", report)
        rows = [f"# Validation: {project}", "", f"Outcome: **{report['outcome']}**.",
                f"Checkpoint jobs complete: {snapshot['complete']} ({snapshot['kind']}). Tests were not exposed to the model.", "",
                "| Target | Outcome | Passed | Failed | Ignored |", "|---|---|---:|---:|---:|"]
        rows += [f"| {t['name']} | {t['outcome']} | {t['counts']['passed']} | {t['counts']['failed']} | {t['counts']['ignored']} |"
                 for t in report["targets"]]
        if report.get("detail"):
            rows += ["", report["detail"]]
        (destination / "report.md").write_text("\n".join(rows) + "\n")
        run.record_validation(report)
    if interrupted:
        raise KeyboardInterrupt
    return report
