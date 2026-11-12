#!/usr/bin/env python3
"""Run every CBench subject using the ampv2 experiment settings.

From the repository root: uv run python pipeline/run_all_cbench.py --jobs 4
The child commands perform the pipeline's normal compilation and validation.
Rerun this script to let each subject's pipeline resume its saved progress.
"""

from __future__ import annotations

import argparse
import csv
import fcntl
import json
import os
import shlex
import shutil
import signal
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path

from c2r.benchmark import find_rust_project
from c2r.runtime import InfrastructureError, compiler_temp_root, storage_preflight


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "runs/all_pre_post_refactored"


@dataclass
class RunningSubject:
    index: int
    source: Path
    crate: Path
    destination: Path
    log: Path
    process: subprocess.Popen


def _positive_int(value: str) -> int:
    count = int(value)
    if count < 1:
        raise argparse.ArgumentTypeError("must be at least 1")
    return count


def _stop_subjects(active: list[RunningSubject]) -> None:
    # Let each pipeline save its checkpoint and clean up its own tool processes.
    for subject in active:
        if subject.process.poll() is None:
            try:
                os.killpg(subject.process.pid, signal.SIGINT)
            except ProcessLookupError:
                pass
    deadline = time.monotonic() + 10
    while any(subject.process.poll() is None for subject in active) and time.monotonic() < deadline:
        time.sleep(0.1)
    for subject in active:
        if subject.process.poll() is None:
            try:
                os.killpg(subject.process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        subject.process.wait()


def main(*, output: Path = OUTPUT, representation: str | None = None,
         description: str | None = None) -> int:
    parser = argparse.ArgumentParser(description=description or __doc__)
    parser.add_argument("--jobs", type=_positive_int, default=1,
                        help="maximum subjects running at once (default: 1)")
    parser.add_argument("--temp-dir", type=Path,
                        help="compiler temporary storage (default: C2R_COMPILER_TMPDIR or runs/compiler-tmp)")
    parser.add_argument("--min-free-mb", type=_positive_int,
                        help="minimum free space on temp/output filesystems (default: C2R_MIN_FREE_MB or 512)")
    args = parser.parse_args()
    if args.temp_dir is not None:
        os.environ["C2R_COMPILER_TMPDIR"] = str(args.temp_dir.expanduser().resolve())
    if args.min_free_mb is not None:
        os.environ["C2R_MIN_FREE_MB"] = str(args.min_free_mb)
    if not os.environ.get("OPENROUTER_API_KEY"):
        raise SystemExit("Export OPENROUTER_API_KEY before running this script.")
    if shutil.which("uv") is None:
        raise SystemExit("uv must be available on PATH.")
    cbench = ROOT / "CBench"
    rbench = ROOT / "RBench"
    if not cbench.is_dir() or not rbench.is_dir():
        raise SystemExit("CBench and RBench must exist in the repository root.")
    subjects = sorted((p for p in cbench.iterdir() if p.is_dir()), key=lambda p: p.name.lower())
    if not subjects:
        raise SystemExit("No CBench subjects found.")

    logs = output / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    # Different subjects have separate pipeline locks; this lock protects the
    # shared batch summary and logs from a second invocation of this script.
    with (output / "batch.lock").open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit(f"Another batch is already using {output}.") from None
        try:
            storage_preflight(output)
            print(f"Compiler temporary storage: {compiler_temp_root()}", flush=True)
            return _run_batch(subjects, rbench, logs, args.jobs,
                              output=output, representation=representation)
        except InfrastructureError as exc:
            print(f"Batch stopped: {exc}", flush=True)
            return 2


def _run_batch(subjects: list[Path], rbench: Path, logs: Path, jobs: int, *,
               output: Path = OUTPUT, representation: str | None = None) -> int:
    failures = 0
    active: list[RunningSubject] = []
    next_index = 0
    summary_path = output / "summary.csv"
    print(f"Running {len(subjects)} subjects with up to {jobs} in parallel.", flush=True)
    with summary_path.open("w", newline="", encoding="utf-8") as summary:
        writer = csv.writer(summary)
        writer.writerow(["subject", "rbench", "exit_code", "outcome", "output", "log"])
        summary.flush()
        try:
            while next_index < len(subjects) or active:
                while next_index < len(subjects) and len(active) < jobs:
                    storage_preflight(output)
                    source = subjects[next_index]
                    next_index += 1
                    subject = _start_subject(next_index, len(subjects), source, rbench, logs, writer,
                                             output=output, representation=representation)
                    summary.flush()
                    if subject is None:
                        failures += 1
                    else:
                        active.append(subject)
                finished = [subject for subject in active if subject.process.poll() is not None]
                for subject in finished:
                    code = subject.process.wait()
                    outcome = "completed" if code == 0 else "failed"
                    report = subject.destination / "pipeline.json"
                    if report.is_file():
                        try:
                            saved_outcome = json.loads(report.read_text()).get("outcome", outcome)
                            if code == 0 or saved_outcome != "completed":
                                outcome = saved_outcome
                        except (OSError, ValueError):
                            pass  # The exit code still records this subject's result.
                    writer.writerow([subject.source.name, str(subject.crate), code, outcome,
                                     str(subject.destination), str(subject.log)])
                    summary.flush()
                    print(f"[{subject.index}/{len(subjects)}] {subject.source.name}: {outcome} (exit {code})", flush=True)
                    active.remove(subject)
                    failures += code != 0
                    if code in (130, -signal.SIGINT):
                        raise KeyboardInterrupt
                    if code != 0 and outcome == "environment_error":
                        raise InfrastructureError(f"{subject.source.name} reported an infrastructure failure; "
                                                  f"see {subject.log}. Existing checkpoints are preserved.")
                if active and not finished:
                    time.sleep(0.2)
        except KeyboardInterrupt:
            print("\nStopping active subjects and saving progress...", flush=True)
            _stop_subjects(active)
            for subject in active:
                writer.writerow([subject.source.name, str(subject.crate), subject.process.returncode,
                                 "interrupted", str(subject.destination), str(subject.log)])
            summary.flush()
            print("Batch interrupted. Rerun the same script to resume.", flush=True)
            return 130
        except InfrastructureError:
            _stop_subjects(active)
            for subject in active:
                writer.writerow([subject.source.name, str(subject.crate), subject.process.returncode,
                                 "interrupted", str(subject.destination), str(subject.log)])
            summary.flush()
            raise
        except BaseException:
            _stop_subjects(active)
            raise

    print(f"Finished {len(subjects)} subjects; {failures} failed or skipped. Summary: {summary_path}", flush=True)
    return 1 if failures else 0


def _start_subject(index: int, total: int, source: Path, rbench: Path, logs: Path,
                   writer, *, output: Path = OUTPUT,
                   representation: str | None = None) -> RunningSubject | None:
    destination = output / source.name
    log = logs / f"{source.name}.log"
    crate = None
    try:
        crate = find_rust_project(rbench, source.name)
        if crate is None:
            raise ValueError(f"No matching RBench crate for {source.name}")
        if not (crate / "Cargo.toml").is_file():
            raise ValueError(f"RBench crate has no Cargo.toml: {crate}")
    except ValueError as exc:
        print(f"[{index}/{total}] {source.name}: skipped ({exc})", flush=True)
        writer.writerow([source.name, str(crate or ""), "", "missing_rbench", str(destination), ""])
        return None

    command = [
        "uv", "run", "c2r", "run", str(source), "--rbench", str(crate),
        "--set", "model.id=deepseek/deepseek-v4-flash-0731",
        "--set", "runner.max_model_calls=2000",
        "--seed", "0", "-o", str(destination),
        "--set", "idiomatic_stage=true",
        "--set", "model.reasoning_effort=high",
        "--set", "model.max_tokens=384000",
        "--set", "model.timeout=600",
    ]
    if representation is not None:
        command += ["--set", f"input.representation={representation}"]
    print(f"[{index}/{total}] {source.name}: starting; log: {log}", flush=True)
    # Append so resuming a batch retains earlier diagnostics.
    with log.open("a", encoding="utf-8") as stream:
        stream.write(f"\n$ {shlex.join(command)}\n")
        stream.flush()
        try:
            process = subprocess.Popen(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT,
                                       stdin=subprocess.DEVNULL, start_new_session=True,
                                       env={**os.environ, "PYTHONUNBUFFERED": "1"})
        except OSError as exc:
            stream.write(f"Could not start subject: {exc}\n")
            print(f"[{index}/{total}] {source.name}: could not start ({exc})", flush=True)
            writer.writerow([source.name, str(crate), "", "launch_failed", str(destination), str(log)])
            return None
    return RunningSubject(index, source, crate, destination, log, process)


if __name__ == "__main__":
    raise SystemExit(main())
