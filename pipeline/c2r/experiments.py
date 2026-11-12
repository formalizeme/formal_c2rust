"""Sequential project × seed × variant runs with resumable result tables."""

from __future__ import annotations

import copy
import csv
import io
import json
from pathlib import Path

import yaml

from .benchmark import discover, select
from .config import Config, config_from_dict, experiment_hash, resolve, to_dict
from .rust_project import _atomic_json, _atomic_write
from .workflow import run_pipeline


def _merge(base, patch):
    for key, value in patch.items():
        if isinstance(value, dict) and isinstance(base.get(key), dict):
            _merge(base[key], value)
        else:
            base[key] = value


def _row(report: dict, variant: str) -> dict:
    stages = report.get("stages", {})
    translation, validation = stages.get("translation", {}), stages.get("validation", {})
    refactor, metrics = stages.get("refactor", {}), stages.get("metrics", {})
    counts = validation.get("counts", {})
    passed, failed = counts.get("passed", 0), counts.get("failed", 0)
    return {"variant": variant, "project": report["project"], "seed": report["seed"],
        "outcome": report["outcome"], "translation_complete": translation.get("completed", False),
        "jobs_completed": translation.get("jobs", {}).get("completed", 0),
        "jobs_failed": translation.get("jobs", {}).get("failed", 0),
        "output_protocol": translation.get("output_protocol"),
        "source_calls": translation.get("model_calls_by_kind", {}).get("source", 0),
        "completion_calls": translation.get("model_calls_by_kind", {}).get("interface_completion", 0),
        "expansion_fallback_items": stages.get("contexts", {}).get("expansion_fallback_items", 0),
        "remaining_placeholders": translation.get("interface_coverage", {}).get("remaining_placeholders"),
        "interface_complete": translation.get("interface_coverage", {}).get("interface_complete"),
        "tests_passed": passed, "tests_failed": failed, "tests_ignored": counts.get("ignored", 0),
        "test_pass_rate": passed / (passed + failed) if passed + failed else None,
        "validation_outcome": validation.get("outcome"),
        "programs_passed": validation.get("programs_passed", 0),
        "programs_failed": validation.get("programs_failed", 0),
        "refactor_accepted": refactor.get("accepted", 0), "refactor_original": refactor.get("original", 0),
        "model_calls": translation.get("model_calls", 0), "reported_cost": translation.get("reported_cost"),
        "calls_missing_cost": translation.get("calls_missing_cost", 0),
        "calls_missing_usage": translation.get("calls_missing_usage", 0),
        "tokens": translation.get("reported_tokens", {}).get("total_tokens"),
        "raw_pointer_type_sites": metrics.get("raw_pointer_type_sites"),
        "unsafe_keyword_sites": metrics.get("unsafe_keyword_sites"),
        "clippy_warnings": metrics.get("clippy", {}).get("clippy_lints"),
        "failure_stages": json.dumps(translation.get("failure_stages", {}), sort_keys=True),
        "idiomatic_outcome": stages.get("idiomatic", {}).get("outcome"),
        "idiomatic_calls": stages.get("idiomatic", {}).get("model_calls", 0),
        "idiomatic_reported_cost": stages.get("idiomatic", {}).get("reported_cost"),
        "idiomatic_calls_missing_cost": stages.get("idiomatic", {}).get("calls_missing_cost", 0),
        "report_path": report.get("report_path"), "error": report.get("error")}


def _write(root: Path, rows: list[dict]) -> None:
    _atomic_json(root / "results.json", {"runs": rows,
        "notes": ["Partial translations are not full-project successes even if their tests pass.",
                  "A missing test pass rate means no tests executed, not zero percent.",
                  "Reported cost may be incomplete; missing accounting is counted separately."]})
    if not rows:
        return
    stream = io.StringIO()
    writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
    writer.writeheader()
    writer.writerows(rows)
    _atomic_write(root / "results.csv", stream.getvalue().encode())
    lines = ["| Variant | Project | Seed | Outcome | Jobs failed | Tests passed | Tests failed |",
             "|---|---|---:|---|---:|---:|---:|"]
    lines += [f"| {r['variant']} | {r['project']} | {r['seed']} | {r['outcome']} | {r['jobs_failed']} | {r['tests_passed']} | {r['tests_failed']} |" for r in rows]
    _atomic_write(root / "results.md", ("\n".join(lines) + "\n").encode())


def run_experiments(cfg: Config, root: Path, *, variants: list[Path] = (), prepare_only: bool = False,
                    dry_run: bool = False, max_runs: int | None = None, progress=print) -> dict:
    root.mkdir(parents=True, exist_ok=True)
    configs = []
    for path in variants:
        patch = yaml.safe_load(path.read_text()) or {}
        if not isinstance(patch, dict):
            raise ValueError(f"variant must be a YAML mapping: {path}")
        base = copy.deepcopy(to_dict(cfg))
        _merge(base, patch)
        configs.append((path.stem, config_from_dict(base)))
    configs = configs or [("main", cfg)]
    rows = []
    try:
        for label, config in configs:
            chosen = select(discover(resolve(config.benchmark.c_dir), resolve(config.benchmark.rust_dir)), config.projects)
            if config.benchmark.rust_project is not None and len(chosen) != 1:
                raise ValueError("an explicit benchmark.rust_project can only accompany one C project")
            for project in chosen:
                for seed in config.seeds:
                    if max_runs is not None and len(rows) >= max_runs:
                        return {"runs": len(rows), "stopped_by_limit": True, "results": str(root / "results.json")}
                    destination = root / label / experiment_hash(config) / project.name / f"seed-{seed}"
                    progress(f"[batch] {label}: {project.name} seed {seed}")
                    try:
                        report = run_pipeline(project.c_dir, config=config, output=destination, seed=seed,
                                              prepare_only=prepare_only, dry_run=dry_run, progress=progress)
                    except (OSError, ValueError, RuntimeError, ImportError) as exc:
                        report = {"project": project.name, "seed": seed, "outcome": "error", "error": str(exc),
                                  "report_path": str(destination / "pipeline.json")}
                    rows.append(_row(report, label))
                    _write(root, rows)
    finally:
        _write(root, rows)
    return {"runs": len(rows), "stopped_by_limit": False, "results": str(root / "results.json")}
