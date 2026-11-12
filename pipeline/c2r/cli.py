"""Command-line entry point for preparation, dependency analysis and checks."""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path

import yaml

from .benchmark import discover, select
from .config import MAIN_CONFIG, ConfigError, config_from_dict, experiment_hash, load_config, resolve, to_dict
from .dependencies import build_project_graph, translation_order_with_candidates, write_graph
from .equiv import CHANGED, EQUAL, check_all, write_report
from .refactor import refactor_all, run_project, run_stage1
from .stats import write_stats
from .rust_project import RustProject, initialize_project
from .llm import ReplayClient
from .translate import translate_run
from .validation import validate_run
from .idiomatic import idiomatize_run
from .workflow import run_pipeline
from .tools import FAIL, doctor
from .translation_units import (build_translation_plan, read_stage1_record, read_translation_plan, unit_ready,
                                write_stage1_record, write_translation_plan)


def _prepare_contexts(cfg, project, args):
    record = None
    cache = resolve(args.stage1_cache) / f"{project.name}.json" if args.stage1_cache else None
    if args.stage1_record:
        record = read_stage1_record(resolve(args.stage1_record), project, cfg=cfg)
    elif cache and cache.is_file():
        record = read_stage1_record(cache, project, cfg=cfg)
    elif cfg.input.representation != "original_c":
        print(f"[stage 1] {project.name}", flush=True)
        record = run_project(cfg, project, include_library_units=True)
        if cache:
            write_stage1_record(record, cache, cfg=cfg)
    return build_translation_plan(
        cfg, project, record=record, clang_args=args.clang_arg,
        compile_commands=resolve(args.compile_commands) if args.compile_commands else None)


def main(argv: list[str] | None = None) -> int:
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("-c", "--config", default=str(MAIN_CONFIG),
                        help="YAML config (default: pipeline/configs/main.yaml)")
    common.add_argument("--set", action="append", default=[], metavar="KEY=VALUE",
                        help="override a field, e.g. --set input.representation=clight")

    parser = argparse.ArgumentParser(prog="c2r", description="C-to-Rust translation pipeline")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("doctor", parents=[common], help="check tools and environment")
    p_config = sub.add_parser("config", parents=[common], help="print the resolved config")
    p_config.add_argument("--json", action="store_true", help="print JSON instead of YAML")
    sub.add_parser("projects", parents=[common], help="list the selected benchmark projects")
    p_refactor = sub.add_parser("refactor", parents=[common],
                                help="run ptridxgen on the selected projects into output.refactored_dir")
    p_refactor.add_argument("-j", "--jobs", type=int, default=4, help="projects processed in parallel")
    p_stats = sub.add_parser("stats", parents=[common],
                             help="per-project pointer statistics (size, pointers, pointer arithmetic, "
                                  "refactored) into a CSV")
    p_stats.add_argument("-o", "--output", default="results/pointer_stats.csv",
                         help="CSV to write (a .md with the column definitions is written next to it)")
    p_deps = sub.add_parser("dependencies", parents=[common],
                            help="build original-C item graphs and dependency-first translation groups")
    p_deps.add_argument("-o", "--output", default="results/dependencies",
                        help="directory for one graph JSON per selected project")
    p_deps.add_argument("--compile-commands", help="compilation database (for a single selected project)")
    p_deps.add_argument("--clang-arg", action="append", default=[],
                        help="extra Clang argument; repeat and use = for flags, e.g. --clang-arg=-DFEATURE")
    p_deps.add_argument("--stage1-status", help="stage-1 status.json supplying accepted per-file preprocessing flags")
    p_context = sub.add_parser("contexts", parents=[common],
                               help="export ordered translation jobs and prompt context without calling an LLM")
    p_context.add_argument("-o", "--output", default="results/contexts",
                           help="root directory for <project>/<experiment-hash>/manifest.json and jobs")
    p_scaffold = sub.add_parser("scaffold", parents=[common],
                                help="create/resume Rust working crates and persistent translation state")
    p_scaffold.add_argument("-o", "--output", help="run root (default: output.runs_dir)")
    p_scaffold.add_argument("--seed", type=int, help="prepare one seed instead of all configured seeds")
    for command in (p_context, p_scaffold):
        command.add_argument("--compile-commands", help="compilation database for one selected project")
        command.add_argument("--clang-arg", action="append", default=[],
                             help="extra graph-parser argument; use = for flags, e.g. --clang-arg=-DFEATURE")
        stage_inputs = command.add_mutually_exclusive_group()
        stage_inputs.add_argument("--stage1-record", help="reuse a text-only stage-1 snapshot for one project")
        stage_inputs.add_argument("--stage1-cache", help="reuse/save <project>.json snapshots in this directory")
        if command is p_scaffold:
            stage_inputs.add_argument("--contexts", help="use an exported context directory or manifest without rebuilding inputs")
    p_state = sub.add_parser("run-state", help="inspect or resume an existing Rust working crate")
    p_state.add_argument("directory", help="Rust crate directory containing .c2r/state.json")
    p_state.add_argument("--resume", action="store_true", help="recover interrupted work and invalidate changed completions")
    p_state.add_argument("--force-recover", action="store_true", help="with --resume, explicitly reclaim in-progress jobs")
    p_state.add_argument("--retry", help="return a failed job to pending")
    p_state.add_argument("--json", action="store_true", help="print the full checkpoint")
    p_translate = sub.add_parser("translate", parents=[common], help="translate jobs in an existing scaffold and repair compiler errors")
    p_translate.add_argument("directory", help="Rust working crate containing .c2r/state.json")
    p_translate.add_argument("--dry-run", action="store_true", help="export current request previews without model calls or job changes")
    p_translate.add_argument("--responses", help="replay a saved response sequence instead of making live model calls")
    p_translate.add_argument("--idiomatic-responses", help="separate replay sequence for the optional idiomatic stage")
    p_translate.add_argument("--max-jobs", type=int, help="stop after this many jobs in this invocation")
    p_translate.add_argument("--retry-failed", action="store_true", help="retry failed jobs using their remaining call budgets")
    p_validate = sub.add_parser("validate", parents=[common], help="evaluate fixed-interface Rust using existing benchmark tests")
    p_validate.add_argument("directory", help="Rust working crate containing .c2r/state.json")
    p_validate.add_argument("-o", "--output", help="report/workspace root (default: .c2r/validation in the run)")
    p_validate.add_argument("--prepare-only", action="store_true", help="prepare the isolated workspace without building or running tests")
    p_idiomatic = sub.add_parser("idiomatize", parents=[common], help="refactor a completed fixed-interface translation into a separately validated Rust v2")
    p_idiomatic.add_argument("directory", help="original completed Rust v1 crate containing .c2r/state.json")
    p_idiomatic.add_argument("-o", "--output", help="stage directory (default: .c2r/idiomatic/<hash> in v1)")
    p_idiomatic.add_argument("--dry-run", action="store_true", help="prepare snapshots and a prompt preview without model calls or Cargo execution")
    p_idiomatic.add_argument("--responses", help="replay a saved idiomatic response sequence")
    p_run = sub.add_parser("run", parents=[common], help="run/resume an original C folder through mixed-source translation and evaluation")
    p_run.add_argument("directory", help="original C project folder (left unchanged)")
    p_run.add_argument("--rbench", help="matching RBench crate directory; otherwise match the C folder name")
    p_run.add_argument("--interface-file", action="append", default=[], help="explicit Rust interface file; repeat for several")
    p_run.add_argument("--compile-commands", help="compilation database file or directory; auto-detected in the C folder")
    p_run.add_argument("--clang-arg", action="append", default=[], help="extra analysis argument; repeat and use = for flags")
    p_run.add_argument("--seed", type=int, default=0, help="one seed for this run (default: 0)")
    p_run.add_argument("-o", "--output", help="pipeline workspace; reuse with identical inputs/settings to resume")
    preparation = p_run.add_mutually_exclusive_group()
    preparation.add_argument("--prepare-only", action="store_true", help="refactor, export contexts and scaffold without model calls or Rust evaluation")
    preparation.add_argument("--dry-run", action="store_true", help="also export ready translation prompts without model calls or Rust evaluation")
    p_run.add_argument("--max-jobs", type=int, help="limit translation jobs attempted in this invocation")
    p_run.add_argument("--retry-failed", action="store_true", help="retry failed jobs using their remaining budgets")
    p_run.add_argument("--skip-validation", action="store_true", help="explicit compilation-only run; incompatible with idiomatic_stage")
    p_run.add_argument("--responses", help="offline translation response replay file")
    p_run.add_argument("--idiomatic-responses", help="separate offline idiomatic response replay file")
    p_batch = sub.add_parser("batch", parents=[common], help="run selected projects × seeds × YAML variants and write result tables")
    p_batch.add_argument("-o", "--output", default="results/experiments", help="batch workspace and results table directory")
    p_batch.add_argument("--variant", action="append", default=[], help="YAML overlay on the base config; repeat for ablations")
    p_batch.add_argument("--prepare-only", action="store_true", help="prepare projects without any model calls")
    p_batch.add_argument("--dry-run", action="store_true", help="also export currently ready prompts without model calls")
    p_batch.add_argument("--max-runs", type=int, help="stop after this many project/seed/variant runs")
    p_model = sub.add_parser("model-check", parents=[common], help="make one small explicit model request and record compatibility/accounting")
    p_model.add_argument("-o", "--output", help="new call-log directory")
    p_model.add_argument("--structured", action="store_true", help="check strict JSON schema (the default E2 protocol uses plain Rust text)")
    p_check = sub.add_parser("check-refactor", parents=[common],
                             help="build and run each accepted or partial project's programs: original C, Clight, "
                                  "refactored Clight")
    p_check.add_argument("-j", "--jobs", type=int, default=2,
                         help="projects processed in parallel (each may use refactor.memory_limit_mb)")

    args = parser.parse_args(argv)
    if args.command == "batch":
        try:
            from .experiments import run_experiments
            if args.max_runs is not None and args.max_runs < 1:
                raise ValueError("--max-runs must be positive")
            if args.prepare_only and args.dry_run:
                raise ValueError("choose --prepare-only or --dry-run")
            result = run_experiments(load_config(args.config, args.set), resolve(args.output),
                variants=[resolve(p) for p in args.variant], prepare_only=args.prepare_only,
                dry_run=args.dry_run, max_runs=args.max_runs)
            print(json.dumps(result, indent=2))
            return 0
        except KeyboardInterrupt:
            print("batch interrupted; completed rows are saved", file=sys.stderr)
            return 130
        except (OSError, ValueError, RuntimeError, ImportError) as exc:
            print(f"batch error: {exc}", file=sys.stderr)
            return 2
    if args.command == "model-check":
        try:
            import uuid
            from .llm import OpenRouterClient
            cfg = load_config(args.config, args.set)
            cfg.model.max_tokens = min(cfg.model.max_tokens, 128)
            cfg.model.temperature = 0
            if args.structured:
                cfg.model.response_format = "json_schema"
            directory = resolve(args.output) if args.output else resolve("results/model-check") / uuid.uuid4().hex[:12]
            schema = ({"type": "object", "additionalProperties": False, "required": ["status"],
                       "properties": {"status": {"type": "string", "enum": ["ok"]}}} if args.structured else None)
            messages = [{"role": "user", "content": 'Return only {"status":"ok"}.' if args.structured else 'Reply with only OK.'}]
            client = OpenRouterClient(cfg.model)
            try:
                completion = client.complete(messages, schema, seed=cfg.seeds[0], directory=directory,
                                             job_id="model-check", call_number=1)
            finally:
                client.close()
            valid = json.loads(completion.text) == {"status": "ok"} if args.structured else completion.text.strip() == "OK"
            print(json.dumps({"valid": valid, "model": completion.model, "usage": completion.usage,
                              "reported_cost": completion.cost, "directory": str(directory)}, indent=2))
            return 0 if valid and completion.finish_reason == "stop" else 1
        except (OSError, ValueError, RuntimeError, ImportError) as exc:
            print(f"model check error: {exc}", file=sys.stderr)
            return 2
    if args.command == "run":
        try:
            cfg = load_config(args.config, args.set)
            if args.rbench:
                cfg.benchmark.rust_project = str(resolve(args.rbench).resolve())
            if args.interface_file:
                cfg.translation.interface_files = [str(resolve(p).resolve()) for p in args.interface_file]
            if args.idiomatic_responses and not cfg.idiomatic_stage:
                raise ValueError("--idiomatic-responses requires idiomatic_stage=true")
            preview = args.prepare_only or args.dry_run
            client = ReplayClient(resolve(args.responses)) if args.responses and not preview else None
            stage_client = ReplayClient(resolve(args.idiomatic_responses)) if args.idiomatic_responses and not preview else None
            report = run_pipeline(resolve(args.directory), config=cfg, seed=args.seed,
                output=resolve(args.output) if args.output else None,
                compile_commands=resolve(args.compile_commands) if args.compile_commands else None,
                clang_args=args.clang_arg, prepare_only=args.prepare_only, dry_run=args.dry_run,
                max_jobs=args.max_jobs, retry_failed=args.retry_failed, skip_validation=args.skip_validation,
                client=client, idiomatic_client=stage_client)
            summary = {key: report[key] for key in ("project", "seed", "outcome", "rust", "report_path")}
            keep = {"refactor": ("status", "accepted", "original"),
                    "contexts": ("source_ready", "graph_complete", "jobs", "manifest", "completion_jobs", "initial_placeholders", "unmatched_placeholders", "interface_coverage"),
                    "translation": ("completed", "jobs", "model_calls", "reported_cost", "failure_stages", "recovered_jobs"),
                    "validation": ("outcome", "counts", "report_path"),
                    "idiomatic": ("outcome", "accepted", "candidate", "model_calls", "report_path"),
                    "metrics": ("raw_pointer_type_sites", "unsafe_keyword_sites", "report_path"),
                    "metrics_v2": ("raw_pointer_type_sites", "unsafe_keyword_sites", "report_path")}
            summary["stages"] = {stage: {k: data[k] for k in keep[stage] if k in data}
                                 for stage, data in report["stages"].items() if stage in keep}
            if report.get("errors"):
                summary["errors"] = report["errors"][:5]
            print(json.dumps(summary, indent=2, sort_keys=True))
            return 0 if report["outcome"] in {"completed", "prepared", "previewed", "compiled_only"} else 1
        except KeyboardInterrupt:
            print("pipeline interrupted; rerun the same command to resume", file=sys.stderr)
            return 130
        except (KeyError, OSError, ValueError, ImportError, RuntimeError) as exc:
            print(f"pipeline error: {exc}", file=sys.stderr)
            return 2
    if args.command == "run-state":
        try:
            run = RustProject(resolve(args.directory))
            if args.force_recover and not args.resume:
                raise ValueError("--force-recover requires --resume")
            if args.resume:
                run.resume(force_recover=args.force_recover)
            if args.retry:
                run.retry_job(args.retry)
            print(json.dumps(run.status() if args.json else run.summary(), indent=2, sort_keys=True))
            return 0
        except (KeyError, OSError, ValueError) as exc:
            print(f"state error: {exc}", file=sys.stderr)
            return 2
    if args.command == "validate":
        try:
            allowed = ("validation.", "tools.cargo=", "tools.rust_toolchain=", "benchmark.rust_dir=", "benchmark.rust_project=")
            if any(not setting.startswith(allowed) for setting in args.set):
                raise ValueError("validate permits validation.*, Cargo/toolchain and benchmark.rust_dir overrides")
            directory = resolve(args.directory)
            data = json.loads((directory / ".c2r/contexts/manifest.json").read_text())["config"]
            if args.config != str(MAIN_CONFIG):
                supplied = load_config(args.config)
                data["validation"] = to_dict(supplied)["validation"]
                data["benchmark"]["rust_dir"] = supplied.benchmark.rust_dir
                if supplied.benchmark.rust_project is not None:
                    data["benchmark"]["rust_project"] = supplied.benchmark.rust_project
                for key in ("cargo", "rust_toolchain"):
                    data["tools"][key] = getattr(supplied.tools, key)
            runtime = config_from_dict(data, args.set)
            report = validate_run(directory, config=runtime,
                                  output=resolve(args.output) if args.output else None, prepare_only=args.prepare_only)
            summary = {key: report[key] for key in ("project", "outcome", "counts", "programs_passed", "programs_failed", "report_path")}
            summary["translation_complete"] = report["source_snapshot"]["complete"]
            summary["feedback_to_model"] = False
            print(json.dumps(summary, indent=2, sort_keys=True))
            return 0 if report["outcome"] in {"passed", "prepared"} else 1 if report["outcome"] in {"test_failed", "compile_failed", "no_tests"} else 2
        except KeyboardInterrupt:
            print("validation interrupted; any completed evaluation logs were saved", file=sys.stderr)
            return 130
        except (KeyError, OSError, ValueError, ImportError, RuntimeError) as exc:
            print(f"validation error: {exc}", file=sys.stderr)
            return 2
    if args.command == "idiomatize":
        try:
            allowed = ("model.", "repair.", "runner.", "validation.", "tools.cargo=", "tools.rust_toolchain=", "benchmark.rust_dir=", "benchmark.rust_project=")
            if any(not setting.startswith(allowed) for setting in args.set):
                raise ValueError("idiomatize permits model/repair/runner/validation and Cargo/toolchain/benchmark overrides")
            directory = resolve(args.directory)
            data = json.loads((directory / ".c2r/contexts/manifest.json").read_text())["config"]
            if args.config != str(MAIN_CONFIG):
                supplied = to_dict(load_config(args.config))
                for section in ("model", "repair", "runner", "validation"):
                    data[section] = supplied[section]
                data["benchmark"]["rust_dir"] = supplied["benchmark"]["rust_dir"]
                if supplied["benchmark"].get("rust_project") is not None:
                    data["benchmark"]["rust_project"] = supplied["benchmark"]["rust_project"]
                for key in ("cargo", "rust_toolchain"):
                    data["tools"][key] = supplied["tools"][key]
            runtime = config_from_dict(data, args.set)
            client = ReplayClient(resolve(args.responses)) if args.responses and not args.dry_run else None
            report = idiomatize_run(directory, config=runtime, client=client,
                                    output=resolve(args.output) if args.output else None, dry_run=args.dry_run)
            print(json.dumps(report, indent=2, sort_keys=True))
            return 0 if report["outcome"] in {"accepted", "unchanged", "prepared"} else 1
        except KeyboardInterrupt:
            print("idiomatic refactoring interrupted; resume using the same v1 directory and settings", file=sys.stderr)
            return 130
        except (KeyError, OSError, ValueError, ImportError, RuntimeError) as exc:
            print(f"idiomatic error: {exc}", file=sys.stderr)
            return 2
    if args.command == "translate":
        try:
            allowed = ("model.", "repair.", "runner.", "validation.", "idiomatic_stage=", "tools.cargo=", "tools.rust_toolchain=")
            if any(not setting.startswith(allowed) for setting in args.set):
                raise ValueError("translate permits model/repair/runner/validation, idiomatic_stage and Cargo/toolchain overrides; source settings are frozen")
            directory = resolve(args.directory)
            source_cfg = read_translation_plan(directory / ".c2r/contexts").config
            data = to_dict(source_cfg)
            if args.config != str(MAIN_CONFIG):
                supplied = load_config(args.config)
                for section in ("model", "repair", "runner", "validation", "idiomatic_stage"):
                    data[section] = to_dict(supplied)[section]
                for key in ("cargo", "rust_toolchain"):
                    data["tools"][key] = getattr(supplied.tools, key)
            runtime = config_from_dict(data, args.set)
            client = ReplayClient(resolve(args.responses)) if args.responses and not args.dry_run else None
            if args.idiomatic_responses and not runtime.idiomatic_stage:
                raise ValueError("--idiomatic-responses requires idiomatic_stage=true")
            idiomatic_client = ReplayClient(resolve(args.idiomatic_responses)) if args.idiomatic_responses and not args.dry_run else None
            summary = translate_run(directory, config=runtime, client=client, max_jobs=args.max_jobs,
                                    dry_run=args.dry_run, retry_failed=args.retry_failed,
                                    idiomatic_client=idiomatic_client,
                                    progress=lambda text: print(text, flush=True))
            print(json.dumps(summary, indent=2, sort_keys=True))
            if args.dry_run:
                return 0 if summary["previews"] else 1
            if "idiomatic" in summary and not summary["idiomatic"]["accepted"]:
                return 1
            return 0 if summary["completed"] or (args.max_jobs is not None and summary["processed_jobs"] == args.max_jobs
                                                  and not summary["jobs"].get("failed")) else 1
        except KeyboardInterrupt:
            print("translation interrupted; progress is saved for the next invocation", file=sys.stderr)
            return 130
        except (KeyError, OSError, ValueError, ImportError, RuntimeError) as exc:
            print(f"translation error: {exc}", file=sys.stderr)
            return 2
    try:
        cfg = load_config(args.config, args.set)
    except (ConfigError, OSError) as exc:
        print(f"config error: {exc}", file=sys.stderr)
        return 2

    if args.command == "doctor":
        checks = doctor(cfg)
        width = max(len(c.name) for c in checks)
        for c in checks:
            print(f"[{c.status:4}] {c.name:<{width}}  {c.detail}")
        return 1 if any(c.status == FAIL for c in checks) else 0

    if args.command == "config":
        data = to_dict(cfg)
        print(json.dumps(data, indent=2) if args.json else yaml.safe_dump(data, sort_keys=False), end="")
        print(f"\n# experiment hash: {experiment_hash(cfg)}")
        return 0

    if args.command == "projects":
        projects = discover(resolve(cfg.benchmark.c_dir), resolve(cfg.benchmark.rust_dir))
        try:
            chosen = select(projects, cfg.projects)
        except KeyError as exc:
            print(f"config error: {exc.args[0]}", file=sys.stderr)
            return 2
        print(f"{'project':<44} {'rust crate':<44} {'.c':>4} {'tests':>5} {'.h':>4} {'iface':>5}")
        for p in chosen:
            crate = p.rust_dir.name if p.rust_dir else "-"
            print(f"{p.name:<44} {crate:<44} {len(p.c_sources):>4} {len(p.c_tests):>5} "
                  f"{len(p.headers):>4} {len(p.interfaces):>5}")
        print(f"\n{len(chosen)} project(s)")
        return 0

    if args.command == "refactor":
        def report(r):
            label = r.status
            if r.status == "partial":
                label += f" {sum(u.accepted for u in r.units)}/{len(r.units)}"
            flags = sorted({" ".join(u.flags) for u in r.units if u.flags} - {""})
            print(f"[{label}] {r.name}" + (f" ({', '.join(flags)})" if flags else ""), flush=True)
        try:
            status = refactor_all(cfg, jobs=args.jobs, progress=report)
        except KeyError as exc:
            print(f"config error: {exc.args[0]}", file=sys.stderr)
            return 2
        entries = status["projects"].values()
        count = {k: sum(e["status"] == k for e in entries) for k in ("accepted", "partial")}
        print(f"\n{count['accepted']} of {len(entries)} projects accepted, {count['partial']} partial; "
              f"see {resolve(cfg.output.refactored_dir) / 'README.md'}")
        return 0

    if args.command == "stats":
        out = resolve(args.output)
        rows = write_stats(cfg, out, progress=lambda name: print(name, flush=True))
        print(f"\n{len(rows)} projects; see {out} and {out.with_suffix('.md')}")
        return 0

    if args.command == "dependencies":
        try:
            chosen = select(discover(resolve(cfg.benchmark.c_dir), resolve(cfg.benchmark.rust_dir)), cfg.projects)
            if args.compile_commands and len(chosen) != 1:
                raise ValueError("--compile-commands requires exactly one selected project")
            status = json.loads(resolve(args.stage1_status).read_text()) if args.stage1_status else {}
            if not isinstance(status, dict) or not isinstance(status.get("projects", {}), dict):
                raise ValueError("stage-1 status must contain a projects mapping")
            output = resolve(args.output)
            incomplete = 0
            for project in chosen:
                saved = status.get("projects", {}).get(project.name, {})
                if not isinstance(saved, dict) or not isinstance(saved.get("units", []), list):
                    raise ValueError(f"stage-1 status for {project.name} must contain a units list")
                unit_args = {}
                for unit in saved.get("units", []):
                    if not isinstance(unit, dict):
                        raise ValueError("stage-1 unit records must be mappings")
                    if unit.get("accepted"):
                        flags = unit.get("flags") or []
                        if (not isinstance(unit.get("path"), str) or not isinstance(flags, list)
                                or not all(isinstance(flag, str) for flag in flags)):
                            raise ValueError("accepted stage-1 units need a path and a string list of flags")
                        unit_args[unit["path"]] = flags
                graph = build_project_graph(
                    cfg, project, clang_args=args.clang_arg, unit_args=unit_args,
                    compile_commands=resolve(args.compile_commands) if args.compile_commands else None)
                path = write_graph(graph, output / f"{project.name}.json")
                incomplete += not graph.complete
                label = "complete" if graph.complete else "incomplete"
                print(f"[{label}] {project.name}: {len(graph.items)} items, {len(graph.edges)} edges, "
                      f"{len(translation_order_with_candidates(graph))} groups; {path}", flush=True)
            print(f"\n{len(chosen)} projects, {incomplete} incomplete; orders for incomplete graphs are provisional")
            return 1 if incomplete else 0
        except (KeyError, OSError, ValueError, ImportError, RuntimeError) as exc:
            print(f"dependency error: {exc}", file=sys.stderr)
            return 2

    if args.command == "contexts":
        try:
            chosen = select(discover(resolve(cfg.benchmark.c_dir), resolve(cfg.benchmark.rust_dir)), cfg.projects)
            if (args.compile_commands or args.stage1_record) and len(chosen) != 1:
                raise ValueError("--compile-commands and --stage1-record require one selected project")
            failed = 0
            for project in chosen:
                plan = _prepare_contexts(cfg, project, args)
                destination = resolve(args.output) / project.name / experiment_hash(cfg)
                manifest = write_translation_plan(plan, destination)
                ready = sum(unit_ready(plan, unit) for unit in plan.units)
                blocked = not plan.complete or ready != len(plan.units)
                failed += blocked
                label = "blocked" if blocked else "prepared"
                print(f"[{label}] {project.name}: {len(plan.units)} jobs, {ready} ready, "
                      f"{plan.interface_mode} interfaces; {manifest}", flush=True)
                errors = [issue for issue in plan.issues if issue.severity == "error"]
                errors += [issue for unit in plan.units for issue in unit.issues if issue.severity == "error"]
                for issue in errors[:5]:
                    print(f"  {issue.code}: {issue.message}", flush=True)
            print(f"\n{len(chosen)} projects, {failed} blocked. No LLM calls were made.")
            return 1 if failed else 0
        except (KeyError, OSError, ValueError, ImportError, RuntimeError) as exc:
            print(f"context error: {exc}", file=sys.stderr)
            return 2

    if args.command == "scaffold":
        try:
            if args.contexts and (args.compile_commands or args.clang_arg or any(
                    not (setting.split("=", 1)[0].startswith("rust_project.")
                         or setting.split("=", 1)[0] in {"seeds", "output.runs_dir"}) for setting in args.set)):
                raise ValueError("with --contexts, use the saved translation settings; only rust_project.*, seeds "
                                 "and output.runs_dir overrides apply")
            blocked = 0
            def scaffold_contexts(path):
                nonlocal blocked
                manifest_path = path if path.is_file() else path / "manifest.json"
                manifest = json.loads(manifest_path.read_text())
                run_cfg = (config_from_dict(manifest["config"], args.set)
                           if args.contexts and args.config == str(MAIN_CONFIG) else cfg)
                seeds = [args.seed] if args.seed is not None else run_cfg.seeds
                output = resolve(args.output or run_cfg.output.runs_dir)
                for seed in seeds:
                    destination = output / manifest["project"] / manifest["experiment_hash"] / f"seed-{seed}" / "rust"
                    run = initialize_project(path, destination, seed=seed, options=run_cfg.rust_project)
                    summary = run.summary()
                    blocked += bool(summary["jobs"].get("blocked"))
                    print(f"[scaffolded] {summary['project']} seed {seed}: {summary['jobs']}, "
                          f"{len(summary['ready_jobs'])} ready; {run.root}", flush=True)
            if args.contexts:
                scaffold_contexts(resolve(args.contexts))
            else:
                chosen = select(discover(resolve(cfg.benchmark.c_dir), resolve(cfg.benchmark.rust_dir)), cfg.projects)
                if (args.compile_commands or args.stage1_record) and len(chosen) != 1:
                    raise ValueError("--compile-commands and --stage1-record require one selected project")
                for project in chosen:
                    plan = _prepare_contexts(cfg, project, args)
                    with tempfile.TemporaryDirectory(prefix="c2r-scaffold-") as tmp:
                        write_translation_plan(plan, Path(tmp))
                        scaffold_contexts(Path(tmp))
            print("\nScaffolding/state only: no model calls, code generation or compiler repairs.")
            return 1 if blocked else 0
        except (KeyError, OSError, ValueError, ImportError, RuntimeError) as exc:
            print(f"scaffold error: {exc}", file=sys.stderr)
            return 2

    if args.command == "check-refactor":
        try:
            records = run_stage1(cfg, jobs=args.jobs, objects=True)
        except KeyError as exc:
            print(f"config error: {exc.args[0]}", file=sys.stderr)
            return 2

        def report_project(name, checks):
            outcomes = ", ".join(sorted({c.outcome for c in checks})) or "no programs"
            print(f"[{outcomes}] {name}", flush=True)
        report = check_all(cfg, records, jobs=args.jobs, progress=report_project)
        path = write_report(cfg, report)
        o = report["summary"]["outcomes"]
        print(f"\n{report['summary']['programs']} programs: {o.get(EQUAL, 0)} same behavior, "
              f"{o.get(CHANGED, 0)} changed by the refactoring; see {path}")
        return 1 if o.get(CHANGED, 0) else 0
    return 2


if __name__ == "__main__":
    sys.exit(main())
