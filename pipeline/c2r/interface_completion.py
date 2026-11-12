"""Plan and rescan final per-file jobs for fixed Rust API placeholders.

Rust-only items stay separate from the original-C graph. A completion job owns
all initially unfinished interface functions in one file; at runtime its request
contains only the functions that are still unfinished after the C jobs.
"""

from __future__ import annotations

import hashlib
from dataclasses import replace
from difflib import SequenceMatcher

from .dependencies import Item, SourceLocation
from .interfaces import definitions, destination_path, normalized
from .rust_edits import source_files


def add_completion_jobs(plan, item_map: dict) -> None:
    from .translation_units import TranslationUnit
    source_jobs = [unit.id for unit in plan.units]
    rows = []
    c_functions = [i for i in plan.graph.items.values() if i.kind == "function" and not i.external]
    for interface in sorted(plan.interfaces, key=lambda f: f.path):
        path = destination_path(interface.path, plan.config.rust_project)
        placeholders = [d for d in definitions(interface.code, interface.path)
                        if d.kind == "function_item" and d.placeholder]
        if not placeholders:
            continue
        items, targets, files, references = [], {}, {}, {}
        for definition in placeholders:
            digest = hashlib.sha256(f"{interface.path}\0{definition.target}\0{definition.start}".encode()).hexdigest()[:20]
            key = f"interface:{digest}"
            items.append(key)
            targets[key], files[key] = [definition.target], path
            location = SourceLocation(interface.path, interface.code.encode()[:definition.start].count(b"\n") + 1, 1, definition.start)
            plan.interface_items[key] = Item(key, definition.target, "interface_function", location,
                linkage="external", is_definition=True, source=definition.code,
                source_start=definition.start, source_end=definition.end)
            matched = sorted(k for k, mapping in item_map.items()
                if definition.target in mapping.get("rust_targets", []) and mapping.get("rust_file", path) == path
                and k in plan.graph.items and plan.graph.items[k].kind == "function")
            related = list(matched)
            if not related:
                ranked = sorted(((SequenceMatcher(None, normalized(i.name), normalized(definition.target)).ratio(), i.id)
                                 for i in c_functions), reverse=True)
                related = [key for score, key in ranked[:2] if score >= 0.55]
            references[key] = related
            rows.append({"item_id": key, "file": path, "interface_file": interface.path,
                         "target": definition.target, "matched_c_items": matched,
                         "related_c_items": related, "unmatched": not bool(matched)})
        digest = hashlib.sha256(path.encode()).hexdigest()[:12]
        job_id = f"interface-{len(plan.units):04}-{digest}"
        unit = TranslationUnit(job_id, len(plan.units), items, list(source_jobs), [], [], [], [], targets,
                               rust_files=files, kind="interface_completion", completion_sources=references)
        plan.units.append(unit)
        source_jobs.append(job_id)  # deterministic final-file ordering, including cross-file helpers
    plan.interface_coverage = {"initial_placeholders": len(rows),
        "matched_placeholders": sum(not row["unmatched"] for row in rows),
        "unmatched_placeholders": sum(row["unmatched"] for row in rows), "functions": rows,
        "notes": ["Unmatched names still have final completion jobs.",
                  "Related-name suggestions are context, not asserted semantic matches.",
                  "Completion requests rescan the installed crate and skip already implemented functions."]}


def pending_completion(plan, unit, working):
    """Return the remaining request and artifacts already implemented by C jobs."""
    from .translation_units import _deduplicate, compact_context
    current = source_files(working)
    indexed = {path: {d.target: d for d in definitions(code, path)} for path, code in current.items()}
    pending, installed = [], {}
    for key in unit.item_ids:
        path, target = unit.rust_files[key], unit.rust_targets[key][0]
        definition = indexed.get(path, {}).get(target)
        if definition is None:
            raise ValueError(f"interface function disappeared: {path}: {target}")
        if definition.placeholder:
            pending.append(key)
        else:
            installed[key] = {"path": path, "code": definition.code, "rust_targets": [target],
                              "definitions": {target: definition.code}}
    references = sorted({key for item in pending for key in unit.completion_sources.get(item, [])})
    context = []
    for source_unit in plan.units:
        if source_unit.kind != "source":
            continue
        chosen = [snippet for snippet in source_unit.sources if set(snippet.item_ids) & set(references)]
        if chosen:
            context += [replace(snippet, role="dependency") for snippet in chosen]
            context += [snippet for snippet in source_unit.context
                        if snippet.role in {"lowered_declaration", "lowered_helper", "source_declaration"}]
    context = compact_context(_deduplicate(context), plan.graph,
        plan.config.translation.max_prompt_chars // 4 if plan.config.translation.max_prompt_chars is not None else None)
    request = replace(unit, item_ids=pending, context=context,
                      dependency_ids=references, rust_dependency_ids=[])
    return request, installed


def coverage_report(plan, working) -> dict:
    current = source_files(working)
    entries, missing_files = [], []
    initial = sum(d.kind == "function_item" and d.placeholder
                  for f in plan.interfaces for d in definitions(f.code, f.path))
    for interface in plan.interfaces:
        path = destination_path(interface.path, plan.config.rust_project)
        if path not in current:
            missing_files.append(path)
            entries += [{"file": path, "target": d.target, "reason": "missing_file"}
                        for d in definitions(interface.code, interface.path)
                        if d.kind == "function_item" and d.placeholder]
            continue
        for definition in definitions(current[path], path):
            if definition.kind == "function_item" and definition.placeholder:
                entries.append({"file": path, "target": definition.target})
    return {"initial_placeholders": initial, "unmatched_placeholders": 0, **plan.interface_coverage,
            "remaining_placeholders": len(entries), "remaining": entries,
            "missing_files": missing_files, "interface_complete": not entries and not missing_files}


def reconcile_source_jobs(plan, working, check, *, progress=print) -> list[str]:
    """Recover failed source jobs whose exact targets were installed by completion.

    Name suggestions are insufficient: every source item and every planned Rust
    target must have a recorded, completed interface-job artifact. Compilation
    is rechecked under the checkpoint lock before accepting the recovery.
    """
    from .rust_edits import validate_rust
    from .rust_project import _now, _sha

    if plan.interface_mode != "fixed":
        return []
    with working._locked() as state:
        failed = {key: job for key, job in state["jobs"].items()
                  if job["status"] == "failed" and job.get("kind", "source") == "source"}
        if not failed or any(job["status"] == "in_progress" for job in state["jobs"].values()):
            return []
        if (working.root / ".c2r/active_edit.json").exists():
            raise ValueError("recover the active edit transaction before reconciling source jobs")
        completed = {item: key for key, job in state["jobs"].items()
                     if job.get("kind") == "interface_completion" and job["status"] == "completed"
                     and job.get("validation", {}).get("cargo_check", {}).get("success")
                     for item in job["item_ids"]}
        if not completed:
            return []
        current = source_files(working)
        indexed = {path: {d.target: d for d in definitions(code, path)} for path, code in current.items()}
        rows = plan.interface_coverage.get("functions", [])
        recoverable = {}
        for key, job in failed.items():
            artifacts, completion_jobs = {}, set()
            for item in job["item_ids"]:
                source = plan.graph.items.get(item)
                placement = state["placements"].get(item, {})
                path, targets = placement.get("path"), placement.get("rust_targets", [])
                if source is None or source.kind != "function" or not targets or path not in state["files"]:
                    break
                installed = {}
                for target in targets:
                    matches = [row for row in rows if item in row.get("matched_c_items", [])
                               and row["target"] == target and row["file"] == path
                               and row["item_id"] in completed]
                    if len(matches) != 1:
                        break
                    row = matches[0]
                    artifact = state["artifacts"].get(row["item_id"], {})
                    definition = indexed.get(path, {}).get(target)
                    if (definition is None or definition.placeholder or artifact.get("path") != path
                            or artifact.get("definitions", {}).get(target) != definition.code):
                        break
                    validate_rust(definition.code, f"{path}: {target}", artifact=True)
                    installed[target] = definition.code
                    completion_jobs.add(completed[row["item_id"]])
                if len(installed) != len(targets):
                    break
                # Keep one contiguous source anchor; definitions track all targets.
                code = next(iter(installed.values()))
                artifacts[item] = {"path": path, "code": code, "definitions": installed,
                                   "sha256": _sha(code.encode())}
            if job["item_ids"] and set(artifacts) == set(job["item_ids"]):
                recoverable[key] = (artifacts, sorted(completion_jobs))
        if not recoverable:
            return []
        progress(f"[translate] checking interface completion recovery for {len(recoverable)} source job(s)")
        details = check(working.root / ".c2r/recovery" / f"revision-{state['revision']:06}")
        if details.get("environment_error"):
            from .runtime import InfrastructureError
            raise InfrastructureError(details["diagnostics"])
        if not details.get("success"):
            progress("[translate] recovery compiler check failed; source jobs remain failed")
            return []
        cargo_hash = _sha((working.root / "Cargo.toml").read_bytes())
        lock_path = working.root / "Cargo.lock"
        lock_hash = _sha(lock_path.read_bytes()) if lock_path.is_file() else None
        for key, (artifacts, completion_jobs) in recoverable.items():
            job = state["jobs"][key]
            recovery = {"kind": "interface_completion", "completion_jobs": completion_jobs,
                        "previous_error": job.get("last_error"), "previous_validation": job.get("validation", {})}
            state["artifacts"].update(artifacts)
            job.update(status="completed", owner=None, completed_at=_now(), last_error=None,
                       recovery=recovery, cargo_manifest_sha256=cargo_hash, cargo_lock_sha256=lock_hash,
                       validation={"cargo_check": details, "recovered_by": completion_jobs,
                                   "semantic_validation": "not performed"})
        recovered = sorted(recoverable)
        working._save(state, "source_jobs_recovered", jobs=recovered,
                      recoveries={key: state["jobs"][key]["recovery"] for key in recovered})
    working.write_artifact_context()
    progress(f"[translate] recovered source jobs: {', '.join(recovered)}")
    return recovered
