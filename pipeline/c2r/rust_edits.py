"""Structured Rust edits, syntactic interface checks and reversible batches."""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass
from functools import cache
from pathlib import Path

from .rust_project import RustProject, _atomic_json, _atomic_write, _inside, _sha, _relative, _wire_modules


@cache
def _language():
    from tree_sitter import Language
    import tree_sitter_rust
    return Language(tree_sitter_rust.language())


def _parse(code: str, label: str):
    from tree_sitter import Parser
    data = code.encode()
    tree = Parser(_language()).parse(data)
    if tree.root_node.has_error:
        pending, errors = [tree.root_node], []
        while pending and len(errors) < 6:
            node = pending.pop()
            if node.type == "ERROR" or node.is_missing:
                errors.append(f"{label}:{node.start_point.row + 1}:{node.start_point.column + 1}: {node.type}")
            pending.extend(reversed(node.children))
        raise ValueError("Rust syntax error: " + "; ".join(errors))
    return data, tree.root_node


def _tokens(node, data: bytes, excluded=None) -> tuple[str, ...]:
    if node == excluded or node.type in {"line_comment", "block_comment"}:
        return ()
    if not node.children or node.type in {"string_literal", "raw_string_literal", "char_literal"}:
        return (data[node.start_byte:node.end_byte].decode(),)
    return tuple(token for child in node.children for token in _tokens(child, data, excluded))


def _contract(code: str, label: str) -> Counter:
    data, root = _parse(code, label)
    result = Counter()
    def scope(node, context=()):
        attributes = []
        for item in node.named_children:
            if item.type in {"line_comment", "block_comment"}:
                continue
            if item.type == "attribute_item":
                attributes.extend(_tokens(item, data))
                continue
            body = item.child_by_field_name("body")
            name_node = item.child_by_field_name("name")
            name = data[name_node.start_byte:name_node.end_byte].decode() if name_node else ""
            container = item.type in {"impl_item", "trait_item", "mod_item"} and body is not None
            omitted = body if container or item.type == "function_item" else None
            signature = (*attributes, *_tokens(item, data, omitted))
            result[(context, item.type, name, signature)] += 1
            attributes = []
            if container:
                scope(body, (*context, (item.type, signature)))
    scope(root)
    return result


def public_contract(code: str, label: str) -> Counter:
    """Conservative API surface, with function bodies omitted.

    Keep public declarations, re-exports, exported macros and trait impls.
    Context includes enclosing module/impl headers, so visibility and receiver
    types remain part of the contract. Private helper functions may change.
    """
    return Counter({key: count for key, count in _contract(code, label).items()
                    if "pub" in key[3] or "macro_export" in key[3]
                    or (key[1] == "impl_item" and "for" in key[3])
                    or any(kind == "trait_item" and "pub" in signature for kind, signature in key[0])
                    or any(kind == "impl_item" and "for" in signature for kind, signature in key[0])})


def validate_rust(code: str, label: str, *, artifact: bool = False) -> None:
    data, root = _parse(code, label)
    if artifact and not any(n.type.endswith("_item") or n.type in {"macro_definition", "use_declaration"}
                            for n in root.named_children):
        raise ValueError(f"{label}: artifact must contain a complete Rust item, not a comment or expression")
    pending = [root]
    while pending:
        node = pending.pop()
        if node.type == "unsafe":
            raise ValueError(f"{label}: unsafe Rust is not permitted")
        if artifact and node.type == "macro_invocation":
            macro = node.child_by_field_name("macro")
            name = data[macro.start_byte:macro.end_byte].decode().split("::")[-1].strip().removeprefix("r#") if macro else ""
            if name in {"todo", "unimplemented"}:
                raise ValueError(f"{label}: a completed artifact still contains {name}!()")
        if node.type not in {"line_comment", "block_comment", "string_literal", "raw_string_literal", "char_literal"}:
            pending.extend(node.children)


def source_files(run: RustProject) -> dict[str, str]:
    files = {}
    for path in sorted((run.root / "src").rglob("*.rs")):
        rel = path.relative_to(run.root).as_posix()
        if path.is_symlink() or any(p.is_symlink() for p in path.parents if p != run.root and p.is_relative_to(run.root)):
            raise ValueError(f"symlinked Rust sources are unsupported for transactional edits: {rel}")
        files[rel] = _inside(run.root, rel).read_text()
    return files


def response_schema(item_ids: list[str]) -> dict:
    return {"type": "object", "additionalProperties": False, "required": ["edits", "items", "notes"],
            "properties": {
                "edits": {"type": "array", "items": {"type": "object", "additionalProperties": False,
                    "required": ["path", "operation", "old", "new"], "properties": {
                        "path": {"type": "string"}, "operation": {"type": "string", "enum": ["replace", "append", "create"]},
                        "old": {"type": "string"}, "new": {"type": "string"}}}},
                "items": {"type": "array", "items": {"type": "object", "additionalProperties": False,
                    "required": ["item_id", "path", "code", "rust_targets"], "properties": {
                        "item_id": {"type": "string", "enum": item_ids}, "path": {"type": "string"},
                        "code": {"type": "string"},
                        "rust_targets": {"type": "array", "items": {"type": "string"}}}}}, "notes": {"type": "string"}}}


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


@dataclass
class TranslationResponse:
    edits: list[dict]
    artifacts: dict[str, dict]
    notes: str


def parse_response(text: str, item_ids: list[str]) -> TranslationResponse:
    text = text.strip()
    if text.startswith("```") and text.endswith("```"):
        text = text.split("\n", 1)[1].rsplit("```", 1)[0]
    data = json.loads(text, object_pairs_hook=_unique_object)
    if not isinstance(data, dict) or set(data) != {"edits", "items", "notes"}:
        raise ValueError("response must contain exactly edits, items and notes")
    if not isinstance(data["edits"], list) or not isinstance(data["items"], list) or not isinstance(data["notes"], str):
        raise ValueError("edits/items must be arrays and notes must be text")
    for edit in data["edits"]:
        if (not isinstance(edit, dict) or set(edit) != {"path", "operation", "old", "new"}
                or not all(isinstance(v, str) for v in edit.values())
                or edit["operation"] not in {"replace", "append", "create"}):
            raise ValueError("each edit needs path, operation (replace/append/create), old and new strings")
        edit["path"] = _relative(edit["path"], rust=True)
    artifacts = {}
    for artifact in data["items"]:
        if (not isinstance(artifact, dict) or set(artifact) != {"item_id", "path", "code", "rust_targets"}
                or not all(isinstance(artifact[k], str) for k in ("item_id", "path", "code")) or not artifact["code"]
                or not isinstance(artifact["rust_targets"], list)
                or not all(isinstance(t, str) for t in artifact["rust_targets"])):
            raise ValueError("each item needs item_id, path, installed Rust code and a rust_targets string list")
        key = artifact["item_id"]
        if key in artifacts:
            raise ValueError(f"duplicate source item: {key}")
        artifacts[key] = {"path": _relative(artifact["path"], rust=True), "code": artifact["code"],
                          "rust_targets": artifact["rust_targets"]}
    if set(artifacts) != set(item_ids):
        raise ValueError("items must account for every source item in this job, and no others")
    return TranslationResponse(data["edits"], artifacts, data["notes"])


def begin_transaction(run: RustProject, job_id: str) -> None:
    with run._locked() as state:
        run._running_job(state, job_id)
        path = _inside(run.root, ".c2r/active_edit.json")
        if path.exists():
            raise ValueError("an edit transaction already exists; resume the run first")
        files = source_files(run)
        _atomic_json(path, {"job_id": job_id, "files": files, "registry": state["files"],
                           "placements": state["placements"],
                           "expected": {p: [_sha(code.encode())] for p, code in files.items()}})


def edited_sources(current: dict[str, str], edits: list[dict]) -> dict[str, str]:
    candidate = dict(current)
    for edit in edits:
        path, old, new, operation = edit["path"], edit["old"], edit["new"], edit["operation"]
        _relative(path, rust=True)
        if operation == "function":  # Internal AST-addressed operation, not JSON edit input.
            from .interfaces import definitions
            matches = [d for d in definitions(candidate.get(path, ""), path)
                       if d.kind == "function_item" and d.target == old]
            if len(matches) != 1:
                raise ValueError(f"{path}: expected a unique function {old}")
            definition = matches[0]
            data = candidate[path].encode()
            candidate[path] = (data[:definition.body_start] + new.encode() + data[definition.body_end:]).decode()
        elif operation == "replace":
            position = candidate.get(path, "").find(old) if old else -1
            if position < 0 or candidate[path].find(old, position + 1) >= 0:
                raise ValueError(f"{path}: replace.old must match exactly once in the current file")
            candidate[path] = candidate[path].replace(old, new, 1)
        elif operation == "append":
            if old or path not in candidate:
                raise ValueError(f"{path}: append requires an existing file and an empty old string")
            candidate[path] += new
        elif operation == "create":
            if old or path in candidate:
                raise ValueError(f"{path}: create requires a new file and an empty old string")
            candidate[path] = new
        else:
            raise ValueError(f"unsupported edit operation: {operation}")
    return candidate


def apply_response(run: RustProject, job_id: str, response: TranslationResponse, *, max_files: int) -> dict[str, str]:
    with run._locked() as state:
        run._running_job(state, job_id)
        journal_path = _inside(run.root, ".c2r/active_edit.json")
        journal = json.loads(journal_path.read_text())
        if journal["job_id"] != job_id:
            raise ValueError("edit transaction belongs to another job")
        current = source_files(run)
        if len({edit["path"] for edit in response.edits}) > max_files:
            raise ValueError(f"response edits more than {max_files} files")
        for edit in response.edits:
            _inside(run.root, edit["path"])
        candidate = edited_sources(current, response.edits)
        _wire_modules(candidate, public=state["interface_mode"] == "free" and state["options"]["public_modules"])
        for path, code in candidate.items():
            validate_rust(code, path)
        if state["interface_mode"] == "fixed":
            contracts = json.loads(_inside(run.root, ".c2r/interfaces.json").read_text())["interfaces"]
            for origin, baseline in contracts.items():
                path = state["metadata"]["interface_destinations"][origin]
                missing = _contract(baseline, origin) - _contract(candidate[path], path)
                if missing:
                    example = next(iter(missing))
                    raise ValueError(f"{path}: fixed interface changed or disappeared ({example[1]} {example[2]})")
        for key, artifact in state["artifacts"].items():
            if artifact["code"] not in candidate.get(artifact["path"], ""):
                raise ValueError(f"edit changes previously completed item {key}; backtracking is not enabled")
            if any(code not in candidate.get(artifact["path"], "") for code in artifact.get("definitions", {}).values()):
                raise ValueError(f"edit changes a completed definition for {key}; backtracking is not enabled")
        for key, artifact in response.artifacts.items():
            if artifact["code"] not in candidate.get(artifact["path"], ""):
                raise ValueError(f"{key}: code is not present in its declared Rust file")
            validate_rust(artifact["code"], key, artifact=True)
        # Write-ahead hashes allow recovery if a process stops between files.
        for path, code in candidate.items():
            journal["expected"].setdefault(path, []).append(_sha(code.encode()))
        _atomic_json(journal_path, journal)
        for path, code in sorted(candidate.items(), key=lambda pair: -pair[0].count("/")):
            if current.get(path) != code:
                _atomic_write(_inside(run.root, path), code.encode(), mode=0o644)
            state["files"].setdefault(path, {"initial_sha256": _sha(code.encode())})
        run._save(state, "edits_applied", job=job_id, files=[p for p in candidate if current.get(p) != candidate[p]])
        return candidate


def recover_transaction(run: RustProject, state: dict) -> bool:
    """Called with the checkpoint lock held, after its owner has stopped."""
    path = _inside(run.root, ".c2r/active_edit.json")
    if not path.exists():
        return False
    journal = json.loads(path.read_text())
    job = state["jobs"][journal["job_id"]]
    if job["status"] == "completed":
        path.unlink()  # Completion was committed before interruption.
        return True
    current = source_files(run)
    for name, content in current.items():
        expected = journal["expected"].get(name)
        if expected is None or _sha(content.encode()) not in expected:
            raise ValueError(f"{name}: edited outside the active transaction; refusing to overwrite it during recovery")
    for name in set(journal["files"]) - current.keys():
        raise ValueError(f"{name}: removed outside the active transaction; restore it before resuming")
    for name, code in journal["files"].items():
        _atomic_write(_inside(run.root, name), code.encode(), mode=0o644)
    for name in current.keys() - journal["files"].keys():
        _inside(run.root, name).unlink()
    state["files"] = journal["registry"]
    state["placements"] = journal["placements"]
    path.unlink()
    return True


def finish_transaction(run: RustProject, job_id: str, *, commit: bool) -> None:
    with run._locked() as state:
        path = _inside(run.root, ".c2r/active_edit.json")
        if not path.exists():
            return
        if json.loads(path.read_text())["job_id"] != job_id:
            raise ValueError("edit transaction belongs to another job")
        if state["jobs"][job_id]["status"] == "in_progress":
            run._running_job(state, job_id)
        if commit:
            if state["jobs"][job_id]["status"] != "completed":
                raise ValueError("only a completed job can commit its edits")
            path.unlink()
        else:
            recover_transaction(run, state)
        run._save(state, "edits_committed" if commit else "edits_rolled_back", job=job_id)
