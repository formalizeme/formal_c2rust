"""Complete Rust items in fenced blocks, installed by AST function identity.

Code is emitted once. Small items=[...] block headers associate source IDs;
artifact snippets and body edits are derived locally after parsing.
"""

from __future__ import annotations

import json
import re

from .interfaces import definitions
from .rust_edits import TranslationResponse, _parse, edited_sources, validate_rust
from .rust_project import _relative


GUIDE = (
    'Return complete Rust items in fenced blocks: ```rust\npath=src/module.rs items=["SOURCE_ID"]\n'
    'fn ... { ... }\n```. Put methods inside their matching impl header (including the trait when applicable). '
    'Each source item ID must occur in exactly one block header; several IDs can share a block '
    'when their C responsibilities are absorbed into the same Rust implementation. '
    'Use items=[] for extra private helpers. Preserve existing function signatures exactly. '
    'Return Rust code once; do not return JSON strings, replace.old, or repeated artifact code. '
    'Only the matching function bodies will be replaced. New helpers must be private. '
    'For an already provided type/constant, returning its unchanged complete item is allowed. '
    'Use fully qualified paths rather than adding use declarations or modules. '
    'Never alter benchmark tests or leave todo!()/unimplemented!() in a returned item.'
)


def parse_fixed_response(text: str, item_ids: list[str], current: dict[str, str],
                         expected_public_targets: dict[str, list[str]] | None = None,
                         expected_paths: dict[str, str] | None = None) -> TranslationResponse:
    edits, blocks, covered, touched = [], [], set(), set()
    pattern = r"^[ \t]*(?P<fence>`{3,})[ \t]*(?:rust|rs)\b(?P<header>[^\n]*)\n(?P<code>.*?)^[ \t]*(?P=fence)[ \t]*$"
    for match in re.finditer(pattern, text, re.S | re.M | re.I):
        header = match["header"]
        body = match["code"]
        # Providers commonly put fence attributes on the first body line.
        # Consume only explicit path/items metadata, never infer missing IDs.
        while not (re.search(r"\bitems\s*=", header) and re.search(r"\bpath\s*=", header)):
            line, separator, rest = body.lstrip("\r\n").partition("\n")
            if not separator or not re.match(r"[ \t]*(?:path|items)\s*=", line):
                break
            header += " " + line.strip()
            body = rest
        item_header = re.search(r"\bitems\s*=\s*", header)
        if item_header is None:
            raise ValueError("Rust fence header needs items=[...]")
        ids, consumed = json.JSONDecoder().raw_decode(header[item_header.end():])
        rest = header[:item_header.start()] + header[item_header.end() + consumed:]
        path_header = re.search(r'''\bpath\s*=\s*(?:"([^"]+)"|'([^']+)'|([^\s]+))''', rest)
        if path_header is None:
            raise ValueError("Rust fence header needs path=src/...rs")
        path = _relative(next(value for value in path_header.groups() if value is not None), rust=True)
        if (not isinstance(ids, list) or not all(isinstance(i, str) for i in ids)
                or len(set(ids)) != len(ids) or set(ids) & covered or set(ids) - set(item_ids)):
            raise ValueError("fixed block items must be unique source IDs from the current job")
        covered.update(ids)
        code = body.strip()
        validate_rust(code, path, artifact=True)
        _, root = _parse(code, path)
        if any(n.type in {"use_declaration", "mod_item", "macro_definition", "macro_invocation"}
               for n in root.named_children):
            raise ValueError("fixed blocks support complete functions, impl methods and private type/constant helpers; use fully qualified paths")
        emitted = definitions(code, path)
        if not emitted:
            raise ValueError("a fixed block must contain complete named Rust items")
        existing = definitions(edited_sources(current, edits).get(path, ""), path)
        targets = []
        for definition in emitted:
            if (path, definition.target) in touched:
                raise ValueError(f"duplicate returned definition: {definition.target}")
            touched.add((path, definition.target))
            candidates = [d for d in existing if d.target == definition.target and d.kind == definition.kind]
            if len(candidates) > 1:
                raise ValueError(f"ambiguous fixed Rust target: {definition.target}")
            if candidates:
                original = candidates[0]
                if definition.signature != original.signature:
                    raise ValueError(f"fixed signature/declaration changed: {definition.target}")
                if definition.kind == "function_item":
                    data = definition.code.encode()
                    offset = definition.body_start - definition.start
                    end = definition.body_end - definition.start
                    edits.append({"path": path, "operation": "function", "old": definition.target,
                                  "new": data[offset:end].decode()})
                elif definition.code != original.code:
                    # Token comparison above permits harmless whitespace only;
                    # preserve the installed declaration verbatim.
                    pass
            else:
                data, root = _parse(definition.code, path)
                item = next(n for n in root.named_children if n.type.endswith("_item"))
                if any(child.type == "visibility_modifier" for child in item.named_children):
                    raise ValueError(f"new helper must be private: {definition.target}")
                source = (definition.attributes + "\n" if definition.attributes else "") + definition.code
                if definition.container:
                    source = definition.container + " {\n" + source + "\n}"
                snapshot = edited_sources(current, edits)
                edits.append({"path": path, "operation": "append" if path in snapshot else "create",
                              "old": "", "new": "\n" + source + "\n"})
            targets.append(definition.target)
        for item in ids:
            required = set((expected_public_targets or {}).get(item, []))
            if required - set(targets):
                raise ValueError(f"{item}: return its mapped public target(s): {sorted(required)}")
            if required and (expected_paths or {}).get(item) and expected_paths[item] != path:
                raise ValueError(f"{item}: mapped public target belongs in {expected_paths[item]}")
        blocks.append((path, ids, targets))
    if covered != set(item_ids):
        raise ValueError("return fenced Rust blocks with path= and items=[...] covering every source item exactly once")
    candidate = edited_sources(current, edits)
    artifacts = {}
    for path, ids, targets in blocks:
        installed = {d.target: d for d in definitions(candidate[path], path)}
        for item in ids:
            # A complete installed item is the recovery anchor; all associated
            # function names are retained as target metadata without duplicating output.
            anchor = next((t for t in targets if installed[t].kind == "function_item"), targets[0])
            representative = installed[anchor]
            artifacts[item] = {"path": path, "code": representative.code, "rust_targets": targets,
                               "definitions": {target: installed[target].code for target in targets}}
    return TranslationResponse(edits, artifacts, "AST-addressed fixed-interface response")
