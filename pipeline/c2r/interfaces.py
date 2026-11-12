"""Rust interface inventory and conservative, recorded C-to-Rust name matches."""

from __future__ import annotations

import re
from pathlib import PurePosixPath
from dataclasses import dataclass

from .rust_edits import _parse, _tokens


def _placeholder(node, data: bytes) -> bool:
    pending = [node]
    while pending:
        current = pending.pop()
        if current.type == "macro_invocation":
            macro = current.child_by_field_name("macro")
            name = data[macro.start_byte:macro.end_byte].decode().split("::")[-1] if macro else ""
            if name.removeprefix("r#") in {"todo", "unimplemented"}:
                return True
        if current.type not in {"line_comment", "block_comment", "string_literal", "raw_string_literal", "char_literal"}:
            pending.extend(current.children)
    return False


@dataclass
class Definition:
    path: str
    target: str
    name: str
    kind: str
    code: str
    signature: tuple[str, ...]
    start: int
    end: int
    body_start: int | None
    body_end: int | None
    placeholder: bool
    container: str = ""
    attributes: str = ""


def definitions(code: str, path: str) -> list[Definition]:
    data, root = _parse(code, path)
    found = []
    def visit(node, prefix="", container=""):
        attributes = []
        for item in node.named_children:
            if item.type == "attribute_item":
                attributes.append(data[item.start_byte:item.end_byte].decode())
                continue
            if item.type in {"line_comment", "block_comment"}:
                continue
            attached = "\n".join(attributes)
            attributes = []
            name = item.child_by_field_name("name")
            body = item.child_by_field_name("body")
            if item.type == "impl_item" and body is not None:
                typ = item.child_by_field_name("type")
                text = data[typ.start_byte:typ.end_byte].decode() if typ else ""
                text = re.sub(r"<.*>", "", text).strip().split("::")[-1]
                trait = item.child_by_field_name("trait")
                if trait is not None:
                    trait_name = re.sub(r"\s+", "", data[trait.start_byte:trait.end_byte].decode())
                    text = f"<{text} as {trait_name}>"
                visit(body, prefix + text + "::", data[item.start_byte:body.start_byte].decode())
            elif item.type == "mod_item" and body is not None and name is not None:
                visit(body, prefix + data[name.start_byte:name.end_byte].decode() + "::")
            elif name is not None and item.type in {
                    "function_item", "struct_item", "enum_item", "union_item", "type_item",
                    "const_item", "static_item", "trait_item"}:
                label = data[name.start_byte:name.end_byte].decode().removeprefix("r#")
                source = data[item.start_byte:item.end_byte].decode()
                function = item.type == "function_item"
                found.append(Definition(path, prefix + label, label, item.type, source,
                    _tokens(item, data, body if function else None), item.start_byte, item.end_byte,
                    body.start_byte if function and body else None, body.end_byte if function and body else None,
                    _placeholder(item, data), container, attached))
    visit(root)
    return found


def normalized(name: str) -> str:
    return re.sub(r"[^a-z0-9]", "", name.lower())


def destination_path(origin: str, options) -> str:
    if origin in options.interface_map:
        return options.interface_map[origin]
    if origin.startswith("src/interfaces/"):
        return "src/" + origin.removeprefix("src/interfaces/")
    return origin if origin.startswith("src/") else "src/" + PurePosixPath(origin).name


def declaration_context(code: str, path: str) -> str:
    """Retain complete types/constants and replace function bodies by signatures."""
    data = code.encode()
    for definition in sorted(definitions(code, path), key=lambda d: d.start, reverse=True):
        if definition.kind == "function_item":
            data = data[:definition.body_start] + b";" + data[definition.body_end:]
    return data.decode()


def match_item(item, inventory: list[Definition]) -> Definition | None:
    if item.kind not in {"function", "global", "struct", "union", "enum", "typedef"}:
        return None
    allowed = ({"function_item"} if item.kind == "function" else
               {"const_item", "static_item"} if item.kind == "global" else
               {"struct_item", "enum_item", "union_item", "type_item"})
    choices = [d for d in inventory if d.kind in allowed]
    name = normalized(item.name.removesuffix("_t") if item.kind != "function" else item.name)
    exact = [d for d in choices if normalized(d.target) == name or normalized(d.name) == name]
    if len(exact) == 1:
        return exact[0]
    if len(exact) > 1:
        same_file = [d for d in exact if normalized(PurePosixPath(d.path).stem)
                     == normalized(PurePosixPath(item.location.file).stem)]
        if len(same_file) == 1:
            return same_file[0]
    if exact or item.kind != "function":
        return None
    # Namespace prefixes are common (base122_encode -> encode). Only accept
    # a unique strongest suffix; ambiguous constructors require an item_map.
    candidates = []
    for d in choices:
        target = normalized(d.target)
        renamed = re.sub(r"(?:init|initialize)$", "new", name)
        if target == renamed or (len(target) >= 3 and name.endswith(target)):
            candidates.append(d)
    if candidates:
        best = max(len(normalized(d.target)) for d in candidates)
        candidates = [d for d in candidates if len(normalized(d.target)) == best]
    return candidates[0] if len(candidates) == 1 else None
