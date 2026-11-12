"""Read-only Rust source metrics; no compilation, execution, or macro expansion.

Pointer operations use conservative local type tracking. Unresolved operations
are reported separately, so callers can leave uncertain CSV cells empty.
"""

from __future__ import annotations

import re
from collections import Counter, defaultdict

from .rust_edits import _parse


ARITHMETIC = set("add sub offset wrapping_add wrapping_sub wrapping_offset byte_add byte_sub byte_offset "
                 "wrapping_byte_add wrapping_byte_sub wrapping_byte_offset offset_from byte_offset_from "
                 "offset_from_unsigned byte_offset_from_unsigned".split())
UNSAFE_RAW = (ARITHMETIC - {name for name in ARITHMETIC if name.startswith("wrapping_")}) | set(
    "read read_unaligned read_volatile write write_unaligned write_volatile copy_to copy_to_nonoverlapping "
    "copy_from copy_from_nonoverlapping as_ref as_mut replace swap drop_in_place".split())
RAW_RESULTS = ARITHMETIC - {"offset_from", "byte_offset_from", "offset_from_unsigned", "byte_offset_from_unsigned"}
POINTER_FUNCTIONS = set("read read_unaligned read_volatile write write_unaligned write_volatile copy "
                        "copy_nonoverlapping drop_in_place replace swap swap_nonoverlapping".split())
SAFE_METHODS = set("len is_empty is_null is_some is_none unwrap expect clone iter iter_mut enumerate zip "
                   "push pop clear reserve extend extend_from_slice count_ones leading_zeros trailing_zeros "
                   "as_ptr as_mut_ptr wrapping_add wrapping_sub wrapping_offset cast cast_mut cast_const".split())
SKIP = {"line_comment", "block_comment"}
LITERALS = {"string_literal", "raw_string_literal", "char_literal", "byte_string_literal"}


def _nodes(root, *, macros=True):
    pending = [root]
    while pending:
        node = pending.pop()
        if node.type in SKIP:
            continue
        yield node
        if node.type not in LITERALS and (macros or node.type not in {"macro_invocation", "macro_definition"}):
            pending.extend(reversed(node.children))


def _raw(kind):
    return bool(kind and kind.startswith("raw:"))


def _callee(node):
    function = node.child_by_field_name("function")
    while function is not None and function.type == "generic_function":
        function = function.child_by_field_name("function") or function.named_children[0]
    return function


def _declaration_pointer(node):
    parent = node.parent
    while parent is not None:
        if parent.type in {"parameter", "field_declaration", "let_declaration", "static_item", "const_item",
                           "type_item", "function_item", "function_signature_item"}:
            return True
        if parent.type in {"block", "type_cast_expression", "generic_function", "macro_invocation", "macro_definition"}:
            return False
        parent = parent.parent
    return False


def count_sources(files: dict[str, str]) -> dict:
    """Return syntactic counts plus per-file unresolved-operation diagnostics."""
    counts = Counter(loc=0, pointer_arithmetic=0, raw_pointer_decleration=0,
                     raw_pointer_derefrences=0, unsafe_lines=0, unsafe_cast=0, unsafe_calls=0)
    unresolved = Counter()
    issues, trees = [], []
    aliases, fields, functions = {}, defaultdict(set), defaultdict(set)
    unsafe_functions = defaultdict(set)
    for path, source in sorted(files.items()):
        try:
            data, root = _parse(source, path)
        except ValueError as exc:
            issues.append({"path": path, "error": str(exc)})
            continue
        trees.append((path, data, root))
        for node in _nodes(root, macros=False):
            name = node.child_by_field_name("name")
            typ = node.child_by_field_name("type")
            if node.type == "type_item" and name is not None and typ is not None:
                aliases[data[name.start_byte:name.end_byte].decode()] = (typ, data)

    def type_kind(node, data, seen=()):
        if node is None:
            return None
        if node.type in {"pointer_type", "reference_type"}:
            prefix = "raw:" if node.type == "pointer_type" else "ref:"
            return prefix + (type_kind(node.child_by_field_name("type"), data, seen) or "?")
        text = data[node.start_byte:node.end_byte].decode().split("::")[-1]
        if text in aliases and text not in seen:
            target, origin = aliases[text]
            return type_kind(target, origin, (*seen, text))
        return "other"

    for _, data, root in trees:
        for node in _nodes(root, macros=False):
            name = node.child_by_field_name("name")
            if name is None:
                continue
            label = data[name.start_byte:name.end_byte].decode()
            if node.type == "field_declaration":
                fields[label].add(type_kind(node.child_by_field_name("type"), data))
            if node.type in {"function_item", "function_signature_item"}:
                functions[label].add(type_kind(node.child_by_field_name("return_type"), data) or "other")
                params = node.child_by_field_name("parameters")
                header = data[node.start_byte:params.start_byte if params else name.end_byte].decode()
                parent = node.parent
                foreign = False
                while parent is not None:
                    foreign |= parent.type == "foreign_mod_item"
                    parent = parent.parent
                unsafe_functions[label].add(bool(re.search(r"\bunsafe\b", header)) or
                                            (foreign and not re.search(r"\bsafe\b", header)))

    def unique(mapping, name):
        choices = mapping.get(name, set())
        return next(iter(choices)) if len(choices) == 1 else None

    for path, data, root in trees:
        text = lambda node: data[node.start_byte:node.end_byte].decode() if node is not None else ""
        code_lines, unsafe_lines = set(), set()
        leaves = [node for node in _nodes(root) if not node.children or node.type in LITERALS]
        for node in leaves:
            for offset, line in enumerate(text(node).splitlines()):
                if line.strip():
                    code_lines.add(node.start_point.row + offset)
        counts["loc"] += len(code_lines)
        counts["raw_pointer_decleration"] += sum(node.type == "pointer_type" and _declaration_pointer(node)
                                                for node in _nodes(root, macros=False))

        def infer(node, env):
            if node is None:
                return None
            if node.type in {"identifier", "self"}:
                return env.get(text(node))
            if node.type == "type_cast_expression":
                return type_kind(node.child_by_field_name("type") or node.named_children[-1], data)
            if node.type == "reference_expression":
                return "ref:" + (infer(node.child_by_field_name("value") or node.named_children[-1], env) or "?")
            if node.type == "parenthesized_expression":
                return infer(node.named_children[0], env) if node.named_children else None
            if node.type == "unary_expression":
                kind = infer(node.named_children[-1], env)
                if text(node).lstrip().startswith("*") and kind and ":" in kind:
                    return kind.split(":", 1)[1].replace("?", "") or None
                return kind
            if node.type == "field_expression":
                return unique(fields, text(node.child_by_field_name("field")))
            if node.type == "call_expression":
                function = _callee(node)
                if function is not None and function.type == "field_expression":
                    method = text(function.child_by_field_name("field"))
                    kind = infer(function.child_by_field_name("value"), env)
                    if method in {"as_ptr", "as_mut_ptr"}:
                        return "raw:?"
                    if _raw(kind) and method in RAW_RESULTS | {"cast", "cast_mut", "cast_const"}:
                        return kind
                    if _raw(kind) and method in {"as_ref", "as_mut"}:
                        return "ref:" + kind.split(":", 1)[1]
                    if method in {"unwrap", "expect"}:
                        return kind
                    return unique(functions, method)
                label = text(function).split("::")[-1]
                if label == "into_raw":
                    return "raw:?"
                return unique(functions, label)
            if node.type.endswith("literal"):
                return "other"
            return None

        def unknown(metric, node):
            unresolved[metric] += 1
            if len(issues) < 150:
                issues.append({"path": path, "line": node.start_point.row + 1,
                               "metric": metric, "expression": text(node)[:160]})

        def visit(node, env, unsafe=False):
            if node.type in SKIP | LITERALS | {"macro_definition", "macro_invocation"}:
                return
            if node.type in {"function_item", "closure_expression"}:
                env = dict(env)
                params = node.child_by_field_name("parameters")
                if params is not None:
                    for parameter in params.named_children:
                        pattern = parameter.child_by_field_name("pattern")
                        if pattern is not None:
                            env[text(pattern).removeprefix("mut ")] = type_kind(parameter.child_by_field_name("type"), data)
                header = data[node.start_byte:params.start_byte if params else node.start_byte].decode()
                unsafe |= bool(re.search(r"\bunsafe\b", header))
            unsafe |= node.type == "unsafe_block"
            if unsafe:
                unsafe_lines.update(range(node.start_point.row, node.end_point.row + 1))
            if node.type == "block":
                env = dict(env)
            if node.type == "let_declaration":
                pattern = node.child_by_field_name("pattern")
                if pattern is not None and re.fullmatch(r"(?:mut\s+)?[A-Za-z_]\w*", text(pattern)):
                    env[text(pattern).removeprefix("mut ")] = (
                        type_kind(node.child_by_field_name("type"), data) if node.child_by_field_name("type") is not None
                        else infer(node.child_by_field_name("value"), env))
            if node.type == "unary_expression" and text(node).lstrip().startswith("*"):
                kind = infer(node.named_children[-1], env)
                if _raw(kind):
                    counts["raw_pointer_derefrences"] += 1
                elif kind is None and unsafe:
                    unknown("raw_pointer_derefrences", node)
            if node.type == "type_cast_expression":
                destination = infer(node, env)
                origin = infer(node.child_by_field_name("value") or node.named_children[0], env)
                if _raw(destination) or _raw(origin):
                    counts["unsafe_cast"] += 1
                elif origin is None and unsafe:
                    unknown("unsafe_cast", node)
            if node.type == "call_expression":
                function = _callee(node)
                label = text(function)
                name = label.split("::")[-1]
                is_unsafe = unique(unsafe_functions, name) is True
                if function is not None and function.type == "field_expression":
                    method = text(function.child_by_field_name("field"))
                    kind = infer(function.child_by_field_name("value"), env)
                    if method in ARITHMETIC:
                        if _raw(kind):
                            counts["pointer_arithmetic"] += 1
                        elif kind is None and unsafe:
                            unknown("pointer_arithmetic", node)
                    if _raw(kind) and method in {"cast", "cast_mut", "cast_const"}:
                        counts["unsafe_cast"] += 1
                    is_unsafe |= unique(unsafe_functions, method) is True
                    is_unsafe |= _raw(kind) and method in UNSAFE_RAW
                    known_safe = method in SAFE_METHODS or unique(unsafe_functions, method) is False
                else:
                    is_unsafe |= ("ptr::" in label and name in POINTER_FUNCTIONS) or (
                        "mem::" in label and name in {"transmute", "transmute_copy", "zeroed", "uninitialized"})
                    if name in {"transmute", "transmute_copy"} and "mem::" in label:
                        counts["unsafe_cast"] += 1
                    known_safe = unique(unsafe_functions, name) is False
                if is_unsafe:
                    counts["unsafe_calls"] += 1
                elif unsafe and not known_safe:
                    unknown("unsafe_calls", node)
            for child in node.named_children:
                visit(child, env, unsafe)

        visit(root, {})
        counts["unsafe_lines"] += len(code_lines & unsafe_lines)
    return {"counts": dict(counts), "unresolved": dict(unresolved), "issues": issues,
            "parse_errors": sum("error" in issue for issue in issues), "files": len(files)}
