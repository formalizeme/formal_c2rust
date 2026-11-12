"""Source-item dependency graphs and dependency-first translation groups.

An edge A -> B means A uses B. This is a syntactic dependency analysis, not
an ownership or points-to analysis. Indirect calls remain explicit unresolved
obligations even when signature-matched candidate edges can be supplied.
"""

from __future__ import annotations

import heapq
import json
import re
from collections import defaultdict
from collections.abc import Mapping, Sequence
from dataclasses import asdict, dataclass, field, replace
from pathlib import Path

from .benchmark import Project
from .c_analysis import ParsedProject, parse_project, preprocessor_flags
from .config import Config, resolve
from .tools import compcert_target

GRAPH_PARSER_VERSION = 3


@dataclass(frozen=True, order=True)
class SourceLocation:
    file: str
    line: int
    column: int
    offset: int


@dataclass
class Item:
    id: str
    name: str
    kind: str
    location: SourceLocation
    type: str = ""
    linkage: str = ""
    external: bool = False
    is_definition: bool = False
    source: str = ""
    declarations: list[SourceLocation] = field(default_factory=list)
    units: list[str] = field(default_factory=list)
    source_start: int = 0
    source_end: int = 0


@dataclass(frozen=True, order=True)
class Dependency:
    source: str
    target: str
    kind: str
    location: SourceLocation


@dataclass
class UnresolvedDependency:
    source: str | None
    kind: str
    location: SourceLocation
    message: str
    candidates: list[str] = field(default_factory=list)
    severity: str = "error"


@dataclass
class DependencyGraph:
    project: str
    items: dict[str, Item] = field(default_factory=dict)
    edges: set[Dependency] = field(default_factory=set)
    units: list[dict] = field(default_factory=list)
    diagnostics: list[dict] = field(default_factory=list)
    unresolved: list[UnresolvedDependency] = field(default_factory=list)
    parser_version: int = GRAPH_PARSER_VERSION
    source_normalizations: dict[str, list[dict]] = field(default_factory=dict)
    header_aliases: dict[str, str] = field(default_factory=dict)

    @property
    def complete(self) -> bool:
        """No blocking gaps; warning-level indirect calls remain approximations."""
        return (bool(self.units) and all(u["parsed"] for u in self.units)
                and not any(i.severity == "error" for i in self.unresolved))


def _adjacency(graph: DependencyGraph, include_external: bool) -> dict[str, list[str]]:
    nodes = {key for key, item in graph.items.items() if include_external or not item.external}
    adjacency: dict[str, set[str]] = {key: set() for key in sorted(nodes)}
    for edge in graph.edges:
        if edge.source in nodes and edge.target in nodes:
            adjacency[edge.source].add(edge.target)
    return {key: sorted(values) for key, values in adjacency.items()}


def strongly_connected_components(graph: DependencyGraph, *, include_external: bool = False) -> list[list[str]]:
    """Iterative Kosaraju, avoiding Python's recursion limit on large projects."""
    adjacency = _adjacency(graph, include_external)
    reverse: dict[str, list[str]] = {key: [] for key in adjacency}
    for source, targets in adjacency.items():
        for target in targets:
            reverse[target].append(source)
    visited, finished = set(), []
    for start in adjacency:
        if start in visited:
            continue
        visited.add(start)
        stack = [(start, iter(adjacency[start]))]
        while stack:
            node, successors = stack[-1]
            target = next(successors, None)
            if target is None:
                finished.append(node)
                stack.pop()
            elif target not in visited:
                visited.add(target)
                stack.append((target, iter(adjacency[target])))
    visited.clear()
    groups = []
    for start in reversed(finished):
        if start in visited:
            continue
        group, pending = [], [start]
        visited.add(start)
        while pending:
            node = pending.pop()
            group.append(node)
            for target in reverse[node]:
                if target not in visited:
                    visited.add(target)
                    pending.append(target)
        groups.append(sorted(group))
    return sorted(groups)


def translation_order(graph: DependencyGraph, *, include_external: bool = False) -> list[list[str]]:
    """SCCs in dependency-first order; external leaves are omitted by default.

    All edge kinds participate, including pointer-type dependencies. The weak
    type_pointer label is retained for future representation planning, but it
    does not currently remove scheduling constraints. Incomplete graphs still
    have a provisional order; consumers must check graph.complete.
    """
    groups = strongly_connected_components(graph, include_external=include_external)
    membership = {node: i for i, group in enumerate(groups) for node in group}
    needs = [set() for _ in groups]
    users = [set() for _ in groups]
    for edge in graph.edges:
        a, b = membership.get(edge.source), membership.get(edge.target)
        if a is not None and b is not None and a != b:
            needs[a].add(b)
            users[b].add(a)
    ready = [i for i, dependencies in enumerate(needs) if not dependencies]
    heapq.heapify(ready)
    ordered = []
    while ready:
        index = heapq.heappop(ready)
        ordered.append(groups[index])
        for user in sorted(users[index]):
            needs[user].remove(index)
            if not needs[user]:
                heapq.heappush(ready, user)
    return ordered


def translation_order_with_candidates(graph: DependencyGraph) -> list[list[str]]:
    """Real SCCs/dependencies are hard constraints; may-call edges are preferences.

    Candidate cycles cannot force unrelated functions into one prompt. Among
    ready real groups, prefer those with fewer candidate callees still pending.
    """
    strong = replace(graph, edges={e for e in graph.edges if e.kind != "may_call"})
    groups = strongly_connected_components(strong)
    owner = {node: i for i, group in enumerate(groups) for node in group}
    needs, users = [set() for _ in groups], [set() for _ in groups]
    hints, hinted_users = [set() for _ in groups], [set() for _ in groups]
    for edge in graph.edges:
        a, b = owner.get(edge.source), owner.get(edge.target)
        if a is None or b is None or a == b:
            continue
        if edge.kind == "may_call":
            hints[a].add(b)
            hinted_users[b].add(a)
        else:
            needs[a].add(b)
            users[b].add(a)
    ready = {i for i, deps in enumerate(needs) if not deps}
    queue = [(len(hints[i]), i) for i in ready]
    heapq.heapify(queue)
    result = []
    while queue:
        score, i = heapq.heappop(queue)
        if i not in ready or score != len(hints[i]):
            continue
        ready.remove(i)
        result.append(groups[i])
        for user in hinted_users[i]:
            hints[user].discard(i)
            if user in ready:
                heapq.heappush(queue, (len(hints[user]), user))
        for user in users[i]:
            needs[user].remove(i)
            if not needs[user]:
                ready.add(user)
                heapq.heappush(queue, (len(hints[user]), user))
    return result


class _Builder:
    def __init__(self, parsed: ParsedProject, project: str):
        import clang.cindex as ci
        self.ci, self.K, self.T = ci, ci.CursorKind, ci.TypeKind
        self.parsed = parsed
        self.graph = DependencyGraph(project, source_normalizations=parsed.normalizations,
                                     header_aliases=parsed.aliases)
        self.cursors: list[tuple[str, str, object]] = []
        self.macros: dict[str, set[str]] = defaultdict(set)
        self.macro_bodies: dict[str, list[str]] = {}
        self.spans: dict[str, list[tuple[int, int, str]]] = defaultdict(list)
        self.indirect: list[tuple[UnresolvedDependency, str]] = []
        self.address_taken: set[str] = set()
        self.signatures: dict[str, str] = {}
        self.reported: set[tuple] = set()
        self.issues: dict[tuple, UnresolvedDependency] = {}
        self.definition_rank: dict[str, int] = {}
        self.source_files: dict[str, bytes] = {}
        self.unit = ""
        self.kinds = {self.K.FUNCTION_DECL: "function", self.K.VAR_DECL: "global",
                      self.K.STRUCT_DECL: "struct", self.K.UNION_DECL: "union",
                      self.K.ENUM_DECL: "enum", self.K.TYPEDEF_DECL: "typedef",
                      self.K.MACRO_DEFINITION: "macro"}

    def location(self, location) -> SourceLocation:
        path = location.file.name if location.file else "<unknown>"
        name = self.parsed.relative_path(path) or self.parsed.stable_text(path)
        return SourceLocation(name, location.line, location.column, location.offset)

    def _local(self, cursor) -> bool:
        parent = cursor.semantic_parent
        while parent and parent.kind != self.K.TRANSLATION_UNIT:
            if parent.kind == self.K.FUNCTION_DECL:
                return True
            parent = parent.semantic_parent
        return False

    def _eligible(self, cursor) -> bool:
        if cursor.kind not in self.kinds or self._local(cursor):
            return False
        return cursor.kind != self.K.VAR_DECL or cursor.semantic_parent.kind == self.K.TRANSLATION_UNIT

    def _id(self, cursor) -> str:
        location = self.location(cursor.location)
        if cursor.kind == self.K.MACRO_DEFINITION:
            return f"macro:{location.file}:{location.offset}:{cursor.spelling}"
        usr = self.parsed.stable_text(cursor.get_usr())
        key = usr or f"{self.kinds[cursor.kind]}:{location.file}:{location.offset}"
        if cursor.kind in {self.K.STRUCT_DECL, self.K.UNION_DECL, self.K.ENUM_DECL, self.K.TYPEDEF_DECL}:
            # Tag names have translation-unit scope. A shared header declaration
            # is one source item, but unrelated same-named tags are not.
            declaration = self.location(cursor.canonical.location)
            key += f"@decl:{declaration.file}:{declaration.offset}"
        if cursor.linkage == self.ci.LinkageKind.INTERNAL:
            key += f"@unit:{self.unit}"
        return key

    def _source(self, cursor) -> str:
        start, end = cursor.extent.start, cursor.extent.end
        if not start.file or not end.file or start.file.name != end.file.name:
            return ""
        try:
            if start.file.name not in self.source_files:
                self.source_files[start.file.name] = self.parsed.original_bytes(start.file.name)
            end_offset = self.parsed.original_end(end.file.name, end.offset)
            return self.source_files[start.file.name][start.offset:end_offset].decode(errors="replace")
        except OSError:
            return ""

    def item(self, cursor) -> str | None:
        if cursor.kind == self.K.ENUM_CONSTANT_DECL:
            cursor = cursor.semantic_parent
        if not self._eligible(cursor):
            return None
        key = self._id(cursor)
        location = self.location(cursor.location)
        local = cursor.location.file and self.parsed.relative_path(cursor.location.file.name) is not None
        if cursor.spelling.startswith("__builtin_"):
            local = False  # Implicit builtin declarations can point into project source.
        definition = cursor.is_definition() or cursor.kind in (self.K.TYPEDEF_DECL, self.K.MACRO_DEFINITION)
        rank = 2 if definition else 0
        # Clang reports a tentative file-scope C definition as not is_definition().
        if cursor.kind == self.K.VAR_DECL and cursor.storage_class != self.ci.StorageClass.EXTERN:
            definition = True
            rank = max(rank, 1)
        existing = self.graph.items.get(key)
        if existing is None:
            existing = Item(key, cursor.spelling or f"<anonymous@{location.line}:{location.column}>",
                            self.kinds[cursor.kind], location, self.parsed.stable_text(cursor.type.spelling),
                            cursor.linkage.name.lower(), not bool(local), definition,
                            self._source(cursor) if local or cursor.kind in {
                                self.K.MACRO_DEFINITION, self.K.TYPEDEF_DECL, self.K.STRUCT_DECL,
                                self.K.UNION_DECL, self.K.ENUM_DECL} else "")
            self.graph.items[key] = existing
            existing.source_start = cursor.extent.start.offset
            existing.source_end = self.parsed.original_end(
                cursor.extent.end.file.name if cursor.extent.end.file else None, cursor.extent.end.offset)
            self.definition_rank[key] = rank
        elif definition and local:
            if (existing.is_definition and existing.location != location
                    and (cursor.kind == self.K.FUNCTION_DECL
                         or (cursor.kind == self.K.VAR_DECL and rank == 2 and self.definition_rank[key] == 2))):
                self.issue(key, "conflicting_definitions", location,
                           "Multiple definitions share external linkage; separate the build/program targets.")
            if rank > self.definition_rank[key] or (rank == self.definition_rank[key] and location < existing.location):
                existing.location, existing.source = location, self._source(cursor)
                existing.type = self.parsed.stable_text(cursor.type.spelling)
                existing.source_start = cursor.extent.start.offset
                existing.source_end = self.parsed.original_end(
                    cursor.extent.end.file.name if cursor.extent.end.file else None, cursor.extent.end.offset)
                self.definition_rank[key] = rank
            existing.is_definition = True
            existing.external = False
        if location not in existing.declarations:
            existing.declarations.append(location)
        if self.unit not in existing.units:
            existing.units.append(self.unit)
        if cursor.kind == self.K.FUNCTION_DECL:
            self.signatures[key] = cursor.type.get_canonical().spelling
        return key

    def edge(self, owner: str, target: str | None, kind: str, location) -> None:
        if target is not None and (owner != target or kind in {"call", "may_call"}):
            self.graph.edges.add(Dependency(owner, target, kind, self.location(location)))

    def issue(self, owner, kind, location, message) -> UnresolvedDependency:
        key = owner, kind, location
        issue = UnresolvedDependency(owner, kind, location, message,
                                     severity="warning" if kind == "macro_token_paste" else "error")
        if key not in self.reported:
            self.graph.unresolved.append(issue)
            self.reported.add(key)
            self.issues[key] = issue
        return self.issues[key]

    def collect_items(self, cursor) -> None:
        for child in cursor.get_children():
            if not child.location.file or self.parsed.relative_path(child.location.file.name) is None:
                continue
            if self.parsed.relative_path(child.location.file.name) in self.parsed.generated_units:
                continue  # The keep-alive table is compiler scaffolding, not a source item.
            if self._eligible(child):
                key = self.item(child)
                self.cursors.append((self.unit, key, child))
                if child.kind == self.K.MACRO_DEFINITION:
                    self.macros[child.spelling].add(key)
                    tokens = list(child.get_tokens())
                    body, parameters = 1, set()
                    if (len(tokens) > 1 and tokens[1].spelling == "("
                            and tokens[1].location.offset == tokens[0].extent.end.offset):
                        while body < len(tokens) and tokens[body].spelling != ")":
                            parameters.add(tokens[body].spelling)
                            body += 1
                        body += 1
                    self.macro_bodies[key] = [token.spelling for token in tokens[body:]
                                              if token.spelling not in parameters]
                    if "##" in self.macro_bodies[key]:
                        self.issue(key, "macro_token_paste", self.location(child.location),
                                   "Token pasting can create dependencies absent from lexical macro-body edges; "
                                   "expanded AST references are still collected at uses.")
                else:
                    start, end = child.extent.start, child.extent.end
                    loc = self.location(start)
                    self.spans[loc.file].append((start.offset, self.parsed.original_end(
                        end.file.name if end.file else None, end.offset), key))
            self.collect_items(child)

    def type_dependencies(self, owner: str, typ, location, weak: bool = False, seen=None) -> None:
        seen = set() if seen is None else seen
        marker = typ.kind, typ.spelling, weak
        if marker in seen or typ.kind == self.T.INVALID:
            return
        seen.add(marker)
        if typ.kind == self.T.POINTER:
            self.type_dependencies(owner, typ.get_pointee(), location, True, seen)
            return
        if typ.kind in {self.T.CONSTANTARRAY, self.T.INCOMPLETEARRAY, self.T.VARIABLEARRAY,
                        self.T.DEPENDENTSIZEDARRAY}:
            self.type_dependencies(owner, typ.element_type, location, weak, seen)
            return
        if typ.kind in {self.T.FUNCTIONPROTO, self.T.FUNCTIONNOPROTO}:
            self.type_dependencies(owner, typ.get_result(), location, False, seen)
            if typ.kind == self.T.FUNCTIONPROTO:
                for arg in typ.argument_types():
                    self.type_dependencies(owner, arg, location, False, seen)
            return
        declaration = typ.get_declaration()
        if declaration.kind in self.kinds:
            self.edge(owner, self.item(declaration), "type_pointer" if weak else "type_value", location)
        canonical = typ.get_canonical()
        if canonical.kind != typ.kind or canonical.spelling != typ.spelling:
            self.type_dependencies(owner, canonical, location, weak, seen)

    def collect_dependencies(self, cursor, owner: str, *, callee: bool = False, weak: bool = False) -> None:
        if self._eligible(cursor) and self._id(cursor) != owner:
            self.edge(owner, self.item(cursor), "type_value", cursor.location)
            return  # A nested type's body belongs to its own node.
        kind = cursor.kind
        if kind == self.K.TYPE_REF:
            ref = cursor.referenced
            if ref:
                self.edge(owner, self.item(ref), "type_pointer" if weak else "type_value", cursor.location)
            return
        self.type_dependencies(owner, cursor.type, cursor.location)
        ref = cursor.referenced
        if kind == self.K.DECL_REF_EXPR:
            if ref and ref.kind == self.K.FUNCTION_DECL:
                target = self.item(ref)
                if not callee:
                    self.edge(owner, target, "function_ref", cursor.location)
                    if target:
                        self.address_taken.add(target)
            elif ref and ref.kind in {self.K.VAR_DECL, self.K.ENUM_CONSTANT_DECL}:
                self.edge(owner, self.item(ref), "global" if ref.kind == self.K.VAR_DECL else "enum_value",
                          cursor.location)
            elif ref is None:
                self.issue(owner, "reference", self.location(cursor.location), "Unresolved declaration reference")
        elif kind == self.K.MEMBER_REF_EXPR and ref:
            self.edge(owner, self.item(ref.semantic_parent), "type_value", cursor.location)
        children = list(cursor.get_children())
        if kind == self.K.CALL_EXPR:
            if ref and ref.kind == self.K.FUNCTION_DECL:
                self.edge(owner, self.item(ref), "call", cursor.location)
            else:
                typ = children[0].type.get_canonical() if children else cursor.type
                if typ.kind == self.T.POINTER:
                    typ = typ.get_pointee().get_canonical()
                issue = self.issue(owner, "indirect_call", self.location(cursor.location),
                                   "Indirect call: candidate edges are signature matches, not a points-to result.")
                self.indirect.append((issue, typ.spelling))
            for i, child in enumerate(children):
                self.collect_dependencies(child, owner, callee=(i == 0))
            return
        pointer = cursor.type.kind == self.T.POINTER
        for child in children:
            self.collect_dependencies(child, owner, callee=callee, weak=pointer or weak)

    def macro_dependencies(self) -> None:
        # Replacement-list names can bind at expansion time, including after a
        # redefinition. Retain all project definitions with that name rather
        # than claiming that the spelling identifies a unique definition.
        for owner, body in self.macro_bodies.items():
            for name in body:
                for target in self.macros.get(name, ()):
                    location = self.graph.items[owner].location
                    self.graph.edges.add(Dependency(owner, target, "macro_body", location))
        for unit in self.parsed.units:
            if unit.tu is None:
                continue
            self.unit = unit.path
            for cursor in unit.tu.cursor.get_children():
                if cursor.kind != self.K.MACRO_INSTANTIATION or not cursor.location.file:
                    continue
                loc = self.location(cursor.location)
                owners = [(end - start, key) for start, end, key in self.spans.get(loc.file, ())
                          if start <= loc.offset < end and unit.path in self.graph.items[key].units]
                if owners and cursor.referenced:
                    _, owner = min(owners)
                    self.edge(owner, self.item(cursor.referenced), "macro", cursor.location)

    def build(self) -> DependencyGraph:
        for unit in self.parsed.units:
            self.unit = unit.path
            errors = unit.error is not None
            if unit.error:
                self.graph.diagnostics.append({"unit": unit.path, "severity": "error",
                                               "message": self.parsed.stable_text(unit.error)})
            for note in unit.compatibility:
                self.graph.diagnostics.append({"unit": unit.path, "severity": "warning",
                                               "message": note, "kind": "parser_compatibility"})
            if unit.tu is not None:
                for diagnostic in unit.tu.diagnostics:
                    severity = diagnostic.severity
                    errors |= severity >= self.ci.Diagnostic.Error
                    self.graph.diagnostics.append({
                        "unit": unit.path,
                        "severity": {0: "ignored", 1: "note", 2: "warning", 3: "error", 4: "fatal"}[severity],
                        "location": asdict(self.location(diagnostic.location)),
                        "message": self.parsed.stable_text(diagnostic.spelling),
                    })
                self.collect_items(unit.tu.cursor)
            self.graph.units.append({"path": unit.path, "configuration": unit.configuration,
                                     "arguments": [self.parsed.stable_text(a) for a in unit.arguments],
                                     "parse_attempts": [{"arguments": [self.parsed.stable_text(a)
                                                                          for a in attempt["arguments"]],
                                                         "errors": [self.parsed.stable_text(e)
                                                                    for e in attempt["errors"]]}
                                                        for attempt in unit.attempts],
                                     "compatibility": unit.compatibility,
                                     "parsed": unit.tu is not None and not errors})
        visited = set()
        for unit, owner, cursor in self.cursors:
            marker = unit, owner, cursor.extent.start.offset, cursor.extent.end.offset
            if marker in visited or cursor.kind == self.K.MACRO_DEFINITION:
                continue
            visited.add(marker)
            self.unit = unit
            self.collect_dependencies(cursor, owner)
        self.macro_dependencies()
        for issue, signature in self.indirect:
            issue.severity = "warning"
            issue.candidates = sorted(key for key, typ in self.signatures.items()
                                      if typ == signature and self.graph.items[key].is_definition)
            for target in issue.candidates:
                self.graph.edges.add(Dependency(issue.source, target, "may_call", issue.location))
        for item in self.graph.items.values():
            if item.kind in {"function", "global"} and not item.is_definition:
                item.external = True
            item.declarations.sort()
            item.units.sort()
        if not self.graph.units:
            self.graph.diagnostics.append({"severity": "error", "message": "No C compilation units found"})
        return self.graph


def build_graph(project: Project, *, clang_args: Sequence[str] = (),
                default_args: Sequence[str] = ("-std=c99", "-U__GNUC__"),
                unit_args: Mapping[str, Sequence[str]] | None = None,
                compile_commands: Path | None = None, clang: str = "clang",
                work_dir: Path | None = None,
                unit_paths: Sequence[str] | None = None,
                double_suffix: bool = False, compatibility: bool = False,
                allow_target_retry: bool = False,
                strict_units: Sequence[str] = ()) -> DependencyGraph:
    """Build an in-memory graph from original source; never run source code."""
    with parse_project(project, clang_args=clang_args, default_args=default_args, unit_args=unit_args,
                       compile_commands=compile_commands, clang=clang, work_dir=work_dir,
                       unit_paths=unit_paths, double_suffix=double_suffix, compatibility=compatibility,
                       allow_target_retry=allow_target_retry, strict_units=strict_units) as parsed:
        return _Builder(parsed, project.name).build()


def build_project_graph(cfg: Config, project: Project, *, clang_args: Sequence[str] = (),
                        compile_commands: Path | None = None,
                        unit_args: Mapping[str, Sequence[str]] | None = None,
                        unit_paths: Sequence[str] | None = None) -> DependencyGraph:
    """Pipeline defaults; explicit database arguments supersede the defaults.

    CompCert-specific -f options are not Clang options. The first configured
    flag set supplies only preprocessing flags; use unit_args (e.g. accepted
    stage-1 flags) or a database when different files need different defines.
    The selected arguments are recorded per unit in the resulting graph.
    """
    flags = ["-std=c99", "-U__GNUC__", "-D__COMPCERT__=1",
             "-U__STDC_IEC_559_COMPLEX__", "-D__STDC_NO_ATOMICS__=1",
             "-D__STDC_NO_COMPLEX__=1", "-D__STDC_NO_THREADS__=1", "-D__STDC_NO_VLA__=1"]
    compcert = resolve(cfg.tools.compcert_dir)
    try:
        version = re.search(r"version=(\d+)\.(\d+)", (compcert / "VERSION").read_text())
        if version:
            major, minor = map(int, version.groups())
            flags += [f"-D__COMPCERT_MAJOR__={major}", f"-D__COMPCERT_MINOR__={minor}",
                      f"-D__COMPCERT_VERSION__={100 * major + minor}"]
    except OSError:
        pass
    target = cfg.target or compcert_target(compcert)
    triples = {"aarch64-linux": "aarch64-unknown-linux-gnu", "x86_64-linux": "x86_64-unknown-linux-gnu"}
    if target in triples:
        flags += ["-target", triples[target]]
        flags += ["-D__COMPCERT_WCHAR_TYPE__=" + ("unsigned int" if target == "aarch64-linux" else "int")]
    stdlib = resolve(cfg.tools.compcert_stdlib) / "include"
    if stdlib.is_dir():
        flags.append(f"-I{stdlib}")
    paths = {u.relative_to(project.c_dir).as_posix() for u in project.units}
    paths |= {"c2r_header_only.c", *(unit_args or {})}
    per_unit = {path: preprocessor_flags([*(unit_args or {}).get(path, cfg.refactor.flag_sets[0]),
                                          *cfg.refactor.extra_flags]) for path in paths}
    compatibility = (["-Wno-error=implicit-function-declaration", "-Wno-error=int-conversion",
                      "-Wno-error=incompatible-pointer-types"] if cfg.translation.legacy_c_diagnostics else [])
    graph = build_graph(project, default_args=flags, clang_args=[*clang_args, *compatibility], unit_args=per_unit,
                        compile_commands=compile_commands, clang=cfg.tools.clang,
                        work_dir=resolve(cfg.output.work_dir), unit_paths=unit_paths,
                        double_suffix=cfg.rewrites.double_suffix,
                        compatibility=cfg.translation.clang_compatibility,
                        allow_target_retry=cfg.target is None, strict_units=tuple(unit_args or {}))
    for issue in graph.unresolved:
        if issue.kind == "indirect_call":
            issue.severity = "warning" if cfg.translation.indirect_calls == "warn" else "error"
    return graph


def write_graph(graph: DependencyGraph, path: Path) -> Path:
    """Write a deterministic, self-contained JSON report (schema version 1)."""
    self_edges = {edge.source for edge in graph.edges if edge.source == edge.target and edge.kind != "may_call"}
    groups = translation_order_with_candidates(graph)
    report = {
        "schema_version": 1, "project": graph.project,
        "parser_version": graph.parser_version,
        "source_normalizations": graph.source_normalizations,
        "header_aliases": graph.header_aliases,
        "edge_direction": "item -> dependency", "complete": graph.complete,
        "units": graph.units,
        "items": [asdict(graph.items[key]) for key in sorted(graph.items)],
        "edges": [asdict(edge) for edge in sorted(graph.edges)],
        "diagnostics": graph.diagnostics,
        "unresolved": [asdict(issue) for issue in sorted(
            graph.unresolved, key=lambda issue: (issue.location, issue.kind, issue.source or ""))],
        "translation_groups": [{"items": group, "recursive": len(group) > 1 or any(n in self_edges for n in group)}
                               for group in groups],
        "order_provisional": not graph.complete or bool(graph.unresolved),
        "candidate_policy": "soft ordering preferences; excluded from SCC membership and prompt expansion",
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return path
