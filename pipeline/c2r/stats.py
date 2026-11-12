"""Per-project pointer statistics for CRUST-Bench (`c2r stats`).

Writes one CSV row per C project: its size, the structs, unions and
functions it defines, the pointers it declares, the pointer arithmetic it
contains (by kind), and what stage 1 refactored. The
source counts come from libclang on the original C (CBench is never
modified); the refactoring counts come from `status.json`, written by
`c2r refactor`. Column definitions are in COLUMNS, and are also written to a
Markdown file next to the CSV.

Counting rules:
- Every C file and header of a project counts, tests included, as in stage 1.
  Each .c file is parsed as a unit, a header-only library through stage 1's
  wrapper, and every header also on its own, so that headers no unit includes
  are counted too.
- Counts are of the program as compiled, after preprocessing: an operation
  in the body of a project macro is counted at every use of the macro (the
  `arith_in_macro_uses` column says how many). Operations that come from macros
  of system headers (`isspace`, `assert`) are not counted: they are not the
  project's code. Operations written in a macro's arguments are counted where
  they are written.
- A declaration or operation is counted once per source location, however
  many units include its header: within one parse, the count at a location
  (start, end, kind) is kept, and across parses, the largest count is taken.
  So nested operations (`m[i][j]` on a `double **` is two subscripts) and
  operations from one macro use are all counted.
- Data pointers only: function pointers are left out. A parameter declared as
  an array (`int a[]`) is a pointer, as C adjusts it.
- Structs, unions and functions count where they are defined (with a body),
  not where they are only declared (`struct s;`, a prototype). An anonymous
  struct or union (`typedef struct { ... } t;`, a nested one) is a definition.
- The moving_ and compared_ columns count pointers, not operations: each
  distinct pointer once. A pointer is *moving* if it is moved: `p++`, `p--`,
  `p += n`, `p -= n`, `p = p + n`, `p = p - n` (the arith_move_ operations).
  A pointer only computed from another one (`p = q + n`, `p = &q[i]`) points
  to one element and is not moving. A pointer is *compared* if it is not
  moving, but compared with another pointer (`<`, `==`, ...) or subtracted
  from one (`p - q`); a comparison with NULL or 0 is a null check, not counted.
  In `p + n < end`, both `p` and `end` are compared. Each is counted by where
  it lives: a local variable or parameter (by its declaration), a global, a
  struct or union member (by the member's declaration: `a->pos` and `b->pos`
  are one), or a pointer reached through another pointer (`*pp`, `a[i]`: by
  the variable it is reached from). `*_refactored` matches the pass's split
  pointers by function and name, in a file a refactored unit compiles
  (clightgen's `__1` suffixes for shadowed names are ignored).
"""

from __future__ import annotations

import csv
import json
import re
import shutil
import tempfile
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

from .benchmark import Project, discover, select
from .config import Config, resolve
from .refactor import (ALIAS_DIR, COPY_IGNORE, WRAPPER, header_aliases, include_dirs, system_include_dirs,
                       write_aliases, write_wrapper)
from .tools import clang_resource_include

# (column, definition). The order is the CSV's.
COLUMNS = [
    ("project", "CBench project directory"),
    ("status", "stage 1: accepted (every C file refactored), partial (some), rejected (none), or empty if "
               "stage 1 has not run"),
    ("header_only", "1 if the library is header-only (refactored through a generated wrapper)"),
    ("c_files", "C files compiled on their own (.c files, tests and examples included; a .c file #included by "
                "another is part of it)"),
    ("c_files_refactored", "the part of c_files that CompCert accepted, so refactored"),
    ("header_files", "header files (.h)"),
    ("loc", "lines of code in .c and .h files: lines with something other than whitespace and comments"),
    ("loc_tests", "lines of code in test files (part of loc)"),
    ("structs", "struct definitions (with a body; anonymous and nested ones included)"),
    ("unions", "union definitions (with a body; anonymous and nested ones included)"),
    ("functions", "function definitions (with a body), tests included"),
    ("ptr_locals", "pointer local variables (automatic storage) in function definitions"),
    ("ptr_params", "pointer parameters of function definitions"),
    ("ptr_globals", "pointer variables with static storage: globals and static locals"),
    ("ptr_fields", "pointer members of structs and unions"),
    ("pointers", "ptr_locals + ptr_params + ptr_globals + ptr_fields"),
    ("arith_offset", "p + n, p - n, n + p (pointer plus or minus an integer), not as part of a move"),
    ("arith_subscript", "p[i] on a pointer (subscripts on arrays are not counted)"),
    ("arith_difference", "p - q (difference of two pointers)"),
    ("arith_move_variable", "p++, p--, ++p, --p, p += n, p -= n, p = p + n, p = p - n on a local variable "
                            "or parameter"),
    ("arith_move_global", "the same on a pointer with static storage"),
    ("arith_move_field", "the same on a struct or union member (r->pos++, s.p += n)"),
    ("arith_move_indirect", "the same on a pointer reached through another pointer ((*pp)++, ++*s, a[i]++)"),
    ("pointer_arith", "sum of the arith_ columns"),
    ("arith_in_macro_uses", "the part of pointer_arith located at a use of a project macro: from the macro's "
                            "body (counted at each use), or written in its arguments when they pass through "
                            "further macros (libclang cannot tell those two apart)"),
    ("pointer_arith_in_refactored", "pointer_arith located in files compiled by a refactored (accepted) unit"),
    ("refactored_variables", "pointer temporaries split into base + index by the pass (Clight temporaries: "
                             "source variables, parameters, and compiler temporaries). A function defined in a "
                             "header counts once, though every unit including it is refactored"),
    ("refactored_variables_source", "the part of refactored_variables that are source variables or parameters "
                                    "(compiler temporaries excluded)"),
    ("refactored_memory", "pointers stored in memory (fields, globals, *pp) given a cache"),
    ("refactored", "refactored_variables + refactored_memory"),
    ("functions_refactored", "functions in which the pass rewrote at least one pointer"),
    ("moving_pointers", "distinct pointers that are moved (p++, p--, p += n, p -= n, p = p + n, p = p - n); a "
                        "pointer only computed from another one (p = q + n, p = &q[i]) is not moving: "
                        "moving_variables + moving_globals + moving_fields + moving_indirect"),
    ("moving_variables", "the part of moving_pointers that are local variables or parameters, the only ones the "
                         "pass can split"),
    ("moving_globals", "the part of moving_pointers that are globals or static locals"),
    ("moving_fields", "the part of moving_pointers that are struct or union members, once per member declaration"),
    ("moving_indirect", "the part of moving_pointers reached through another pointer ((*pp)++, a[i]++), once per "
                        "variable they are reached from"),
    ("moving_refactored", "the part of moving_variables that the pass split into base + index"),
    ("compared_pointers", "distinct pointers that are not moving but are compared with another pointer (<, <=, "
                          ">, >=, ==, !=) or subtracted from one (p - q); comparisons with NULL or 0 don't count: "
                          "compared_variables + compared_globals + compared_fields + compared_indirect"),
    ("compared_variables", "the part of compared_pointers that are local variables or parameters"),
    ("compared_globals", "the part of compared_pointers that are globals or static locals"),
    ("compared_fields", "the part of compared_pointers that are struct or union members"),
    ("compared_indirect", "the part of compared_pointers reached through another pointer"),
    ("compared_refactored", "the part of compared_variables that the pass split (as members of a moving group)"),
]
ARITH = [c for c, _ in COLUMNS if c.startswith("arith_") and c != "arith_in_macro_uses"]
DEFINITIONS = ["structs", "unions", "functions"]
POINTERS = ["ptr_locals", "ptr_params", "ptr_globals", "ptr_fields"]
PLACES = ["variables", "globals", "fields", "indirect"]           # where a moving or compared pointer lives
COMPARISONS = {"<", ">", "<=", ">=", "==", "!="}
BINARY_OPS = {"+", "-", "*", "/", "%", "<<", ">>", "<", ">", "<=", ">=", "==", "!=", "&", "|", "^", "&&", "||",
              "=", ","}


def code_lines(text: str) -> int:
    """Lines with code: anything but whitespace and comments. String and
    character literals are code, even when they contain // or /*."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
            out.append("\n" * text.count("\n", i, j))      # keep line structure
            i = j
        elif c in "\"'":
            j = i + 1
            while j < n and text[j] != c and text[j] != "\n":
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        else:
            out.append(c)
            i += 1
    return sum(1 for line in "".join(out).splitlines() if line.strip())


# ---------------------------------------------------------------------------
# Source counts (libclang)

@dataclass
class SourceCounts:
    decls: dict[str, Counter] = field(default_factory=dict)        # file -> Counter of (location, category):
                                                                   # pointer declarations, and definitions
    ops: dict[str, Counter] = field(default_factory=dict)          # file -> Counter of (location, kind)
    covers: dict[str, set[str]] = field(default_factory=dict)      # unit -> project files it compiles
    header_functions: set[str] = field(default_factory=set)        # functions defined in project headers
    moving: set[tuple] = field(default_factory=set)                # pointer keys (pointer_key) of moving pointers
    compared: set[tuple] = field(default_factory=set)              # ... and of compared ones (moving included)


def _merge(into: dict, file: str, counts: Counter) -> None:
    """Across parses, the largest count at each location."""
    cur = into.setdefault(file, Counter())
    for k, v in counts.items():
        cur[k] = max(cur[k], v)


def _parse_counts(tu, root: Path, ci) -> tuple[dict[str, Counter], dict[str, Counter], set[str], set[str],
                                               set[tuple], set[tuple]]:
    K = ci.CursorKind

    def strip(c):
        while c.kind in (K.UNEXPOSED_EXPR, K.PAREN_EXPR) and list(c.get_children()):
            c = next(c.get_children())
        return c

    def canonical(t):
        return t.get_canonical()

    def is_data_ptr(t) -> bool:
        t = canonical(t)
        return t.kind == ci.TypeKind.POINTER and canonical(t.get_pointee()).kind not in (
            ci.TypeKind.FUNCTIONPROTO, ci.TypeKind.FUNCTIONNOPROTO)

    def is_ptr(t) -> bool:
        return canonical(t).kind == ci.TypeKind.POINTER

    def static_storage(d) -> bool:
        return (d.semantic_parent is not None and d.semantic_parent.kind == K.TRANSLATION_UNIT) \
            or d.storage_class == ci.StorageClass.STATIC

    def moved(c) -> str:
        c = strip(c)
        if c.kind == K.DECL_REF_EXPR and c.referenced is not None and c.referenced.kind in (K.VAR_DECL, K.PARM_DECL):
            return "arith_move_global" if c.referenced.kind == K.VAR_DECL and static_storage(c.referenced) \
                else "arith_move_variable"
        if c.kind == K.MEMBER_REF_EXPR:
            return "arith_move_field"
        return "arith_move_indirect"

    def tokens(c):
        return [t.spelling for t in c.get_tokens()]

    def op_after(c, first):
        return next((t.spelling for t in c.get_tokens() if t.extent.start.offset >= first.extent.end.offset), None)

    def same(a, b) -> bool:
        return tokens(strip(a)) == tokens(strip(b))

    def strip_casts(c):
        while c.kind in (K.UNEXPOSED_EXPR, K.PAREN_EXPR, K.CSTYLE_CAST_EXPR) and list(c.get_children()):
            c = list(c.get_children())[-1]
        return c

    def is_null(c) -> bool:
        return strip_casts(c).kind in (K.INTEGER_LITERAL, K.GNU_NULL_EXPR, K.CXX_NULL_PTR_LITERAL_EXPR)

    def place(d) -> tuple[str, int]:
        f = d.location.file
        path = Path(f.name).resolve() if f is not None else None
        name = str(path.relative_to(root)) if path is not None and root in path.parents else str(path)
        return name, d.location.offset

    def function_of(d) -> str:
        p = d.semantic_parent
        while p is not None and p.kind not in (K.FUNCTION_DECL, K.TRANSLATION_UNIT):
            p = p.semantic_parent
        return p.spelling if p is not None and p.kind == K.FUNCTION_DECL else ""

    def decl_key(d) -> tuple:
        """(where it lives, file, offset, function or struct, name): one pointer."""
        if d.kind == K.FIELD_DECL:
            parent = d.semantic_parent
            return ("fields", *place(d), parent.spelling if parent is not None else "", d.spelling)
        if d.kind == K.VAR_DECL:
            d = d.canonical                       # a global's extern declaration and its definition are one
        return ("globals" if d.kind == K.VAR_DECL and static_storage(d) else "variables", *place(d),
                function_of(d), d.spelling)

    def root_key(c) -> tuple:
        """A pointer reached through another pointer (*pp, a[i]), counted by the variable it is reached from."""
        d = next((x.referenced for x in c.walk_preorder() if x.kind == K.DECL_REF_EXPR and x.referenced is not None
                  and x.referenced.kind in (K.VAR_DECL, K.PARM_DECL)), None)
        if d is None:
            return ("indirect", rel(c) or "", c.extent.start.offset, "", "")
        return ("indirect", *place(d.canonical if d.kind == K.VAR_DECL else d), function_of(d), d.spelling)

    def pointer_key(c) -> tuple | None:
        """The pointer that [c] reads, or None (a call result, an array, a literal)."""
        c = strip_casts(c)
        kids = list(c.get_children())
        if c.kind in (K.DECL_REF_EXPR, K.MEMBER_REF_EXPR):
            d = c.referenced
            ok = d is not None and d.kind in (K.VAR_DECL, K.PARM_DECL, K.FIELD_DECL) and is_data_ptr(c.type)
            return decl_key(d) if ok else None
        if c.kind == K.ARRAY_SUBSCRIPT_EXPR:
            return root_key(c) if is_data_ptr(c.type) else None
        if c.kind == K.BINARY_OPERATOR and len(kids) == 2 and is_ptr(c.type):       # p + n reads p
            ptrs = [k for k in kids if is_ptr(k.type)]
            return pointer_key(ptrs[0]) if len(ptrs) == 1 else None
        if c.kind == K.UNARY_OPERATOR and len(kids) == 1:
            t, kt = canonical(c.type), canonical(kids[0].type)
            if t == kt:                                                       # p++ inside an expression
                return pointer_key(kids[0])
            if kt.kind == ci.TypeKind.POINTER and canonical(kt.get_pointee()) == t:  # *pp
                return root_key(c) if is_data_ptr(c.type) else None
            inner = strip_casts(kids[0])
            if t.kind == ci.TypeKind.POINTER and inner.kind == K.ARRAY_SUBSCRIPT_EXPR:  # &q[i] reads q
                return pointer_key(list(inner.get_children())[0])
        return None


    decls: dict[str, Counter] = {}
    ops: dict[str, Counter] = {}
    skip: set[tuple] = set()            # the + of p = p + n, counted as the move
    files: set[str] = set()
    header_functions: set[str] = set()
    moving: set[tuple] = set()
    compared: set[tuple] = set()
    defined: set = set()                # a struct named by a typedef is visited twice: count it once

    # Macro expansions in project files: (file, start) -> (end, macro defined in the project).
    # Code from a macro body has the location of the whole expansion.
    expansions: dict[tuple, tuple[int, bool]] = {}
    for c in tu.cursor.get_children():
        if c.kind == K.MACRO_INSTANTIATION and c.extent.start.file is not None:
            path = Path(c.extent.start.file.name).resolve()
            if root in path.parents:
                d = c.referenced
                own = d is not None and d.location.file is not None and root in Path(d.location.file.name).resolve().parents
                expansions[(str(path.relative_to(root)), c.extent.start.offset)] = (c.extent.end.offset, own)

    def in_project(d) -> bool:
        return d is not None and d.location.file is not None and root in Path(d.location.file.name).resolve().parents

    def names_project(c) -> bool:
        """[c] refers to a variable, parameter or member declared in the project."""
        return any(x.kind in (K.DECL_REF_EXPR, K.MEMBER_REF_EXPR) and in_project(x.referenced)
                   for x in c.walk_preorder())

    def origin(file: str, c, operand=None) -> str:
        """"code", "macro" (from a project macro) or "system" (from a system header's macro, so not
        the project's code). Code from a macro has the location of the macro's use: a range that
        starts where the use starts and ends within it (code written in a macro's arguments has its
        own location, except through nested macros). A system macro never names the project's
        variables, so an operation there whose pointer does was written in the argument."""
        e = expansions.get((file, c.extent.start.offset))
        if e is None or c.extent.end.offset > e[0]:
            return "code"
        if e[1]:
            return "macro"
        return "code" if operand is not None and names_project(operand) else "system"

    def rel(c) -> str | None:
        f = c.extent.start.file
        if f is None:
            return None
        path = Path(f.name).resolve()
        if root not in path.parents:
            return None
        r = path.relative_to(root)
        if r.parts[0] == ALIAS_DIR or r.name == WRAPPER:
            return None
        return str(r)

    for c in tu.cursor.walk_preorder():
        file = rel(c)
        if file is None:
            continue
        files.add(file)
        loc = (c.extent.start.offset, c.extent.end.offset, c.kind.value)
        if c.kind == K.FUNCTION_DECL and c.is_definition() and file.endswith(".h"):
            header_functions.add(c.spelling)

        # Declarations
        cat = None
        if c.kind in (K.STRUCT_DECL, K.UNION_DECL, K.FUNCTION_DECL) and c.is_definition():
            if c in defined:
                continue
            defined.add(c)
            cat = {K.STRUCT_DECL: "structs", K.UNION_DECL: "unions", K.FUNCTION_DECL: "functions"}[c.kind]
        elif c.kind == K.FIELD_DECL and is_data_ptr(c.type):
            cat = "ptr_fields"
        elif c.kind == K.VAR_DECL and c.storage_class != ci.StorageClass.EXTERN and is_data_ptr(c.type):
            # extern declarations are not counted; the definition is
            cat = "ptr_globals" if static_storage(c) else "ptr_locals"
        elif c.kind == K.PARM_DECL:
            parent = c.semantic_parent
            t = canonical(c.type)
            array = t.kind in (ci.TypeKind.CONSTANTARRAY, ci.TypeKind.INCOMPLETEARRAY, ci.TypeKind.VARIABLEARRAY)
            if parent is not None and parent.kind == K.FUNCTION_DECL and parent.is_definition() \
                    and (is_data_ptr(c.type) or array):
                cat = "ptr_params"
        if cat:
            if origin(file, c) != "system":
                decls.setdefault(file, Counter())[(loc, cat)] += 1
            continue

        # Pointer arithmetic
        kids = list(c.get_children())
        kind = None
        operand = None                  # the pointer the operation is about
        relation = None                 # two pointers compared or subtracted
        if c.kind == K.ARRAY_SUBSCRIPT_EXPR and kids and is_ptr(strip(kids[0]).type):
            kind, operand = "arith_subscript", kids[0]
        elif c.kind == K.BINARY_OPERATOR and len(kids) == 2:
            a, b = kids
            op = op_after(c, a)
            if op not in BINARY_OPS:
                # Inside a macro expansion the tokens are the macro call's:
                # tell + and - from the types (an integer added to a
                # pointer gives a pointer; a difference gives a long).
                if is_ptr(c.type) and is_ptr(a.type) != is_ptr(b.type):
                    op = "+"
                elif is_ptr(a.type) and is_ptr(b.type) and canonical(c.type).kind == ci.TypeKind.LONG:
                    op = "-"
            if op in ("+", "-") and (is_ptr(a.type) or is_ptr(b.type)):
                if (file, loc) not in skip:
                    kind = "arith_difference" if op == "-" and is_ptr(a.type) and is_ptr(b.type) else "arith_offset"
                    operand = a if is_ptr(a.type) else b
                    if kind == "arith_difference":
                        relation = kids
            elif is_ptr(a.type) and is_ptr(b.type) and (op in COMPARISONS or (
                    op not in BINARY_OPS and canonical(c.type).kind == ci.TypeKind.INT)):
                if not is_null(a) and not is_null(b):
                    relation = kids
            elif op == "=" and is_ptr(a.type):
                rhs = strip(b)
                rk = list(rhs.get_children())
                if rhs.kind == K.BINARY_OPERATOR and len(rk) == 2 and op_after(rhs, rk[0]) in ("+", "-") \
                        and is_ptr(rk[0].type) and same(rk[0], a):
                    kind, operand = moved(a), a
                    skip.add((rel(rhs), (rhs.extent.start.offset, rhs.extent.end.offset, rhs.kind.value)))
        elif c.kind == K.UNARY_OPERATOR and len(kids) == 1 and is_ptr(kids[0].type) \
                and canonical(c.type) == canonical(kids[0].type):
            # The only unary operators giving back the pointer's own type are
            # ++ and -- (*p and &p change it). Types, not tokens: macros.
            kind, operand = moved(kids[0]), kids[0]
        elif c.kind == K.COMPOUND_ASSIGNMENT_OPERATOR and len(kids) == 2 and is_ptr(kids[0].type):
            kind, operand = moved(kids[0]), kids[0]          # on a pointer, only += and -= exist
        if kind:
            where = origin(file, c, operand)
            if where != "system":
                ops.setdefault(file, Counter())[((loc, where == "macro"), kind)] += 1
                if kind.startswith("arith_move_"):
                    moving.add(pointer_key(operand) or root_key(operand))
        if relation is not None and origin(file, c, c) != "system":
            compared.update(k for k in map(pointer_key, relation) if k is not None)
    return decls, ops, files, header_functions, moving, compared


def source_counts(cfg: Config, project: Project) -> SourceCounts:
    import clang.cindex as ci
    isystem = clang_resource_include(cfg.tools.clang)
    out = SourceCounts()
    scratch = resolve(cfg.output.work_dir)
    scratch.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="c2r-stats-", dir=scratch) as tmp:
        work = Path(tmp) / project.name
        shutil.copytree(project.c_dir, work, ignore=COPY_IGNORE)
        copy = Project(project.name, work, project.rust_dir)
        units = copy.units                           # before the generated files
        headers = copy.headers
        dirs = include_dirs(copy)
        aliases = header_aliases(copy, dirs, [*system_include_dirs(), resolve(cfg.tools.compcert_stdlib) / "include"])
        write_aliases(copy, aliases)
        parses = [(u, str(u.relative_to(work))) for u in units]
        if not copy.c_sources:
            wrapper, _ = write_wrapper(copy, dirs, isystem)
            parses.insert(0, (wrapper, WRAPPER))
        parses += [(h, None) for h in headers]       # headers on their own: not units
        args = ["-std=gnu17", "-D_DEFAULT_SOURCE", *[f"-I{d}" for d in dirs],
                *([f"-I{work / ALIAS_DIR}"] if aliases else []), *(["-isystem", str(isystem)] if isystem else [])]
        index = ci.Index.create()
        root = work.resolve()
        for path, unit in parses:
            try:
                tu = index.parse(str(path), args=args + (["-x", "c"] if path.suffix == ".h" else []),
                                 options=ci.TranslationUnit.PARSE_DETAILED_PROCESSING_RECORD)
            except ci.TranslationUnitLoadError:
                continue
            decls, ops, files, header_functions, moving, compared = _parse_counts(tu, root, ci)
            out.header_functions |= header_functions
            out.moving |= moving
            out.compared |= compared
            for f, cnt in decls.items():
                _merge(out.decls, f, cnt)
            for f, cnt in ops.items():
                _merge(out.ops, f, cnt)
            if unit is not None:
                out.covers[unit] = files | ({unit} if unit != WRAPPER else set())
    return out


# ---------------------------------------------------------------------------
# One row per project

def project_row(cfg: Config, project: Project, status: dict | None) -> dict:
    counts = source_counts(cfg, project)
    row: dict[str, object] = {"project": project.name}
    units = status["units"] if status else []
    accepted_units = {u["path"] for u in units if u["accepted"]}
    row["status"] = status.get("status", "") if status else ""
    row["header_only"] = int(not project.c_sources)
    row["c_files"] = len(project.units)
    row["c_files_refactored"] = sum(1 for u in units if u["accepted"] and u["kind"] != "wrapper")
    row["header_files"] = len(project.headers)

    files = project._files(".c") + project.headers
    loc = {str(f.relative_to(project.c_dir)): code_lines(f.read_text(errors="replace")) for f in files}
    row["loc"] = sum(loc.values())
    row["loc_tests"] = sum(n for f, n in loc.items() if project.is_test(project.c_dir / f))

    decl = Counter()
    for cnt in counts.decls.values():
        for (_, cat), n in cnt.items():
            decl[cat] += n
    for c in DEFINITIONS + POINTERS:
        row[c] = decl[c]
    row["pointers"] = sum(decl[c] for c in POINTERS)

    arith = Counter()
    covered = set().union(*(counts.covers.get(u, set()) for u in accepted_units)) if accepted_units else set()
    in_refactored = from_macros = 0
    for f, cnt in counts.ops.items():
        for ((_, macro), kind), n in cnt.items():
            arith[kind] += n
            from_macros += n if macro else 0
            if f in covered:
                in_refactored += n
    for c in ARITH:
        row[c] = arith[c]
    row["pointer_arith"] = sum(arith.values())
    row["arith_in_macro_uses"] = from_macros
    row["pointer_arith_in_refactored"] = in_refactored

    # A function defined in a header is compiled, and refactored, in every unit
    # that includes it: count it once (by name). Elsewhere, per unit: two
    # files may each have a main.
    functions: dict[tuple, dict] = {}
    for u in units:
        if u["accepted"]:
            for f in u.get("split", []):
                key = (f["name"],) if f["name"] in counts.header_functions else (u["path"], f["name"])
                functions.setdefault(key, f)
    split = [s for f in functions.values() for s in f["split"]]
    cached = [k for f in functions.values() for k in f.get("cached", [])]
    row["refactored_variables"] = len(split)
    row["refactored_variables_source"] = sum(1 for s in split if not s["pointer"].startswith("$"))
    row["refactored_memory"] = len(cached)
    row["refactored"] = len(split) + len(cached)
    row["functions_refactored"] = sum(1 for f in functions.values() if f["split"] or f.get("cached"))

    # The pass's split source pointers, per refactored unit: (function, name).
    split_names = {u["path"]: {(f["name"], re.sub(r"__\d+$", "", s["pointer"]))
                               for f in u.get("split", []) for s in f["split"] if not s["pointer"].startswith("$")}
                   for u in units if u["accepted"]}

    def was_split(key) -> bool:
        where, file, _, function, name = key
        return where == "variables" and any((function, name) in names and file in counts.covers.get(u, set())
                                            for u, names in split_names.items())

    for role, keys in (("moving", counts.moving), ("compared", counts.compared - counts.moving)):
        row[f"{role}_pointers"] = len(keys)
        for where in PLACES:
            row[f"{role}_{where}"] = sum(1 for k in keys if k[0] == where)
        row[f"{role}_refactored"] = sum(1 for k in keys if was_split(k))
    if not status:
        for c in ("c_files_refactored", "pointer_arith_in_refactored", "refactored_variables",
                  "refactored_variables_source", "refactored_memory", "refactored", "functions_refactored",
                  "moving_refactored", "compared_refactored"):
            row[c] = ""
    return row


def write_stats(cfg: Config, out: Path, progress=lambda name: None) -> list[dict]:
    projects = select(discover(resolve(cfg.benchmark.c_dir), resolve(cfg.benchmark.rust_dir)), cfg.projects)
    status_path = resolve(cfg.output.refactored_dir) / "status.json"
    statuses = json.loads(status_path.read_text())["projects"] if status_path.exists() else {}
    rows = []
    for p in sorted(projects, key=lambda p: p.name.lower()):
        rows.append(project_row(cfg, p, statuses.get(p.name)))
        progress(p.name)
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=[c for c, _ in COLUMNS])
        w.writeheader()
        w.writerows(rows)
    out.with_suffix(".md").write_text(render_columns(rows, out.name, status_path.exists()))
    return rows


def render_columns(rows: list[dict], csv_name: str, have_status: bool) -> str:
    numeric = [c for c, _ in COLUMNS if c not in ("project", "status")]
    totals = {c: sum(r[c] for r in rows if r[c] != "") for c in numeric}
    lines = [
        "# Pointer statistics per project",
        "",
        f"`{csv_name}` has one row per CBench project. Generated by `uv run c2r stats` (pipeline/c2r/stats.py) "
        "from the original C with libclang, and from stage 1's `results/refactored/status.json` for the "
        "refactoring columns" + ("" if have_status else " (missing when this was generated: those columns are empty)")
        + ". Every C file counts, tests included; each declaration and operation is counted once per source "
        "location. See the module's docstring for the counting rules.",
        "",
        f"Projects: {len(rows)}. Totals: " + ", ".join(f"{c} {totals[c]}" for c in
                                                        ("loc", "functions", "pointers", "pointer_arith",
                                                         "moving_pointers", "refactored")) + ".",
        "",
        "| Column | Meaning | Total |",
        "|---|---|---|",
    ]
    for c, meaning in COLUMNS:
        lines.append(f"| `{c}` | {meaning} | {totals.get(c, '')} |")
    return "\n".join(lines) + "\n"
