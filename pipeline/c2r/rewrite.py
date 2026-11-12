"""Meaning-preserving source rewrites applied before CompCert sees a project.

Each rewrite turns a GNU extension or C23 feature that CompCert rejects into
standard C with the meaning GCC gives it. Each targets only constructs that
CompCert always rejects, so code that would compile is never changed. They run
on the temporary copy of a project (never on CBench), each can be turned off
in the config (`rewrites.<name>`), and every rewritten file records what was
done to it. They are outside the refactoring's proof; the differential check
validates them, since its front-end comparison builds the untouched original
with gcc.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from .config import RewritesConfig

COMPAT_HEADER = "c2r_compat.h"
MAX_CASE_RANGE = 4096          # longer case ranges are left alone
VOID_ROUNDS = 5                # nested void * arithmetic is rewritten one level per round


@dataclass
class Token:
    kind: str                  # num | ident | str | char | punct
    text: str
    start: int
    end: int


_PUNCT = sorted(["...", "<<=", ">>=", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||",
                 "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "##", "::"], key=len, reverse=True)


def tokenize(text: str) -> list[Token]:
    """C tokens, without comments. No preprocessing: directives are tokens too."""
    toks, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n\f\v\\":
            i += 1
        elif text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            i = n if j < 0 else j + 2
        elif c in "\"'":
            j = i + 1
            while j < n and text[j] not in (c, "\n"):
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            toks.append(Token("str" if c == '"' else "char", text[i:j], i, j))
            i = j
        elif c.isalpha() or c == "_":
            j = i + 1
            while j < n and (text[j].isalnum() or text[j] == "_"):
                j += 1
            toks.append(Token("ident", text[i:j], i, j))
            i = j
        elif c.isdigit() or (c == "." and i + 1 < n and text[i + 1].isdigit()):
            j = i + 1
            while j < n:
                if text[j] in "eEpP" and j + 1 < n and text[j + 1] in "+-":
                    j += 2
                elif text[j].isalnum() or text[j] in "._":
                    j += 1
                else:
                    break
            toks.append(Token("num", text[i:j], i, j))
            i = j
        else:
            p = next((p for p in _PUNCT if text.startswith(p, i)), c)
            toks.append(Token("punct", p, i, i + len(p)))
            i += len(p)
    return toks


Edit = tuple[int, int, str]      # replace text[start:end] with the string


def applicable(edits: list[Edit]) -> list[Edit]:
    """The edits that apply_edits applies: of two overlapping ones, the later one."""
    kept, last = [], None
    for start, end, new in sorted(set(edits), reverse=True):
        if last is None or end <= last:
            kept.append((start, end, new))
            last = start
    return kept


def apply_edits(text: str, edits: list[Edit]) -> str:
    out, last = [], len(text)
    for start, end, new in applicable(edits):
        out += [text[end:last], new]
        last = start
    out.append(text[:last])
    return "".join(reversed(out))


# ---------------------------------------------------------------------------
# Literals

_BINARY = re.compile(r"0[bB]([01]+)([uUlL]*)")
_DOUBLE_D = re.compile(r"((?:\d+\.\d*|\.\d+)(?:[eE][+-]?\d+)?|\d+[eE][+-]?\d+)[dD]")
_DECIMAL = re.compile(r"[1-9]\d*")


def literal_edits(toks: list[Token], opts: RewritesConfig) -> tuple[list[Edit], dict[str, int]]:
    edits, counts = [], {}

    def add(t: Token, new: str, name: str) -> None:
        edits.append((t.start, t.end, new))
        counts[name] = counts.get(name, 0) + 1

    for t in toks:
        if t.kind != "num":
            continue
        if opts.binary_literals and (m := _BINARY.fullmatch(t.text)):
            add(t, f"0x{int(m.group(1), 2):x}{m.group(2)}", "binary_literals")
        elif opts.double_suffix and (m := _DOUBLE_D.fullmatch(t.text)):
            add(t, m.group(1), "double_suffix")
        elif opts.large_literals and _DECIMAL.fullmatch(t.text) and 2**63 <= int(t.text) < 2**64:
            # GCC types it __int128, which CompCert lacks: this keeps the value,
            # not the type (hence off by default).
            add(t, t.text + "ULL", "large_literals")
    return edits, counts


# ---------------------------------------------------------------------------
# Statements

def label_edits(toks: list[Token]) -> list[Edit]:
    """`label: }`: a ':' directly followed by '}' ends a label (or case) with
    no statement, which C23 allows; insert an empty statement."""
    return [(a.end, a.end, " ;") for a, b in zip(toks, toks[1:]) if a.text == ":" and b.text == "}"]


_ESCAPES = {"n": 10, "t": 9, "r": 13, "0": 0, "\\": 92, "'": 39, '"': 34, "a": 7, "b": 8, "f": 12, "v": 11}


def _char_value(body: str) -> int | None:
    if len(body) == 1 and ord(body) < 128:
        return ord(body)
    if body.startswith("\\x") and len(body) > 2:
        return int(body[2:], 16)
    if body.startswith("\\") and body[1:].isdigit():
        return int(body[1:], 8)
    if len(body) == 2 and body[0] == "\\":
        return _ESCAPES.get(body[1])
    return None


def _int_value(t: Token) -> int | None:
    if t.kind == "char" and t.text.startswith("'") and t.text.endswith("'"):
        return _char_value(t.text[1:-1])
    if t.kind != "num":
        return None
    s = t.text.rstrip("uUlL")
    try:
        if s[:2] in ("0x", "0X"):
            return int(s, 16)
        if s[:2] in ("0b", "0B"):
            return int(s[2:], 2)
        if len(s) > 1 and s[0] == "0":
            return int(s, 8)
        return int(s, 10)
    except ValueError:
        return None


def _bound(toks: list[Token], i: int) -> tuple[int | None, bool, int]:
    """A case-range bound at toks[i]: (value, was a char literal, index after it)."""
    neg = i < len(toks) and toks[i].text == "-"
    j = i + 1 if neg else i
    if j >= len(toks):
        return None, False, j
    v = _int_value(toks[j])
    return (None if v is None else -v if neg else v), toks[j].kind == "char", j + 1


def case_range_edits(toks: list[Token]) -> list[Edit]:
    """`case 1 ... 3:` -> `case 1: case 2: case 3:` when both bounds are literals."""
    edits = []
    for i, t in enumerate(toks):
        if t.text != "case":
            continue
        lo, lo_char, j = _bound(toks, i + 1)
        if lo is None or j >= len(toks) or toks[j].text != "...":
            continue
        hi, hi_char, k = _bound(toks, j + 1)
        if hi is None or k >= len(toks) or toks[k].text != ":" or not 0 <= hi - lo < MAX_CASE_RANGE:
            continue
        as_char = lo_char and hi_char and all(32 <= v < 127 and chr(v) not in "'\\" for v in (lo, hi))
        labels = [f"case '{chr(v)}':" if as_char else f"case {v}:" for v in range(lo, hi + 1)]
        edits.append((t.start, toks[k].end, " ".join(labels)))
    return edits


# ---------------------------------------------------------------------------
# Empty initializers

def _matching(toks: list[Token], open_: str, close: str) -> dict[int, int]:
    pairs, stack = {}, []
    for i, t in enumerate(toks):
        if t.text == open_:
            stack.append(i)
        elif t.text == close and stack:
            j = stack.pop()
            pairs[j] = i
            pairs[i] = j
    return pairs


def empty_initializer_edits(toks: list[Token]) -> list[Edit]:
    """`= {}` and compound literals `(T){}`: an empty initializer (C23, GNU)
    zero-initializes, as `{0}` does. Only braces inside an initializer change,
    never an empty block such as `if (x) {}`."""
    braces, parens = _matching(toks, "{", "}"), _matching(toks, "(", ")")

    def starts_initializer(i: int) -> bool:
        if i == 0:
            return False
        prev = toks[i - 1]
        if prev.text == "=":
            return True
        if prev.text != ")" or i - 1 not in parens:
            return False
        j = parens[i - 1]                      # the '(' of `(T){...}`, or of `if (...)`, `f(...)`
        before = toks[j - 1] if j > 0 else None
        return (before is None or (before.kind == "punct" and before.text not in (")", "]"))
                or before.text == "return")

    edits = []
    for i, t in enumerate(toks):
        if t.text == "{" and starts_initializer(i) and i in braces:
            for k in range(i, braces[i]):
                if toks[k].text == "{" and toks[k + 1].text == "}":
                    edits.append((toks[k].start, toks[k + 1].end, "{0}"))
    return edits


# ---------------------------------------------------------------------------
# GCC builtins

BUILTINS = ("__builtin_popcount", "__builtin_popcountl", "__builtin_popcountll", "__builtin_parity",
            "__builtin_parityl", "__builtin_parityll", "__builtin_memcpy", "__builtin_memmove",
            "__builtin_memset", "__builtin_memcmp", "__builtin_strlen", "__builtin_strcmp")

COMPAT_TEXT = """\
/* Generated by c2r: portable definitions of GCC builtins that CompCert lacks,
   with the meaning GCC gives them. Passed to the preprocessor with -include. */
#ifndef C2R_COMPAT_H
#define C2R_COMPAT_H
#include <stddef.h>
void *memcpy(void *, const void *, size_t);
void *memmove(void *, const void *, size_t);
void *memset(void *, int, size_t);
int memcmp(const void *, const void *, size_t);
size_t strlen(const char *);
int strcmp(const char *, const char *);
static int c2r_popcount(unsigned long long x) { int n = 0; for (; x; x &= x - 1) n++; return n; }
#define __builtin_popcount(x) c2r_popcount((unsigned int)(x))
#define __builtin_popcountl(x) c2r_popcount((unsigned long)(x))
#define __builtin_popcountll(x) c2r_popcount((unsigned long long)(x))
#define __builtin_parity(x) (c2r_popcount((unsigned int)(x)) & 1)
#define __builtin_parityl(x) (c2r_popcount((unsigned long)(x)) & 1)
#define __builtin_parityll(x) (c2r_popcount((unsigned long long)(x)) & 1)
#define __builtin_memcpy memcpy
#define __builtin_memmove memmove
#define __builtin_memset memset
#define __builtin_memcmp memcmp
#define __builtin_strlen strlen
#define __builtin_strcmp strcmp
#endif
"""


# ---------------------------------------------------------------------------
# Arithmetic on void *

_SIDE_EFFECT_FREE = re.compile(r"[\w\s.\->\[\]]+")


def _is_void_ptr(cursor) -> bool:
    import clang.cindex as ci
    t = cursor.type.get_canonical()
    return t.kind == ci.TypeKind.POINTER and t.get_pointee().kind == ci.TypeKind.VOID


def _is_integer(cursor) -> bool:
    import clang.cindex as ci
    k = cursor.type.get_canonical().kind
    return k in (ci.TypeKind.BOOL, ci.TypeKind.CHAR_U, ci.TypeKind.UCHAR, ci.TypeKind.USHORT, ci.TypeKind.UINT,
                 ci.TypeKind.ULONG, ci.TypeKind.ULONGLONG, ci.TypeKind.CHAR_S, ci.TypeKind.SCHAR,
                 ci.TypeKind.SHORT, ci.TypeKind.INT, ci.TypeKind.LONG, ci.TypeKind.LONGLONG, ci.TypeKind.ENUM)


def _void_edit(cursor, text: str) -> Edit | None:
    """The rewrite of one operator on a void * operand, or None."""
    import clang.cindex as ci
    start, end = cursor.extent.start.offset, cursor.extent.end.offset
    toks = [t.spelling for t in cursor.get_tokens()]
    # Only expressions written out in this file: not ones from a macro expansion.
    if [t.text for t in tokenize(text[start:end])] != toks:
        return None
    kids = list(cursor.get_children())
    src = lambda k: text[k.extent.start.offset:k.extent.end.offset]

    if cursor.kind == ci.CursorKind.UNARY_OPERATOR and len(kids) == 1 and _is_void_ptr(kids[0]):
        a = src(kids[0])
        prefix = toks[0] in ("++", "--")
        op = toks[0] if prefix else toks[-1]
        if op not in ("++", "--") or not _SIDE_EFFECT_FREE.fullmatch(a):
            return None
        if not prefix:
            # A postfix ++/-- yields the old value: only rewrite where it is discarded.
            before = text[:start].rstrip()[-1:]
            after = text[end:].lstrip()[:1]
            if before not in (";", "{", "}") or after not in (";", ")"):
                return None
        ty = kids[0].type.spelling
        return start, end, f"({a} = ({ty})((char *)({a}) {op[0]} 1))"

    if len(kids) != 2:
        return None
    a, b = kids
    op = next((t.spelling for t in cursor.get_tokens() if t.extent.start.offset >= a.extent.end.offset), None)
    if cursor.kind == ci.CursorKind.COMPOUND_ASSIGNMENT_OPERATOR:
        if op in ("+=", "-=") and _is_void_ptr(a) and _is_integer(b) and _SIDE_EFFECT_FREE.fullmatch(src(a)):
            return start, end, f"({src(a)} = ({a.type.spelling})((char *)({src(a)}) {op[0]} ({src(b)})))"
        return None
    if cursor.kind != ci.CursorKind.BINARY_OPERATOR:
        return None
    if op in ("+", "-") and _is_void_ptr(a) and _is_integer(b):
        return start, end, f"(({a.type.spelling})((char *)({src(a)}) {op} ({src(b)})))"
    if op == "+" and _is_integer(a) and _is_void_ptr(b):
        return start, end, f"(({b.type.spelling})(({src(a)}) + (char *)({src(b)})))"
    if op == "-" and _is_void_ptr(a) and _is_void_ptr(b):
        return start, end, f"((char *)({src(a)}) - (char *)({src(b)}))"
    return None


def void_pointer_edits(units: list[Path], files: set[Path], args: list[str]) -> dict[Path, list[Edit]]:
    """Edits, per project file, for arithmetic on void * (a GNU extension with
    sizeof(void) == 1): the same arithmetic on char *, cast back to the
    original type. Parsing each unit covers the headers it includes."""
    import clang.cindex as ci
    kinds = (ci.CursorKind.BINARY_OPERATOR, ci.CursorKind.COMPOUND_ASSIGNMENT_OPERATOR,
             ci.CursorKind.UNARY_OPERATOR)
    index = ci.Index.create()
    edits: dict[Path, list[Edit]] = {}
    texts: dict[Path, str] = {}
    for unit in units:
        try:
            tu = index.parse(str(unit), args=args)
        except ci.TranslationUnitLoadError:
            continue
        for c in tu.cursor.walk_preorder():
            if c.kind not in kinds or not c.extent.start.file:
                continue
            path = Path(c.extent.start.file.name).resolve()
            if path not in files:
                continue
            if path not in texts:
                texts[path] = path.read_text(errors="replace")
            edit = _void_edit(c, texts[path])
            if edit:
                edits.setdefault(path, []).append(edit)
    return edits


# ---------------------------------------------------------------------------
# Applying them to a project

def apply_rewrites(opts: RewritesConfig, root: Path, files: list[Path], units: list[Path],
                   clang_args: list[str]) -> tuple[dict[str, dict[str, int]], list[str]]:
    """Rewrite the project files under `root` in place. Returns what was done
    to each file (path relative to root -> rewrite -> count) and extra
    preprocessor flags (the -include of the builtins header)."""
    applied: dict[str, dict[str, int]] = {}
    real_root = root.resolve()

    def note(path: Path, name: str, n: int) -> None:
        if n:
            counts = applied.setdefault(str(path.resolve().relative_to(real_root)), {})
            counts[name] = counts.get(name, 0) + n

    uses_builtins = False
    for f in files:
        text = f.read_text(errors="replace")
        toks = tokenize(text)
        edits, counts = literal_edits(toks, opts)
        for name, n in counts.items():
            note(f, name, n)
        for name, enabled, found in (("labels_at_block_end", opts.labels_at_block_end, label_edits),
                                     ("case_ranges", opts.case_ranges, case_range_edits),
                                     ("empty_initializers", opts.empty_initializers, empty_initializer_edits)):
            if enabled:
                new = found(toks)
                note(f, name, len(new))
                edits += new
        if opts.gnu_builtins:
            n = sum(1 for t in toks if t.kind == "ident" and t.text in BUILTINS)
            note(f, "gnu_builtins", n)
            uses_builtins |= n > 0
        if edits:
            f.write_text(apply_edits(text, edits))

    flags = []
    if uses_builtins:
        (root / COMPAT_HEADER).write_text(COMPAT_TEXT)
        flags = ["-include", COMPAT_HEADER]

    if opts.void_pointer_arithmetic:
        project_files = {f.resolve() for f in files}
        args = [*clang_args, *(["-include", str(root / COMPAT_HEADER)] if uses_builtins else [])]
        for _ in range(VOID_ROUNDS):          # an outer operator is rewritten once its inner ones are
            edits = void_pointer_edits(units, project_files, args)
            if not edits:
                break
            for path, file_edits in edits.items():
                path.write_text(apply_edits(path.read_text(errors="replace"), file_edits))
                note(path, "void_pointer_arithmetic", len(applicable(file_edits)))
    return applied, flags
