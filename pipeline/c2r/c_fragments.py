"""Index top-level declarations in normalized C emitted by PrintClight.

This is a balanced-token splitter for that printer's output, not a C type
checker. It preserves the emitted text, including dollar-prefixed identifiers.
The original C is analyzed with libclang instead.
"""

from __future__ import annotations

import re
from dataclasses import dataclass


_TOKEN = re.compile(
    r'(?P<skip>\s+|/\*.*?\*/|//[^\n]*)'
    r'|(?P<string>(?:u8|[LuU])?"(?:\\.|[^"\\])*"|(?:[LuU])?\'(?:\\.|[^\'\\])*\')'
    r'|(?P<identifier>[a-zA-Z_$][a-zA-Z_0-9$]*)'
    r'|(?P<other>.)', re.S)
_IDENTIFIER = re.compile(r"[a-zA-Z_$][a-zA-Z_0-9$]*\Z")
_TYPE_WORDS = {"void", "char", "short", "int", "long", "float", "double", "signed", "unsigned",
               "const", "volatile", "restrict", "extern", "static", "register", "_Bool",
               "_Complex", "__builtin_va_list", "inline", "__inline__", "struct", "union", "enum"}


@dataclass(frozen=True)
class Token:
    text: str
    start: int
    end: int


def tokens(source: str) -> list[Token]:
    return [Token(m.group(), m.start(), m.end()) for m in _TOKEN.finditer(source) if m.lastgroup != "skip"]


def identifiers(source: str) -> set[str]:
    return {t.text for t in tokens(source) if _IDENTIFIER.fullmatch(t.text)}


def _declarator(header: list[Token]) -> tuple[str, bool]:
    """PrintClight uses primitive/tag types, so the first declarator name wins.

    This also handles arrays of function pointers and functions returning a
    function pointer: (*table[N])(...) versus (*factory(...))(...).
    """
    for i, token in enumerate(header):
        if (_IDENTIFIER.fullmatch(token.text) and token.text not in _TYPE_WORDS
                and (not i or header[i - 1].text not in {"struct", "union", "enum"})):
            return token.text, i + 1 < len(header) and header[i + 1].text == "("
    return "", False


def _function_name(header: list[Token]) -> str | None:
    if any(t.text == "=" for t in header):
        return None
    name, function = _declarator(header)
    return name if function else None


@dataclass(frozen=True)
class CFragment:
    kind: str
    name: str
    code: str
    declaration: str
    definition: bool
    start: int
    end: int


class FragmentIndex:
    def __init__(self, source: str):
        self.fragments: list[CFragment] = []
        self.by_name: dict[str, list[CFragment]] = {}
        ts = tokens(source)
        start = 0
        parens = brackets = braces = 0
        function = None
        opening = None
        for i, token in enumerate(ts):
            word = token.text
            if word == "(":
                parens += 1
            elif word == ")":
                parens -= 1
            elif word == "[":
                brackets += 1
            elif word == "]":
                brackets -= 1
            elif word == "{":
                if braces == parens == brackets == 0:
                    opening = i
                    function = _function_name(ts[start:i])
                braces += 1
            elif word == "}":
                braces -= 1
                if braces == 0 and function:
                    self._add(source, ts[start:i + 1], function, opening - start)
                    start = i + 1
                    function = opening = None
            elif word == ";" and braces == parens == brackets == 0:
                self._add(source, ts[start:i + 1], None, None)
                start = i + 1
                opening = None
            if min(parens, brackets, braces) < 0:
                raise ValueError("unbalanced delimiters in emitted Clight C")
        if parens or brackets or braces or start < len(ts):
            raise ValueError("incomplete declaration in emitted Clight C")

    def _add(self, source: str, ts: list[Token], function: str | None, opening: int | None) -> None:
        if not ts:
            return
        start, end = ts[0].start, ts[-1].end
        code = source[start:end]
        if function:
            declaration = source[start:ts[opening].start].rstrip() + ";"
            fragment = CFragment("function", function, code, declaration, True, start, end)
        else:
            words = [t.text for t in ts]
            record = next((i for i, w in enumerate(words) if w in {"struct", "union"}), None)
            if (record is not None and record + 2 < len(words)
                    and words[record + 2] in {"{", ";"} and "=" not in words[:record + 2]):
                fragment = CFragment(words[record], words[record + 1], code, code,
                                     words[record + 2] == "{", start, end)
            elif name := _function_name(ts):
                fragment = CFragment("function", name, code, code, False, start, end)
            else:
                # PrintClight emits a separate declaration for each global.
                eq = words.index("=") if "=" in words else len(words) - 1
                head = words[:eq]
                name, _ = _declarator(ts[:eq])
                if not name or name in _TYPE_WORDS:
                    raise ValueError(f"cannot identify emitted declaration: {code[:100]}")
                declaration = source[start:ts[eq].start].rstrip() + ";" if "=" in words else code
                fragment = CFragment("global", name, code, declaration, "extern" not in head, start, end)
        self.fragments.append(fragment)
        self.by_name.setdefault(fragment.name, []).append(fragment)

    def find(self, kind: str, name: str) -> CFragment | None:
        matches = [f for f in self.by_name.get(name, ()) if f.kind == kind]
        definitions = [f for f in matches if f.definition]
        if len(definitions) > 1:
            raise ValueError(f"ambiguous emitted definition for {kind} {name}")
        return definitions[0] if definitions else matches[0] if matches else None

    def support(self, code: str, excluded: set[tuple[str, str]], *,
                definitions: set[tuple[str, str]] | None = None) -> list[CFragment]:
        """Follow declarations, plus required generated definitions when asked."""
        definitions = definitions or set()
        pending = list(sorted(identifiers(code)))
        seen, chosen = set(), {}
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            for fragment in self.by_name.get(name, ()):
                key = fragment.kind, fragment.name
                if key in excluded or key in chosen:
                    continue
                best = self.find(*key)
                chosen[key] = best
                pending.extend(sorted(identifiers(best.code if key in definitions else best.declaration) - seen))
        return sorted(chosen.values(), key=lambda f: f.start)
