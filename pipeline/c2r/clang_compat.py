"""Small, auditable compatibility steps for dependency parsing only.

Source normalization preserves byte offsets. Retry flags are selected from
actual diagnostics; explicit compilation databases and accepted CompCert units
are never retried under a different preprocessing or target configuration.
"""

from __future__ import annotations

import json
import os
import re
from collections.abc import Sequence
from importlib.metadata import PackageNotFoundError, version
from pathlib import Path

from .config import REPO_ROOT
from .rewrite import _DOUBLE_D, tokenize


def local_headers() -> tuple[Path | None, Path | None]:
    """Find headers extracted by setup_clang_parser.py for this libclang."""
    try:
        installed = version("libclang")
    except PackageNotFoundError:
        return None, None
    cache = Path(os.environ.get("C2R_CLANG_HEADERS", str(REPO_ROOT / "tools/.cache/c2r-clang"))).expanduser()
    metadata = cache / f"libclang-{installed}" / "metadata.json"
    if not metadata.is_file():
        return None, None
    data = json.loads(metadata.read_text())
    if data.get("libclang_version") != installed:
        return None, None
    resource, x86 = Path(data["resource_include"]), Path(data["x86_include"])
    return (resource if (resource / "stddef.h").is_file() else None,
            x86 if (x86 / "sys/mman.h").is_file() else None)


def x86_system_arguments(args: Sequence[str], include: Path | None) -> list[str]:
    if include is None or str(include) in args:
        return []
    if any(a in {"--sysroot", "-isysroot", "-nostdinc", "-nostdlibinc"}
           or a.startswith(("--sysroot=", "-isysroot")) for a in args):
        return []
    return ["-nostdlibinc", "-isystem", str(include)]


def target_is_x86(args: Sequence[str]) -> bool:
    target = ""
    for i, arg in enumerate(args):
        if arg in {"-target", "--target", "-arch"} and i + 1 < len(args):
            target = args[i + 1]
        elif arg.startswith(("--target=", "-target=", "-arch=")):
            target = arg.split("=", 1)[1]
    return target.startswith(("x86_64", "amd64"))


def literal_build_definitions(root: Path) -> dict[str, str]:
    """Read simple quoted -DNAME=\"$(VAR)\" strings; never execute make.

    Only a unique literal assignment is usable. This does not evaluate make;
    commands and further variable expansion are unsupported.
    """
    values: dict[str, set[str]] = {}
    references: dict[str, set[str]] = {}
    for filename in ("Makefile", "makefile", "GNUmakefile", "config.mk"):
        path = root / filename
        if not path.is_file():
            continue
        text = path.read_text(errors="replace")
        for name, value in re.findall(r"^\s*([A-Za-z_]\w*)\s*[:?]?=\s*([A-Za-z0-9_.+-]+)\s*$", text, re.M):
            values.setdefault(name, set()).add(value)
        for name, variable in re.findall(r'-D([A-Za-z_]\w*)=\\?"\$\(([A-Za-z_]\w*)\)\\?"', text):
            references.setdefault(name, set()).add(variable)
    definitions = {}
    for name, variables in references.items():
        if len(variables) == 1:
            options = values.get(next(iter(variables)), set())
            if len(options) == 1:
                definitions[name] = f'-D{name}="{next(iter(options))}"'
    return definitions


def normalize_double_suffix(data: bytes) -> tuple[bytes, list[dict]]:
    # Latin-1 gives one character per byte, including in non-ASCII comments.
    # Tokenization avoids changing strings, character literals and comments.
    normalized = bytearray(data)
    edits = []
    for token in tokenize(data.decode("latin-1")):
        if token.kind == "num" and _DOUBLE_D.fullmatch(token.text):
            offset = token.end - 1
            normalized[offset] = ord(" ")
            edits.append({"rule": "double_suffix", "offset": offset,
                          "original": token.text, "parsed": token.text[:-1]})
    return bytes(normalized), edits


def _defines(args: Sequence[str], name: str) -> bool:
    for i, arg in enumerate(args):
        if arg in {"-D", "-U"} and i + 1 < len(args):
            value = args[i + 1]
        elif arg.startswith(("-D", "-U")):
            value = arg[2:]
        else:
            continue
        if value.split("=", 1)[0] == name:
            return True
    return False


def explicit_target(args: Sequence[str]) -> bool:
    return any(arg in {"-target", "--target", "-arch"}
               or arg.startswith(("--target=", "-target=", "-arch=")) for arg in args)


def retry_arguments(args: list[str], messages: Sequence[str], *,
                    allow_target: bool, allow_standard: bool,
                    x86_include: Path | None = None,
                    build_definitions: dict[str, str] | None = None) -> tuple[list[str], list[str]]:
    """Return a bounded next configuration, or the unchanged flags if unknown.

    Do not invent platform constants or suppress parse errors. Feature macros
    expose the declarations from the selected platform's real system headers.
    """
    out = list(args)
    notes = []
    text = "\n".join(messages)
    missing_math = re.search(r"undeclared identifier 'M_(?:E|LOG2E|LOG10E|LN2|LN10|PI|PI_2|PI_4|1_PI|2_PI|2_SQRTPI|SQRT2|SQRT1_2)'", text)
    missing_map = "undeclared identifier 'MAP_32BIT'" in text
    missing_posix = any(message in text for message in (
        "undeclared identifier 'CLOCK_REALTIME'", "undeclared identifier 'CLOCK_MONOTONIC'",
        "undeclared identifier 'PATH_MAX'", "undeclared identifier 'ssize_t'",
        "incomplete type 'struct timespec'", "incomplete element type 'struct timespec'",
        "incomplete type 'struct sigaction'"))
    if (missing_math or missing_map or missing_posix) and not _defines(out, "_DEFAULT_SOURCE"):
        out.append("-D_DEFAULT_SOURCE=1")
        notes.append("Enabled _DEFAULT_SOURCE to expose system-header declarations.")
    for name, definition in sorted((build_definitions or {}).items()):
        if f"undeclared identifier '{name}'" in text and not _defines(out, name):
            out.append(definition)
            notes.append(f"Recovered {definition} from a unique literal build-file definition.")
    if allow_standard and "requires a named parameter before '...'" in text:
        if not any(arg in {"-std=c2x", "-std=gnu2x", "-std=c23", "-std=gnu23"} for arg in out):
            out.append("-std=c2x")
            notes.append("Selected C23 parsing for a variadic function without a named parameter.")
    needs_x86 = "only meant to be used on x86 and x64 architecture" in text or missing_map
    if allow_target and needs_x86:
        # A target option changes builtins and headers together. Defining
        # __x86_64__ alone would mix incompatible ABI assumptions.
        filtered = []
        skip = False
        for arg in out:
            if skip:
                skip = False
                continue
            if arg in {"-target", "--target", "-arch"}:
                skip = True
            elif not arg.startswith(("--target=", "-target=", "-arch=", "-D__COMPCERT_WCHAR_TYPE__=")):
                filtered.append(arg)
        out = [*filtered, "-target", "x86_64-unknown-linux-gnu", "-D__COMPCERT_WCHAR_TYPE__=int"]
        out += x86_system_arguments(out, x86_include)
        if out != args:
            notes.append("Selected x86_64 for original-C dependency parsing after x86-only header diagnostics; this is not a CompCert proof or target conversion.")
    return out, notes
