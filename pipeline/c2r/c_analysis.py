"""Parse original C in a temporary project copy, without invoking CompCert.

Headers are parsed through compilation units, not as standalone programs.
The caller must keep this context open while using cursors or source extents.
"""

from __future__ import annotations

import json
import re
import shlex
import shutil
import tempfile
from collections.abc import Iterator, Mapping, Sequence
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path

from .benchmark import Project
from .clang_compat import (explicit_target, literal_build_definitions, local_headers,
                           normalize_double_suffix, retry_arguments, target_is_x86,
                           x86_system_arguments)
from .refactor import (ALIAS_DIR, COPY_IGNORE, WRAPPER, header_aliases, include_dirs,
                       system_include_dirs, write_aliases, write_wrapper)
from .tools import clang_resource_include


@dataclass
class ParsedUnit:
    path: str
    arguments: list[str]
    configuration: str
    tu: object | None
    error: str | None = None
    attempts: list[dict] = field(default_factory=list)
    compatibility: list[str] = field(default_factory=list)


@dataclass
class ParsedProject:
    root: Path
    original_root: Path
    units: list[ParsedUnit]
    generated_units: set[str] = field(default_factory=set)
    normalizations: dict[str, list[dict]] = field(default_factory=dict)
    aliases: dict[str, str] = field(default_factory=dict)

    def original_bytes(self, path: str) -> bytes:
        relative = self.relative_path(path)
        original = self.original_root / relative if relative is not None else None
        return original.read_bytes() if original is not None and original.is_file() else Path(path).read_bytes()

    def original_end(self, path: str | None, offset: int) -> int:
        relative = self.relative_path(path) if path else None
        # A normalized suffix becomes trailing whitespace. A declaration's
        # final token may end just before it; include the suffix in the saved
        # original source extent, without shifting any other locations.
        return offset + int(any(e["offset"] == offset for e in self.normalizations.get(relative, [])))

    def relative_path(self, path: str | Path) -> str | None:
        resolved = Path(path).resolve()
        for root in (self.root, self.original_root):
            if resolved.is_relative_to(root):
                return resolved.relative_to(root).as_posix()
        return None

    def stable_text(self, text: str) -> str:
        for root in (self.root, self.original_root):
            text = re.sub(re.escape(str(root)) + r"(?=/|$)", "$PROJECT", text)
        return text


def compilation_commands(path: Path) -> dict[Path, list[tuple[Path, list[str]]]]:
    """Read a compile_commands.json; never execute its command strings."""
    if path.is_dir():
        path = path / "compile_commands.json"
    data = json.loads(path.read_text())
    if not isinstance(data, list):
        raise ValueError(f"{path}: expected an array of compilation commands")
    commands: dict[Path, list[tuple[Path, list[str]]]] = {}
    for entry in data:
        if not isinstance(entry, dict) or not isinstance(entry.get("file"), str):
            raise ValueError(f"{path}: each command needs a file")
        directory_name = entry.get("directory", str(path.resolve().parent))
        if not isinstance(directory_name, str):
            raise ValueError(f"{path}: directory must be a string")
        directory = Path(directory_name)
        if not directory.is_absolute():
            directory = path.resolve().parent / directory
        directory = directory.resolve()
        argv = entry.get("arguments")
        if argv is None and isinstance(entry.get("command"), str):
            argv = shlex.split(entry["command"])
        if not isinstance(argv, list) or not argv or not all(isinstance(a, str) for a in argv):
            raise ValueError(f"{path}: each command needs nonempty arguments or a command string")
        source = (directory / entry["file"]).resolve()
        commands.setdefault(source, []).append((directory, argv))
    return commands


def _parse_arguments(argv: list[str], source: Path, directory: Path) -> list[str]:
    """Remove driver/output arguments, retaining actual preprocessing options."""
    i = 1
    if Path(argv[0]).name in {"ccache", "sccache", "distcc"}:
        i += 1
    out = []
    takes_value = {"-o", "-MF", "-MT", "-MQ", "-MJ", "--serialize-diagnostics"}
    path_options = {"-I", "-isystem", "-iquote", "-idirafter", "-include", "-imacros",
                    "-isysroot", "-resource-dir", "--sysroot", "-F", "-iframework"}
    other_options = {"-D", "-U", "-x", "-target", "--target", "-std", "-Xclang",
                     "-Xpreprocessor", "-arch"}
    while i < len(argv):
        arg = argv[i]
        i += 1
        if arg.startswith("@"):
            raise ValueError("response files in compilation commands are not supported; expand them first")
        if arg in takes_value:
            i += 1
        elif arg in {"-c", "-S", "-E", "-MD", "-MMD", "-MP", "-MG"}:
            continue
        elif any(arg.startswith(p) and arg != p for p in ("-o", "-MF", "-MT", "-MQ", "-MJ")):
            continue
        elif arg in path_options | other_options:
            if i == len(argv):
                raise ValueError(f"missing argument after {arg}")
            out.extend((arg, argv[i]))
            i += 1
        elif not arg.startswith("-") and (directory / arg).resolve() == source:
            continue
        else:
            out.append(arg)
    return out


def preprocessor_flags(flags: Sequence[str]) -> list[str]:
    """The subset of CompCert flags understood as preprocessing flags by Clang."""
    out = []
    i = 0
    while i < len(flags):
        flag = flags[i]
        i += 1
        if flag in {"-D", "-U", "-I", "-include", "-imacros", "-isystem", "-iquote",
                    "-idirafter", "-isysroot", "--sysroot"}:
            if i == len(flags):
                raise ValueError(f"missing argument after {flag}")
            out.extend((flag, flags[i]))
            i += 1
        elif flag.startswith(("-D", "-U", "-I", "-std=", "-Wp,", "--sysroot=",
                              "-isystem", "-iquote", "-idirafter", "-isysroot", "-include", "-imacros")):
            out.append(flag)
    return out


def _remap_arguments(args: Sequence[str], original: Path, root: Path) -> list[str]:
    # Never rewrite a -D value: it may intentionally contain a source string
    # naming the original directory rather than a compiler search path.
    out = []
    definition = False
    for arg in args:
        if definition or arg.startswith(("-D", "-U")):
            out.append(arg)
        else:
            out.append(re.sub(re.escape(str(original)) + r"(?=/|$)", str(root), arg))
        definition = arg in {"-D", "-U"}
    return out


@contextmanager
def parse_project(project: Project, *, clang_args: Sequence[str] = (),
                  default_args: Sequence[str] = ("-std=c99", "-U__GNUC__"),
                  unit_args: Mapping[str, Sequence[str]] | None = None,
                  compile_commands: Path | None = None, clang: str = "clang",
                  work_dir: Path | None = None,
                  unit_paths: Sequence[str] | None = None,
                  double_suffix: bool = False, compatibility: bool = False,
                  allow_target_retry: bool = False,
                  strict_units: Sequence[str] = ()) -> Iterator[ParsedProject]:
    """Parse all units, retaining failed parses and their diagnostics.

    A compilation database supplies the base arguments when present. Otherwise
    default_args and per-unit overrides are used. clang_args is appended in
    either case. Multiple database commands for one file are ambiguous and
    recorded as a failure rather than silently merging build configurations.
    Compatibility parsing normalizes double suffixes only in this temporary
    copy, keeping byte offsets. Optional diagnostic-driven retries are limited
    to units without an explicit database or accepted stage-1 configuration.
    """
    import clang.cindex as ci

    original = project.c_dir.resolve()
    database = compile_commands
    if database is None and (original / "compile_commands.json").is_file():
        database = original / "compile_commands.json"
    commands = compilation_commands(database) if database is not None else None
    if work_dir:
        work_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="c2r-dependencies-", dir=work_dir) as tmp:
        root = Path(tmp) / project.name
        shutil.copytree(original, root, ignore=COPY_IGNORE)
        root = root.resolve()
        copy = Project(project.name, root, project.rust_dir)
        build_definitions = literal_build_definitions(root) if compatibility else {}
        normalizations = {}
        if double_suffix:
            for path in [*copy._files(".c"), *copy.headers]:
                data, edits = normalize_double_suffix(path.read_bytes())
                if edits:
                    path.write_bytes(data)
                    normalizations[path.relative_to(root).as_posix()] = edits
        units = copy.units
        if unit_paths is not None:
            selected = set(unit_paths)
            # A library .c can be included directly by a test while still being
            # a standalone library translation unit in the selected scope.
            units = sorted(root / p for p in selected if (root / p).is_file())
        dirs = include_dirs(copy)
        aliases = header_aliases(copy, dirs, list(system_include_dirs()))
        write_aliases(copy, aliases)
        local_resource, x86_include = local_headers()
        resource = local_resource or clang_resource_include(clang)
        generated_units = set()
        if not copy.c_sources and copy.headers:
            wrapper, _ = write_wrapper(copy, dirs, resource)
            units = [wrapper, *units]
            generated_units.add(WRAPPER)
        includes = [f"-I{d}" for d in dirs]
        if aliases:
            includes.append(f"-I{root / ALIAS_DIR}")
        if resource:
            includes.extend(("-isystem", str(resource)))
        parsed = ParsedProject(root, original, [], generated_units, normalizations,
                               {alias: path.relative_to(root).as_posix() for alias, path in aliases.items()})
        try:
            index = ci.Index.create()
        except ci.LibclangError as exc:
            raise RuntimeError(f"cannot load libclang: {exc}") from exc
        for source in units:
            rel = source.relative_to(root).as_posix()
            original_source = original / rel
            configuration = "defaults"
            args: list[str] = []
            attempts = []
            notes = []
            try:
                if commands is not None and rel != WRAPPER:
                    entries = commands.get(original_source, [])
                    if len(entries) != 1:
                        raise ValueError(f"expected one compilation command for {rel}, found {len(entries)}")
                    directory, argv = entries[0]
                    args = ["-working-directory", str(directory),
                            *_parse_arguments(argv, original_source, directory)]
                    configuration = "compilation_database"
                else:
                    args = [*default_args, *(unit_args or {}).get(rel, ())]
                    configuration = "per_unit" if rel in (unit_args or {}) else "defaults"
                # Fallback include paths come last, so explicit build paths win.
                include_args = includes
                if resource and any(a == "-resource-dir" or a.startswith("-resource-dir=")
                                    for a in [*args, *clang_args]):
                    include_args = includes[:-2]  # Let Clang honor the explicit resource directory.
                args += [*clang_args, *include_args]
                args = _remap_arguments(args, original, root)
                if commands is None and target_is_x86(args):
                    args += x86_system_arguments(args, x86_include)
                for _ in range(4):
                    tu = index.parse(str(source), args=args,
                                     options=ci.TranslationUnit.PARSE_DETAILED_PROCESSING_RECORD)
                    errors = [d.spelling for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
                    attempts.append({"arguments": list(args), "errors": errors})
                    if not errors or not compatibility or commands is not None or rel in strict_units:
                        break
                    next_args, changes = retry_arguments(args, errors,
                        allow_target=allow_target_retry and not explicit_target(clang_args),
                        allow_standard=not any(a.startswith("-std") for a in clang_args),
                        x86_include=x86_include, build_definitions=build_definitions)
                    if next_args == args or len(attempts) == 4:
                        break
                    args = next_args
                    notes.extend(changes)
                parsed.units.append(ParsedUnit(rel, args, configuration, tu, attempts=attempts,
                                               compatibility=notes))
            except (ci.TranslationUnitLoadError, ValueError) as exc:
                parsed.units.append(ParsedUnit(rel, args, configuration, None, str(exc), attempts, notes))
        yield parsed
