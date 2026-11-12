"""Stage 1: run ptridxgen on every C file of each project.

`run_project` compiles a temporary copy of a project and returns a
ProjectRecord holding what later stages need, in memory: each unit's original
C, its Clight without the refactoring, its Clight after the refactoring, and
the facts ptridxgen reports. A project is accepted when CompCert accepts every
one of its units.

`write_view` writes a readable view of the stage into <refactored_dir>: for an
accepted project only the refactored files, for a rejected one only its
original .c and .h files, plus status.json and README.md for every project
processed so far.
"""

from __future__ import annotations

import functools
import json
import os
import re
import shutil
import tempfile
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import date
from pathlib import Path

from .benchmark import Project, discover, select, source_code
from .config import Config, resolve
from .diagnose import categorize, first_errors, needed_options, primary_error
from .rewrite import apply_rewrites
from .tools import clang_resource_include, compcert_target, run

WRAPPER = "c2r_header_only.c"
ALIAS_DIR = "c2r_include"     # forwarding headers for includes the benchmark layout broke
COPY_IGNORE = shutil.ignore_patterns("CMakeFiles", "*.o", ".git")

# `#ifdef FOO_IMPLEMENTATION`-style switches that single-header libraries use
# to emit their code. Include guards (`..._H`) are not switches.
_IMPL_GUARD = re.compile(r"^\s*#\s*if(?:n?def)?\s+(?:defined\s*\(\s*)?(\w*IMPL\w*|[A-Z][A-Z0-9_]*_MAIN)\b", re.M)
_INCLUDE = re.compile(r'^\s*#\s*include\s*"([^"]+)"', re.M)
_ANY_INCLUDE = re.compile(r'^\s*#\s*include\s*[<"]([^">]+)[">]', re.M)


@dataclass
class UnitRecord:
    path: str                        # the C file, relative to the project root
    kind: str                        # library | test | auxiliary | wrapper
    out_path: str                    # where its refactored Clight goes in the view
    source: str                      # the original C (for the wrapper: the generated wrapper)
    accepted: bool = False
    flags: list[str] | None = None   # the CompCert flags that were accepted
    clight: str | None = None        # Clight without the refactoring (ptridxgen -no-pass)
    refactored: str | None = None    # Clight after the refactoring
    rocq: str | None = None          # the refactored program as a Rocq AST, if refactor.keep_rocq_ast
    facts: dict | None = None        # ptridxgen's facts file
    clight_obj: bytes | None = None      # the Clight compiled by CompCert's backend (objects=True)
    refactored_obj: bytes | None = None  # the refactored Clight compiled by CompCert's backend
    object_error: str | None = None      # why the objects could not be compiled
    rewrites: dict[str, int] = field(default_factory=dict)   # source rewrites applied to this file
    errors: list[dict] = field(default_factory=list)   # one {"flags", "error", "category"} per failed attempt


@dataclass
class ProjectRecord:
    name: str
    c_dir: Path                      # the original project
    accepted: bool                   # every unit accepted
    header_only: bool
    units: list[UnitRecord]
    aliases: dict[str, str] = field(default_factory=dict)   # #include path -> real header
    rewrites: dict[str, dict[str, int]] = field(default_factory=dict)   # file -> rewrites applied

    @property
    def status(self) -> str:
        """accepted (every unit), partial (some), or rejected (none)."""
        n = sum(u.accepted for u in self.units)
        return "accepted" if self.units and n == len(self.units) else "partial" if n else "rejected"


# ---------------------------------------------------------------------------
# Preparing a project for CompCert

def include_dirs(project: Project) -> list[Path]:
    """The project root, every directory with a header and their parents (for
    includes such as "genetic/population.h"), and every directory with a .c
    file (for includes such as "../tinyfseq.h" from test/fuzz/)."""
    dirs = {project.c_dir} | {u.parent for u in project.units}
    for h in project.headers:
        d = h.parent
        while d != project.c_dir and project.c_dir in d.parents:
            dirs.add(d)
            d = d.parent
    return sorted(dirs)


@functools.lru_cache(maxsize=None)
def system_include_dirs() -> tuple[Path, ...]:
    """The preprocessor's <...> search path (CompCert preprocesses with gcc)."""
    _, out = run(["gcc", "-E", "-v", "-x", "c", "/dev/null"])
    lines = [line.strip() for line in out.splitlines()]
    try:
        start, end = lines.index("#include <...> search starts here:") + 1, lines.index("End of search list.")
    except ValueError:
        return ()
    return tuple(Path(line) for line in lines[start:end])


def header_aliases(project: Project, dirs: list[Path], system_dirs: list[Path]) -> dict[str, Path]:
    """Includes that resolve nowhere but name exactly one project header.

    CRUST-Bench moved some projects' headers, so their own #include paths no
    longer resolve: gfc includes <gfc/gfc.h>, which is now src/gfc.h. Anything
    the system include path resolves is left alone, so a project header can
    never shadow a system one.
    A unique punctuation-normalized name also matches benchmark-renamed
    generated headers, such as tibs.tsp.h -> tibs_tsp.h.
    """
    by_name: dict[str, list[Path]] = {}
    by_normalized_name: dict[str, list[Path]] = {}
    for h in project.headers:
        by_name.setdefault(h.name.lower(), []).append(h)   # the benchmark also renamed some files
        normalized = re.sub(r"[._-]+", "_", h.name.lower())
        by_normalized_name.setdefault(normalized, []).append(h)
    aliases = {}
    for f in project.units + project.headers:
        for inc in _ANY_INCLUDE.findall(source_code(f)):
            # Only plain relative paths: an alias must stay inside ALIAS_DIR.
            if inc.endswith(".c") or Path(inc).is_absolute() or ".." in Path(inc).parts:
                continue
            if any((d / inc).is_file() for d in [f.parent, *dirs, *system_dirs]):
                continue
            matches = by_name.get(Path(inc).name.lower(), [])
            if not matches:
                # CRUST-Bench also flattens punctuation in generated header
                # names: tibs.tsp.h becomes tibs_tsp.h. Only an unambiguous
                # missing include gets an alias; real headers always win.
                normalized = re.sub(r"[._-]+", "_", Path(inc).name.lower())
                matches = by_normalized_name.get(normalized, [])
            if len(matches) == 1:
                aliases[inc] = matches[0]
    return aliases


def write_aliases(project: Project, aliases: dict[str, Path]) -> None:
    for inc, target in aliases.items():
        alias = project.c_dir / ALIAS_DIR / inc
        alias.parent.mkdir(parents=True, exist_ok=True)
        alias.write_text(f"/* Generated by c2r: the benchmark moved this header. */\n"
                         f'#include "{os.path.relpath(target, alias.parent)}"\n')


def write_wrapper(project: Project, dirs: list[Path] | None = None,
                  isystem: Path | None = None) -> tuple[Path, list[Path]]:
    """A .c file that makes CompCert compile a header-only library's code, and
    the library's top-level headers (those no other header includes).

    CompCert drops static functions that nothing uses, and a header-only
    library is often nothing but static (inline) functions. So the wrapper
    ends with a table that refers to each of them.
    """
    headers = [h for h in project.headers if not project.is_test(h)]
    included = {(h.parent / inc).resolve() for h in headers for inc in _INCLUDE.findall(source_code(h))
                if (h.parent / inc).resolve() != h.resolve()}
    top = [h for h in headers if h.resolve() not in included]
    guards = sorted({g for h in headers for g in _IMPL_GUARD.findall(source_code(h)) if not g.endswith("_H")})
    text = "/* Generated by c2r: makes CompCert compile this header-only library's code. */\n"
    text += "".join(f"#define {g}\n" for g in guards)
    text += "".join(f'#include "{h.relative_to(project.c_dir)}"\n' for h in top)
    path = project.c_dir / WRAPPER
    path.write_text(text)

    statics = static_functions(path, {h.resolve() for h in headers}, dirs or [project.c_dir], isystem)
    if statics:
        text += ("\n/* CompCert drops unused static functions; this table keeps the library's. */\n"
                 "void (*const c2r_keep[])(void) = {\n"
                 + "".join(f"  (void (*)(void)) {name},\n" for name in statics) + "};\n")
        path.write_text(text)
    return path, top


def static_functions(source: Path, files: set[Path], dirs: list[Path], isystem: Path | None) -> list[str]:
    """Names of static functions defined in `files`, as libclang sees `source`."""
    try:
        import clang.cindex as ci
        args = [f"-I{d}" for d in dirs] + (["-isystem", str(isystem)] if isystem else [])
        tu = ci.Index.create().parse(str(source), args=args)
    except Exception:   # no usable libclang: fall back to no table
        return []
    names = {c.spelling for c in tu.cursor.get_children()
             if c.kind == ci.CursorKind.FUNCTION_DECL and c.is_definition()
             and c.storage_class == ci.StorageClass.STATIC
             and c.location.file and Path(c.location.file.name).resolve() in files}
    return sorted(names)


# ---------------------------------------------------------------------------
# Running ptridxgen

def count_functions(light_c: str) -> int:
    """Function definitions in PrintClight output: a header line followed by '{'."""
    lines = light_c.splitlines()
    return sum(1 for head, nxt in zip(lines, lines[1:]) if nxt == "{" and head.endswith(")"))


def split_pointers(facts: dict | None) -> int:
    return sum(len(f["split"]) for f in facts["functions"]) if facts else 0


def cached_pointers(facts: dict | None) -> int:
    """Pointers stored in memory that got a cache (base and index temporaries)."""
    return sum(len(f.get("cached", [])) for f in facts["functions"]) if facts else 0


def fallback_functions(facts: dict | None) -> int:
    """Functions with pointers to split that the pass left unchanged."""
    return sum(1 for f in facts["functions"] if f.get("fallback")) if facts else 0


def _ptridxgen(cfg: Config, work: Path, rel: Path, flags: list[str], includes: list[str],
               outdir: Path, *extra: str) -> tuple[int, str]:
    outdir.mkdir(parents=True, exist_ok=True)
    memory = ["-memory"] if cfg.refactor.memory_pointers else []     # A8
    cmd = [str(resolve(cfg.tools.compcert_dir) / "ptridxgen"), "-stdlib", str(resolve(cfg.tools.compcert_stdlib)),
           *memory, *extra, *flags, *cfg.refactor.extra_flags, *includes, "-outdir", str(outdir), str(rel)]
    # Relative source paths, so the source path recorded in the outputs doesn't
    # depend on where the temporary copy lives.
    return run(cmd, timeout=cfg.refactor.timeout, cwd=work, big_stack=True,
               memory_mb=cfg.refactor.memory_limit_mb)


def compile_unit(cfg: Config, work: Path, src: Path, kind: str, out_path: str,
                 includes: list[str], outdir: Path, objects: bool = False,
                 source: str | None = None, unit_flags: list[str] | None = None) -> UnitRecord:
    """Run ptridxgen on one unit. With `objects`, also compile its Clight with
    and without the refactoring through CompCert's backend (ptridxgen -c).
    Compiling objects is a separate step: the backend can fail (out of memory
    on a huge function) on a file the front end and the pass accept.
    `source` is the file's original text, before any rewrite."""
    rel = src.relative_to(work)
    unit = UnitRecord(str(rel), kind, out_path, source if source is not None else src.read_text(errors="replace"))
    rocq = ["-rocq"] if cfg.refactor.keep_rocq_ast else []
    for variant in cfg.refactor.flag_sets:
        flags = [*variant, *(unit_flags or [])]
        code, msg = _ptridxgen(cfg, work, rel, flags, includes, outdir / "pass", *rocq)
        if code != 0:
            error = first_errors(msg)
            unit.errors.append({"flags": flags, "error": error, "category": categorize(error, work)})
            continue
        stem = outdir / "pass" / src.stem
        unit.accepted, unit.flags = True, flags
        unit.refactored = stem.with_suffix(".light.c").read_text()
        unit.facts = json.loads(stem.with_suffix(".ptridx.json").read_text())
        if rocq:
            unit.rocq = stem.with_suffix(".v").read_text()
        # Same front end and flags, so this cannot fail where the pass succeeded.
        code, msg = _ptridxgen(cfg, work, rel, flags, includes, outdir / "nopass", "-no-pass")
        if code != 0:
            raise RuntimeError(f"ptridxgen -no-pass failed on {rel} after the pass succeeded: {msg}")
        unit.clight = (outdir / "nopass" / src.stem).with_suffix(".light.c").read_text()
        if objects:
            _compile_objects(cfg, work, rel, flags, includes, outdir, unit)
        return unit
    return unit


def _compile_objects(cfg: Config, work: Path, rel: Path, flags: list[str], includes: list[str],
                     outdir: Path, unit: UnitRecord) -> None:
    for attr, sub, extra in (("refactored_obj", "obj_pass", ()), ("clight_obj", "obj_nopass", ("-no-pass",))):
        code, msg = _ptridxgen(cfg, work, rel, flags, includes, outdir / sub, "-c", *extra)
        if code != 0:
            error = first_errors(msg)
            unit.object_error = f"{categorize(error, work)}: {error.splitlines()[0] if error else f'exit {code}'}"
            unit.refactored_obj = unit.clight_obj = None
            return
        setattr(unit, attr, (outdir / sub / rel.stem).with_suffix(".o").read_bytes())


def run_project(cfg: Config, project: Project, objects: bool = False, *,
                unit_flags: dict[str, list[str]] | None = None,
                include_library_units: bool = False) -> ProjectRecord:
    """Stage 1 on one project, on a temporary copy; nothing is written elsewhere.
    With `objects`, each accepted unit also carries its CompCert-compiled objects."""
    scratch = resolve(cfg.output.work_dir)
    scratch.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="c2r-stage1-", dir=scratch) as tmp:
        work = Path(tmp) / project.name
        shutil.copytree(project.c_dir, work, ignore=COPY_IGNORE)
        copy = Project(project.name, work, project.rust_dir)
        sources = copy.units         # before any generated file (wrapper, aliases) is added
        if include_library_units:
            sources = sorted(set(sources) | set(copy.c_units))

        header_only = not copy.c_sources
        dirs = include_dirs(copy)
        system_dirs = [*system_include_dirs(), resolve(cfg.tools.compcert_stdlib) / "include"]
        aliases = header_aliases(copy, dirs, system_dirs)
        write_aliases(copy, aliases)
        includes = [f"-I{d.relative_to(work)}" for d in dirs] + ([f"-I{ALIAS_DIR}"] if aliases else [])

        units: list[tuple[Path, str, str]] = []      # (source, kind, out_path)
        if header_only:
            wrapper, top = write_wrapper(copy, dirs, clang_resource_include(cfg.tools.clang))
            # Named after the header when there is one, so the view reads like the source.
            name = top[0].relative_to(work).with_suffix(".light.c") if len(top) == 1 else Path("c2r_header_only.light.c")
            units.append((wrapper, "wrapper", str(name)))
        units += [(u, copy.kind(u), str(u.relative_to(work).with_suffix(".light.c"))) for u in sources]
        originals = {src: src.read_text(errors="replace") for src, _, _ in units}

        isystem = clang_resource_include(cfg.tools.clang)
        clang_args = ["-std=gnu17", "-D_DEFAULT_SOURCE", *[f"-I{d}" for d in dirs],
                      *([f"-I{work / ALIAS_DIR}"] if aliases else []), *(["-isystem", str(isystem)] if isystem else [])]
        rewrites, rewrite_flags = apply_rewrites(cfg.rewrites, work, copy._files(".c") + copy.headers,
                                                 [src for src, _, _ in units], clang_args)

        outs = Path(tmp) / "out"
        # Keep persisted flags in original-project coordinates; only tool
        # invocations use the temporary copy's include paths.
        from .c_analysis import _remap_arguments
        records = []
        for i, (src, kind, out_path) in enumerate(units):
            extra = (unit_flags or {}).get(src.relative_to(work).as_posix(), [])
            mapped = _remap_arguments(extra, project.c_dir.resolve(), work.resolve())
            unit = compile_unit(cfg, work, src, kind, out_path, [*rewrite_flags, *includes], outs / str(i),
                                objects, originals[src], unit_flags=mapped)
            if unit.flags is not None:
                unit.flags = _remap_arguments(unit.flags, work.resolve(), project.c_dir.resolve())
            for error in unit.errors:
                error["flags"] = _remap_arguments(error["flags"], work.resolve(), project.c_dir.resolve())
            records.append(unit)
        for u in records:
            u.rewrites = rewrites.get(u.path, {})
        accepted = bool(records) and all(u.accepted for u in records)
        return ProjectRecord(project.name, project.c_dir, accepted, header_only, records,
                             {inc: str(t.relative_to(work)) for inc, t in aliases.items()}, rewrites)


def run_stage1(cfg: Config, jobs: int = 4, progress: Callable[[ProjectRecord], None] = lambda r: None,
               objects: bool = False) -> list[ProjectRecord]:
    """Stage 1 on the configured projects, in memory."""
    projects = select(discover(resolve(cfg.benchmark.c_dir), resolve(cfg.benchmark.rust_dir)), cfg.projects)
    records = []
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for fut in as_completed([pool.submit(run_project, cfg, p, objects) for p in projects]):
            records.append(fut.result())
            progress(records[-1])
    return sorted(records, key=lambda r: r.name.lower())


def refactor_all(cfg: Config, jobs: int = 4,
                 progress: Callable[[ProjectRecord], None] = lambda r: None) -> dict:
    """`c2r refactor`: stage 1, then its view on disk."""
    return write_view(cfg, run_stage1(cfg, jobs, progress))


# ---------------------------------------------------------------------------
# The view on disk

def write_view(cfg: Config, records: list[ProjectRecord]) -> dict:
    out_root = resolve(cfg.output.refactored_dir)
    out_root.mkdir(parents=True, exist_ok=True)
    for r in records:
        dest = out_root / r.name
        if dest.exists():
            shutil.rmtree(dest)
        dest.mkdir()
        # Accepted units: their refactored Clight. Rejected units: their
        # original file, with the project's original headers, which they include.
        for u in r.units:
            if u.accepted:
                _write(dest / u.out_path, u.refactored)
                if u.rocq is not None:
                    _write((dest / u.out_path).with_name(Path(u.out_path).name.removesuffix(".light.c") + ".v"), u.rocq)
            elif u.kind != "wrapper":
                _write(dest / u.path, u.source)
        if r.status != "accepted":
            original = Project(r.name, r.c_dir, None)
            for f in original.headers:
                _write(dest / f.relative_to(r.c_dir), f.read_text(errors="replace"))
            # .c files that are not units (included by another .c file) go with the headers.
            unit_paths = {u.path for u in r.units}
            for f in original._files(".c"):
                if str(f.relative_to(r.c_dir)) not in unit_paths:
                    _write(dest / f.relative_to(r.c_dir), f.read_text(errors="replace"))

    status = _merge_status(cfg, out_root, records)
    (out_root / "status.json").write_text(json.dumps(status, indent=2) + "\n")
    (out_root / "README.md").write_text(render_readme(status))
    return status


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def _status_entry(r: ProjectRecord) -> dict:
    return {
        "name": r.name, "status": r.status, "accepted": r.accepted, "header_only": r.header_only,
        "aliases": r.aliases, "rewrites": r.rewrites,
        "units": [{"path": u.path, "kind": u.kind, "out_path": u.out_path if u.accepted else u.path,
                   "accepted": u.accepted, "flags": u.flags, "rewrites": u.rewrites,
                   "functions": count_functions(u.refactored) if u.refactored else 0,
                   "split_pointers": split_pointers(u.facts),
                   "cached_pointers": cached_pointers(u.facts),
                   "fallback_functions": fallback_functions(u.facts),
                   "split": u.facts["functions"] if u.facts else [],
                   "errors": u.errors} for u in r.units],
    }


def _merge_status(cfg: Config, out_root: Path, records: list[ProjectRecord]) -> dict:
    """Combine this run with earlier ones, so a partial run keeps the other projects."""
    path = out_root / "status.json"
    old = json.loads(path.read_text())["projects"] if path.exists() else {}
    # Earlier entries are kept only if their directory exists and they have
    # this format (units with a "kind").
    merged = {name: e for name, e in old.items()
              if (out_root / name).is_dir() and all("kind" in u for u in e["units"])}
    for e in merged.values():          # entries written before partial projects existed
        n = sum(u["accepted"] for u in e["units"])
        e.setdefault("status", "accepted" if e["accepted"] else "partial" if n else "rejected")
    merged.update({r.name: _status_entry(r) for r in records})
    merged = dict(sorted(merged.items(), key=lambda kv: kv[0].lower()))
    compcert = resolve(cfg.tools.compcert_dir)
    code, version = run([str(compcert / "ptridxgen"), "-version"])
    passes = {u.facts["pass"] for r in records for u in r.units if u.facts}
    return {"generated": date.today().isoformat(),
            "tool": {"ptridxgen": version if code == 0 else None,
                     "target": compcert_target(compcert),
                     "pass": ", ".join(sorted(passes)) or None},
            "flag_sets": cfg.refactor.flag_sets,
            "extra_flags": cfg.refactor.extra_flags,
            "projects": merged}


# ---------------------------------------------------------------------------
# README.md

PASS_DESCRIPTIONS = {
    "temporaries": "pointer temporaries that move become a base plus an index; pointers stored in "
                   "memory are left alone (`refactor.memory_pointers: false`, the default). This is the "
                   "pass `CompCert/ptridx/PtrIdxproof.v` proves correct",
    "temporaries, memory": "pointer temporaries that move become a base plus an index; a pointer stored "
                           "in memory that moves (a struct field, a global) gets a base and an index "
                           "kept in step with it, and memory is still updated at every store. The caches "
                           "are not covered by the proof",
}


def _version(banner: str | None) -> str:
    m = re.search(r"version (\S+)", banner or "")
    return m.group(1) if m else "(unknown version)"


def _cell(text: str) -> str:
    return text.replace("|", "\\|").replace("\n", " ").strip()


def _project_reasons(entry: dict) -> list[str]:
    reported = [primary_error(u["errors"]) for u in entry["units"] if not u["accepted"]]
    return sorted({e.get("category") or categorize(e["error"]) for e in reported})


def _rewrites_note(e: dict) -> str:
    counts: dict[str, int] = {}
    for per_file in e.get("rewrites", {}).values():
        for name, n in per_file.items():
            counts[name] = counts.get(name, 0) + n
    return ", ".join(f"{name} ({n})" for name, n in sorted(counts.items()))


def render_readme(status: dict) -> str:
    projects = status["projects"]
    groups = {k: {n: e for n, e in projects.items() if e["status"] == k} for k in ("accepted", "partial", "rejected")}
    accepted, partial, rejected = groups["accepted"], groups["partial"], groups["rejected"]
    needs_flags = [n for n, e in accepted.items() if any(u["flags"] for u in e["units"])]
    rewritten = [n for n, e in projects.items() if e["status"] != "rejected" and e.get("rewrites")]
    tool = status["tool"]
    units = [u for e in projects.values() for u in e["units"] if u["accepted"]]
    split = sum(u["split_pointers"] for u in units)
    cached = sum(u.get("cached_pointers", 0) for u in units)
    fallbacks = sum(u.get("fallback_functions", 0) for u in units)

    lines = [
        "# Stage 1: refactored projects",
        "",
        f"Generated by `c2r refactor` on {status['generated']}, using ptridxgen from CompCert "
        f"{_version(tool['ptridxgen'])}, target {tool['target']}. CompCert flag sets tried in order: "
        + ", ".join(f"`{' '.join(fs) or '(default)'}`" for fs in status["flag_sets"])
        + (f", each with `{' '.join(status['extra_flags'])}`" if status.get("extra_flags") else "") + ".",
        "",
        f"Refactoring pass: `{tool['pass']}` ({PASS_DESCRIPTIONS.get(tool['pass'], 'see PtrIdx.v')}).",
        "",
        f"- **Accepted:** {len(accepted)} of {len(projects)} projects"
        + (f" ({len(needs_flags)} only with extra flags)" if needs_flags else "") + ": every C file refactored.",
        f"- **Partial:** {len(partial)} projects: some C files refactored, the others kept as they are.",
        f"- **Rejected:** {len(rejected)} projects: no C file refactored.",
        f"- {len(units)} C files refactored, {split} pointer temporaries split, {cached} pointers in memory "
        "cached"
        + (f", {fallbacks} functions left unchanged because the pass could not rewrite them exactly"
           if fallbacks else "")
        + (f"; {len(rewritten)} of the accepted and partial projects needed source rewrites" if rewritten else "")
        + ".",
        "",
        "Every C file of a project is a unit: library code, tests, benchmarks and examples alike. A unit that "
        "CompCert accepts is refactored, and its directory holds the refactored Clight, printed as C: "
        "`x.light.c` for `x.c`. A unit that CompCert rejects is kept as its original `x.c`; a project with such "
        "a unit also keeps its original `.h` files (and any `.c` file another one includes), which the "
        "original files need. "
        f"A header-only library is compiled through a generated wrapper (`{WRAPPER}`), which refers to the "
        "library's static functions so that CompCert keeps them; its output is named after the header. Where "
        "the benchmark moved a header so that the project's own `#include` no longer resolves, a forwarding "
        f"header in `{ALIAS_DIR}/` is used. Before CompCert sees a project, mechanical, meaning-preserving "
        "source rewrites (`rewrites` in the config: binary literals, case ranges, empty initializers, "
        "arithmetic on `void *`, ...) turn GNU and C23 extensions that CompCert lacks into standard C; they "
        "change only a temporary copy, and the files kept as originals here are the untouched ones. "
        "`status.json` has every file's result, the rewrites applied to it, the pointers that were split, and "
        "every error.",
        "",
    ]

    def failures(title: str, group: dict[str, dict], header: str) -> None:
        nonlocal lines
        lines += [f"## {title}", ""]
        if not group:
            lines += ["None.", ""]
            return
        lines += [header, "|---|---|---|---|"]
        for name, e in group.items():
            bad = [u for u in e["units"] if not u["accepted"]]
            kinds = sorted({u["kind"] for u in bad})
            first = primary_error(bad[0]["errors"])["error"].splitlines()[0]
            lines.append(f"| {name} | {', '.join(_project_reasons(e))} | {len(bad)} of {len(e['units'])} "
                         f"({', '.join(kinds)}) | `{_cell(first)}` |")
        lines.append("")

    failures("Rejected projects", rejected, "| Project | Reason | Files kept original | First error |")
    failures("Partial projects", partial, "| Project | Reason | Files kept original | First error |")

    by_reason: dict[str, list[str]] = {}
    for name, e in {**rejected, **partial}.items():
        for reason in _project_reasons(e):
            by_reason.setdefault(reason, []).append(name + (" (partial)" if e["status"] == "partial" else ""))
    if by_reason:
        lines += ["### Rejected files by reason", "", "| Reason | Projects | Names |", "|---|---|---|"]
        for reason, names in sorted(by_reason.items(), key=lambda kv: (-len(kv[1]), kv[0])):
            lines.append(f"| {reason} | {len(names)} | {', '.join(names)} |")
        lines.append("")

    lines += ["## Accepted and partial projects", "",
              "| Project | Status | Flags used | Needs | Refactored files | Functions | Split pointers "
              "| Cached pointers | Source rewrites | Note |",
              "|---|---|---|---|---|---|---|---|---|---|"]
    for name, e in {**accepted, **partial}.items():
        e = {**e, "units": [u for u in e["units"] if u["accepted"]]}
        flags = sorted({" ".join(u["flags"]) for u in e["units"]} - {""})
        needs = needed_options(e["units"])
        functions = sum(u["functions"] for u in e["units"])
        notes = (["header-only"] if e["header_only"] else []) + \
                ([f"header aliases for {', '.join(f'`{i}`' for i in e['aliases'])}"] if e.get("aliases") else []) + \
                (["long double is treated as double"] if "-flongdouble" in needs else []) + \
                (["no functions in Clight"] if functions == 0 else [])
        lines.append(f"| {name} | {e['status']} | {', '.join(f'`{f}`' for f in flags) or 'default'} "
                     f"| {', '.join(f'`{n}`' for n in needs)} | {len(e['units'])} | {functions} "
                     f"| {sum(u['split_pointers'] for u in e['units'])} "
                     f"| {sum(u.get('cached_pointers', 0) for u in e['units'])} | {_rewrites_note(e)} "
                     f"| {'; '.join(notes)} |")
    return "\n".join(lines) + "\n"
