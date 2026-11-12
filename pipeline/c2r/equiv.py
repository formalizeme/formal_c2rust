"""Differential check of stage 1: build the programs of each accepted or
partial project and compare what they do.

A program is a unit that defines `main`, linked with every unit that doesn't
(a header-only library's wrapper is left out: its tests include the code).
In a partial project, the units CompCert rejected are compiled from their
original source with gcc, the same way in every build compared.

- **Refactoring check.** The Clight without the refactoring and the Clight
  after it are both compiled by CompCert's own backend (ptridxgen -c), which
  preserves Clight semantics, and linked with CompCert's runtime library.
  Their behavior must never differ.
- **Front-end check.** Where the project's original C also builds with gcc,
  it is compared with the CompCert-compiled Clight. This covers CompCert's
  front end, which the refactoring's proof does not.

Every program runs in its own copy of the project with no input. The Clight
build runs twice; a program whose two runs differ is reported as
nondeterministic instead of compared.
"""

from __future__ import annotations

import json
import re
import shutil
import tempfile
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass
from pathlib import Path

from .benchmark import _COMMENT, Project
from .config import Config, resolve
from .refactor import (ALIAS_DIR, COPY_IGNORE, ProjectRecord, header_aliases, include_dirs,
                       system_include_dirs, write_aliases)
from .tools import run

_MAIN = re.compile(r"^int main\([^;]*\)$", re.M)      # a definition in PrintClight output
_SOURCE_MAIN = re.compile(r"^[ \t]*(?:int|void)[ \t\n]+main[ \t\n]*\([^;]*?\)[ \t\n]*\{", re.M)
RUN_TIMEOUT = 10
RUN_MEMORY_MB = 1024     # address-space cap for each program run

# Outcomes of the refactoring check.
EQUAL = "same behavior"
EQUAL_TIMING = "same behavior (timings masked)"   # reads the clock; equal with numbers masked
CHANGED = "REFACTORING CHANGED BEHAVIOR"
NONDET = "nondeterministic"
NO_LINK = "does not link"
NO_OBJECT = "not compiled by CompCert's backend"


@dataclass
class ProgramCheck:
    main: str                        # the unit that defines main
    outcome: str                     # one of the outcomes above
    front_end: str                   # "same behavior", "different behavior", or "original does not build"
    detail: str = ""


def _defines_main(u) -> bool:
    if u.accepted:
        return bool(u.clight and _MAIN.search(u.clight))
    return bool(_SOURCE_MAIN.search(_COMMENT.sub(" ", u.source)))      # kept as original C


def _text(u) -> str:
    return u.clight if u.accepted else u.source


def _fresh_copy(record: ProjectRecord, where: Path) -> Path:
    shutil.copytree(record.c_dir, where, ignore=COPY_IGNORE)
    return where


def _gcc_flags(cfg: Config, work: Path) -> list[str]:
    """gcc flags for the original C in the project copy `work` (writing its header aliases)."""
    copy = Project(work.name, work, None)
    dirs = include_dirs(copy)
    aliases = header_aliases(copy, dirs, [*system_include_dirs(), resolve(cfg.tools.compcert_stdlib) / "include"])
    write_aliases(copy, aliases)
    includes = [f"-I{d.relative_to(work)}" for d in dirs] + ([f"-I{ALIAS_DIR}"] if aliases else [])
    return ["-w", "-std=gnu17", "-D_DEFAULT_SOURCE", *includes]


def _link(cfg: Config, work: Path, members: list, attr: str, runtime: Path, exe: Path) -> tuple[int, str]:
    """Link CompCert's objects of the accepted members with gcc's of the rejected ones."""
    objs = []
    gcc = _gcc_flags(cfg, work) if not all(u.accepted for u in members) else []
    for i, u in enumerate(members):
        obj = work / f"c2r_{attr}_{i}.o"
        if u.accepted:
            obj.write_bytes(getattr(u, attr))
        else:
            code, msg = run(["gcc", *gcc, "-c", "-o", str(obj), u.path], cwd=work)
            if code != 0:
                return code, f"gcc on the original {u.path}: error: {msg.strip()}"
        objs.append(str(obj))
    return run(["gcc", "-o", str(exe), *objs, str(runtime), "-lm"], cwd=work)


def _build_original(cfg: Config, work: Path, members: list, exe: Path) -> tuple[int, str]:
    return run(["gcc", *_gcc_flags(cfg, work), "-o", str(exe), *[u.path for u in members], "-lm"], cwd=work)


def _run(exe: Path, cwd: Path) -> tuple[int, str]:
    return run([str(exe)], timeout=RUN_TIMEOUT, cwd=cwd, memory_mb=RUN_MEMORY_MB)


def _first_difference(a: tuple[int, str], b: tuple[int, str], names: tuple[str, str]) -> str:
    (ca, oa), (cb, ob) = a, b
    if ca != cb:
        return f"exit {ca} ({names[0]}) vs {cb} ({names[1]})"
    for i, (la, lb) in enumerate(zip(oa.splitlines(), ob.splitlines())):
        if la != lb:
            return f"line {i + 1}: {la[:80]!r} ({names[0]}) vs {lb[:80]!r} ({names[1]})"
    return f"output length {len(oa)} ({names[0]}) vs {len(ob)} ({names[1]})"


def check_project(cfg: Config, record: ProjectRecord) -> list[ProgramCheck]:
    """`record` must come from run_project(..., objects=True)."""
    if record.status == "rejected":
        return []
    runtime = resolve(cfg.tools.compcert_stdlib) / "libcompcert.a"
    units = [u for u in record.units if u.kind != "wrapper"]
    mains = [u for u in units if _defines_main(u)]
    others = [u for u in units if not _defines_main(u)]
    checks = []
    scratch = resolve(cfg.output.work_dir)
    scratch.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="c2r-equiv-", dir=scratch) as tmp:
        for k, m in enumerate(mains):
            members = [m, *others]
            missing = [u for u in members if u.object_error]
            if missing:
                checks.append(ProgramCheck(m.path, NO_OBJECT, "not compared",
                                           f"{missing[0].path}: {missing[0].object_error}"))
                continue
            root = Path(tmp) / f"p{k}"
            runs = {}
            failed = None
            for attr in ("clight_obj", "refactored_obj"):
                work = _fresh_copy(record, root / attr / record.name)
                code, msg = _link(cfg, work, members, attr, runtime, work / "c2r_program")
                if code != 0:
                    failed = f"{attr}: {next((l for l in msg.splitlines() if 'error' in l), msg)[:160]}"
                    break
                runs[attr] = _run(work / "c2r_program", work)
                if attr == "clight_obj":
                    again = _fresh_copy(record, root / "again" / record.name)
                    shutil.copy(work / "c2r_program", again / "c2r_program")
                    if _run(again / "c2r_program", again) != runs[attr]:
                        failed = NONDET
                        break

            # The front-end check, independent of the outcome above.
            work = _fresh_copy(record, root / "original" / record.name)
            code, _ = _build_original(cfg, work, members, work / "c2r_program")
            if code != 0:
                front_end = "original does not build"
            elif "clight_obj" in runs and failed != NONDET:
                front_end = ("same behavior" if _run(work / "c2r_program", work) == runs["clight_obj"]
                             else "different behavior")
            else:
                front_end = "not compared"

            if failed == NONDET:
                checks.append(ProgramCheck(m.path, NONDET, front_end, "two runs of the Clight build differ"))
            elif failed:
                checks.append(ProgramCheck(m.path, NO_LINK, front_end, failed))
            elif runs["clight_obj"] == runs["refactored_obj"]:
                checks.append(ProgramCheck(m.path, EQUAL, front_end))
            elif _reads_clock(members) and _masked(runs["clight_obj"]) == _masked(runs["refactored_obj"]):
                # The clock is an input: a timing that differs is not a change
                # of behavior, and the refactored code may run slower.
                checks.append(ProgramCheck(m.path, EQUAL_TIMING, front_end,
                                           _first_difference(runs["clight_obj"], runs["refactored_obj"],
                                                             ("clight", "refactored"))))
            elif not _stable(record, root, runs["clight_obj"]):
                # Two equal runs can be luck (a benchmark printing timings).
                checks.append(ProgramCheck(m.path, NONDET, front_end,
                                           f"the Clight build's output varies over {CONFIRM_RUNS + 2} runs"))
            else:
                checks.append(ProgramCheck(m.path, CHANGED, front_end,
                                           _first_difference(runs["clight_obj"], runs["refactored_obj"],
                                                             ("clight", "refactored"))))
    return checks


CONFIRM_RUNS = 3
_CLOCK = re.compile(r"\b(clock|time|gettimeofday|clock_gettime|timespec_get)\(")
_NUMBER = re.compile(r"\d+(\.\d+)?")


def _reads_clock(members: list) -> bool:
    return any(_CLOCK.search(_text(u)) for u in members)


def _masked(result: tuple[int, str]) -> tuple[int, str]:
    code, out = result
    return code, _NUMBER.sub("N", out)


def _stable(record: ProjectRecord, root: Path, first: tuple[int, str]) -> bool:
    """Before reporting a change: whether the Clight build, run again in fresh
    copies of the project, keeps producing exactly `first`."""
    exe = root / "clight_obj" / record.name / "c2r_program"
    for i in range(CONFIRM_RUNS):
        again = _fresh_copy(record, root / f"confirm{i}" / record.name)
        shutil.copy(exe, again / "c2r_program")
        if _run(again / "c2r_program", again) != first:
            return False
    return True


def check_all(cfg: Config, records: list[ProjectRecord], jobs: int = 4,
              progress: Callable[[str, list[ProgramCheck]], None] = lambda n, c: None) -> dict:
    accepted = [r for r in records if r.status != "rejected"]
    results: dict[str, list[ProgramCheck]] = {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {pool.submit(check_project, cfg, r): r.name for r in accepted}
        for fut in as_completed(futures):
            results[futures[fut]] = fut.result()
            progress(futures[fut], results[futures[fut]])
    projects = {n: [asdict(c) for c in results[n]] for n in sorted(results, key=str.lower)}
    split = {r.name: sum(len(f["split"]) + len(f.get("cached", []))
                         for u in r.units if u.facts for f in u.facts["functions"])
             for r in accepted}
    partial = sorted((r.name for r in accepted if r.status == "partial"), key=str.lower)
    return {"projects": projects, "split_pointers": split, "partial": partial,
            "summary": summarize(projects, split)}


def summarize(projects: dict[str, list[dict]], split: dict[str, int]) -> dict:
    outcomes: dict[str, int] = {}
    front_end: dict[str, int] = {}
    for checks in projects.values():
        for c in checks:
            outcomes[c["outcome"]] = outcomes.get(c["outcome"], 0) + 1
            front_end[c["front_end"]] = front_end.get(c["front_end"], 0) + 1
    exercised = [n for n, checks in projects.items() if split.get(n) and any(c["outcome"] in (EQUAL, EQUAL_TIMING) for c in checks)]
    return {"programs": sum(outcomes.values()), "outcomes": outcomes, "front_end": front_end,
            "projects": len(projects), "projects without programs": sum(1 for c in projects.values() if not c),
            "projects with rewritten pointers and a compared program": len(exercised)}


def render_report(report: dict) -> str:
    s = report["summary"]
    lines = [
        "# Differential check of stage 1",
        "",
        "Generated by `c2r check-refactor`. The programs of each accepted or partial project (a unit that "
        "defines `main`, linked with every unit that doesn't) are built from the Clight without the "
        "refactoring and from the Clight after it, both compiled by CompCert's own backend, and run in their "
        "own copy of the project with no input. In a partial project, the files CompCert rejected are "
        "compiled from their original C with gcc, the same way in both builds. The Clight build runs twice, and a program whose runs differ is reported as "
        "nondeterministic instead of compared; before a difference counts as a change, the Clight build "
        f"runs {CONFIRM_RUNS} more times. The clock is an input, so a program that reads it (`clock`, "
        "`time`, `gettimeofday`, ...) and whose outputs differ only in numbers is reported as "
        f"\"{EQUAL_TIMING}\". Where the original C also builds with gcc, it is compared "
        "with the Clight build too; that checks CompCert's front end, which the refactoring's proof does "
        "not cover.",
        "",
        f"**{s['programs']} programs** in {s['projects']} accepted or partial projects "
        f"({len(report.get('partial', []))} partial) "
        f"({s['projects without programs']} have no program). "
        f"{s['projects with rewritten pointers and a compared program']} projects have rewritten pointers (split or cached) and at "
        "least one compared program.",
        "",
        "## Refactoring: Clight vs refactored Clight",
        "",
        "| Outcome | Programs |",
        "|---|---|",
    ]
    for outcome in (EQUAL, EQUAL_TIMING, CHANGED, NONDET, NO_LINK, NO_OBJECT):
        lines.append(f"| {outcome} | {s['outcomes'].get(outcome, 0)} |")
    lines += ["", "## Front end: original C (gcc) vs Clight (CompCert)", "", "| Outcome | Programs |", "|---|---|"]
    for outcome in ("same behavior", "different behavior", "original does not build", "not compared"):
        lines.append(f"| {outcome} | {s['front_end'].get(outcome, 0)} |")
    lines += ["", "## Programs", "",
              "| Project | Rewritten pointers | Program | Refactoring | Front end | Detail |", "|---|---|---|---|---|---|"]
    for name, checks in report["projects"].items():
        for c in checks:
            detail = c["detail"].replace("|", "\\|").replace("\n", " ")
            shown = name + (" (partial)" if name in report.get("partial", []) else "")
            lines.append(f"| {shown} | {report['split_pointers'].get(name, 0)} | `{c['main']}` | {c['outcome']} "
                         f"| {c['front_end']} | {detail} |")
    return "\n".join(lines) + "\n"


def write_report(cfg: Config, report: dict) -> Path:
    out = resolve(cfg.output.refactored_dir)
    out.mkdir(parents=True, exist_ok=True)
    (out / "differential.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "differential.md").write_text(render_report(report))
    return out / "differential.md"
