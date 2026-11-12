"""CBench/RBench project discovery (CRUST-Bench layout).

RBench directory names are Rust crate names: case is ignored, '-' becomes '_',
and names that start with a digit get a 'proj_' prefix ('2DPartInt' becomes
'proj_2DPartInt').
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

# Benchmarks, examples and demos: programs around the library, not part of it.
AUX_WORDS = {"bench", "benchmark", "benchmarks", "example", "examples", "demo", "demos",
             "bin", "cli", "cmd", "tools"}
SKIP_PARTS = {"CMakeFiles", ".git"}     # build-system artifacts, not project code
_INCLUDE_C = re.compile(r'^\s*#\s*include\s*"([^"]+\.c)"', re.M)


def _words(path: Path) -> list[str]:
    return re.split(r"[^a-z0-9]+", path.stem.lower())


_COMMENT = re.compile(r"/\*.*?\*/|//[^\n]*", re.S)


def source_code(path: Path) -> str:
    """A C file's text with comments removed, for scanning #include and #define lines."""
    return _COMMENT.sub(" ", path.read_text(errors="replace"))


def _standalone(files: list[Path]) -> list[Path]:
    included = {(f.parent / inc).resolve() for f in files for inc in _INCLUDE_C.findall(source_code(f))}
    return [f for f in files if f.resolve() not in included]


def canonical_name(dirname: str) -> str:
    return dirname.lower().replace("-", "_").removeprefix("proj_")


def find_rust_project(root: Path, project: str, explicit: Path | None = None) -> Path | None:
    """Resolve an explicit crate or a unique benchmark-name match."""
    if explicit is not None:
        path = explicit.resolve()
        if not (path / "Cargo.toml").is_file():
            raise ValueError(f"RBench crate must contain Cargo.toml: {path}")
        return path
    matches = [p for p in root.iterdir() if p.is_dir() and canonical_name(p.name) == canonical_name(project)] if root.is_dir() else []
    if len(matches) > 1:
        raise ValueError(f"multiple Rust benchmark crates match {project}")
    return matches[0].resolve() if matches else None


@dataclass(frozen=True)
class Project:
    name: str                 # CBench directory name
    c_dir: Path
    rust_dir: Path | None     # matching RBench crate, if any

    def _files(self, suffix: str) -> list[Path]:
        return sorted(p for p in self.c_dir.rglob(f"*{suffix}")
                      if p.is_file() and not SKIP_PARTS & set(p.relative_to(self.c_dir).parts))

    def is_test(self, path: Path) -> bool:
        # Heuristic: a word of the file name or of a directory name starts with
        # "test" (test_list.c, testmdb.c, satc-test.c, unit_tests/, testing/,
        # but not shortest.c).
        rel = path.relative_to(self.c_dir)
        return any(w.startswith("test") for w in _words(path)) or any(
            w.startswith("test") for part in rel.parts[:-1] for w in re.split(r"[^a-z0-9]+", part.lower()))

    def is_auxiliary(self, path: Path) -> bool:
        # A benchmark/example/demo directory, or one of those words in the file name.
        rel = path.relative_to(self.c_dir)
        return (any(part.lower() in AUX_WORDS for part in rel.parts[:-1])
                or any(w in AUX_WORDS for w in _words(path)))

    @property
    def c_sources(self) -> list[Path]:
        """Library code: every .c file that is neither a test nor auxiliary."""
        return [p for p in self._files(".c") if not (self.is_test(p) or self.is_auxiliary(p))]

    @property
    def c_auxiliary(self) -> list[Path]:
        return [p for p in self._files(".c") if self.is_auxiliary(p) and not self.is_test(p)]

    @property
    def c_units(self) -> list[Path]:
        """Library sources compiled on their own: c_sources minus any that another source #includes."""
        return _standalone(self.c_sources)

    @property
    def units(self) -> list[Path]:
        """Every .c file compiled on their own (library, tests, auxiliary), minus
        any that another .c file #includes: those are compiled as part of it."""
        return _standalone(self._files(".c"))

    def kind(self, path: Path) -> str:
        return "test" if self.is_test(path) else "auxiliary" if self.is_auxiliary(path) else "library"

    @property
    def c_tests(self) -> list[Path]:
        return [p for p in self._files(".c") if self.is_test(p)]

    @property
    def headers(self) -> list[Path]:
        return self._files(".h")

    @property
    def interfaces(self) -> list[Path]:
        if self.rust_dir is None:
            return []
        return sorted((self.rust_dir / "src" / "interfaces").glob("*.rs"))

    @property
    def rust_tests(self) -> list[Path]:
        if self.rust_dir is None:
            return []
        return sorted((self.rust_dir / "src" / "bin").glob("*.rs"))


def discover(c_root: Path, rust_root: Path) -> list[Project]:
    rust = {}
    if rust_root.is_dir():
        rust = {canonical_name(d.name): d for d in rust_root.iterdir() if d.is_dir()}
    return [Project(d.name, d, rust.get(canonical_name(d.name)))
            for d in sorted(c_root.iterdir(), key=lambda p: p.name.lower()) if d.is_dir()]


def select(projects: list[Project], selection: list[str] | str) -> list[Project]:
    """Pick projects by CBench name or canonical name; 'all' keeps every project."""
    if selection == "all":
        return projects
    by_name = {canonical_name(p.name): p for p in projects}
    missing = [s for s in selection if canonical_name(s) not in by_name]
    if missing:
        raise KeyError(f"unknown project(s): {missing}")
    return [by_name[canonical_name(s)] for s in selection]
