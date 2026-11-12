"""Environment checks for the external tools the pipeline drives (`c2r doctor`)."""

from __future__ import annotations

import os
import resource
import subprocess
from dataclasses import dataclass
from importlib import metadata
from pathlib import Path

from .benchmark import discover
from .config import Config, resolve
from .runtime import compiler_environment, storage_error, InfrastructureError

OK, WARN, FAIL = "ok", "warn", "fail"


@dataclass
class Check:
    name: str
    status: str
    detail: str


BIG_STACK = 1 << 30      # 1 GB


def _limits(big_stack: bool, memory_mb: int | None):
    def apply() -> None:
        if big_stack:
            _, hard = resource.getrlimit(resource.RLIMIT_STACK)
            soft = BIG_STACK if hard == resource.RLIM_INFINITY else min(BIG_STACK, hard)
            resource.setrlimit(resource.RLIMIT_STACK, (soft, hard))
        if memory_mb is not None:
            cap = memory_mb << 20
            resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
    return apply if big_stack or memory_mb is not None else None


# A fixed build date: __DATE__ and __TIME__ (which gcc's preprocessor, and so
# CompCert's, takes from SOURCE_DATE_EPOCH) must not differ between two builds
# that are compared, or a program printing them seems to change behavior.
BUILD_ENV = {**os.environ, "SOURCE_DATE_EPOCH": "0"}


def run(cmd: list[str], timeout: int = 120, cwd: Path | None = None,
        big_stack: bool = False, memory_mb: int | None = None) -> tuple[int, str]:
    """Run a command; return (exit code, combined output). A missing program gives code 127.

    big_stack raises the child's stack limit to 1 GB: CompCert's C parser
    recurses deeply on large files and overflows the default 8 MB.
    memory_mb caps the child's address space, so a process that needs more
    fails on its own instead of exhausting the machine (CompCert's backend
    needs more than 2 GB for libfor's test.c).
    Every command runs with a fixed SOURCE_DATE_EPOCH (BUILD_ENV).
    """
    try:
        with compiler_environment(cwd or Path.cwd(), BUILD_ENV) as env:
            proc = subprocess.run(cmd, capture_output=True, text=True, errors="replace", timeout=timeout, cwd=cwd,
                                  stdin=subprocess.DEVNULL, preexec_fn=_limits(big_stack, memory_mb), env=env)
    except FileNotFoundError:
        return 127, f"not found: {cmd[0]}"
    except subprocess.TimeoutExpired:
        return 124, f"timed out after {timeout}s: {' '.join(cmd)}"
    output = (proc.stdout + proc.stderr).strip()
    if proc.returncode and storage_error(output):
        raise InfrastructureError(output)
    return proc.returncode, output


def compcert_target(compcert_dir: Path) -> str | None:
    """Target CompCert was configured for, e.g. 'aarch64-linux', from Makefile.config."""
    try:
        lines = (compcert_dir / "Makefile.config").read_text().splitlines()
    except OSError:
        return None
    values = dict(line.split("=", 1) for line in lines if "=" in line)
    arch, system = values.get("ARCH"), values.get("SYSTEM")
    return f"{arch}-{system}" if arch and system else None


def clang_resource_include(clang: str) -> Path | None:
    """clang's builtin-header directory (stddef.h etc.), which libclang needs on -isystem."""
    code, out = run([clang, "-print-resource-dir"])
    if code != 0:
        return None
    include = Path(out.splitlines()[-1]) / "include"
    return include if (include / "stddef.h").is_file() else None


def doctor(cfg: Config) -> list[Check]:
    checks = []

    projects = discover(resolve(cfg.benchmark.c_dir), resolve(cfg.benchmark.rust_dir))
    paired = sum(p.rust_dir is not None for p in projects)
    checks.append(Check("benchmark", OK if projects and paired == len(projects) else WARN,
                        f"{len(projects)} C projects, {paired} paired with an RBench crate"))

    compcert = resolve(cfg.tools.compcert_dir)
    for tool in ("ccomp", "clightgen", "ptridxgen"):
        exe = compcert / tool
        if not os.access(exe, os.X_OK):
            checks.append(Check(tool, FAIL, f"missing: {exe} (run `make {tool}` in {compcert})"))
            continue
        code, out = run([str(exe), "-version"])
        checks.append(Check(tool, OK if code == 0 else FAIL, out.splitlines()[0] if out else f"exit {code}"))

    stdlib = resolve(cfg.tools.compcert_stdlib)
    checks.append(Check("compcert headers", OK if (stdlib / "include" / "stdarg.h").is_file() else FAIL,
                        f"{stdlib / 'include'} (passed as -stdlib {stdlib})"))

    target = compcert_target(compcert)
    if target is None:
        checks.append(Check("target", FAIL, f"cannot read {compcert / 'Makefile.config'}"))
    elif cfg.target is None:
        checks.append(Check("target", WARN, f"decision D3 open; CompCert is configured for {target}"))
    else:
        checks.append(Check("target", OK if cfg.target == target else FAIL,
                            f"config {cfg.target}, CompCert configured for {target}"))

    opam = str(Path(cfg.tools.opam).expanduser())
    code, out = run([opam, "exec", f"--switch={cfg.tools.opam_switch}", "--", "rocq", "--print-version"])
    if code == 0:
        # `rocq --print-version` prints "<rocq version> <ocaml version>".
        rocq_v, _, ocaml_v = out.partition(" ")
        checks.append(Check("rocq", OK, f"Rocq {rocq_v}, OCaml {ocaml_v} (opam switch {cfg.tools.opam_switch})"))
    else:
        checks.append(Check("rocq", FAIL, out))

    tc = cfg.tools.rust_toolchain
    for name, cmd in (("cargo", [cfg.tools.cargo, f"+{tc}", "--version"]),
                      ("clippy", [cfg.tools.cargo, f"+{tc}", "clippy", "--version"])):
        code, out = run(cmd)
        checks.append(Check(name, OK if code == 0 else FAIL,
                            f"{out} (toolchain {tc})" if code == 0
                            else f"{out}; install with `rustup toolchain install {tc} -c clippy -c rustfmt`"))

    try:
        import clang.cindex as ci
        ci.Index.create().parse("probe.c", unsaved_files=[("probe.c", "int f(void) { return 0; }")])
        checks.append(Check("libclang", OK, f"python package libclang {metadata.version('libclang')}"))
    except Exception as exc:  # the bindings raise various errors when libclang.so is missing
        checks.append(Check("libclang", FAIL, f"{type(exc).__name__}: {exc}"))

    include = clang_resource_include(cfg.tools.clang)
    checks.append(Check("clang headers", OK if include else WARN,
                        str(include) if include else f"no builtin headers via `{cfg.tools.clang} -print-resource-dir`; "
                        "libclang will miss stddef.h and macros like NULL"))

    has_key = bool(os.environ.get(cfg.model.api_key_env))
    checks.append(Check("openrouter key", OK if has_key else WARN,
                        f"{cfg.model.api_key_env} is set" if has_key
                        else f"{cfg.model.api_key_env} not set (needed before any LLM call)"))
    checks.append(Check("model", OK if cfg.model.id else WARN,
                        cfg.model.id or "model.id not set (needed before any LLM call)"))
    return checks
