"""Temporary storage and infrastructure failures for local compiler processes."""

from __future__ import annotations

import os
import re
import shutil
import tempfile
from contextlib import contextmanager
from pathlib import Path


class InfrastructureError(RuntimeError):
    """An environment failure that must not trigger paid code repair."""


def storage_error(message: str) -> bool:
    return bool(re.search(r"disk quota exceeded|quota exceeded|no space left on device|"
                          r"\[errno (?:28|122)\]|os error (?:28|122)\b", message, re.I))


def compiler_temp_root() -> Path:
    # A dedicated setting avoids inheriting a quota-limited system /tmp.
    configured = os.environ.get("C2R_COMPILER_TMPDIR")
    return (Path(configured).expanduser() if configured else
            Path(__file__).resolve().parents[2] / "runs/compiler-tmp").resolve()


def storage_preflight(output: Path) -> Path:
    """Check filesystem space and probe writes, since free space ignores quotas."""
    base = compiler_temp_root()
    try:
        minimum = int(os.environ.get("C2R_MIN_FREE_MB", "512"))
        if minimum < 1:
            raise ValueError
    except ValueError:
        raise InfrastructureError("C2R_MIN_FREE_MB must be a positive integer") from None
    try:
        base.mkdir(parents=True, exist_ok=True)
        destination = output.resolve()
        while not destination.exists():
            destination = destination.parent
        for path in {base, destination}:
            free = shutil.disk_usage(path).free
            if free < minimum * 1024 * 1024:
                raise InfrastructureError(
                    f"Insufficient storage at {path}: {free // (1024 * 1024)} MiB free; "
                    f"reserve is {minimum} MiB. Free build storage or set C2R_COMPILER_TMPDIR "
                    "to a filesystem with available space and quota.")
            with tempfile.TemporaryFile(dir=path) as probe:
                probe.write(b"\0" * 65536)
                probe.flush()
                os.fsync(probe.fileno())
    except OSError as exc:
        raise InfrastructureError(f"Compiler storage is unavailable ({base}): {exc}") from None
    return base


@contextmanager
def compiler_environment(output: Path, env: dict | None = None):
    """Give each compiler invocation a private, automatically cleaned temp dir."""
    base = storage_preflight(output)
    try:
        with tempfile.TemporaryDirectory(prefix="compile-", dir=base) as directory:
            yield {**(os.environ if env is None else env), "TMPDIR": directory,
                   "TMP": directory, "TEMP": directory}
    except OSError as exc:
        if storage_error(str(exc)):
            raise InfrastructureError(f"Compiler temporary storage failed: {exc}") from None
        raise
