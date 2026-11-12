"""Syntactic generated-Rust metrics and optional bounded Clippy diagnostics."""

from __future__ import annotations

import json
import os
import shlex
from pathlib import Path

from .config import Config
from .rust_edits import _parse, source_files
from .rust_project import RustProject, _atomic_json
from .validation import _execute, candidate_fingerprint


def collect_metrics(directory: Path, cfg: Config, destination: Path) -> dict:
    run = RustProject(directory)
    rows = []
    for path, code in source_files(run).items():
        data, root = _parse(code, path)
        raw, unsafe = 0, 0
        pending = [root]
        while pending:
            node = pending.pop()
            raw += node.type == "pointer_type"
            unsafe += node.type == "unsafe"
            if node.type not in {"line_comment", "block_comment", "string_literal", "raw_string_literal"}:
                pending.extend(node.children)
        rows.append({"path": path, "lines": len(code.splitlines()), "raw_pointer_type_sites": raw,
                     "unsafe_keyword_sites": unsafe})
    result = {"candidate_sha256": candidate_fingerprint(run), "files": rows,
              "raw_pointer_type_sites": sum(r["raw_pointer_type_sites"] for r in rows),
              "unsafe_keyword_sites": sum(r["unsafe_keyword_sites"] for r in rows),
              "unsafe_policy": "compiler forbids unsafe code (-F unsafe_code); zero is enforced, not a comparative finding",
              "scope": "source syntax only; macro expansion, dependencies and runtime pointer operations are not counted",
              "clippy": {"outcome": "disabled"}}
    destination.parent.mkdir(parents=True, exist_ok=True)
    if cfg.metrics.clippy:
        env = dict(os.environ)
        env.pop("CARGO_TARGET_DIR", None)
        flags = (env["CARGO_ENCODED_RUSTFLAGS"].split("\x1f") if "CARGO_ENCODED_RUSTFLAGS" in env
                 else shlex.split(env.get("RUSTFLAGS", "")))
        env["CARGO_ENCODED_RUSTFLAGS"] = "\x1f".join([*flags, "-F", "unsafe_code"])
        command = [cfg.tools.cargo, *([f"+{cfg.tools.rust_toolchain}"] if cfg.tools.rust_toolchain else []),
                   "clippy", "--lib", "--no-deps", "--message-format=json", "--jobs", str(cfg.runner.cargo_jobs)]
        if cfg.runner.offline:
            command.append("--offline")
        build, output = _execute(command, run.root, cfg.metrics.timeout,
                                 destination.with_suffix(".clippy.txt"), env)
        diagnostics = []
        for line in output.splitlines():
            try:
                item = json.loads(line)
            except ValueError:
                continue
            if item.get("reason") == "compiler-message":
                diagnostics.append(item["message"])
        result["clippy"] = {**build, "outcome": "timeout" if build["timeout"] else
                            "completed" if build["exit_code"] == 0 else "unavailable_or_failed",
                            "diagnostics": diagnostics,
                            "warnings": sum(d.get("level") == "warning" for d in diagnostics),
                            "clippy_lints": sum(d.get("level") == "warning" and
                                (d.get("code") or {}).get("code", "").startswith("clippy::") for d in diagnostics)}
    result["report_path"] = str(destination)
    _atomic_json(destination, result)
    return result
