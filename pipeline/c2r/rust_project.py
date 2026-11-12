"""Rust crate scaffolding and resumable translation state.

Only supplied interface files are copied in fixed mode. Reference Rust bodies
and benchmark tests are not copied. This module does not generate Rust, apply
model patches, run Cargo, or decide that submitted code preserves behavior.
"""

from __future__ import annotations

import fcntl
import copy
import hashlib
import json
import os
import re
import socket
import tempfile
import tomllib
from collections import Counter, defaultdict
from collections.abc import Mapping
from contextlib import contextmanager
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

from .benchmark import canonical_name, find_rust_project
from .config import RustProjectConfig, config_from_dict, resolve, resume_budget_changes
from .translation_units import RustArtifact, TranslationPlan, write_translation_plan


_KEYWORDS = set("as async await break const continue crate dyn else enum extern false fn for if impl in let loop "
                "match mod move mut pub ref return self Self static struct super trait true type unsafe use where "
                "while abstract become box do final gen macro override priv try typeof unsized virtual yield".split())


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _fingerprint(data) -> str:
    return _sha(json.dumps(data, sort_keys=True, separators=(",", ":")).encode())


def _relative(path: str, *, rust: bool = False) -> str:
    p = PurePosixPath(path)
    if not path or p.is_absolute() or any(s in {".", ".."} for s in path.split("/")) or "\\" in path:
        raise ValueError(f"expected a relative path without traversal: {path!r}")
    if rust and (len(p.parts) < 2 or p.parts[0] != "src" or p.suffix != ".rs"):
        raise ValueError(f"Rust placements must be src/...rs: {path!r}")
    return p.as_posix()


def _inside(root: Path, path: str) -> Path:
    candidate = root / _relative(path)
    if not candidate.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"path leaves the project directory: {path}")
    return candidate


@dataclass
class _Inputs:
    manifest: dict
    jobs: list[dict]
    items: dict[str, dict]
    interfaces: dict[str, str]
    files: dict[str, bytes]
    fingerprint: str


def _read_contexts(path: Path) -> _Inputs:
    root = path.resolve().parent if path.is_file() else path.resolve()
    manifest_path = path.resolve() if path.is_file() else root / "manifest.json"
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    if (not isinstance(manifest, dict) or manifest.get("schema_version") != 1
            or manifest.get("interface_mode") not in {"fixed", "free"}
            or not isinstance(manifest.get("project"), str) or not isinstance(manifest.get("config"), dict)
            or not isinstance(manifest.get("jobs"), list) or not manifest["jobs"]):
        raise ValueError("expected a nonempty translation-context manifest (schema version 1)")
    config_from_dict(manifest["config"])
    if (len(PurePosixPath(_relative(manifest["project"])).parts) != 1
            or not re.fullmatch(r"[a-f0-9]{12}", manifest.get("experiment_hash", ""))):
        raise ValueError("invalid project name or experiment hash in context manifest")
    graph_bytes = (root / "dependencies.json").read_bytes()
    graph = json.loads(graph_bytes)
    if graph.get("project") != manifest["project"]:
        raise ValueError("manifest and dependency graph refer to different projects")
    items = {item["id"]: item for item in graph["items"]}
    if len(items) != len(graph["items"]):
        raise ValueError("dependency graph contains duplicate item IDs")
    for item in manifest.get("interface_items", []):
        if (not isinstance(item, dict) or not isinstance(item.get("id"), str)
                or not item["id"].startswith("interface:") or item["id"] in items
                or item.get("kind") != "interface_function"):
            raise ValueError("invalid interface-completion item")
        items[item["id"]] = item
    files = {"manifest.json": manifest_bytes, "dependencies.json": graph_bytes}
    jobs, interfaces, seen, owned = [], {}, set(), set()
    for entry in manifest["jobs"]:
        key = entry.get("id", "")
        if not re.fullmatch(r"[A-Za-z0-9_-]+", key) or key in seen:
            raise ValueError(f"invalid or duplicate job ID: {key}")
        filename = _relative(entry["json"])
        content = _inside(root, filename).read_bytes()
        if _sha(content) != entry.get("sha256"):
            raise ValueError(f"context file changed since export: {filename}")
        report = json.loads(content)
        if (report.get("id") != key or report.get("item_ids") != entry.get("items")
                or report.get("interface_mode") != manifest["interface_mode"]
                or report.get("order") != len(jobs)
                or entry.get("order") != len(jobs)
                or report.get("prerequisite_units") != entry.get("prerequisite_units")
                or any(p not in seen for p in report.get("prerequisite_units", []))
                or any(item not in items or item in owned for item in report["item_ids"])):
            raise ValueError(f"invalid dependency order or item membership for {key}")
        if any(not isinstance(f.get("path"), str) or not isinstance(f.get("code"), str)
               for f in report.get("interfaces", [])):
            raise ValueError("interface paths and code must be strings")
        supplied = {f["path"]: f["code"] for f in report.get("interfaces", [])}
        if jobs and supplied != interfaces:
            raise ValueError("interface contracts differ between jobs")
        interfaces = supplied
        files[filename] = content
        jobs.append(report)
        seen.add(key)
        owned.update(report["item_ids"])
    if manifest["interface_mode"] == "fixed" and not interfaces:
        raise ValueError("fixed-interface scaffolding requires supplied interface files")
    if manifest["interface_mode"] == "free" and interfaces:
        raise ValueError("free-interface contexts must not contain fixed interface contracts")
    for name, code in interfaces.items():
        if _sha(code.encode()) != manifest.get("interfaces_sha256", {}).get(name):
            raise ValueError(f"interface contract hash mismatch: {name}")
    return _Inputs(manifest, jobs, items, interfaces, files,
                   _fingerprint({name: _sha(data) for name, data in sorted(files.items())}))


def _toml_value(value) -> str:
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=False)
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return str(value)
    if isinstance(value, list):
        return "[" + ", ".join(_toml_value(v) for v in value) + "]"
    if isinstance(value, dict):
        return "{ " + ", ".join(f"{json.dumps(k)} = {_toml_value(v)}" for k, v in value.items()) + " }"
    raise ValueError(f"unsupported Cargo manifest value: {type(value).__name__}")


def _manifest(inputs: _Inputs, options: RustProjectConfig) -> tuple[str, dict]:
    template = {}
    if inputs.manifest["interface_mode"] == "fixed":
        settings = inputs.manifest["config"]["benchmark"]
        crate = find_rust_project(resolve(settings["rust_dir"]), inputs.manifest["project"],
                                  resolve(settings["rust_project"]) if settings.get("rust_project") else None)
        if crate and (crate / "Cargo.toml").is_file():
            template = tomllib.loads((crate / "Cargo.toml").read_text())
    package = template.get("package", {})
    name = options.crate_name or package.get("name") or canonical_name(inputs.manifest["project"])
    if not options.crate_name and not package.get("name"):
        if name and name[0].isdigit():
            name = "proj_" + name
        if name in _KEYWORDS:
            name = "c_" + name
    if not isinstance(name, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9-]*", name) or name.replace("-", "_") in _KEYWORDS:
        raise ValueError(f"invalid Rust crate name: {name!r}; set rust_project.crate_name")
    edition = options.edition if options.edition != "auto" else package.get("edition", "2021")
    if not isinstance(edition, str) or edition not in {"2018", "2021", "2024"}:
        raise ValueError(f"unsupported template edition: {edition!r}; set rust_project.edition")
    data = {"package": {"name": name, "version": package.get("version", "0.1.0"), "edition": edition,
                        "publish": False, "build": False, "autobins": False, "autotests": False,
                        "autoexamples": False, "autobenches": False},
            "lib": {"path": "src/lib.rs"}, "dependencies": {}, "workspace": {}}
    if template.get("lib", {}).get("name"):
        data["lib"]["name"] = template["lib"]["name"]
    if options.copy_manifest_dependencies:
        for key in ("dependencies", "features", "target"):
            if key in template:
                data[key] = template[key]
    data["dependencies"].update(options.dependencies)
    def validate_dependencies(dependencies):
        for key, value in dependencies.items():
            if isinstance(value, dict) and ("path" in value or "workspace" in value):
                raise ValueError(f"dependency {key!r} uses path/workspace inheritance; supply an explicit registry override")
    validate_dependencies(data["dependencies"])
    for target in data.get("target", {}).values():
        # Build and test targets belong to later pipeline stages.
        for key in ("build-dependencies", "dev-dependencies"):
            target.pop(key, None)
        dependencies = target.get("dependencies", {})
        dependencies.update({key: value for key, value in options.dependencies.items() if key in dependencies})
        validate_dependencies(dependencies)
    lines = ["# Generated by c2r scaffold.\n"]
    for section, fields in data.items():
        lines.append(f"[{section}]")
        lines += [f"{json.dumps(k)} = {_toml_value(v)}" for k, v in fields.items()]
        lines.append("")
    text = "\n".join(lines)
    tomllib.loads(text)
    return text, data


def _identifier(text: str) -> str:
    text = re.sub(r"[^A-Za-z_0-9]", "_", text)
    if not text or text[0].isdigit() or text in _KEYWORDS or text in {"lib", "main", "mod"}:
        text = "c_" + text
    return text


def _module(path: str) -> tuple[str, ...]:
    p = PurePosixPath(_relative(path, rust=True))
    if str(p) == "src/lib.rs":
        return ()
    parts = p.parts[1:-1] if p.name == "mod.rs" else (*p.parts[1:-1], p.stem)
    if not parts or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", p) or p in {"crate", "self", "super", "Self"}
                        for p in parts):
        raise ValueError(f"unsupported Rust module path: {path}")
    return tuple(parts)


def _rust_name(name: str) -> str:
    return "r#" + name if name in _KEYWORDS else name


def _wire_modules(files: dict[str, str], *, public: bool) -> None:
    modules = {}
    files.setdefault("src/lib.rs", "// Generated crate root.\n")
    for path in list(files):
        logical = _module(path)
        if logical in modules:
            raise ValueError(f"two Rust files define the same module: {modules[logical]} and {path}")
        modules[logical] = path
    for logical in sorted(list(modules), key=lambda p: (len(p), p)):
        for length in range(1, len(logical)):
            prefix = logical[:length]
            if prefix not in modules:
                path = "src/" + "/".join(prefix) + ".rs"
                modules[prefix] = path
                files[path] = "// Generated parent module.\n"
    for logical, path in sorted(modules.items()):
        if not logical:
            continue
        parent = modules[logical[:-1]]
        name = logical[-1]
        pattern = rf"(?m)^\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+(?:r#)?{re.escape(name)}\s*[;{{]"
        if not re.search(pattern, files[parent]):
            files[parent] = files[parent].rstrip() + "\n" + ("pub " if public else "") + f"mod {_rust_name(name)};\n"


def _free_paths(inputs: _Inputs, options: RustProjectConfig) -> dict[str, str]:
    origins = set()
    for job in inputs.jobs:
        for key in job["item_ids"]:
            item = inputs.items[key]
            origin = item["location"]["file"]
            if item.get("linkage") == "internal" and not origin.endswith(".c") and len(item["units"]) == 1:
                origin = item["units"][0]
            origins.add(origin)
    logical = {}
    for origin in sorted(origins):
        if origin in options.module_map:
            logical[origin] = _relative(options.module_map[origin], rust=True)
            continue
        parts = list(PurePosixPath(_relative(origin)).with_suffix("").parts)
        if len(parts) > 1 and parts[0] in {"src", "include", "inc"}:
            parts.pop(0)
        logical[origin] = "src/" + "/".join(_identifier(p) for p in parts) + ".rs"
    # A foo.c/foo.h pair intentionally shares a module; unrelated names that
    # sanitize identically are disambiguated rather than overwritten.
    aliases = defaultdict(list)
    for origin, path in logical.items():
        aliases[path].append(origin)
    for path, sources in aliases.items():
        stems = {PurePosixPath(s).with_suffix("").as_posix().removeprefix("src/").removeprefix("include/").removeprefix("inc/")
                 for s in sources}
        if len(stems) > 1 and not any(s in options.module_map for s in sources):
            for source in sources:
                p = PurePosixPath(path)
                stem = PurePosixPath(source).with_suffix("").as_posix().removeprefix("src/").removeprefix("include/").removeprefix("inc/")
                logical[source] = str(p.with_name(p.stem + "_" + _sha(stem.encode())[:8] + ".rs"))
    return logical


def _layout(inputs: _Inputs, options: RustProjectConfig) -> tuple[dict[str, str], dict, dict]:
    fixed = inputs.manifest["interface_mode"] == "fixed"
    files, interface_destinations = {}, {}
    for origin, code in inputs.interfaces.items() if fixed else ():
        path = options.interface_map.get(origin)
        if path is None:
            if origin.startswith("src/interfaces/"):
                path = "src/" + origin.removeprefix("src/interfaces/")
            elif origin.startswith("src/"):
                path = origin
            else:
                path = "src/" + PurePosixPath(origin).name
        path = _relative(path, rust=True)
        if path in files:
            raise ValueError(f"interface destination collision: {path}; configure rust_project.interface_map")
        files[path] = code
        interface_destinations[origin] = path
    source_paths = _free_paths(inputs, options) if not fixed else {}
    interface_files = dict(files)
    placements = {}
    for job in inputs.jobs:
        for key in job["item_ids"]:
            item = inputs.items[key]
            origin = item["location"]["file"]
            if item.get("linkage") == "internal" and not origin.endswith(".c") and len(item["units"]) == 1:
                origin = item["units"][0]
            targets = job.get("rust_targets", {}).get(key, [])
            explicit = job.get("rust_files", {}).get(key) or options.module_map.get(origin)
            path, strategy = explicit, "explicit"
            if not path and not fixed:
                path, strategy = source_paths[origin], "source_file"
            if not path and fixed:
                names = [t.split("::")[-1] for t in targets] or [item["name"]]
                matching = [p for p, code in interface_files.items()
                            if all(re.search(rf"\b(?:fn|struct|enum|type|trait|const|static)\s+(?:r#)?{re.escape(n)}\b", code)
                                   for n in names)]
                if len(matching) == 1:
                    path, strategy = matching[0], "unique_interface_symbol"
                elif len(interface_files) == 1:
                    path, strategy = next(iter(interface_files)), "single_interface_file"
                else:
                    basename = _identifier(PurePosixPath(origin).stem) + ".rs"
                    matching = [p for p in interface_files if PurePosixPath(p).name == basename]
                    if len(matching) == 1:
                        path, strategy = matching[0], "matching_interface_module"
                    else:
                        strategy = "unassigned"
            if path:
                path = _relative(path, rust=True)
                files.setdefault(path, "// Generated translation module; source items are recorded in .c2r/state.json.\n")
            header = any(d["file"].endswith(".h") for d in item.get("declarations", []))
            visibility = "private" if item.get("linkage") == "internal" else "public" if header else "crate"
            placements[key] = {"job_id": job["id"], "source_file": origin, "path": path,
                               "module": "::".join(("crate", *map(_rust_name, _module(path)))) if path else None,
                               "rust_targets": targets, "visibility": visibility, "strategy": strategy}
    _wire_modules(files, public=fixed or options.public_modules)
    manifest, cargo = _manifest(inputs, options)
    files["Cargo.toml"] = manifest
    return files, placements, {"cargo": cargo, "interface_destinations": interface_destinations}


def _atomic_write(path: Path, content: bytes, *, mode: int = 0o600) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix=".checkpoint-", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            os.fchmod(stream.fileno(), path.stat().st_mode & 0o777 if path.exists() else mode)
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(name, path)
        parent = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(parent)
        finally:
            os.close(parent)
    finally:
        if os.path.exists(name):
            os.unlink(name)


def _atomic_json(path: Path, data: dict) -> None:
    _atomic_write(path, (json.dumps(data, indent=2, sort_keys=True) + "\n").encode())


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _process_start(pid: int) -> str | None:
    try:
        return Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[19]
    except (OSError, IndexError):
        return None


def _owner_alive(owner: dict) -> bool | None:
    if owner.get("host") != socket.gethostname():
        return None
    pid = owner.get("pid")
    if not isinstance(pid, int) or pid <= 0:
        return False
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    start = _process_start(pid)
    return start == owner["process_start"] if start and owner.get("process_start") else True


def initialize_project(contexts: Path, directory: Path, *, seed: int = 0,
                       options: RustProjectConfig | None = None) -> RustProject:
    """Create a crate or resume its matching checkpoint without overwriting code."""
    inputs = _read_contexts(contexts)
    options = options or config_from_dict(inputs.manifest["config"]).rust_project
    files, placements, metadata = _layout(inputs, options)
    scaffold_fingerprint = _fingerprint({"files": files, "placements": placements, "options": asdict(options)})
    directory = directory.resolve()
    state_path = directory / ".c2r/state.json"
    if state_path.is_file():
        existing = RustProject(directory)
        state = existing.status()
        if (state["plan_fingerprint"] != inputs.fingerprint or state["scaffold_fingerprint"] != scaffold_fingerprint
                or state["seed"] != seed):
            raise ValueError(f"{directory}: inputs/settings differ from the checkpoint; use a new run directory")
        existing.resume()
        return existing
    if directory.exists() and any(directory.iterdir()):
        raise ValueError(f"refusing to overwrite a nonempty directory without a c2r checkpoint: {directory}")
    directory.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".c2r-scaffold-", dir=directory.parent) as tmp:
        stage = Path(tmp) / "crate"
        stage.mkdir()
        for name, code in files.items():
            target = _inside(stage, name)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(code)
        for name, content in inputs.files.items():
            target = _inside(stage / ".c2r/contexts", name)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
        _atomic_json(stage / ".c2r/interfaces.json", {"interfaces": inputs.interfaces})
        global_errors = [i for i in inputs.manifest.get("issues", []) if i["severity"] == "error"]
        jobs = {}
        for job in inputs.jobs:
            errors = global_errors + [i for i in job.get("issues", []) if i["severity"] == "error"]
            jobs[job["id"]] = {"order": job["order"], "item_ids": job["item_ids"],
                                "kind": job.get("kind", "source"),
                                "prerequisite_units": job["prerequisite_units"],
                                "rust_dependency_ids": job["rust_dependency_ids"],
                                "status": "blocked" if errors else "pending", "attempts": 0,
                                "blocked_reasons": errors, "last_error": None, "owner": None,
                                "validation": {}, "completed_at": None}
        state = {"schema_version": 1, "project": inputs.manifest["project"], "seed": seed,
                 "experiment_hash": inputs.manifest["experiment_hash"], "interface_mode": inputs.manifest["interface_mode"],
                 "plan_fingerprint": inputs.fingerprint, "scaffold_fingerprint": scaffold_fingerprint,
                 "options": asdict(options), "metadata": metadata, "placements": placements,
                 "files": {name: {"initial_sha256": _sha(code.encode())} for name, code in files.items()},
                 "jobs": jobs, "artifacts": {}, "supplied_artifacts": inputs.manifest.get("rust_artifacts", {}),
                 "require_rust_context": inputs.manifest["config"]["translation"]["require_rust_context"],
                 "allow_failed_prerequisites": (inputs.manifest["interface_mode"] == "fixed" and
                     inputs.manifest["config"]["translation"].get("continue_after_failure", False)),
                 "revision": 0, "created_at": _now(), "updated_at": _now(),
                 "history": [{"event": "initialized", "at": _now()}]}
        _atomic_json(stage / ".c2r/state.json", state)
        # Another initializer may have won the destination while we prepared.
        os.replace(stage, directory)
    return RustProject(directory)


def create_rust_project(plan: TranslationPlan, directory: Path, *, seed: int = 0) -> RustProject:
    """In-memory context-builder integration, with the same persistent snapshot."""
    with tempfile.TemporaryDirectory(prefix="c2r-scaffold-contexts-") as tmp:
        write_translation_plan(plan, Path(tmp))
        return initialize_project(Path(tmp), directory, seed=seed, options=plan.config.rust_project)


class RustProject:
    def __init__(self, directory: Path):
        self.root = directory.resolve()
        self.state_path = _inside(self.root, ".c2r/state.json")
        if not self.state_path.is_file():
            raise ValueError(f"no c2r checkpoint in {self.root}")

    @contextmanager
    def _locked(self):
        with _inside(self.root, ".c2r/state.lock").open("a+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            state = json.loads(self.state_path.read_text())
            if state.get("schema_version") != 1 or not isinstance(state.get("jobs"), dict):
                raise ValueError("invalid c2r checkpoint")
            yield state

    def _save(self, state: dict, event: str, **detail) -> None:
        state["revision"] += 1
        state["updated_at"] = _now()
        state["history"].append({"event": event, "at": state["updated_at"], **detail})
        _atomic_json(self.state_path, state)

    def status(self) -> dict:
        with self._locked() as state:
            return state

    def _ready(self, state: dict) -> list[str]:
        if any(job["status"] == "in_progress" for job in state["jobs"].values()):
            return []  # One writer/translator per crate; independent runs can run concurrently.
        artifacts = {**state["supplied_artifacts"], **state["artifacts"]}
        failed_items = {item for job in state["jobs"].values() if job["status"] == "failed"
                        for item in job["item_ids"]} if state.get("allow_failed_prerequisites") else set()
        return [key for key, job in sorted(state["jobs"].items(), key=lambda pair: pair[1]["order"])
                if job["status"] == "pending"
                and all(state["jobs"][p]["status"] == "completed" or
                        (state.get("allow_failed_prerequisites") and state["jobs"][p]["status"] == "failed")
                        for p in job["prerequisite_units"])
                and (not state["require_rust_context"] or all(k in artifacts or k in failed_items
                                                             for k in job["rust_dependency_ids"]))]

    def ready_jobs(self) -> list[str]:
        return self._ready(self.status())

    def start_job(self, key: str) -> dict:
        with self._locked() as state:
            if key not in self._ready(state):
                raise ValueError(f"{key} is not ready; inspect prerequisites, status and required Rust context")
            job = state["jobs"][key]
            job.update(status="in_progress", attempts=job["attempts"] + 1, last_error=None,
                       owner={"pid": os.getpid(), "host": socket.gethostname(), "process_start": _process_start(os.getpid())})
            self._save(state, "started", job=key)
            return job

    def _running_job(self, state: dict, key: str) -> dict:
        if key not in state["jobs"] or state["jobs"][key]["status"] != "in_progress":
            raise ValueError(f"{key} is not in progress")
        job = state["jobs"][key]
        if job["owner"] != {"pid": os.getpid(), "host": socket.gethostname(), "process_start": _process_start(os.getpid())}:
            raise ValueError("job is owned by another process; resume interrupted work before claiming it")
        return job

    def set_placement(self, item_id: str, path: str, *, rust_targets: list[str] | None = None) -> None:
        path = _relative(path, rust=True)
        _inside(self.root, path)
        module = "::".join(("crate", *map(_rust_name, _module(path))))
        with self._locked() as state:
            placement = state["placements"].get(item_id)
            if placement is None:
                raise ValueError(f"unknown source item: {item_id}")
            job = state["jobs"][placement["job_id"]]
            if job["status"] == "completed":
                raise ValueError("invalidate the completed job before changing its placement")
            if job["status"] == "in_progress":
                self._running_job(state, placement["job_id"])
            placement.update(path=path, module=module, strategy="explicit")
            if rust_targets is not None:
                if not all(isinstance(t, str) for t in rust_targets):
                    raise ValueError("rust_targets must contain strings")
                placement["rust_targets"] = rust_targets
            self._save(state, "placement_updated", item=item_id)

    def register_module(self, path: str, *, public: bool | None = None) -> None:
        """Wire an existing/new Rust module without inserting generated items.

        A future code integrator can install a module's code first, then call
        this method before recording completion. Other working files remain.
        """
        path = _relative(path, rust=True)
        _module(path)
        with self._locked() as state:
            for key, job in state["jobs"].items():
                if job["status"] == "in_progress":
                    self._running_job(state, key)
            files = {name: _inside(self.root, name).read_text() for name in state["files"] if name.endswith(".rs")}
            target = _inside(self.root, path)
            files[path] = target.read_text() if target.is_file() else "// Generated translation module.\n"
            visibility = public if public is not None else (
                state["interface_mode"] == "free" and state["options"]["public_modules"])
            _wire_modules(files, public=visibility)
            # Write descendants before parents that declare them. State is
            # committed after all module files have been installed.
            for name, code in sorted(files.items(), key=lambda pair: -len(_module(pair[0]))):
                destination = _inside(self.root, name)
                destination.parent.mkdir(parents=True, exist_ok=True)
                if not destination.is_file() or destination.read_text() != code:
                    _atomic_write(destination, code.encode(), mode=0o644)
                state["files"].setdefault(name, {"initial_sha256": _sha(code.encode())})
            self._save(state, "module_registered", path=path)

    def complete_job(self, key: str, artifacts: Mapping[str, object], *, validation: dict | None = None) -> None:
        """Register already-installed item code, not an unapplied model response.

        Cargo/testing results can be attached by the future runner. Completion
        here records its decision; this method does not perform those checks.
        """
        with self._locked() as state:
            job = self._running_job(state, key)
            if set(artifacts) != set(job["item_ids"]):
                raise ValueError("completion must account for every source item in the job, and no others")
            installed = {}
            for item, value in artifacts.items():
                if isinstance(value, RustArtifact):
                    value = asdict(value)
                elif isinstance(value, str):
                    value = {"code": value, "path": state["placements"][item]["path"]}
                if (not isinstance(value, dict) or not isinstance(value.get("code"), str) or not value["code"]
                        or not isinstance(value.get("path"), str)):
                    raise ValueError(f"{item}: provide nonempty installed Rust code and its path")
                path = _relative(value["path"], rust=True)
                if path not in state["files"]:
                    raise ValueError(f"{path} is not a registered module; call register_module first")
                target = _inside(self.root, path)
                if value["code"] not in target.read_text():
                    raise ValueError(f"{item}: registered code is not present in {path}")
                module = "::".join(("crate", *map(_rust_name, _module(path))))
                installed[item] = {"code": value["code"], "path": path, "sha256": _sha(value["code"].encode())}
                definitions = value.get("definitions", {})
                if (not isinstance(definitions, dict) or not all(isinstance(k, str) and isinstance(v, str) and v
                                                                for k, v in definitions.items())):
                    raise ValueError("installed definitions must map target names to nonempty Rust code")
                if any(code not in target.read_text() for code in definitions.values()):
                    raise ValueError(f"{item}: an installed definition is not present in {path}")
                if definitions:
                    installed[item]["definitions"] = definitions
                state["placements"][item].update(path=path, module=module)
            state["artifacts"].update(installed)
            job.update(status="completed", owner=None, completed_at=_now(), validation=validation or {},
                       cargo_manifest_sha256=_sha((self.root / "Cargo.toml").read_bytes()),
                       cargo_lock_sha256=_sha((self.root / "Cargo.lock").read_bytes()) if (self.root / "Cargo.lock").is_file() else None)
            self._save(state, "completed", job=key, validation=validation or {})

    def fail_job(self, key: str, error: str, *, details: dict | None = None) -> None:
        with self._locked() as state:
            job = self._running_job(state, key)
            job.update(status="failed", owner=None, last_error=error, validation=details or {})
            self._save(state, "failed", job=key, error=error, details=details or {})

    def interrupt_job(self, key: str) -> None:
        with self._locked() as state:
            job = self._running_job(state, key)
            job.update(status="pending", owner=None, last_error="Interrupted before completion")
            self._save(state, "interrupted", job=key)

    def retry_job(self, key: str) -> None:
        with self._locked() as state:
            job = state["jobs"].get(key)
            if job is None or job["status"] != "failed":
                raise ValueError("only a failed job can be retried; invalidate completed jobs explicitly")
            job["status"] = "pending"
            self._save(state, "retry_requested", job=key)

    def configure_execution(self, settings: dict, *, allow_token_limit_increase: bool = False,
                            allow_request_limit_decrease: bool = False) -> None:
        """Freeze settings, with audited pipeline output/call-budget exceptions."""
        identity = _fingerprint(settings)
        with self._locked() as state:
            if "execution" in state:
                execution = state["execution"]
                if execution["settings_sha256"] != identity:
                    previous = execution["settings"]
                    changes = resume_budget_changes(
                        {"model": previous.get("model", {}), "runner": previous.get("runner", {})},
                        {"model": settings.get("model", {}), "runner": settings.get("runner", {})})
                    restored = copy.deepcopy(settings)
                    compatible = changes is not None
                    token_increased = False
                    for change in changes or []:
                        section, field = change["setting"].split(".")
                        restored[section][field] = change["old"]
                        if section == "model":
                            token_increased = True
                            compatible &= allow_token_limit_increase
                            if "max_tokens" in previous.get("client", {}):
                                compatible &= (previous["client"]["max_tokens"] == change["old"]
                                               and restored.get("client", {}).get("max_tokens") == change["new"])
                                restored["client"]["max_tokens"] = change["old"]
                        else:
                            compatible &= allow_request_limit_decrease
                    if changes:
                        restored["experiment_hash"] = previous.get("experiment_hash")
                    if not compatible or restored != previous:
                        raise ValueError("runner/model settings differ from the checkpoint; use a fresh run directory")
                    execution.setdefault("settings_history", []).append({
                        "at": _now(), "settings": previous, "settings_sha256": execution["settings_sha256"],
                        "through_call": execution["model_calls"], "reason": "request_budgets_changed",
                        "changes": changes})
                    execution.update(settings=settings, settings_sha256=identity)
                    if token_increased:
                        execution["job_call_offsets"] = dict(execution["job_calls"])
                    self._save(state, "request_budgets_changed", changes=changes)
                return
            state["execution"] = {"settings": settings, "settings_sha256": identity,
                                  "model_calls": 0, "job_calls": {}, "calls": {}}
            self._save(state, "execution_configured")

    def reserve_model_call(self, key: str, *, job_limit: int, total_limit: int | None) -> int:
        """Reserve before sending, so interrupted requests still consume the budget."""
        with self._locked() as state:
            self._running_job(state, key)
            execution = state["execution"]
            used = execution["job_calls"].get(key, 0) - execution.get("job_call_offsets", {}).get(key, 0)
            if used >= job_limit:
                raise ValueError("this job has exhausted its model-call/repair budget")
            if total_limit is not None and execution["model_calls"] >= total_limit:
                raise ValueError("the run has exhausted runner.max_model_calls")
            execution["model_calls"] += 1
            execution["job_calls"][key] = execution["job_calls"].get(key, 0) + 1
            number = execution["model_calls"]
            execution["calls"][str(number)] = {"job_id": key, "status": "reserved", "reserved_at": _now(),
                                               "settings_sha256": execution["settings_sha256"],
                                               "max_tokens": execution["settings"].get("model", {}).get(
                                                   "max_tokens", execution["settings"].get("client", {}).get("max_tokens"))}
            self._save(state, "model_call_reserved", job=key, call_number=number)
            return number

    def record_model_call(self, number: int, details: dict) -> None:
        with self._locked() as state:
            call = state["execution"]["calls"][str(number)]
            self._running_job(state, call["job_id"])
            call.update(details, finished_at=_now())
            self._save(state, "model_call_recorded", call_number=number)

    def _invalidate(self, state: dict, keys: set[str], reason: str) -> list[str]:
        affected = set(keys)
        while True:
            added = {key for key, job in state["jobs"].items()
                     if (set(job["prerequisite_units"]) |
                         set(job.get("recovery", {}).get("completion_jobs", []))) & affected} - affected
            if not added:
                break
            affected |= added
        for key in affected:
            job = state["jobs"][key]
            if job["status"] == "in_progress" and _owner_alive(job["owner"]) is not False:
                raise ValueError("cannot invalidate work owned by a live or unknown process")
        for key in affected:
            job = state["jobs"][key]
            job.pop("recovery", None)
            for item in job["item_ids"]:
                state["artifacts"].pop(item, None)
            job.update(status="blocked" if job["blocked_reasons"] else "pending", owner=None,
                       last_error=reason, completed_at=None, validation={})
        return sorted(affected, key=lambda k: state["jobs"][k]["order"])

    def invalidate_job(self, key: str, reason: str) -> list[str]:
        with self._locked() as state:
            if key not in state["jobs"]:
                raise ValueError(f"unknown job: {key}")
            affected = self._invalidate(state, {key}, reason)
            self._save(state, "invalidated", jobs=affected, reason=reason)
            return affected

    def resume(self, *, force_recover: bool = False) -> dict:
        archived = _read_contexts(self.root / ".c2r/contexts")
        with self._locked() as state:
            if archived.fingerprint != state["plan_fingerprint"]:
                raise ValueError("archived context inputs have changed; the checkpoint cannot be resumed")
            recovered = []
            for key, job in state["jobs"].items():
                if job["status"] == "in_progress" and (force_recover or _owner_alive(job["owner"]) is False):
                    job.update(status="pending", owner=None, last_error="Interrupted before completion")
                    recovered.append(key)
            invalid = set()
            restored_edits = False
            # Do not inspect partially edited files while a translator is active.
            if not any(job["status"] == "in_progress" for job in state["jobs"].values()):
                from .rust_edits import recover_transaction
                restored_edits = recover_transaction(self, state)
                cargo_hash = _sha((self.root / "Cargo.toml").read_bytes())
                lock_hash = _sha((self.root / "Cargo.lock").read_bytes()) if (self.root / "Cargo.lock").is_file() else None
                for key, job in state["jobs"].items():
                    if job["status"] != "completed":
                        continue
                    if job.get("cargo_manifest_sha256") != cargo_hash:
                        invalid.add(key)
                    if "cargo_lock_sha256" in job and job["cargo_lock_sha256"] != lock_hash:
                        invalid.add(key)
                    for item in job["item_ids"]:
                        artifact = state["artifacts"].get(item)
                        try:
                            text = _inside(self.root, artifact["path"]).read_text() if artifact else ""
                            present = artifact and artifact["code"] in text and all(
                                code in text for code in artifact.get("definitions", {}).values())
                        except OSError:
                            present = False
                        if not present:
                            invalid.add(key)
            affected = self._invalidate(state, invalid, "Recorded Rust code or Cargo manifest changed") if invalid else []
            if recovered or affected or restored_edits:
                self._save(state, "resumed", recovered=recovered, invalidated=affected, recovered_edits=restored_edits)
            return state

    def rust_artifacts(self) -> dict[str, RustArtifact]:
        state = self.status()
        supplied = {**state["supplied_artifacts"], **state["artifacts"]}
        return {key: RustArtifact("\n\n".join(f"// {target}\n{code}" for target, code in value["definitions"].items())
                                 if value.get("definitions") else value["code"], value.get("path", ""))
                for key, value in supplied.items()}

    def write_artifact_context(self, path: Path | None = None) -> Path:
        state = self.status()
        artifacts = {key: asdict(value) for key, value in self.rust_artifacts().items()}
        destination = path or self.root / ".c2r/rust_artifacts.json"
        _atomic_json(destination, {"projects": {state["project"]: artifacts}})
        return destination

    def record_validation(self, report: dict) -> None:
        """Attach evaluation evidence without changing translation job status."""
        from .validation import candidate_fingerprint
        with self._locked() as state:
            if report["project"] != state["project"] or report["seed"] != state["seed"]:
                raise ValueError("validation report belongs to a different translation run")
            summary = {"id": report["id"], "outcome": report["outcome"],
                       "report_path": report["report_path"], "candidate_sha256": report["candidate_sha256"],
                       "counts": report["counts"], "programs_passed": report["programs_passed"],
                       "programs_failed": report["programs_failed"],
                       "translation_complete": report["source_snapshot"]["complete"],
                       "suite_sha256": report.get("suite", {}).get("suite_sha256"),
                       "settings_sha256": _fingerprint(report["settings"]),
                       "current_at_recording": candidate_fingerprint(self) == report["candidate_sha256"],
                       "finished_at": report["finished_at"], "feedback_to_model": False}
            state.setdefault("validations", []).append(summary)
            self._save(state, "validated", validation_id=report["id"], outcome=report["outcome"])

    def summary(self) -> dict:
        state = self.status()
        summary = {"project": state["project"], "seed": state["seed"], "crate": str(self.root),
                "interface_mode": state["interface_mode"], "revision": state["revision"],
                "jobs": dict(Counter(job["status"] for job in state["jobs"].values())),
                "ready_jobs": self._ready(state),
                "unassigned_items": [key for key, placement in state["placements"].items() if not placement["path"]]}
        if state.get("validations"):
            from .validation import candidate_fingerprint
            latest = state["validations"][-1]
            summary["latest_validation"] = {**latest, "current": candidate_fingerprint(self) == latest["candidate_sha256"]}
        if state.get("idiomatic_runs"):
            from .validation import candidate_fingerprint
            latest = state["idiomatic_runs"][-1]
            summary["latest_idiomatic"] = {**latest, "current": candidate_fingerprint(self) == latest["source_sha256"]}
        return summary
