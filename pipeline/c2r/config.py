"""Pipeline configuration: one YAML file plus command-line overrides.

Every ablation switch from steps.md §5 is a field here. Unknown keys are
errors, so a typo in an ablation file fails loudly instead of being ignored.
"""

from __future__ import annotations

import dataclasses
import copy
import hashlib
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, get_type_hints

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
MAIN_CONFIG = REPO_ROOT / "pipeline" / "configs" / "main.yaml"

EXPERIMENTS = ("E1", "E2")
TARGETS = ("aarch64-linux", "x86_64-linux")
REPRESENTATIONS = ("original_c", "clight", "clight_pass", "original_c+clight_pass")
CONTEXTS = ("none", "direct", "scc")
GRANULARITIES = ("unit", "project")
HINT_KINDS = ("array", "derived", "mutability", "ownership", "length", "string",
              "nullability", "aliasing", "liveness")
FEEDBACK = ("compiler", "tests")
RENAMINGS = ("none", "meaningful")
INTERFACE_MODES = ("auto", "fixed", "free")
SOURCE_SCOPES = ("library", "all")
MISSING_REPRESENTATIONS = ("error", "original_c", "failed_units")
INCOMPLETE_GRAPHS = ("error", "allow")


class ConfigError(ValueError):
    pass


class PromptBudgetError(ValueError):
    def __init__(self, actual: int, limit: int):
        self.actual, self.limit = actual, limit
        super().__init__(f"Prompt has {actual} characters; limit is {limit}; no code was truncated")


@dataclass
class BenchmarkConfig:
    c_dir: str = "CBench"
    rust_dir: str = "RBench"
    rust_project: str | None = None   # explicit RBench crate, independent of C folder name


@dataclass
class ModelConfig:
    provider: str = "openrouter"
    id: str | None = None          # OpenRouter model id; required before any LLM call (A9)
    temperature: float = 0.2
    max_tokens: int = 8192
    base_url: str = "https://openrouter.ai/api/v1"
    api_key_env: str = "OPENROUTER_API_KEY"
    timeout: int = 600             # supervised wall-clock deadline for live model requests
    response_format: str = "json_schema"  # json_schema | json_object | none
    reasoning_effort: str | None = None  # null keeps the provider default; support varies by model


@dataclass
class InputConfig:
    representation: str = "clight_pass"   # A1
    restore_names: bool = False           # full §30 restoration is not implemented


@dataclass
class RefactorConfig:
    memory_pointers: bool = False         # A8: also cache pointers stored in memory (unverified)
    # CompCert flag sets tried in order until one is accepted.
    # - CompCert's defaults reject struct passing by value, long double, inline
    #   asm, packed structs and unstructured switch; -fall enables all of them.
    # - CompCert preprocesses with -std=c99, which hides the POSIX/BSD
    #   declarations (M_PI, struct timespec, ...) that GCC's default gnu17 mode
    #   shows; -D_DEFAULT_SOURCE shows them again. It is not always on, because
    #   it also makes aarch64 system headers declare __int128 types, which
    #   CompCert rejects.
    flag_sets: list[list[str]] = field(default_factory=lambda: [
        [], ["-D_DEFAULT_SOURCE"], ["-fall"], ["-fall", "-D_DEFAULT_SOURCE"]])
    extra_flags: list[str] = field(default_factory=list)   # added to every attempt
    timeout: int = 120                    # seconds per ptridxgen call
    memory_limit_mb: int = 2048           # address-space cap per ptridxgen call
    keep_rocq_ast: bool = False           # keep <file>.v outputs (large; only needed for Rocq work)


@dataclass
class RewritesConfig:
    """Meaning-preserving source rewrites applied before CompCert (c2r/rewrite.py).
    Each turns a GNU extension or C23 feature that CompCert rejects into
    standard C with the meaning GCC gives it."""
    binary_literals: bool = True          # 0b1010u -> 0xau
    double_suffix: bool = True            # 9.81d -> 9.81
    # Off: GCC types a decimal literal above LLONG_MAX as __int128, which
    # CompCert lacks; ...ULL keeps the value but not the type.
    large_literals: bool = False          # decimal literal above LLONG_MAX -> ...ULL
    labels_at_block_end: bool = True      # default: } -> default: ; }
    case_ranges: bool = True              # case 1 ... 3: -> case 1: case 2: case 3:
    empty_initializers: bool = True       # = {} and (T){} -> {0}
    gnu_builtins: bool = True             # __builtin_popcount etc. -> portable definitions
    void_pointer_arithmetic: bool = True  # p + n on void * -> (void *)((char *)(p) + (n))


@dataclass
class HintsConfig:                        # A4, A4b
    enabled: bool = False
    kinds: list[str] = field(default_factory=lambda: [
        "array", "derived", "mutability", "ownership", "nullability"])
    include_heuristic: bool = False
    show_tags: bool = True


@dataclass
class RepairConfig:                       # A7
    max_retries: int = 3
    feedback: list[str] = field(default_factory=lambda: ["compiler"])


@dataclass
class TranslationConfig:
    interface_mode: str = "auto"    # E2 -> fixed, E1 -> free; can be overridden independently
    interface_files: list[str] = field(default_factory=list)  # empty: use project.interfaces
    scope: str = "library"          # omit C tests and examples unless explicitly requested
    translate_macros: bool = False  # otherwise macros are context, not separate translation jobs
    include_external: bool = True
    dependency_depth: int = 1       # direct edges; SCC expansion follows cfg.context
    incomplete_graph: str = "error"
    missing_representation: str = "error"  # explicit fallback for unavailable lowered bodies
    require_rust_context: bool = False     # useful when preparing a job for actual execution
    max_prompt_chars: int | None = 64000  # exact requests are checked before reserving a paid call
    lowered_expansion_ratio: float = 8.0
    lowered_expansion_min_chars: int = 8000
    item_map: str | None = None     # explicit C-lowered symbol and Rust target mappings, keyed by item ID
    rust_artifacts: str | None = None  # previously translated Rust, keyed by item ID
    indirect_calls: str = "warn"    # signature candidates are context, not a points-to proof
    legacy_c_diagnostics: bool = True
    clang_compatibility: bool = True  # bounded, recorded retries for original C
    continue_after_failure: bool = True  # fixed interfaces only; retain failed placeholders


@dataclass
class RustProjectConfig:
    crate_name: str | None = None   # default: fixed-interface package name or normalized C project name
    edition: str = "auto"          # template edition in fixed mode, otherwise 2021
    public_modules: bool = True
    copy_manifest_dependencies: bool = True  # fixed mode only; never copy reference implementation files
    dependencies: dict[str, Any] = field(default_factory=dict)
    module_map: dict[str, str] = field(default_factory=dict)    # original C file -> src/...rs
    interface_map: dict[str, str] = field(default_factory=dict) # supplied interface path -> src/...rs


@dataclass
class RunnerConfig:
    compile_timeout: int = 120
    offline: bool = True
    cargo_jobs: int = 1
    max_model_calls: int | None = None  # cumulative, including interrupted/failed requests
    max_edit_files: int = 16
    continue_on_failure: bool = True
    output_protocol: str = "auto"   # auto: fixed_functions for E2, edits for free mode


@dataclass
class ValidationConfig:
    build_timeout: int = 120
    test_timeout: int = 30
    offline: bool = True
    cargo_jobs: int = 1
    test_threads: int = 1
    include_ignored: bool = False
    targets: list[str] = field(default_factory=list)   # empty: all discovered benchmark targets
    support_files: list[str] = field(default_factory=list)  # explicit benchmark-relative fixtures/helpers
    dependencies: dict[str, Any] = field(default_factory=dict)  # isolated harness dev-dependency overrides
    keep_workspace: bool = True


@dataclass
class MetricsConfig:
    enabled: bool = True
    clippy: bool = False
    timeout: int = 120


@dataclass
class ToolsConfig:
    compcert_dir: str = "CompCert"        # in-tree build; ptridxgen is built here too
    # CompCert's own standard headers (stdarg.h, stddef.h, ...). The in-tree
    # binaries look for them at <bin>/../lib/compcert, which doesn't exist, and
    # would silently fall back to GCC's.
    compcert_stdlib: str = "CompCert/runtime"
    opam: str = "~/.local/bin/opam"
    opam_switch: str = "compcert"
    cargo: str = "cargo"
    rust_toolchain: str = "nightly-2025-05-13"   # passed as `cargo +<toolchain>`
    clang: str = "clang"                  # only for its resource dir (builtin headers for libclang)


@dataclass
class OutputConfig:
    runs_dir: str = "runs"
    refactored_dir: str = "results/refactored"   # stage 1 over the benchmark (`c2r refactor`)
    work_dir: str = "runs/work"           # scratch space on disk (/tmp is RAM-backed here)


@dataclass
class Config:
    experiment: str = "E2"
    projects: list[str] | str = "all"
    seeds: list[int] = field(default_factory=lambda: [0])
    target: str | None = None             # D3, still open
    benchmark: BenchmarkConfig = field(default_factory=BenchmarkConfig)
    model: ModelConfig = field(default_factory=ModelConfig)
    input: InputConfig = field(default_factory=InputConfig)
    refactor: RefactorConfig = field(default_factory=RefactorConfig)
    rewrites: RewritesConfig = field(default_factory=RewritesConfig)
    context: str = "scc"                  # A2
    granularity: str = "unit"             # A6
    hints: HintsConfig = field(default_factory=HintsConfig)
    repair: RepairConfig = field(default_factory=RepairConfig)
    translation: TranslationConfig = field(default_factory=TranslationConfig)
    rust_project: RustProjectConfig = field(default_factory=RustProjectConfig)
    runner: RunnerConfig = field(default_factory=RunnerConfig)
    validation: ValidationConfig = field(default_factory=ValidationConfig)
    metrics: MetricsConfig = field(default_factory=MetricsConfig)
    idiomatic_stage: bool = False         # A3
    renaming: str = "none"                # C1
    tools: ToolsConfig = field(default_factory=ToolsConfig)
    output: OutputConfig = field(default_factory=OutputConfig)


def resolve(path: str) -> Path:
    """Resolve a config path: '~' expands, relative paths are relative to the repo root."""
    p = Path(path).expanduser()
    return p if p.is_absolute() else REPO_ROOT / p


def load_config(path: Path | str | None = MAIN_CONFIG, overrides: list[str] = ()) -> Config:
    """Load a YAML config and apply KEY=VALUE overrides (dotted keys, YAML values)."""
    data: dict[str, Any] = {}
    if path is not None:
        with open(path) as fh:
            data = yaml.safe_load(fh) or {}
    return config_from_dict(data, overrides)


def config_from_dict(data: dict[str, Any], overrides: list[str] = ()) -> Config:
    """Validate an exported configuration, optionally applying CLI overrides."""
    data = copy.deepcopy(data)
    for item in overrides:
        key, sep, raw = item.partition("=")
        if not sep or not key.strip():
            raise ConfigError(f"override {item!r}: expected KEY=VALUE")
        _set_dotted(data, key.strip(), yaml.safe_load(raw))
    cfg = _build(Config, data, "")
    _validate(cfg)
    _normalize(cfg)
    return cfg


# Fields that don't change what a run computes: which projects and seeds are
# selected (both are part of the cache key on their own), where tools live and
# where results go.
# Evaluation settings are recorded in validation reports, not translation IDs.
_NOT_HASHED = ("projects", "seeds", "tools", "output", "validation", "metrics")


def experiment_hash(cfg: Config) -> str:
    d = to_dict(cfg)
    for key in _NOT_HASHED:
        d.pop(key)
    if d["benchmark"].get("rust_project") is None:
        d["benchmark"].pop("rust_project", None)  # preserve existing run IDs
    blob = json.dumps(d, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(blob.encode()).hexdigest()[:12]


def to_dict(cfg: Config) -> dict[str, Any]:
    data = dataclasses.asdict(cfg)
    # An unset reasoning option must preserve existing run/checkpoint identities.
    if cfg.model.reasoning_effort is None:
        data["model"].pop("reasoning_effort")
    # Keep existing checkpoint identities when the new parser policy uses its
    # default. Graph exports separately record the parser implementation version.
    if cfg.translation.clang_compatibility:
        data["translation"].pop("clang_compatibility")
    return data


def token_limit_increase(previous: dict, current: dict) -> tuple[int, int] | None:
    """Recognize exactly one configuration change: a higher output budget."""
    before = previous.get("model", {}).get("max_tokens")
    after = current.get("model", {}).get("max_tokens")
    if (type(before) is not int or type(after) is not int
            or before < 1 or after <= before):
        return None
    restored = copy.deepcopy(current)
    restored["model"]["max_tokens"] = before
    return (before, after) if restored == previous else None


def resume_budget_changes(previous: dict, current: dict) -> list[dict] | None:
    """Allow only a higher output limit and/or a lower cumulative call cap."""
    restored = copy.deepcopy(current)
    changes = []
    for section, field in (("model", "max_tokens"), ("runner", "max_model_calls")):
        before = previous.get(section, {}).get(field)
        after = current.get(section, {}).get(field)
        if before == after:
            continue
        if section == "model":
            allowed = type(before) is int and type(after) is int and 0 < before < after
        else:
            allowed = (type(after) is int and after > 0
                       and (before is None or (type(before) is int and after < before)))
        if not allowed:
            return None
        restored[section][field] = before
        changes.append({"setting": f"{section}.{field}", "old": before, "new": after})
    return changes if changes and restored == previous else None


def _set_dotted(data: dict[str, Any], dotted: str, value: Any) -> None:
    *parents, last = dotted.split(".")
    node = data
    for part in parents:
        node = node.setdefault(part, {})
        if not isinstance(node, dict):
            raise ConfigError(f"override {dotted!r}: {part!r} is not a section")
    node[last] = value


def _build(cls: type, data: Any, where: str) -> Any:
    if not isinstance(data, dict):
        raise ConfigError(f"{where or 'config'}: expected a mapping, got {type(data).__name__}")
    names = {f.name for f in dataclasses.fields(cls)}
    unknown = sorted(set(data) - names)
    if unknown:
        raise ConfigError(f"{where or 'config'}: unknown key(s) {unknown}")
    types = get_type_hints(cls)
    kwargs = {}
    for name, value in data.items():
        if dataclasses.is_dataclass(types[name]):
            value = _build(types[name], value, f"{where}.{name}" if where else name)
        kwargs[name] = value
    return cls(**kwargs)


def _check(ok: bool, message: str) -> None:
    if not ok:
        raise ConfigError(message)


def _one_of(value: Any, choices: tuple[str, ...], key: str) -> None:
    _check(value in choices, f"{key}: {value!r} is not one of {list(choices)}")


def _is_bool(value: Any, key: str) -> None:
    _check(isinstance(value, bool), f"{key}: expected true or false, got {value!r}")


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _validate(cfg: Config) -> None:
    _one_of(cfg.experiment, EXPERIMENTS, "experiment")
    _check(cfg.projects == "all" or (isinstance(cfg.projects, list) and cfg.projects
                                     and all(isinstance(p, str) for p in cfg.projects)),
           "projects: expected 'all' or a non-empty list of project names")
    _check(isinstance(cfg.seeds, list) and cfg.seeds and all(_is_int(s) for s in cfg.seeds),
           "seeds: expected a non-empty list of integers")
    _check(cfg.target is None or cfg.target in TARGETS,
           f"target: {cfg.target!r} is not null or one of {list(TARGETS)}")
    _check(cfg.benchmark.rust_project is None or (isinstance(cfg.benchmark.rust_project, str)
                                                and bool(cfg.benchmark.rust_project)),
           "benchmark.rust_project: expected null or a crate directory")

    m = cfg.model
    _one_of(m.provider, ("openrouter",), "model.provider")
    _check(m.id is None or (isinstance(m.id, str) and m.id != ""), "model.id: expected a model id or null")
    _check(isinstance(m.temperature, (int, float)) and not isinstance(m.temperature, bool)
           and 0 <= m.temperature <= 2, "model.temperature: expected a number in [0, 2]")
    _check(_is_int(m.max_tokens) and m.max_tokens > 0, "model.max_tokens: expected a positive integer")
    _check(_is_int(m.timeout) and m.timeout > 0, "model.timeout: expected a positive integer")
    _one_of(m.response_format, ("json_schema", "json_object", "none"), "model.response_format")
    if m.reasoning_effort is not None:
        _one_of(m.reasoning_effort, ("none", "minimal", "low", "medium", "high", "xhigh", "max"),
                "model.reasoning_effort")
    _check(isinstance(m.base_url, str) and m.base_url.startswith(("https://", "http://")),
           "model.base_url: expected an HTTP(S) URL")
    _check(isinstance(m.api_key_env, str) and bool(m.api_key_env), "model.api_key_env: expected an environment variable name")

    _one_of(cfg.input.representation, REPRESENTATIONS, "input.representation")
    _is_bool(cfg.input.restore_names, "input.restore_names")
    _check(not cfg.input.restore_names, "input.restore_names is not implemented; use false (prompts include reading guidance)")
    _is_bool(cfg.refactor.memory_pointers, "refactor.memory_pointers")
    fs = cfg.refactor.flag_sets
    _check(isinstance(fs, list) and fs and all(isinstance(s, list) and all(isinstance(f, str) for f in s)
                                               for s in fs),
           "refactor.flag_sets: expected a non-empty list of flag lists, e.g. [[], [-fall]]")
    _check(isinstance(cfg.refactor.extra_flags, list)
           and all(isinstance(f, str) for f in cfg.refactor.extra_flags),
           "refactor.extra_flags: expected a list of flags")
    _check(_is_int(cfg.refactor.timeout) and cfg.refactor.timeout > 0,
           "refactor.timeout: expected a positive integer")
    _check(_is_int(cfg.refactor.memory_limit_mb) and cfg.refactor.memory_limit_mb > 0,
           "refactor.memory_limit_mb: expected a positive integer")
    _is_bool(cfg.refactor.keep_rocq_ast, "refactor.keep_rocq_ast")
    for f in dataclasses.fields(RewritesConfig):
        _is_bool(getattr(cfg.rewrites, f.name), f"rewrites.{f.name}")
    _one_of(cfg.context, CONTEXTS, "context")
    _one_of(cfg.granularity, GRANULARITIES, "granularity")

    h = cfg.hints
    _is_bool(h.enabled, "hints.enabled")
    _check(not h.enabled, "pointer hints are not implemented; hints.enabled must be false")
    _check(isinstance(h.kinds, list), "hints.kinds: expected a list")
    for kind in h.kinds:
        _one_of(kind, HINT_KINDS, "hints.kinds")
    _is_bool(h.include_heuristic, "hints.include_heuristic")
    _is_bool(h.show_tags, "hints.show_tags")

    r = cfg.repair
    _check(_is_int(r.max_retries) and r.max_retries >= 0, "repair.max_retries: expected an integer >= 0")
    _check(isinstance(r.feedback, list), "repair.feedback: expected a list")
    for kind in r.feedback:
        _one_of(kind, FEEDBACK, "repair.feedback")

    t = cfg.translation
    _one_of(t.interface_mode, INTERFACE_MODES, "translation.interface_mode")
    _one_of(t.scope, SOURCE_SCOPES, "translation.scope")
    _one_of(t.missing_representation, MISSING_REPRESENTATIONS, "translation.missing_representation")
    _one_of(t.incomplete_graph, INCOMPLETE_GRAPHS, "translation.incomplete_graph")
    _one_of(t.indirect_calls, ("warn", "error"), "translation.indirect_calls")
    for key in ("legacy_c_diagnostics", "clang_compatibility", "continue_after_failure"):
        _is_bool(getattr(t, key), f"translation.{key}")
    _check(isinstance(t.interface_files, list) and all(isinstance(p, str) and p for p in t.interface_files),
           "translation.interface_files: expected a list of paths")
    _check(_is_int(t.dependency_depth) and t.dependency_depth >= 1,
           "translation.dependency_depth: expected an integer >= 1")
    _check(t.max_prompt_chars is None or (_is_int(t.max_prompt_chars) and t.max_prompt_chars > 0),
           "translation.max_prompt_chars: expected null or an integer > 0")
    _check(isinstance(t.lowered_expansion_ratio, (int, float)) and not isinstance(t.lowered_expansion_ratio, bool)
           and t.lowered_expansion_ratio > 1, "translation.lowered_expansion_ratio: expected a number > 1")
    _check(_is_int(t.lowered_expansion_min_chars) and t.lowered_expansion_min_chars > 0,
           "translation.lowered_expansion_min_chars: expected positive characters")
    for key in ("translate_macros", "include_external", "require_rust_context"):
        _is_bool(getattr(t, key), f"translation.{key}")
    for key in ("item_map", "rust_artifacts"):
        value = getattr(t, key)
        _check(value is None or (isinstance(value, str) and value), f"translation.{key}: expected null or a path")

    rp = cfg.rust_project
    _check(rp.crate_name is None or (isinstance(rp.crate_name, str) and bool(rp.crate_name)),
           "rust_project.crate_name: expected null or a nonempty name")
    _one_of(rp.edition, ("auto", "2018", "2021", "2024"), "rust_project.edition")
    _is_bool(rp.public_modules, "rust_project.public_modules")
    _is_bool(rp.copy_manifest_dependencies, "rust_project.copy_manifest_dependencies")
    for key in ("module_map", "interface_map"):
        value = getattr(rp, key)
        _check(isinstance(value, dict) and all(isinstance(k, str) and isinstance(v, str) and k and v
                                              for k, v in value.items()),
               f"rust_project.{key}: expected a mapping of paths to Rust file paths")
    _check(isinstance(rp.dependencies, dict) and all(isinstance(k, str) and isinstance(v, (str, dict))
                                                   for k, v in rp.dependencies.items()),
           "rust_project.dependencies: expected dependency names mapped to versions or tables")

    runner = cfg.runner
    _one_of(runner.output_protocol, ("auto", "edits", "fixed_functions"), "runner.output_protocol")
    for key in ("compile_timeout", "cargo_jobs", "max_edit_files"):
        _check(_is_int(getattr(runner, key)) and getattr(runner, key) > 0, f"runner.{key}: expected a positive integer")
    for key in ("offline", "continue_on_failure"):
        _is_bool(getattr(runner, key), f"runner.{key}")
    _check(runner.max_model_calls is None or (_is_int(runner.max_model_calls) and runner.max_model_calls > 0),
           "runner.max_model_calls: expected null or a positive integer")

    v = cfg.validation
    for key in ("build_timeout", "test_timeout", "cargo_jobs", "test_threads"):
        _check(_is_int(getattr(v, key)) and getattr(v, key) > 0, f"validation.{key}: expected a positive integer")
    for key in ("offline", "include_ignored", "keep_workspace"):
        _is_bool(getattr(v, key), f"validation.{key}")
    for key in ("targets", "support_files"):
        value = getattr(v, key)
        _check(isinstance(value, list) and all(isinstance(p, str) and p for p in value),
               f"validation.{key}: expected a list of nonempty strings")
    _check(isinstance(v.dependencies, dict) and all(isinstance(k, str) and isinstance(x, (str, dict))
                                                  for k, x in v.dependencies.items()),
           "validation.dependencies: expected dependency names mapped to versions or tables")

    _is_bool(cfg.idiomatic_stage, "idiomatic_stage")
    _is_bool(cfg.metrics.enabled, "metrics.enabled")
    _is_bool(cfg.metrics.clippy, "metrics.clippy")
    _check(_is_int(cfg.metrics.timeout) and cfg.metrics.timeout > 0, "metrics.timeout: expected positive seconds")
    _one_of(cfg.renaming, RENAMINGS, "renaming")
    _check(cfg.renaming == "none", "renaming is not implemented; use none")


def _normalize(cfg: Config) -> None:
    # Order and duplicates in these lists don't matter, so they mustn't change the hash.
    cfg.hints.kinds = sorted(set(cfg.hints.kinds))
    cfg.repair.feedback = sorted(set(cfg.repair.feedback))
    cfg.validation.targets = sorted(set(cfg.validation.targets))
    cfg.validation.support_files = sorted(set(cfg.validation.support_files))
