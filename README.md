# Pointer-arithmetic refactoring on CompCert

This is CompCert 3.18 with one added pass in `ptridx/`. The pass rewrites
each pointer that moves into a base and an integer index, on Clight.

| File | Contents |
|---|---|
| `ptridx/PtrIdx.v` | The pass |
| `ptridx/PtrIdxproof.v` | Its proof (forward simulation) |
| `ptridx/PtrIdxFrontend.v` | The proof composed with CompCert's front end (`c_to_refactored_correct`) |
| `ptridx/PtrIdxDriver.ml` | `ptridxgen`, the command-line tool |

## Dependencies

Tested with OCaml 4.14.2, Rocq 9.2.0 and Menhir 20260209, installed with opam.

```sh
opam switch create compcert 4.14.2
eval $(opam env --switch=compcert)
opam install rocq-core.9.2.0 rocq-stdlib.9.2.0 menhir
```

## Build

```sh
./configure -clightgen x86_64-linux     # or aarch64-linux
make -j4
```

`make` checks every proof, CompCert's and the pass's, and builds `ccomp`,
`clightgen` and `ptridxgen`. To check only the pass and what it depends on,
run `make ptridx/PtrIdxFrontend.vo`.

To list the axioms of the main theorem (the standard axioms of CompCert):

```sh
printf 'Require Import PtrIdxFrontend.\nPrint Assumptions c_to_refactored_correct.\n' > ptridx/Assumptions.v
make ptridx/Assumptions.vo
```

## Run

```sh
mkdir -p out
./ptridxgen -outdir out foo.c
```

This writes `out/foo.light.c`, the refactored Clight in CompCert's C-like
syntax, and
`out/foo.ptridx.json`, a summary of what the pass rewrote. `-no-pass` skips
the pass, `-rocq` also writes the program as a Rocq term, and `-help` lists
every option.

# Setup and run Rustine

Run from the repository root. Keep `pipeline/`, `pyproject.toml`, `uv.lock`,
`rust-toolchain.toml`, `CBench/`, `RBench/`, and the modified `CompCert/`.

## Setup

Install **uv, Python 3.12+, rustup, Clang, GCC, and Make**. Refactored-C runs also
need an opam switch named `compcert` with **OCaml 4.14.2, Rocq 9.2, and Menhir**.

```bash
uv sync --locked --no-dev
rustup toolchain install nightly-2025-05-13 -c clippy -c rustfmt
uv run python pipeline/setup_clang_parser.py  # requires apt-get and dpkg-deb
read -rsp 'OpenRouter API key: ' OPENROUTER_API_KEY; echo
export OPENROUTER_API_KEY
```

For refactored-C runs, build CompCert if not already built for this machine:

```bash
eval "$(opam env --switch=compcert)"
(
  set -e
  cd CompCert
  ./configure -clightgen x86_64-linux  # use aarch64-linux on ARM64 Linux
  make depend && make -j3 proof && make extraction
  make -j3 ccomp clightgen ptridxgen
)
```

## Run all subjects

```bash
# Refactor C first, translate, validate, then refactor Rust:
uv run python pipeline/run_all_cbench.py --jobs 4

# Original C input, with the same Rust translation and post-refactoring stages:
uv run python pipeline/run_all_cbench_original.py --jobs 4
```

## Run one subject

```bash
uv run c2r run CBench/amp --rbench RBench/amp --seed 0 -o runs/amp-new \
  --set model.id=deepseek/deepseek-v4-flash-0731 \
  --set model.reasoning_effort=high --set model.max_tokens=384000 \
  --set runner.max_model_calls=2000 --set idiomatic_stage=true
```

Add `--set input.representation=original_c` to skip C refactoring.
