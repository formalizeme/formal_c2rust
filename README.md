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
