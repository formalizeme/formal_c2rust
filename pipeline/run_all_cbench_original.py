#!/usr/bin/env python3
"""Run every CBench subject using original C, without CompCert refactoring.

From the repository root:
    uv run python pipeline/run_all_cbench_original.py --jobs 4

Uses the same model, seed, translation, validation and Rust post-refactoring
settings as run_all_cbench.py. Outputs and resumable checkpoints are separate:
    runs/all_original_post_refactored
"""

from run_all_cbench import ROOT, main


if __name__ == "__main__":
    raise SystemExit(main(output=ROOT / "runs/all_original_post_refactored",
                          representation="original_c", description=__doc__))
