"""ptridxgen against clightgen, and the refactored code against the original.

- With -no-pass, ptridxgen must reproduce clightgen's Clight exactly.
- With the pass, the refactored Clight, compiled by gcc, must behave exactly
  like the original C on a driver that exercises every function.
"""

import json
import re
import os
import shutil
from pathlib import Path

import pytest

from c2r.config import REPO_ROOT
from c2r.tools import run

COMPCERT = REPO_ROOT / "CompCert"
DATA = Path(__file__).parent / "data"
PTR_WALK = DATA / "ptr_walk.c"
needs_tools = pytest.mark.skipif(
    not all(os.access(COMPCERT / t, os.X_OK) for t in ("clightgen", "ptridxgen")),
    reason="clightgen/ptridxgen not built")
needs_gcc = pytest.mark.skipif(shutil.which("gcc") is None, reason="gcc not installed")


def clightgen(src, out):
    out.mkdir()
    code, msg = run([str(COMPCERT / "clightgen"), "-dclight", str(src), "-o", str(out / f"{src.stem}.v")],
                    cwd=out)   # -dclight writes into the current directory
    assert code == 0, msg
    return out


def ptridxgen(src, out, *flags):
    out.mkdir()
    code, msg = run([str(COMPCERT / "ptridxgen"), *flags, "-outdir", str(out), str(src)])
    assert code == 0, msg
    return out


@needs_tools
def test_no_pass_matches_clightgen(tmp_path):
    ref = clightgen(PTR_WALK, tmp_path / "clightgen")
    got = ptridxgen(PTR_WALK, tmp_path / "ptridxgen", "-no-pass", "-rocq")
    for name in ("ptr_walk.light.c", "ptr_walk.v"):
        assert (got / name).read_text() == (ref / name).read_text(), name
    facts = json.loads((got / "ptr_walk.ptridx.json").read_text())
    assert facts["refactored"] is False and facts["functions"] == []


@needs_tools
def test_pass_splits_the_moving_pointers(tmp_path):
    got = ptridxgen(PTR_WALK, tmp_path / "out")
    facts = json.loads((got / "ptr_walk.ptridx.json").read_text())
    split = {f["name"]: {s["pointer"] for s in f["split"]} for f in facts["functions"]}
    assert {"out", "start"} <= split["fill"]          # a walk plus a copy of its start
    assert split["count_nonzero"] == {"p"}
    assert {"d", "s"} <= split["copy_bytes"]            # the char * walks ...
    assert not {"dst", "src"} & split["copy_bytes"]     # ... but never the void *
    assert "span" not in split                          # nothing moves
    assert "next_u32" not in split                      # a pointer in memory: left alone (caches are opt-in)
    text = (got / "ptr_walk.light.c").read_text()
    assert "*($out_base + $t128_idx)" in text           # one shared base for the group
    assert "$out_base = $t" not in text                 # ... so no base copies


@needs_tools
@needs_gcc
def test_refactored_code_behaves_like_the_original(tmp_path):
    got = ptridxgen(PTR_WALK, tmp_path / "out")
    outputs = []
    for name, lib in (("original", PTR_WALK), ("refactored", got / "ptr_walk.light.c")):
        exe = tmp_path / name
        code, msg = run(["gcc", "-w", "-o", str(exe), str(lib), str(DATA / "ptr_walk_driver.c")])
        assert code == 0, msg
        code, out = run([str(exe)])
        assert code == 0, out
        outputs.append(out)
    assert outputs[0] == outputs[1]
    assert outputs[0].count("\n") > 50                 # the driver really ran


MEM_WALK = DATA / "mem_walk.c"


def facts_of(out, stem):
    return json.loads((out / f"{stem}.ptridx.json").read_text())


@needs_tools
def test_moving_pointers_in_memory_are_cached(tmp_path):
    got = ptridxgen(MEM_WALK, tmp_path / "out", "-memory")
    facts = facts_of(got, "mem_walk")
    assert facts["pass"] == "temporaries, memory"
    cached = {f["name"]: [c["location"] for c in f["cached"]] for f in facts["functions"]}
    assert cached == {
        "count_lines": ["(*r).pos"], "sum_bytes": ["(*r).pos"], "take_string": ["(*r).pos"],
        "put_char": ["(*w).out"], "put_string": ["(*w).out"], "skip_spaces": ["cursor"],
        "next_int": ["*pp"], "total": ["(*r).pos"], "rewind_and_count": ["(*r).pos"],
    }
    text = (got / "mem_walk.light.c").read_text()
    count_lines = text[text.index("int count_lines(struct reader *$r)\n{"):]
    count_lines = count_lines[:count_lines.index("\n}\n")]
    # Loaded once before the loop, never inside it: the store to the other
    # field (line) cannot overlap pos.
    assert count_lines.count("$r_pos_base = (*$r).pos - $r_pos_idx;") == 1
    assert count_lines.index("$r_pos_base = (*$r).pos") < count_lines.index("while (1)")
    assert "$r_pos_idx = $r_pos_idx + 1LL;\n    (*$r).pos = $r_pos_base + $r_pos_idx;" in count_lines


@needs_tools
def test_cache_is_reloaded_where_memory_may_have_changed(tmp_path):
    got = ptridxgen(MEM_WALK, tmp_path / "out", "-memory")
    text = (got / "mem_walk.light.c").read_text()
    take = text[text.index("unsigned char *take_string(struct reader *$r)\n{"):]
    take = take[:take.index("\n}\n")]
    # read_u32 (no stores) and malloc keep the cache; memcpy does not, and the
    # reload keeps counting from the index (4).
    assert take.count("(*$r).pos - $r_pos_idx_2") == 2
    assert take.index("memcpy(") < take.rindex("(*$r).pos - $r_pos_idx_2")
    assert take.index("malloc(") > take.index("(*$r).pos - $r_pos_idx_2")
    total = text[text.index("int total(struct reader *$rs, int $k)\n{"):]
    # r changes: a different location, whose index restarts.
    assert "$r_idx = $rs_idx + (long long) $i;\n    $r_pos_idx_3 = 0LL;" in total


@needs_tools
@pytest.mark.parametrize("flags", [(), ("-no-memory",)])
def test_pointers_in_memory_are_left_alone_by_default(tmp_path, flags):
    got = ptridxgen(MEM_WALK, tmp_path / "out", *flags)
    facts = facts_of(got, "mem_walk")
    assert facts["pass"] == "temporaries"
    assert all(f["cached"] == [] for f in facts["functions"])
    assert "_base" not in (got / "mem_walk.light.c").read_text().split("int count_lines")[1].split("}\n")[0]


SHARE = DATA / "share.c"


def function_text(text, header):
    body = text[text.index(header + "\n{"):]
    return body[:body.index("\n}\n")]


@needs_tools
def test_liveness_decides_base_sharing(tmp_path):
    got = ptridxgen(SHARE, tmp_path / "out")
    facts = facts_of(got, "share")
    bases = {f["name"]: {s["pointer"]: s["base"] for s in f["split"]} for f in facts["functions"]}
    # Rebased in a loop (and in a goto loop), with the copy dead at the rebase: one base.
    assert len(set(bases["longest"].values())) == 1 and {"line", "s"} <= set(bases["longest"])
    assert len(set(bases["token_lengths"].values())) == 1
    # start is live when p is rebased (and s when w is): no sharing.
    assert bases["field_widths"]["start"] != bases["field_widths"]["p"]
    assert bases["words"]["s"] != bases["words"]["w"]


@needs_tools
def test_label_without_goto_keeps_shared_base(tmp_path):
    # The check tests the members live at every label against planning's sets,
    # so planning must compute them even when no goto uses the label.
    src = tmp_path / "label.c"
    src.write_text("long skip2(char *s) {\n  char *start = s;\n  s++;\nlbl:\n  s++;\n"
                   "  return s - start;\n}\n")
    f, = facts_of(ptridxgen(src, tmp_path / "out"), "label")["functions"]
    assert not f["fallback"]
    assert {s["pointer"] for s in f["split"]} >= {"s", "start"}
    assert len({s["base"] for s in f["split"]}) == 1


@needs_tools
def test_byte_pointer_comparisons_use_indices(tmp_path):
    text = (ptridxgen(SHARE, tmp_path / "out") / "share.light.c").read_text()
    longest = function_text(text, "unsigned long long longest(void)")
    assert re.search(r"\(\$s_idx\w* - \$line_idx\w*\)", longest)          # s - line
    count = function_text(text, "unsigned long long count_char(unsigned char *$buf, unsigned long long $n, "
                                "unsigned char $c)")
    assert re.search(r"! \(\$p_idx\w* != \$end_idx\w*\)", count)            # p != end
    ints = function_text(text, "int count_ints(int *$v, int *$end, int $x)")
    assert "($v_base + $v_idx != $end)" in ints                           # 4-byte elements: pointers


@needs_tools
def test_split_temporaries_are_no_longer_declared(tmp_path):
    text = (ptridxgen(SHARE, tmp_path / "out") / "share.light.c").read_text()
    longest = function_text(text, "unsigned long long longest(void)")
    assert "register unsigned char *$s;" not in longest and "*$line;" not in longest
    assert "$s_base" in longest
