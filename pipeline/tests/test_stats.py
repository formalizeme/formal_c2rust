import shutil
from collections import Counter
from pathlib import Path

import pytest

from c2r.benchmark import Project
from c2r.config import MAIN_CONFIG, load_config
from c2r.stats import COLUMNS, code_lines, project_row, source_counts

DATA = Path(__file__).parent / "data"

try:
    import clang.cindex as ci
    ci.Index.create()
    HAVE_LIBCLANG = True
except Exception:        # the bindings raise various errors when libclang.so is missing
    HAVE_LIBCLANG = False
needs_libclang = pytest.mark.skipif(not HAVE_LIBCLANG, reason="libclang not available")


def test_code_lines_ignore_comments_and_blank_lines():
    text = ('int a;  // one\n'
            '\n'
            '/* a comment\n'
            '   on two lines */\n'
            'char *s = "/* not a comment */";\n'
            '   /* */   \n'
            "char c = '/';  /* trailing */\n"
            'int b; /* opens\n'
            ' closes */ int d;\n')
    assert code_lines(text) == 5      # a; s; c; b (opens); d (after closes)


def sample_project(tmp_path):
    proj = tmp_path / "sample"
    proj.mkdir()
    shutil.copy(DATA / "stats_sample.c", proj / "sample.c")
    return Project("sample", proj, None)


def totals(counts, attr):
    out = Counter()
    for cnt in getattr(counts, attr).values():
        for (_, k), n in cnt.items():
            out[k] += n
    return out


@needs_libclang
def test_every_kind_is_counted_once(tmp_path):
    counts = source_counts(load_config(MAIN_CONFIG), sample_project(tmp_path))
    assert totals(counts, "decls") == {"ptr_fields": 2, "ptr_globals": 2, "ptr_params": 6, "ptr_locals": 1,
                                       "structs": 2, "unions": 1, "functions": 3}
    assert totals(counts, "ops") == {"arith_subscript": 2, "arith_move_variable": 3, "arith_difference": 1,
                                     "arith_offset": 1, "arith_move_field": 1, "arith_move_global": 1,
                                     "arith_move_indirect": 1}


@needs_libclang
def test_project_row(tmp_path):
    project = sample_project(tmp_path)
    split = [{"pointer": "p", "base": "p_base", "index": "p_idx", "elem_size": 1},
             {"pointer": "$128", "base": "p_base", "index": "t128_idx", "elem_size": 1}]
    status = {"status": "accepted", "units": [
        {"path": "sample.c", "kind": "library", "accepted": True,
         "split": [{"name": "count", "split": split, "cached": []},
                   {"name": "advance", "split": [],
                    "cached": [{"location": "(*b).pos", "base": "b_pos_base", "index": "b_pos_idx",
                                "elem_size": 1}]}]}]}
    row = project_row(load_config(MAIN_CONFIG), project, status)
    assert list(row) == [c for c, _ in COLUMNS]
    assert row["c_files"] == row["c_files_refactored"] == 1
    assert (row["structs"], row["unions"], row["functions"]) == (2, 1, 3)
    assert row["pointers"] == 11 and row["pointer_arith"] == 10 == row["pointer_arith_in_refactored"]
    assert row["arith_in_macro_uses"] == 1                      # NEXT(p)
    assert (row["refactored_variables"], row["refactored_variables_source"], row["refactored_memory"],
            row["refactored"], row["functions_refactored"]) == (2, 1, 1, 3, 2)
    assert row["loc"] == code_lines((DATA / "stats_sample.c").read_text())
    # Without stage 1, the refactoring columns are empty.
    assert project_row(load_config(MAIN_CONFIG), project, None)["refactored"] == ""


@needs_libclang
def test_header_functions_count_once(tmp_path):
    proj = tmp_path / "lib"
    proj.mkdir()
    (proj / "walk.h").write_text("static inline int walk(const char *p) { int n = 0; while (*p++) n++; return n; }\n")
    for t in ("test1.c", "test2.c"):
        (proj / t).write_text('#include "walk.h"\nint main(void) { const char *s = "ab"; s++; return walk(s); }\n')
    split = lambda name: {"name": name, "split": [{"pointer": "p" if name == "walk" else "s", "base": "b",
                                                  "index": "i", "elem_size": 1}], "cached": []}
    status = {"status": "accepted", "units": [
        {"path": t, "kind": "test", "accepted": True, "split": [split("walk"), split("main")]}
        for t in ("test1.c", "test2.c")]}
    row = project_row(load_config(MAIN_CONFIG), Project("lib", proj, None), status)
    assert row["functions"] == 3                     # walk once; each test's main
    assert row["refactored_variables"] == 3          # walk's p once; each test's main has its own s
    assert row["functions_refactored"] == 3


@needs_libclang
def test_moving_and_compared_pointers(tmp_path):
    proj = tmp_path / "walk"
    proj.mkdir()
    (proj / "walk.c").write_text("""\
#include <stddef.h>
struct r { const char *pos; const char *end; };
const char *g;
size_t len(const char *s) {               /* s: compared (p - s) */
    const char *p = s;                    /* a copy: not moving by itself */
    while (*p) p++;                       /* p: moving */
    return p - s;
}
int scan(const char *s, size_t n, struct r *rd, const char **pp, struct r *other) {
    const char *end = s + n;              /* one element, not moving; compared below */
    const char *q = &s[1];                /* one element, not moving, never compared: not counted */
    const char *t;
    {
        const char *end = q + 1;          /* shadows end (clightgen: end__1); not counted */
        t = end - 1;                      /* not moving; compared below */
    }
    if (s == NULL || q != 0) return 0;    /* null checks: not comparisons */
    g++;                                  /* g: a moving global */
    rd->pos++;                            /* the member pos: moving */
    other->pos += 2;                      /* the same member */
    (*pp)++;                              /* reached through pp: moving */
    return (rd->end > s) + (t < end);     /* the member end, s, t and end: compared */
}
""")
    status = {"status": "accepted", "units": [
        {"path": "walk.c", "kind": "library", "accepted": True, "split": [
            {"name": "len", "split": [{"pointer": "s"}, {"pointer": "p"}, {"pointer": "$128"}], "cached": []},
            {"name": "scan", "split": [{"pointer": "end"}, {"pointer": "end__1"}, {"pointer": "t"}],
             "cached": []}]}]}
    row = project_row(load_config(MAIN_CONFIG), Project("walk", proj, None), status)
    moving = {c: row[f"moving_{c}"] for c in ("pointers", "variables", "globals", "fields", "indirect", "refactored")}
    compared = {c: row[f"compared_{c}"] for c in ("pointers", "variables", "globals", "fields", "indirect",
                                                  "refactored")}
    # moving: len's p, g, the member pos, *pp. p was split.
    assert moving == {"pointers": 4, "variables": 1, "globals": 1, "fields": 1, "indirect": 1, "refactored": 1}
    # compared: len's s; scan's s, t, end; the member end. len's s, t and end were split.
    assert compared == {"pointers": 5, "variables": 4, "globals": 0, "fields": 1, "indirect": 0, "refactored": 3}
