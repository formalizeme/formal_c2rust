import os
import shutil
import subprocess
from dataclasses import replace
from pathlib import Path

import pytest

from c2r.benchmark import Project
from c2r.config import MAIN_CONFIG, REPO_ROOT, RewritesConfig, load_config
from c2r.equiv import EQUAL, check_project
from c2r.refactor import run_project
from c2r.rewrite import (COMPAT_HEADER, apply_edits, apply_rewrites, case_range_edits, empty_initializer_edits,
                         label_edits, literal_edits, tokenize)
from c2r.tools import clang_resource_include

DATA = Path(__file__).parent / "data"
needs_gcc = pytest.mark.skipif(shutil.which("gcc") is None, reason="gcc missing")
needs_tools = pytest.mark.skipif(
    not os.access(REPO_ROOT / "CompCert" / "ptridxgen", os.X_OK) or shutil.which("gcc") is None,
    reason="ptridxgen or gcc missing")


def rewrite(text: str, find) -> str:
    return apply_edits(text, find(tokenize(text)))


def literals(text: str, **opts) -> str:
    return apply_edits(text, literal_edits(tokenize(text), RewritesConfig(**opts))[0])


def clang_args() -> list[str]:
    inc = clang_resource_include("clang")
    return ["-std=gnu17", *(["-isystem", str(inc)] if inc else [])]


# --- tokens and edits ----------------------------------------------------------

def test_tokenize_skips_comments_and_keeps_strings_whole():
    toks = tokenize('x = "a /* b */ c"; // 0b11\n/* case 1 ... 2: */ y = \'\\n\';')
    assert [t.text for t in toks] == ["x", "=", '"a /* b */ c"', ";", "y", "=", "'\\n'", ";"]


def test_tokenize_numbers_with_exponents():
    assert [t.text for t in tokenize("1e-5 + 0x1p+3 - 2.5f")] == ["1e-5", "+", "0x1p+3", "-", "2.5f"]


def test_apply_edits_prefers_the_inner_of_overlapping_edits():
    assert apply_edits("abcdef", [(1, 5, "X"), (2, 3, "Y")]) == "abYdef"
    assert apply_edits("abc", [(1, 1, "+"), (3, 3, ";")]) == "a+bc;"


# --- each rewrite --------------------------------------------------------------

def test_literals():
    assert literals("int m = 0b1010u | 0B1;") == "int m = 0xau | 0x1;"
    assert literals("double g = 9.81d, h = 1e3D, k = .5d;") == "double g = 9.81, h = 1e3, k = .5;"
    assert literals("x = 0x1d + 12;") == "x = 0x1d + 12;"           # a hex digit, not a suffix
    big = "u = 14695981039346656037;"
    assert literals(big) == big                                      # large_literals is off by default
    assert literals(big, large_literals=True) == "u = 14695981039346656037ULL;"


def test_labels_at_block_end():
    assert rewrite("{ default: }", label_edits) == "{ default: ; }"
    assert rewrite("{ out: } x ? a : b;", label_edits) == "{ out: ; } x ? a : b;"
    assert rewrite("{ out: return; }", label_edits) == "{ out: return; }"


def test_case_ranges():
    assert rewrite("case 1 ... 3: f();", case_range_edits) == "case 1: case 2: case 3: f();"
    assert rewrite("case 'a' ... 'c':", case_range_edits) == "case 'a': case 'b': case 'c':"
    assert rewrite("case -2 ... 0x0:", case_range_edits) == "case -2: case -1: case 0:"
    for unchanged in ("case N ... M:", "case 0 ... 100000:", "case 3 ... 1:", "f(a, ...);"):
        assert rewrite(unchanged, case_range_edits) == unchanged


def test_empty_initializers():
    assert rewrite("struct s x = {};", empty_initializer_edits) == "struct s x = {0};"
    assert rewrite("y = (struct s){};", empty_initializer_edits) == "y = (struct s){0};"
    assert rewrite("return (T){};", empty_initializer_edits) == "return (T){0};"
    assert rewrite("int g[2][2] = { {}, {1, 2} };", empty_initializer_edits) == "int g[2][2] = { {0}, {1, 2} };"
    for unchanged in ("void f(void) {}", "if (x) {}", "while ((p = q)) {}", "else {}", "do {} while (0);",
                      "int (*get(void))(int) {}"):
        assert rewrite(unchanged, empty_initializer_edits) == unchanged


def test_rewrites_can_be_turned_off(tmp_path):
    src = tmp_path / "x.c"
    text = "int f(int c) { switch (c) { case 1 ... 2: return 0b1; default: } return 0; }\n"
    src.write_text(text)
    off = RewritesConfig(**{name: False for name in RewritesConfig.__dataclass_fields__})
    assert apply_rewrites(off, tmp_path, [src], [src], clang_args()) == ({}, [])
    assert src.read_text() == text


def test_builtins_use_the_compat_header(tmp_path):
    src = tmp_path / "x.c"
    src.write_text("int f(unsigned x) { return __builtin_popcount(x); }\n")
    applied, flags = apply_rewrites(RewritesConfig(), tmp_path, [src], [src], clang_args())
    assert applied == {"x.c": {"gnu_builtins": 1}}
    assert flags == ["-include", COMPAT_HEADER] and (tmp_path / COMPAT_HEADER).exists()
    assert "__builtin_popcount" in src.read_text()          # the file itself is unchanged


def test_void_pointer_arithmetic(tmp_path):
    src = tmp_path / "x.c"
    src.write_text("void *f(void *p, const void *q, int n) {\n"
                   "    p += n; p++; long d = q - p; (void)d;\n"
                   "    return 1 + (p + n);\n"
                   "}\n"
                   "char *g(char *s) { return s + 1; }\n")
    applied, _ = apply_rewrites(RewritesConfig(), tmp_path, [src], [src], clang_args())
    assert applied == {"x.c": {"void_pointer_arithmetic": 5}}
    text = src.read_text()
    assert "(p = (void *)((char *)(p) + (n)));" in text
    assert "(p = (void *)((char *)(p) + 1));" in text
    assert "((char *)(q) - (char *)(p))" in text
    assert "return ((void *)((1) + (char *)((((void *)((char *)(p) + (n)))))));" in text  # nested: two rounds
    assert "return s + 1;" in text                                                    # char * is untouched


def test_void_pointer_arithmetic_in_a_macro_is_left_alone(tmp_path):
    src = tmp_path / "x.c"
    text = "#define AT(p, n) ((p) + (n))\nvoid *f(void *p) { return AT(p, 4); }\n"
    src.write_text(text)
    apply_rewrites(RewritesConfig(), tmp_path, [src], [src], clang_args())
    assert src.read_text() == text


# --- meaning ------------------------------------------------------------------

@needs_gcc
def test_rewritten_program_is_iso_c_with_the_same_output(tmp_path):
    orig, new = tmp_path / "orig", tmp_path / "new"
    for d in (orig, new):
        d.mkdir()
        shutil.copy(DATA / "extensions.c", d)
    applied, flags = apply_rewrites(RewritesConfig(), new, [new / "extensions.c"], [new / "extensions.c"],
                                    clang_args())
    assert set(applied["extensions.c"]) == {"binary_literals", "double_suffix", "labels_at_block_end",
                                            "case_ranges", "empty_initializers", "gnu_builtins",
                                            "void_pointer_arithmetic"}
    subprocess.run(["gcc", "-w", "-std=gnu17", "-o", "prog", "extensions.c"], cwd=orig, check=True)
    subprocess.run(["gcc", "-std=c11", "-pedantic-errors", *flags, "-o", "prog", "extensions.c"],
                   cwd=new, check=True)
    run = lambda d: subprocess.run(["./prog"], cwd=d, capture_output=True, text=True, check=True).stdout
    assert run(orig) == run(new)


@needs_tools
def test_compcert_accepts_the_rewritten_program_and_it_behaves_like_the_original(tmp_path):
    proj = tmp_path / "ext"
    proj.mkdir()
    shutil.copy(DATA / "extensions.c", proj)
    cfg = load_config(MAIN_CONFIG)
    record = run_project(cfg, Project("ext", proj, None), objects=True)
    [unit] = record.units
    assert record.status == "accepted", unit.errors
    assert unit.source == (DATA / "extensions.c").read_text()          # the original text is kept
    assert unit.rewrites["void_pointer_arithmetic"] == 5
    [check] = check_project(cfg, record)
    assert check.outcome == EQUAL, check.detail
    assert check.front_end == "same behavior"                           # gcc on the untouched original


@needs_tools
def test_without_rewrites_compcert_rejects_the_program(tmp_path):
    proj = tmp_path / "ext"
    proj.mkdir()
    shutil.copy(DATA / "extensions.c", proj)
    cfg = load_config(MAIN_CONFIG)
    cfg = replace(cfg, rewrites=RewritesConfig(**{name: False for name in RewritesConfig.__dataclass_fields__}))
    record = run_project(cfg, Project("ext", proj, None))
    assert record.status == "rejected" and record.rewrites == {}
