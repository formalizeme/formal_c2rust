import pytest

from c2r.benchmark import canonical_name, discover, select
from c2r.config import REPO_ROOT

C_ROOT, RUST_ROOT = REPO_ROOT / "CBench", REPO_ROOT / "RBench"
needs_benchmark = pytest.mark.skipif(not (C_ROOT.is_dir() and RUST_ROOT.is_dir()),
                                     reason="CBench/RBench not present")


@pytest.mark.parametrize("c_name, rust_name", [
    ("amp", "amp"),
    ("btree-map", "btree_map"),
    ("Genetic-neural-network-for-simple-control", "Genetic_neural_network_for_simple_control"),
    ("2DPartInt", "proj_2DPartInt"),
    ("42-Kocaeli-Printf", "proj_42_Kocaeli_Printf"),
])
def test_canonical_names_pair_up(c_name, rust_name):
    assert canonical_name(c_name) == canonical_name(rust_name)


@needs_benchmark
def test_every_project_has_a_rust_crate():
    projects = discover(C_ROOT, RUST_ROOT)
    assert len(projects) == 100
    assert all(p.rust_dir is not None for p in projects)


@needs_benchmark
def test_amp_layout():
    [amp] = select(discover(C_ROOT, RUST_ROOT), ["amp"])
    rel = lambda paths, root: [str(p.relative_to(root)) for p in paths]
    assert rel(amp.c_sources, amp.c_dir) == ["src/amp.c"]
    assert rel(amp.c_tests, amp.c_dir) == ["tests/test.c"]
    assert rel(amp.headers, amp.c_dir) == ["src/amp.h"]
    assert rel(amp.interfaces, amp.rust_dir) == ["src/interfaces/amp.rs"]
    assert rel(amp.rust_tests, amp.rust_dir) == ["src/bin/test.rs"]


@needs_benchmark
@pytest.mark.parametrize("project, rel, expected", [
    ("fslib", "src/shortest.c", False),          # "test" inside a word, not a test
    ("mdb", "testmdb.c", True),
    ("satc", "satc-test.c", True),
    ("libm17", "unit_tests/unit_tests.c", True),
])
def test_test_file_heuristic(project, rel, expected):
    [p] = select(discover(C_ROOT, RUST_ROOT), [project])
    assert p.is_test(p.c_dir / rel) is expected


@needs_benchmark
def test_cmake_artifacts_are_skipped():
    for p in discover(C_ROOT, RUST_ROOT):
        assert not any("CMakeFiles" in str(f) for f in p.c_sources + p.c_tests)


@needs_benchmark
def test_unknown_project_is_an_error():
    with pytest.raises(KeyError):
        select(discover(C_ROOT, RUST_ROOT), ["no-such-project"])
