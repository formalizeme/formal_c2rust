import os
import shutil
from pathlib import Path

import pytest

from c2r.benchmark import Project
from c2r.config import MAIN_CONFIG, REPO_ROOT, load_config
from c2r.equiv import EQUAL, check_project
from c2r.refactor import run_project

DATA = Path(__file__).parent / "data"
needs_tools = pytest.mark.skipif(
    not os.access(REPO_ROOT / "CompCert" / "ptridxgen", os.X_OK) or shutil.which("gcc") is None,
    reason="ptridxgen or gcc missing")


@needs_tools
def test_refactored_program_behaves_like_the_original(tmp_path):
    proj = tmp_path / "ptrwalk"
    proj.mkdir()
    shutil.copy(DATA / "ptr_walk.c", proj)
    shutil.copy(DATA / "ptr_walk_driver.c", proj / "main.c")
    record = run_project(load_config(MAIN_CONFIG), Project("ptrwalk", proj, None), objects=True)
    assert record.accepted
    assert all(u.clight_obj and u.refactored_obj for u in record.units)
    [check] = check_project(load_config(MAIN_CONFIG), record)
    assert check.main == "main.c"
    assert check.outcome == EQUAL, check.detail
    assert check.front_end == "same behavior"


@needs_tools
def test_partial_project_links_the_rejected_file_compiled_by_gcc(tmp_path):
    proj = tmp_path / "partial"
    shutil.copytree(DATA / "partial", proj)
    record = run_project(load_config(MAIN_CONFIG), Project("partial", proj, None), objects=True)
    assert record.status == "partial"
    assert {u.path: u.accepted for u in record.units} == {"main.c": True, "sum.c": True, "vla.c": False}
    [check] = check_project(load_config(MAIN_CONFIG), record)
    assert check.main == "main.c"
    assert check.outcome == EQUAL, check.detail
    assert check.front_end == "same behavior"



def project_from(tmp_path, name, files):
    proj = tmp_path / name
    proj.mkdir()
    for src, dst in files:
        shutil.copy(DATA / src, proj / dst)
    return Project(name, proj, None)


@needs_tools
@pytest.mark.parametrize("name, files, overrides", [
    # Caches for pointers in memory are opt-in (refactor.memory_pointers).
    ("memwalk", [("mem_walk.c", "mem_walk.c"), ("mem_walk_driver.c", "main.c")], ["refactor.memory_pointers=true"]),
    ("memalias", [("mem_alias.c", "mem_alias.c")], ["refactor.memory_pointers=true"]),
    ("share", [("share.c", "share.c")], []),
])
def test_rewritten_pointers_keep_behavior(tmp_path, name, files, overrides):
    cfg = load_config(MAIN_CONFIG, overrides)
    record = run_project(cfg, project_from(tmp_path, name, files), objects=True)
    assert record.accepted
    assert sum(len(f["cached"]) + len(f["split"]) for u in record.units if u.facts for f in u.facts["functions"]) >= 9
    [check] = check_project(cfg, record)
    assert check.outcome == EQUAL, check.detail
    assert check.front_end == "same behavior"


@needs_tools
@pytest.mark.parametrize("overrides, pass_name", [
    ([], "temporaries"),                                          # the default: the proved pass
    (["refactor.memory_pointers=true"], "temporaries, memory"),
])
def test_memory_pointers_switch(tmp_path, overrides, pass_name):
    cfg = load_config(MAIN_CONFIG, overrides)
    record = run_project(cfg, project_from(tmp_path, "memwalk", [("mem_walk.c", "mem_walk.c")]))
    [unit] = record.units
    assert unit.facts["pass"] == pass_name
    assert any(f["cached"] for f in unit.facts["functions"]) == (pass_name == "temporaries, memory")


@needs_tools
def test_builds_have_a_fixed_date(tmp_path):
    # A program printing __DATE__/__TIME__ must print the same in every build
    # (recordManager's tests print __TIME__).
    proj = tmp_path / "stamp"
    proj.mkdir()
    shutil.copy(DATA / "ptr_walk.c", proj)
    (proj / "main.c").write_text('#include <stdio.h>\nint main(void) { printf("%s %s\\n", __DATE__, __TIME__); '
                                 'return 0; }\n')
    cfg = load_config(MAIN_CONFIG)
    record = run_project(cfg, Project("stamp", proj, None), objects=True)
    [main] = [u for u in record.units if u.path == "main.c"]
    assert '"Jan  1 1970"' in main.clight and '"00:00:00"' in main.clight
    [check] = check_project(cfg, record)
    assert check.outcome == EQUAL and check.front_end == "same behavior"
