import pytest

from c2r.config import MAIN_CONFIG, ConfigError, experiment_hash, load_config


def test_main_config_loads():
    cfg = load_config(MAIN_CONFIG)
    assert cfg.experiment == "E2"
    assert cfg.input.representation == "clight_pass"
    assert len(experiment_hash(cfg)) == 12


def test_overrides_parse_yaml_values():
    cfg = load_config(MAIN_CONFIG, ["input.representation=clight", "hints.enabled=false",
                                    "repair.max_retries=0", "hints.kinds=[array]"])
    assert cfg.input.representation == "clight"
    assert cfg.hints.enabled is False
    assert cfg.repair.max_retries == 0
    assert cfg.hints.kinds == ["array"]


def test_hash_tracks_experiment_fields_only():
    base = experiment_hash(load_config(MAIN_CONFIG))
    assert experiment_hash(load_config(MAIN_CONFIG, ["input.representation=clight"])) != base
    assert experiment_hash(load_config(MAIN_CONFIG, ["seeds=[7]", "projects=all",
                                                     "tools.cargo=/opt/cargo"])) == base


def test_list_order_does_not_change_hash():
    a = load_config(MAIN_CONFIG, ["hints.kinds=[array, ownership]"])
    b = load_config(MAIN_CONFIG, ["hints.kinds=[ownership, array, array]"])
    assert experiment_hash(a) == experiment_hash(b)


@pytest.mark.parametrize("override", [
    "input.reprsentation=clight",      # typo in a key
    "input.representation=assembly",   # value outside the allowed set
    "hints.enabled=yes please",        # not a boolean
    "seeds=[]",
    "model.temperature=5",
    "hints.kinds=[array, vibes]",
])
def test_invalid_configs_are_rejected(override):
    with pytest.raises(ConfigError):
        load_config(MAIN_CONFIG, [override])


def test_override_needs_key_and_value():
    with pytest.raises(ConfigError):
        load_config(MAIN_CONFIG, ["input.representation"])
