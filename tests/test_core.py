import json
from pathlib import Path

import numpy as np
import pandas as pd

import insacermo_memguard as memguard


def healthy_asymmetric_convergence(n=24):
    x = np.linspace(0.0, 1.0, n)
    train = 0.90 * np.exp(-5.0 * x) + 0.02
    val = 1.00 * np.exp(-3.0 * x) + 0.10
    return pd.DataFrame({"t": np.arange(1, n + 1) * 100, "train": train, "val": val})


def strong_overfit(n=24):
    x = np.linspace(0.0, 1.0, n)
    train = 0.90 * np.exp(-4.5 * x) + 0.02
    val = 0.95 * np.exp(-4.0 * x) + 0.12
    turn = 10
    val[turn:] += np.linspace(0.0, 0.45, n - turn)
    return pd.DataFrame({"t": np.arange(1, n + 1) * 100, "train": train, "val": val})


def moderate_overfit(n=24):
    x = np.linspace(0.0, 1.0, n)
    train = 0.90 * np.exp(-8.0 * x) + 0.02
    val = 0.95 * np.exp(-4.0 * x) + 0.12
    turn = 12
    val[turn:] += np.linspace(0.0, 0.18, n - turn)
    return pd.DataFrame({"t": np.arange(1, n + 1) * 50, "train": train, "val": val})


def noisy_plateau(seed=42, n=80, sigma=0.015):
    rng = np.random.default_rng(seed)
    x = np.linspace(0.0, 1.0, n)
    train = 0.90 * np.exp(-12.0 * x) + 0.02
    val = 0.30 + rng.normal(0.0, sigma, n)
    return pd.DataFrame({"t": np.arange(1, n + 1) * 50, "train": train, "val": val})


def structural_gap(n=40):
    x = np.linspace(0.0, 1.0, n)
    train = 0.55 * np.exp(-5.0 * x) + 0.02
    val = 0.55 * np.exp(-5.0 * x) + 0.28
    return pd.DataFrame({"t": np.arange(1, n + 1) * 50, "train": train, "val": val})


def single_late_spike(n=30):
    x = np.linspace(0.0, 1.0, n)
    train = 0.80 * np.exp(-5.0 * x) + 0.02
    val = 0.90 * np.exp(-4.0 * x) + 0.10
    val[-1] += 0.20
    return pd.DataFrame({"t": np.arange(1, n + 1) * 50, "train": train, "val": val})


def test_healthy_widening_gap_is_not_false_positive():
    report = memguard.analyze(healthy_asymmetric_convergence())
    assert report["recommended_action"] == "HEALTHY"
    assert report["risk_reason"] == "VALIDATION_STILL_IMPROVING"
    assert report["stop_t"] is None


def test_strong_overfit_triggers_noise_aware_stop():
    report = memguard.analyze(strong_overfit(), total_steps_scheduled=3000)
    assert report["recommended_action"] == "EARLY_STOP"
    assert report["risk_reason"] == "NOISE_AWARE_CONFIRMED_DEGRADATION"
    assert report["stop_t"] is not None
    assert report["compute_saved_pct"] is not None
    assert report["early_warn_t"] <= report["stop_t"]


def test_moderate_overfit_remains_detectable():
    report = memguard.analyze(moderate_overfit(), total_steps_scheduled=1600)
    assert report["recommended_action"] == "EARLY_STOP"
    assert report["early_warn_t"] <= report["stop_t"]


def test_noisy_plateau_does_not_early_stop():
    report = memguard.analyze(noisy_plateau(seed=42))
    assert report["recommended_action"] != "EARLY_STOP"
    assert report["stop_t"] is None
    assert report["risk_reason"] in {
        "NOISE_COMPATIBLE_PLATEAU",
        "VALIDATION_STILL_IMPROVING",
        "GAP_WIDENING_WITHOUT_NOISE_AWARE_CONFIRMATION",
    }


def test_noisy_plateau_monte_carlo_false_stop_rate_is_bounded():
    stops = 0
    n_trials = 100
    for seed in range(n_trials):
        report = memguard.analyze(noisy_plateau(seed=seed))
        stops += report["recommended_action"] == "EARLY_STOP"
    # A regression guard, not a formal performance claim.
    assert stops <= 2


def test_structural_large_gap_is_healthy():
    report = memguard.analyze(structural_gap())
    assert report["recommended_action"] == "HEALTHY"
    assert report["stop_t"] is None


def test_single_late_spike_does_not_stop():
    report = memguard.analyze(single_late_spike())
    assert report["recommended_action"] != "EARLY_STOP"
    assert report["stop_t"] is None


def test_hf_merge_asof_keeps_all_eval_points(tmp_path: Path):
    history = []
    # Train every 100 steps, eval every 25 steps after a first train point.
    for step in range(100, 1101, 100):
        history.append({"step": step, "loss": 1.0 / (1.0 + step / 200.0)})
    eval_steps = list(range(125, 1101, 25))
    for step in eval_steps:
        history.append({"step": step, "eval_loss": 1.1 / (1.0 + step / 250.0)})
    path = tmp_path / "trainer_state.json"
    path.write_text(json.dumps({"log_history": history}), encoding="utf-8")
    frame = memguard.load(path)
    assert len(frame) == len(eval_steps)
    assert frame["train"].notna().all()


def test_insufficient_data():
    frame = healthy_asymmetric_convergence(5)
    report = memguard.analyze(frame)
    assert report["recommended_action"] == "INSUFFICIENT_DATA"


def test_csv_loader():
    from io import StringIO

    text = "step,train_loss,eval_loss\n1,1.0,1.1\n2,0.9,1.0\n"
    frame = memguard.load(StringIO(text))
    assert list(frame.columns) == ["t", "train", "val"]
