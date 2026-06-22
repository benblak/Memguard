"""Noise-aware conservative overfitting guard.

MemGuard treats the train/eval gap as a supporting signal only.  Automatic
stopping requires a persistent post-best validation degradation that is large
relative to the validation series' own noise and accompanied by a sustained
positive trend.  This avoids two common false positives:

1. train loss falls faster while validation loss is still improving;
2. a noisy validation plateau returns to its mean after an accidental minimum.
"""

from __future__ import annotations

import json
import math
import os
from typing import IO, Any

import numpy as np
import pandas as pd

CFG: dict[str, Any] = {
    "EMA_ALPHA": 0.35,
    "W_SLOPE": 4,
    "SLOPE_SCALE": 0.03,
    "GAP_MIN": 0.10,
    "MEM_WARN": 0.70,
    "MEM_ALERT": 0.90,
    "MIN_POINTS": 8,
    "PATIENCE": 3,
    # Validation-specific safeguards.
    "VAL_SMOOTH_WIN": 3,
    "VAL_TREND_WIN": 6,
    "VAL_TOL_REL": 1e-3,
    "VAL_TOL_ABS": 1e-8,
    "STOP_MIN_REL_DEGRADATION": 5e-3,
    "VAL_NOISE_MULT": 3.0,
    "VAL_TREND_Z_MIN": 2.0,
    "VAL_SHIFT_Z_MIN": 2.0,
    "VAL_CONFIRM_WINDOWS": 3,
    "PRE_WIN": 5,
    "POST_WIN": 10,
}


def _sigmoid(z: float) -> float:
    return 1.0 / (1.0 + math.exp(-max(-50.0, min(50.0, float(z)))))


def _pick_col(cols, candidates):
    cols_l = {str(c).lower(): c for c in cols}
    for candidate in candidates:
        if candidate in cols_l:
            return cols_l[candidate]
    for candidate in candidates:
        for col in cols:
            if candidate in str(col).lower():
                return col
    return None


def _ema(values: np.ndarray, alpha: float) -> np.ndarray:
    out: list[float] = []
    for i, value in enumerate(values):
        out.append(float(value) if i == 0 else alpha * float(value) + (1.0 - alpha) * out[-1])
    return np.asarray(out, dtype=float)


def _rolling_median(values: np.ndarray, window: int) -> np.ndarray:
    """Trailing rolling median: robust to isolated validation spikes."""
    return (
        pd.Series(np.asarray(values, dtype=float))
        .rolling(max(1, int(window)), min_periods=1)
        .median()
        .to_numpy(dtype=float)
    )


def _mem_score(gap_s: np.ndarray, window: int, scale: float) -> np.ndarray:
    mem = np.zeros(len(gap_s), dtype=float)
    for i in range(window, len(gap_s)):
        recent = gap_s[i - window + 1 : i + 1]
        slope = (recent[-1] - recent[0]) / max(1, window - 1)
        mem[i] = _sigmoid(slope / (scale + 1e-12))
    return mem


def _slope_stats(values: np.ndarray, window: int) -> tuple[float, float]:
    """Return OLS slope and a noise-normalized slope score.

    The score resembles a t statistic but is used only as a deterministic guard,
    not as a formal p-value (overlapping sequential windows violate independence).
    """
    w = min(max(3, int(window)), len(values))
    if w < 3:
        return 0.0, 0.0
    y = np.asarray(values[-w:], dtype=float)
    x = np.arange(w, dtype=float)
    x_centered = x - x.mean()
    y_centered = y - y.mean()
    sxx = float(np.dot(x_centered, x_centered))
    if sxx <= 0:
        return 0.0, 0.0
    slope = float(np.dot(x_centered, y_centered) / sxx)
    fitted = y.mean() + slope * x_centered
    residual = y - fitted
    residual_var = float(np.dot(residual, residual) / max(1, w - 2))
    slope_se = math.sqrt(max(residual_var, 1e-18) / sxx)
    score = float(slope / slope_se) if slope_se > 0 else 0.0
    return slope, score


def _robust_noise_sigma(values: np.ndarray) -> float:
    """Estimate point noise from second differences using MAD.

    Second differences remove a local linear trend.  For iid Gaussian point
    noise with standard deviation sigma, second differences have std sqrt(6)*sigma.
    """
    values = np.asarray(values, dtype=float)
    d2 = np.diff(values, n=2)
    if len(d2) < 3:
        return 0.0
    median = float(np.median(d2))
    mad = float(np.median(np.abs(d2 - median)))
    if mad > 0:
        sigma_d2 = mad / 0.6744897501960817
    else:
        sigma_d2 = float(np.std(d2, ddof=1)) if len(d2) > 1 else 0.0
    return max(0.0, sigma_d2 / math.sqrt(6.0))


def _mean_shift_score(values: np.ndarray, window: int, noise_sigma: float) -> float:
    """Compare two adjacent half-windows, normalized by estimated point noise."""
    w = min(max(4, int(window)), len(values))
    half = max(2, w // 2)
    if len(values) < 2 * half:
        return 0.0
    previous = np.asarray(values[-2 * half : -half], dtype=float)
    current = np.asarray(values[-half:], dtype=float)
    shift = float(current.mean() - previous.mean())
    standard_error = max(float(noise_sigma), 1e-12) * math.sqrt(2.0 / half)
    return shift / standard_error


def _tolerance(reference: float, cfg: dict[str, Any]) -> float:
    return max(float(cfg["VAL_TOL_ABS"]), abs(float(reference)) * float(cfg["VAL_TOL_REL"]))


def load(path: str | os.PathLike | IO[str]) -> pd.DataFrame:
    """Load CSV or Hugging Face ``trainer_state.json`` logs.

    Returned columns are ``t``, ``train``, ``val`` and optionally ``lr``.
    Hugging Face eval rows are aligned with the most recent train-loss row at
    or before the eval step via ``merge_asof``.
    """
    if hasattr(path, "read"):
        return _load_csv(path)
    path_str = str(path)
    if path_str.endswith(".json") or os.path.basename(path_str) == "trainer_state.json":
        return _load_hf_json(path_str)
    return _load_csv(path_str)


def _load_csv(path) -> pd.DataFrame:
    df = pd.read_csv(path)
    if df.empty:
        raise ValueError("Empty file.")

    t_col = _pick_col(df.columns, ["step", "global_step", "iteration", "iter", "epoch"])
    train_col = _pick_col(df.columns, ["train_loss", "loss_train", "training_loss", "train", "loss"])
    val_col = _pick_col(df.columns, ["eval_loss", "val_loss", "validation_loss", "eval", "valid"])
    lr_col = _pick_col(df.columns, ["learning_rate", "lr"])

    if t_col is None or train_col is None or val_col is None:
        raise ValueError(
            f"Required columns not found: step={t_col}, train={train_col}, val={val_col}. "
            f"Available columns: {list(df.columns)}"
        )

    cols = [t_col, train_col, val_col] + ([lr_col] if lr_col else [])
    out = df[cols].copy()
    out.columns = ["t", "train", "val"] + (["lr"] if lr_col else [])
    out = out.dropna(subset=["t", "train", "val"]).sort_values("t").reset_index(drop=True)
    return out


def _load_hf_json(path: str) -> pd.DataFrame:
    with open(path, encoding="utf-8") as handle:
        data = json.load(handle)
    history = pd.DataFrame(data.get("log_history", []))
    if history.empty:
        raise ValueError("trainer_state.json contains no log_history.")
    if "step" not in history or "loss" not in history or "eval_loss" not in history:
        raise ValueError("trainer_state.json must contain step, loss and eval_loss entries.")

    train = history.loc[history["loss"].notna(), ["step", "loss"]].copy()
    evaluation = history.loc[history["eval_loss"].notna(), ["step", "eval_loss"]].copy()
    if train.empty or evaluation.empty:
        raise ValueError("Training or evaluation loss rows are missing.")

    train = train.groupby("step", as_index=False).last().sort_values("step")
    evaluation = evaluation.groupby("step", as_index=False).last().sort_values("step")
    merged = pd.merge_asof(evaluation, train, on="step", direction="backward")
    merged = merged.dropna(subset=["loss", "eval_loss"])
    if merged.empty:
        raise ValueError("Could not align evaluation rows with prior training-loss rows.")

    out = merged.rename(columns={"step": "t", "loss": "train", "eval_loss": "val"})
    if "learning_rate" in history:
        lr = history.loc[history["learning_rate"].notna(), ["step", "learning_rate"]]
        lr = lr.groupby("step", as_index=False).last().sort_values("step")
        out = pd.merge_asof(out.sort_values("t"), lr, left_on="t", right_on="step", direction="backward")
        out = out.drop(columns=["step"], errors="ignore").rename(columns={"learning_rate": "lr"})
    return out.reset_index(drop=True)


def analyze(
    df: pd.DataFrame,
    cfg: dict[str, Any] | None = None,
    total_steps_scheduled: float | None = None,
) -> dict[str, Any]:
    """Analyze an aligned log DataFrame and return a noise-aware verdict."""
    cfg = {**CFG, **(cfg or {})}
    required = {"t", "train", "val"}
    missing = required.difference(df.columns)
    if missing:
        raise ValueError(f"Missing required columns: {sorted(missing)}")

    clean = df.dropna(subset=["t", "train", "val"]).sort_values("t").reset_index(drop=True)
    n = len(clean)
    if n < int(cfg["MIN_POINTS"]):
        return {
            "n_points": n,
            "recommended_action": "INSUFFICIENT_DATA",
            "risk_reason": "INSUFFICIENT_DATA",
            "compute_saved_pct": None,
            "early_warn_t": None,
            "stop_t": None,
        }

    t = clean["t"].astype(float).to_numpy()
    train = clean["train"].astype(float).to_numpy()
    val = clean["val"].astype(float).to_numpy()
    if not (np.isfinite(t).all() and np.isfinite(train).all() and np.isfinite(val).all()):
        raise ValueError("Non-finite values found in t/train/val.")

    w_dyn = max(2, min(int(cfg["W_SLOPE"]), n // 3))
    gap = val - train
    gap_s = _ema(gap, float(cfg["EMA_ALPHA"]))
    mem = _mem_score(gap_s, w_dyn, float(cfg["SLOPE_SCALE"]))

    val_smooth = _rolling_median(val, int(cfg["VAL_SMOOTH_WIN"]))
    best_i = int(np.argmin(val_smooth))
    best_val = float(val_smooth[best_i])
    final_val = float(val[-1])
    final_val_smooth = float(val_smooth[-1])
    base_tol = _tolerance(best_val, cfg)
    noise_sigma = _robust_noise_sigma(val)
    degradation_threshold = max(
        base_tol,
        abs(best_val) * float(cfg["STOP_MIN_REL_DEGRADATION"]),
        noise_sigma * float(cfg["VAL_NOISE_MULT"]),
    )

    recent_val_slope, recent_val_slope_z = _slope_stats(val_smooth, int(cfg["VAL_TREND_WIN"]))
    recent_shift_z = _mean_shift_score(val_smooth, int(cfg["VAL_TREND_WIN"]), noise_sigma)
    latest_is_best = best_i == n - 1 or final_val_smooth <= best_val + base_tol
    validation_still_improving = latest_is_best or (
        recent_val_slope < 0.0 and recent_val_slope_z <= -float(cfg["VAL_TREND_Z_MIN"])
    )
    post_best_points = max(0, n - 1 - best_i)
    relative_degradation = max(0.0, (final_val_smooth - best_val) / max(abs(best_val), 1e-12))

    gap_warning_i = None
    for i in range(w_dyn, n):
        if gap_s[i] > float(cfg["GAP_MIN"]) and mem[i] >= float(cfg["MEM_WARN"]):
            gap_warning_i = i
            break

    # Automatic stopping requires repeated noise-aware evidence.  The loop
    # cannot confirm a stop before the first warning, fixing the v0.2 display
    # inconsistency where stop_t could precede early_warn_t.
    stop_i = None
    candidate_streak = 0
    stop_slope_z = None
    stop_shift_z = None
    stop_noise_sigma = None
    stop_threshold = None

    if gap_warning_i is not None:
        start_i = max(best_i + int(cfg["PATIENCE"]), gap_warning_i)
        for i in range(start_i, n):
            prefix_val = val[: i + 1]
            prefix_smooth = val_smooth[: i + 1]
            sigma_i = _robust_noise_sigma(prefix_val)
            threshold_i = max(
                base_tol,
                abs(best_val) * float(cfg["STOP_MIN_REL_DEGRADATION"]),
                sigma_i * float(cfg["VAL_NOISE_MULT"]),
            )
            recent = prefix_smooth[-min(int(cfg["VAL_TREND_WIN"]), len(prefix_smooth)) :]
            recent_level = float(np.mean(recent))
            degradation_i = recent_level - best_val
            slope_i, slope_z_i = _slope_stats(prefix_smooth, int(cfg["VAL_TREND_WIN"]))
            shift_z_i = _mean_shift_score(prefix_smooth, int(cfg["VAL_TREND_WIN"]), sigma_i)
            patience = int(cfg["PATIENCE"])
            persistent_high = bool(
                i + 1 >= patience
                and np.all(prefix_smooth[-patience:] > best_val + 0.5 * threshold_i)
            )

            candidate = bool(
                degradation_i >= threshold_i
                and slope_i > 0.0
                and slope_z_i >= float(cfg["VAL_TREND_Z_MIN"])
                and shift_z_i >= float(cfg["VAL_SHIFT_Z_MIN"])
                and persistent_high
            )
            candidate_streak = candidate_streak + 1 if candidate else 0

            if candidate_streak >= int(cfg["VAL_CONFIRM_WINDOWS"]):
                stop_i = i
                stop_slope_z = slope_z_i
                stop_shift_z = shift_z_i
                stop_noise_sigma = sigma_i
                stop_threshold = threshold_i
                break

    # GAI remains diagnostic only; it never triggers a stop by itself.
    gai_value = None
    if gap_warning_i is not None:
        pre_start = max(0, gap_warning_i - int(cfg["PRE_WIN"]))
        pre = float(np.mean(gap_s[pre_start:gap_warning_i])) if gap_warning_i > 0 else float(gap_s[0])
        post = float(np.mean(gap_s[gap_warning_i : min(n, gap_warning_i + int(cfg["POST_WIN"]))]))
        if abs(pre) > 0.03 and abs(post) > 1e-12:
            ratio = abs(post / pre)
            if ratio > 0:
                gai_value = round(float(np.clip(abs(math.log(ratio)), 0.0, 3.0)), 4)

    noise_compatible_plateau = bool(
        not validation_still_improving
        and abs(recent_val_slope_z) < float(cfg["VAL_TREND_Z_MIN"])
        and recent_shift_z < float(cfg["VAL_SHIFT_Z_MIN"])
    )

    if stop_i is not None:
        action = "EARLY_STOP"
        reason = "NOISE_AWARE_CONFIRMED_DEGRADATION"
    elif validation_still_improving:
        action = "HEALTHY"
        reason = "VALIDATION_STILL_IMPROVING"
    elif noise_compatible_plateau:
        action = "MONITOR"
        reason = "NOISE_COMPATIBLE_PLATEAU"
    elif gap_warning_i is not None and post_best_points > 0:
        action = "MONITOR_CLOSELY"
        reason = "GAP_WIDENING_WITHOUT_NOISE_AWARE_CONFIRMATION"
    elif gap_warning_i is not None:
        action = "MONITOR"
        reason = "GAP_WIDENING_WITHOUT_CONFIRMED_DEGRADATION"
    else:
        action = "HEALTHY"
        reason = "NO_CONFIRMED_DEGRADATION"

    saved = None
    reference_steps = float(total_steps_scheduled) if total_steps_scheduled else float(t[-1])
    if stop_i is not None and reference_steps > 0:
        saved = round(max(0.0, (reference_steps - float(t[stop_i])) / reference_steps * 100.0), 2)

    return {
        "n_points": n,
        "recommended_action": action,
        "risk_reason": reason,
        "compute_saved_pct": saved,
        "early_warn_t": float(t[gap_warning_i]) if gap_warning_i is not None else None,
        "stop_t": float(t[stop_i]) if stop_i is not None else None,
        "best_val": round(best_val, 8),
        "t_best": float(t[best_i]),
        "final_val": round(final_val, 8),
        "final_val_smoothed": round(final_val_smooth, 8),
        "final_gap": round(float(gap[-1]), 8),
        "final_mem": round(float(mem[-1]), 6),
        "validation_recent_slope": round(recent_val_slope, 8),
        "validation_recent_slope_z": round(recent_val_slope_z, 6),
        "validation_recent_shift_z": round(recent_shift_z, 6),
        "validation_noise_sigma": round(noise_sigma, 8),
        "degradation_threshold": round(degradation_threshold, 8),
        "validation_still_improving": bool(validation_still_improving),
        "noise_compatible_plateau": noise_compatible_plateau,
        "post_best_points": int(post_best_points),
        "relative_degradation": round(relative_degradation, 8),
        "stop_slope_z": round(float(stop_slope_z), 6) if stop_slope_z is not None else None,
        "stop_shift_z": round(float(stop_shift_z), 6) if stop_shift_z is not None else None,
        "stop_noise_sigma": round(float(stop_noise_sigma), 8) if stop_noise_sigma is not None else None,
        "stop_degradation_threshold": round(float(stop_threshold), 8) if stop_threshold is not None else None,
        "gap_acceleration_index": gai_value,
    }


def analyze_file(path: str | os.PathLike | IO[str], total_steps_scheduled: float | None = None, cfg=None):
    return analyze(load(path), cfg=cfg, total_steps_scheduled=total_steps_scheduled)
