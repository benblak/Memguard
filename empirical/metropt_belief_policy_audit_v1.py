#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import math
import os
import re
import sys
import urllib.request
import zipfile
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.linear_model import LogisticRegression, Ridge
from sklearn.metrics import (
    average_precision_score,
    brier_score_loss,
    mean_squared_error,
    roc_auc_score,
)
from sklearn.mixture import GaussianMixture
from sklearn.preprocessing import OneHotEncoder, StandardScaler

SEED = 20260914
np.random.seed(SEED)

URL = "https://archive.ics.uci.edu/static/public/791/metropt%2B3%2Bdataset.zip"
EXPECTED_SHA256 = "aab991a970e58210de853bb8078ce0e63abb4d9412fdc5c79792dae3d8e1721a"

TRAIN_START = pd.Timestamp("2020-02-01 00:00:00")
TRAIN_END = pd.Timestamp("2020-03-31 23:59:59")
CAL_START = pd.Timestamp("2020-04-01 00:00:00")
CAL_END = pd.Timestamp("2020-05-31 23:59:59")
TEST_START = pd.Timestamp("2020-06-01 00:00:00")
TEST_END = pd.Timestamp("2020-09-01 03:59:50")

FAILURES = [
    (pd.Timestamp("2020-04-18 00:00:00"), pd.Timestamp("2020-04-18 23:59:00"), "F1"),
    (pd.Timestamp("2020-05-29 23:30:00"), pd.Timestamp("2020-05-30 06:00:00"), "F2"),
    (pd.Timestamp("2020-06-05 10:00:00"), pd.Timestamp("2020-06-07 14:30:00"), "F3"),
    (pd.Timestamp("2020-07-15 14:30:00"), pd.Timestamp("2020-07-15 19:00:00"), "F4"),
]

K = 8
BIN = "5min"
EXPECTED_PER_BIN = 30
MIN_COVERAGE = 0.80
FUTURE_STEPS = 6  # 30 minutes at 5-minute bins
WARNING_HOURS = 24
POST_FAILURE_EXCLUDE_HOURS = 12

OUT = Path(os.environ.get("INSACERMO_OUT", "empirical/metropt_results_v1"))
OUT.mkdir(parents=True, exist_ok=True)
DATA_DIR = OUT / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def sha256_file(path: Path, chunk=1024 * 1024) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        while True:
            b = f.read(chunk)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def download_with_retry(url: str, path: Path, tries=5) -> None:
    if path.exists() and sha256_file(path) == EXPECTED_SHA256:
        return
    last = None
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "INSACERMO-MetroPT-Audit/1.0"})
            with urllib.request.urlopen(req, timeout=180) as r, path.open("wb") as f:
                while True:
                    chunk = r.read(1024 * 1024)
                    if not chunk:
                        break
                    f.write(chunk)
            got = sha256_file(path)
            if got != EXPECTED_SHA256:
                raise RuntimeError(f"archive SHA256 mismatch: got {got}")
            return
        except Exception as e:
            last = e
            if path.exists():
                path.unlink()
            import time
            time.sleep(10 * (i + 1))
    raise RuntimeError(f"download failed after {tries} attempts: {last}")


def normalize_name(x: str) -> str:
    x = str(x).strip().lower()
    x = re.sub(r"[^a-z0-9]+", "_", x).strip("_")
    return x


def load_raw() -> tuple[pd.DataFrame, str, Path]:
    zpath = DATA_DIR / "metropt3.zip"
    download_with_retry(URL, zpath)
    digest = sha256_file(zpath)
    with zipfile.ZipFile(zpath) as z:
        csv_names = [n for n in z.namelist() if n.lower().endswith(".csv")]
        if not csv_names:
            raise RuntimeError("No CSV in UCI archive")
        # largest CSV is the telemetry file
        csv_name = max(csv_names, key=lambda n: z.getinfo(n).file_size)
        target = DATA_DIR / Path(csv_name).name
        if not target.exists():
            with z.open(csv_name) as src, target.open("wb") as dst:
                import shutil
                shutil.copyfileobj(src, dst)
    df = pd.read_csv(target, low_memory=False)
    df.columns = [normalize_name(c) for c in df.columns]
    # common UCI saved-index column
    for c in list(df.columns):
        if c.startswith("unnamed") or c in {"index", "id"}:
            if c != "timestamp":
                df = df.drop(columns=c)
    if "timestamp" not in df.columns:
        candidates = [c for c in df.columns if "time" in c or "date" in c]
        if not candidates:
            raise RuntimeError(f"No timestamp column found; columns={df.columns.tolist()}")
        df = df.rename(columns={candidates[0]: "timestamp"})
    df["timestamp"] = pd.to_datetime(df["timestamp"], errors="coerce")
    df = df.dropna(subset=["timestamp"]).sort_values("timestamp").reset_index(drop=True)
    return df, digest, target


def engineer_5min(df: pd.DataFrame) -> tuple[pd.DataFrame, list[str]]:
    numeric_cols = [c for c in df.columns if c != "timestamp" and pd.api.types.is_numeric_dtype(df[c])]
    if len(numeric_cols) < 10:
        # coerce numeric-looking columns if parser inferred objects
        for c in df.columns:
            if c != "timestamp":
                df[c] = pd.to_numeric(df[c], errors="coerce")
        numeric_cols = [c for c in df.columns if c != "timestamp" and pd.api.types.is_numeric_dtype(df[c])]

    known_digital = {
        "comp", "dv_electric", "dv_eletric", "towers", "mpg", "lps",
        "pressure_switch", "oil_level", "caudal_impulses",
    }
    digital = [c for c in numeric_cols if c in known_digital]
    analog = [c for c in numeric_cols if c not in digital]

    work = df[["timestamp"] + numeric_cols].copy()
    work["bin"] = work["timestamp"].dt.floor(BIN)
    g = work.groupby("bin", sort=True)
    counts = g.size().rename("sample_count")

    parts = [counts]
    if analog:
        a = g[analog].agg(["mean", "std", "min", "max"])
        a.columns = [f"{c}_{s}" for c, s in a.columns]
        parts.append(a)
    if digital:
        d = g[digital].mean()
        d.columns = [f"{c}_mean" for c in d.columns]
        parts.append(d)
    feat = pd.concat(parts, axis=1).sort_index()
    feat["coverage"] = feat["sample_count"] / EXPECTED_PER_BIN
    feat = feat[feat["coverage"] >= MIN_COVERAGE].copy()
    feature_cols = [c for c in feat.columns if c not in {"sample_count", "coverage"}]
    feat[feature_cols] = feat[feature_cols].replace([np.inf, -np.inf], np.nan)
    # std may be NaN only in degenerate bins; fill from training-neutral zero variation
    feat[feature_cols] = feat[feature_cols].fillna(0.0)
    return feat, feature_cols


def masks(index: pd.DatetimeIndex):
    train = (index >= TRAIN_START) & (index <= TRAIN_END)
    cal = (index >= CAL_START) & (index <= CAL_END)
    test = (index >= TEST_START) & (index <= TEST_END)
    return train, cal, test


def warning_labels(index: pd.DatetimeIndex) -> tuple[np.ndarray, np.ndarray, list[dict]]:
    y = np.zeros(len(index), dtype=int)
    excluded = np.zeros(len(index), dtype=bool)
    episodes = []
    for start, end, name in FAILURES:
        pre = (index >= start - pd.Timedelta(hours=WARNING_HOURS)) & (index < start)
        y[pre] = 1
        bad = (index >= start) & (index <= end + pd.Timedelta(hours=POST_FAILURE_EXCLUDE_HOURS))
        excluded[bad] = True
        episodes.append({"name": name, "start": str(start), "end": str(end), "pre_count": int(pre.sum())})
    return y, excluded, episodes


def one_hot_modes(modes: np.ndarray, k: int) -> np.ndarray:
    out = np.zeros((len(modes), k), dtype=float)
    out[np.arange(len(modes)), modes.astype(int)] = 1.0
    return out


def entropy_rows(p: np.ndarray) -> np.ndarray:
    q = np.clip(p, 1e-15, 1.0)
    return -(q * np.log(q)).sum(axis=1)


def representations(Xz: np.ndarray, gmm: GaussianMixture, train_mask: np.ndarray):
    post = gmm.predict_proba(Xz)
    mode = post.argmax(axis=1)
    anomaly = -gmm.score_samples(Xz)
    mu = float(anomaly[train_mask].mean())
    sd = float(anomaly[train_mask].std()) or 1.0
    az = (anomaly - mu) / sd
    ent = entropy_rows(post)
    oh = one_hot_modes(mode, K)
    reps = {
        "MAP_ONLY": oh,
        "MAP_SCALAR": np.column_stack([oh, az]),
        "FULL_BELIEF": np.column_stack([post, az, ent]),
        "RAW_SNAPSHOT": Xz,
    }
    return reps, post, mode, anomaly, az, ent


def contiguous_future_target(index: pd.DatetimeIndex, Xz: np.ndarray, steps: int):
    Y = np.full_like(Xz, np.nan, dtype=float)
    valid = np.zeros(len(index), dtype=bool)
    if len(index) <= steps:
        return Y, valid
    expected = pd.Timedelta(minutes=5 * steps)
    delta = index[steps:] - index[:-steps]
    good = np.asarray(delta == expected)
    pos = np.where(good)[0]
    Y[pos] = Xz[pos + steps]
    valid[pos] = True
    return Y, valid


def nmse(y_true: np.ndarray, y_pred: np.ndarray) -> float:
    # Target is standardized on train scale. Mean squared error is therefore already normalized dimensionwise.
    return float(np.mean((y_true - y_pred) ** 2))


def safe_auc(fn, y, p):
    try:
        return float(fn(y, p))
    except Exception:
        return float("nan")


def eval_warning(name: str, X: np.ndarray, y: np.ndarray, excluded: np.ndarray,
                 cal_mask: np.ndarray, test_mask: np.ndarray, index: pd.DatetimeIndex):
    fit = cal_mask & (~excluded)
    hold = test_mask & (~excluded)
    if y[fit].sum() == 0:
        raise RuntimeError("No calibration positives; official failure windows/split mismatch")
    clf = LogisticRegression(
        C=1.0, class_weight="balanced", max_iter=3000, solver="lbfgs", random_state=SEED
    )
    clf.fit(X[fit], y[fit])
    p_cal = clf.predict_proba(X[fit])[:, 1]
    y_cal = y[fit]
    neg_cal = p_cal[y_cal == 0]
    threshold = float(np.quantile(neg_cal, 0.99))

    p = clf.predict_proba(X[hold])[:, 1]
    yh = y[hold]
    ih = index[hold]
    alerts = p >= threshold
    neg = yh == 0
    pos = yh == 1

    episode_details = []
    hits = 0
    for start, end, ep in FAILURES:
        if not (TEST_START <= start <= TEST_END):
            continue
        m = (ih >= start - pd.Timedelta(hours=WARNING_HOURS)) & (ih < start)
        ep_alerts = np.where(m & alerts)[0]
        if len(ep_alerts):
            hits += 1
            earliest_time = ih[ep_alerts[0]]
            lead_h = (start - earliest_time).total_seconds() / 3600.0
            episode_details.append({"episode": ep, "hit": True, "earliest_alert": str(earliest_time), "lead_hours": lead_h})
        else:
            episode_details.append({"episode": ep, "hit": False, "earliest_alert": None, "lead_hours": None})

    metrics = {
        "representation": name,
        "calibration_n": int(fit.sum()),
        "calibration_positive_n": int(y[fit].sum()),
        "threshold_cal_neg_q99": threshold,
        "holdout_n": int(hold.sum()),
        "holdout_positive_n": int(pos.sum()),
        "pr_auc": safe_auc(average_precision_score, yh, p),
        "roc_auc": safe_auc(roc_auc_score, yh, p),
        "brier": float(brier_score_loss(yh, p)),
        "positive_recall_at_threshold": float(alerts[pos].mean()) if pos.any() else float("nan"),
        "negative_alert_burden": float(alerts[neg].mean()) if neg.any() else float("nan"),
        "episode_hits": int(hits),
        "episode_total": int(len(episode_details)),
        "episodes": episode_details,
    }
    return clf, metrics, hold, p


def anomaly_deciles(anomaly: np.ndarray, train_mask: np.ndarray) -> np.ndarray:
    qs = np.quantile(anomaly[train_mask], np.linspace(0.1, 0.9, 9))
    return np.digitize(anomaly, qs, right=False)


def mixed_code_audit(index, mode, anomaly, train_mask, test_valid, y, p_full, p_scalar):
    dec = anomaly_deciles(anomaly, train_mask)
    df = pd.DataFrame({
        "time": index[test_valid],
        "mode": mode[test_valid],
        "decile": dec[test_valid],
        "y": y[test_valid],
        "p_full": p_full,
        "p_scalar": p_scalar,
    })
    grouped = df.groupby(["mode", "decile"])["y"].agg(["min", "max", "count", "sum"])
    mixed_idx = grouped[(grouped["min"] == 0) & (grouped["max"] == 1)].index
    if len(mixed_idx) == 0:
        return {
            "mixed_codes": 0,
            "positive_bins_in_mixed_codes_fraction": 0.0,
            "witness": None,
        }
    key_series = list(zip(df["mode"], df["decile"]))
    is_mixed = np.array([k in mixed_idx for k in key_series])
    pos = df["y"].to_numpy() == 1
    frac = float((is_mixed & pos).sum() / max(1, pos.sum()))

    # deterministic witness: mixed-code pos/neg pair with largest |p_full difference|;
    # ties broken by earliest positive then earliest negative chronology.
    best = None
    for key in sorted(mixed_idx):
        sub = df[(df["mode"] == key[0]) & (df["decile"] == key[1])]
        pp = sub[sub["y"] == 1].sort_values(["p_full", "time"])
        nn = sub[sub["y"] == 0].sort_values(["p_full", "time"])
        if pp.empty or nn.empty:
            continue
        candidates = [
            (pp.iloc[-1], nn.iloc[0]),
            (pp.iloc[0], nn.iloc[-1]),
        ]
        for a, b in candidates:
            diff = abs(float(a.p_full) - float(b.p_full))
            rec = {
                "coarse_mode": int(key[0]),
                "coarse_anomaly_decile": int(key[1]),
                "positive_time": str(a.time),
                "negative_time": str(b.time),
                "positive_full_probability": float(a.p_full),
                "negative_full_probability": float(b.p_full),
                "positive_scalar_probability": float(a.p_scalar),
                "negative_scalar_probability": float(b.p_scalar),
                "full_probability_gap": diff,
                "scalar_probability_gap": abs(float(a.p_scalar) - float(b.p_scalar)),
            }
            tie = (str(a.time), str(b.time))
            if best is None or diff > best[0] + 1e-15 or (abs(diff - best[0]) <= 1e-15 and tie < best[1]):
                best = (diff, tie, rec)
    return {
        "mixed_codes": int(len(mixed_idx)),
        "positive_bins_in_mixed_codes_fraction": frac,
        "witness": best[2] if best else None,
    }


def main():
    print("[1/8] Downloading and verifying official MetroPT-3 archive", flush=True)
    raw, archive_sha, csv_path = load_raw()
    raw_rows = len(raw)
    print(f"raw rows={raw_rows:,}; csv={csv_path}", flush=True)

    print("[2/8] Engineering frozen 5-minute representation", flush=True)
    feat, feature_cols = engineer_5min(raw)
    del raw
    index = pd.DatetimeIndex(feat.index)
    train_mask, cal_mask, test_mask = masks(index)
    if min(train_mask.sum(), cal_mask.sum(), test_mask.sum()) == 0:
        raise RuntimeError("One chronological split is empty")

    X = feat[feature_cols].to_numpy(dtype=float)
    scaler = StandardScaler()
    scaler.fit(X[train_mask])
    Xz = scaler.transform(X)

    print("[3/8] Fitting train-only K=8 diagonal GMM belief proxy", flush=True)
    gmm = GaussianMixture(
        n_components=K, covariance_type="diag", random_state=SEED,
        n_init=3, max_iter=300, reg_covar=1e-6,
    )
    gmm.fit(Xz[train_mask])
    reps, post, mode, anomaly, az, ent = representations(Xz, gmm, train_mask)

    print("[4/8] Test A: 30-minute future-trajectory proxy", flush=True)
    Y, future_valid = contiguous_future_target(index, Xz, FUTURE_STEPS)
    future_metrics = {}
    fit_future = cal_mask & future_valid
    hold_future = test_mask & future_valid
    for name, R in reps.items():
        reg = Ridge(alpha=1.0)
        reg.fit(R[fit_future], Y[fit_future])
        pred = reg.predict(R[hold_future])
        future_metrics[name] = {
            "nmse": nmse(Y[hold_future], pred),
            "n_holdout": int(hold_future.sum()),
        }

    scalar_nmse = future_metrics["MAP_SCALAR"]["nmse"]
    full_nmse = future_metrics["FULL_BELIEF"]["nmse"]
    structural_improvement = (scalar_nmse - full_nmse) / scalar_nmse if scalar_nmse > 0 else float("nan")
    test_a_pass = bool(structural_improvement >= 0.05)

    print("[5/8] Creating official failure-warning labels", flush=True)
    y, excluded, episode_meta = warning_labels(index)

    print("[6/8] Test B: frozen early-warning policy proxy", flush=True)
    warning_results = {}
    clfs = {}
    hold_masks = {}
    hold_probs = {}
    for name, R in reps.items():
        clf, m, hm, hp = eval_warning(name, R, y, excluded, cal_mask, test_mask, index)
        clfs[name] = clf
        warning_results[name] = m
        hold_masks[name] = hm
        hold_probs[name] = hp

    wf = warning_results["FULL_BELIEF"]
    ws = warning_results["MAP_SCALAR"]
    recall_rel = (
        (wf["positive_recall_at_threshold"] - ws["positive_recall_at_threshold"]) /
        max(ws["positive_recall_at_threshold"], 1e-12)
    )
    burden_ok = wf["negative_alert_burden"] <= ws["negative_alert_burden"] + 0.015
    operational_alt = (
        wf["episode_hits"] >= ws["episode_hits"] + 1
        or (recall_rel >= 0.25 and burden_ok)
    )
    test_b_pass = bool(wf["pr_auc"] > ws["pr_auc"] and operational_alt)

    print("[7/8] Test C: deterministic unsafe-merge witness audit", flush=True)
    # all warning models share same holdout validity mask by construction
    hm = hold_masks["FULL_BELIEF"]
    assert np.array_equal(hm, hold_masks["MAP_SCALAR"])
    mixed = mixed_code_audit(
        index, mode, anomaly, train_mask, hm, y,
        hold_probs["FULL_BELIEF"], hold_probs["MAP_SCALAR"],
    )
    test_c_pass = bool(mixed["mixed_codes"] >= 1)

    if test_a_pass and test_b_pass and test_c_pass:
        verdict = "DECISIVE_EMPIRICAL_SUPPORT_V1"
    elif test_a_pass and test_c_pass:
        verdict = "PARTIAL_SUPPORT_V1"
    else:
        verdict = "NO_DECISIVE_SUPPORT_V1"

    results = {
        "schema": "INSACERMO_METROPT_BELIEF_POLICY_REALDATA_AUDIT_V1",
        "seed": SEED,
        "dataset": {
            "doi": "10.24432/C5VW3R",
            "url": URL,
            "expected_archive_sha256": EXPECTED_SHA256,
            "observed_archive_sha256": archive_sha,
            "raw_rows": raw_rows,
            "valid_5min_bins": int(len(feat)),
            "engineered_feature_count": int(len(feature_cols)),
            "train_bins": int(train_mask.sum()),
            "calibration_bins": int(cal_mask.sum()),
            "holdout_bins": int(test_mask.sum()),
        },
        "frozen": {
            "bin": BIN,
            "min_coverage": MIN_COVERAGE,
            "gmm_k": K,
            "future_horizon_minutes": 30,
            "warning_horizon_hours": WARNING_HOURS,
            "negative_alert_quantile": 0.99,
        },
        "test_a_future_trajectory": {
            "representations": future_metrics,
            "full_vs_map_scalar_relative_nmse_reduction": structural_improvement,
            "criterion_pass": test_a_pass,
        },
        "test_b_failure_warning": {
            "representations": warning_results,
            "full_vs_map_scalar_relative_recall_change": recall_rel,
            "burden_constraint_ok": burden_ok,
            "criterion_pass": test_b_pass,
        },
        "test_c_unsafe_merge": {
            **mixed,
            "criterion_pass": test_c_pass,
        },
        "failure_episode_metadata": episode_meta,
        "overall_verdict": verdict,
    }

    (OUT / "METROPT_BELIEF_POLICY_V1_RESULTS.json").write_text(json.dumps(results, indent=2, allow_nan=False), encoding="utf-8")

    # Flat metrics CSV for easy audit.
    rows = []
    for name, m in future_metrics.items():
        rows.append({"test": "A_future_trajectory", "representation": name, "metric": "nmse", "value": m["nmse"]})
    for name, m in warning_results.items():
        for key in ["pr_auc", "roc_auc", "brier", "positive_recall_at_threshold", "negative_alert_burden", "episode_hits"]:
            rows.append({"test": "B_failure_warning", "representation": name, "metric": key, "value": m[key]})
    pd.DataFrame(rows).to_csv(OUT / "METROPT_BELIEF_POLICY_V1_METRICS.csv", index=False)

    # Reproducible holdout score table, compact enough at 5-minute level.
    valid_hold = hm
    hold_df = pd.DataFrame({
        "timestamp": index[valid_hold].astype(str),
        "pre_failure_24h": y[valid_hold],
        "map_mode": mode[valid_hold],
        "anomaly_score": anomaly[valid_hold],
        "belief_entropy": ent[valid_hold],
        "p_map_scalar": hold_probs["MAP_SCALAR"],
        "p_full_belief": hold_probs["FULL_BELIEF"],
    })
    hold_df.to_csv(OUT / "METROPT_BELIEF_POLICY_V1_HOLDOUT_SCORES.csv", index=False)

    report = []
    report.append("# INSACERMO — MetroPT-3 Belief-Policy Real-Data Audit V1\n")
    report.append("## Verdict\n")
    report.append(f"**{verdict}**\n")
    report.append("This is an empirical stress test of a concrete learned belief proxy. It is not a claim that the proxy equals the Lean-defined canonical future state.\n")
    report.append("## Data integrity\n")
    report.append(f"- UCI DOI: `10.24432/C5VW3R`\n- Raw rows: **{raw_rows:,}**\n- Valid 5-minute bins: **{len(feat):,}**\n- Archive SHA256 verified: `{archive_sha}`\n")
    report.append("## Frozen chronological split\n")
    report.append(f"- Representation learning bins: {train_mask.sum():,}\n- Calibration bins: {cal_mask.sum():,}\n- Untouched holdout bins: {test_mask.sum():,}\n")
    report.append("## Test A — 30-minute future trajectory\n")
    for name, m in future_metrics.items():
        report.append(f"- {name}: NMSE = **{m['nmse']:.6f}**\n")
    report.append(f"\nFULL_BELIEF relative NMSE reduction vs MAP_SCALAR = **{100*structural_improvement:.2f}%**; preregistered ≥5% criterion: **{'PASS' if test_a_pass else 'FAIL'}**.\n")
    report.append("## Test B — 24-hour failure warning on untouched later failures\n")
    for name, m in warning_results.items():
        report.append(
            f"- {name}: PR-AUC **{m['pr_auc']:.6f}**, ROC-AUC **{m['roc_auc']:.6f}**, "
            f"Brier **{m['brier']:.6f}**, recall **{m['positive_recall_at_threshold']:.3f}**, "
            f"negative alert burden **{m['negative_alert_burden']:.3f}**, episodes **{m['episode_hits']}/{m['episode_total']}**.\n"
        )
    report.append(f"\nPreregistered operational criterion: **{'PASS' if test_b_pass else 'FAIL'}**.\n")
    report.append("## Test C — coarse unsafe-merge audit\n")
    report.append(f"- Future-mixed coarse codes: **{mixed['mixed_codes']}**\n")
    report.append(f"- Positive holdout bins lying in mixed codes: **{100*mixed['positive_bins_in_mixed_codes_fraction']:.2f}%**\n")
    report.append(f"- Criterion: **{'PASS' if test_c_pass else 'FAIL'}**\n")
    if mixed["witness"]:
        w = mixed["witness"]
        report.append("\n### Deterministic witness pair\n")
        report.append(
            f"Same coarse code `(mode={w['coarse_mode']}, anomaly_decile={w['coarse_anomaly_decile']})`, "
            f"but one bin lies in a real 24h pre-failure window and the other does not.\n\n"
            f"- Positive: {w['positive_time']}; FULL_BELIEF p={w['positive_full_probability']:.6f}; MAP_SCALAR p={w['positive_scalar_probability']:.6f}.\n"
            f"- Negative: {w['negative_time']}; FULL_BELIEF p={w['negative_full_probability']:.6f}; MAP_SCALAR p={w['negative_scalar_probability']:.6f}.\n"
            f"- FULL_BELIEF probability gap: {w['full_probability_gap']:.6f}; MAP_SCALAR gap: {w['scalar_probability_gap']:.6f}.\n"
        )
    report.append("## Interpretation guardrail\n")
    report.append(
        "The Lean theorem says that exact future-safe merging is characterized by equality of complete future policy behavior. "
        "This empirical audit cannot enumerate that complete object. It tests the weaker, falsifiable prediction that a richer belief proxy can retain future-relevant distinctions lost by a coarse current-state summary. "
        "Failure of the preregistered criteria counts against this concrete empirical instantiation, not against the already kernel-checked abstract theorem.\n"
    )
    (OUT / "METROPT_REALDATA_BELIEF_POLICY_V1_REPORT.md").write_text("\n".join(report), encoding="utf-8")

    # Receipt / hashes
    files = [
        OUT / "METROPT_BELIEF_POLICY_V1_RESULTS.json",
        OUT / "METROPT_BELIEF_POLICY_V1_METRICS.csv",
        OUT / "METROPT_BELIEF_POLICY_V1_HOLDOUT_SCORES.csv",
        OUT / "METROPT_REALDATA_BELIEF_POLICY_V1_REPORT.md",
    ]
    with (OUT / "SHA256SUMS.txt").open("w", encoding="utf-8") as f:
        for p in files:
            f.write(f"{sha256_file(p)}  {p.name}\n")

    print(json.dumps({
        "verdict": verdict,
        "test_a_pass": test_a_pass,
        "test_b_pass": test_b_pass,
        "test_c_pass": test_c_pass,
        "full_vs_scalar_nmse_reduction": structural_improvement,
        "full_pr_auc": wf["pr_auc"],
        "scalar_pr_auc": ws["pr_auc"],
        "full_episode_hits": wf["episode_hits"],
        "scalar_episode_hits": ws["episode_hits"],
        "mixed_codes": mixed["mixed_codes"],
    }, indent=2))


if __name__ == "__main__":
    main()
