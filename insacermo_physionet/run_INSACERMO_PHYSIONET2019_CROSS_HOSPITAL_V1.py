#!/usr/bin/env python3
"""
INSACERMO — PhysioNet/CinC 2019 Cross-Hospital Sepsis Runner V1

Implements the frozen preregistration:
  INSACERMO_PHYSIONET2019_CROSS_HOSPITAL_PREREG_V1.md

Inputs may be either:
  - a directory containing patient .psv files, or
  - the official training_setA.zip / training_setB.zip archives.

No future HOLDOUT value is used for fitting.
This is a structural representation experiment, not a clinical tool.
"""

from __future__ import annotations

import argparse
import io
import json
import math
import zipfile
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, List, Tuple

import numpy as np
import pandas as pd
from sklearn.cluster import MiniBatchKMeans
from sklearn.preprocessing import StandardScaler
from sklearn.tree import DecisionTreeClassifier


SEED = 20260909
H_TRAIN = 6
H_MAX = 12
PRIMARY_K = 32
ROBUST_K = 64

PHYS = [
    "HR", "O2Sat", "Temp", "SBP", "MAP", "DBP", "Resp",
    "Glucose", "Lactate", "Creatinine", "WBC", "Platelets",
]
STATIC = ["Age", "Gender"]
REQUIRED = PHYS + STATIC + ["SepsisLabel"]

KMEANS_BATCH_SIZE = 4096
KMEANS_N_INIT = 10
KMEANS_MAX_ITER = 100


def iter_patient_frames(source: Path) -> Iterator[Tuple[str, pd.DataFrame]]:
    source = Path(source)
    if source.is_dir():
        files = sorted(source.rglob("*.psv"))
        for p in files:
            yield p.stem, pd.read_csv(p, sep="|")
        return
    if source.suffix.lower() == ".zip":
        with zipfile.ZipFile(source, "r") as z:
            names = sorted(n for n in z.namelist() if n.lower().endswith(".psv") and not n.endswith("/"))
            for name in names:
                with z.open(name, "r") as f:
                    b = f.read()
                yield Path(name).stem, pd.read_csv(io.BytesIO(b), sep="|")
        return
    raise ValueError(f"Unsupported source: {source}")


def future_signature_bits(labels: np.ndarray, t: int, H: int) -> int:
    out = 0
    for j in range(H + 1):
        out |= (int(labels[t + j]) & 1) << j
    return out


def patient_rows(patient_id: str, df: pd.DataFrame):
    missing = [c for c in REQUIRED if c not in df.columns]
    if missing:
        raise ValueError(f"{patient_id}: missing columns {missing}")
    df = df.reset_index(drop=True)
    n = len(df)
    if n <= H_MAX + 1:
        return None
    labels = pd.to_numeric(df["SepsisLabel"], errors="coerce").fillna(0).astype(int).to_numpy()
    raw_phys = df[PHYS].apply(pd.to_numeric, errors="coerce")
    missing_now = raw_phys.isna().astype(np.float32)
    ff = raw_phys.ffill()
    lag1 = ff.shift(1)
    diff1 = ff - lag1
    age = pd.to_numeric(df["Age"], errors="coerce")
    gender = pd.to_numeric(df["Gender"], errors="coerce")
    parts = []
    colnames = []
    for c in PHYS:
        parts.extend([
            ff[c].to_numpy(dtype=np.float32),
            lag1[c].to_numpy(dtype=np.float32),
            diff1[c].to_numpy(dtype=np.float32),
            missing_now[c].to_numpy(dtype=np.float32),
        ])
        colnames.extend([f"{c}_cur", f"{c}_lag1", f"{c}_diff1", f"{c}_missing"])
    parts.extend([age.to_numpy(dtype=np.float32), gender.to_numpy(dtype=np.float32)])
    colnames.extend(["Age", "Gender"])
    Xall = np.column_stack(parts).astype(np.float32)
    prior_positive = np.maximum.accumulate(labels)
    eligible = []
    sig6 = []
    sigs = {H: [] for H in range(1, H_MAX + 1)}
    for t in range(1, n - H_MAX):
        if labels[t] != 0:
            continue
        if prior_positive[t] != 0:
            continue
        eligible.append(t)
        sig6.append(future_signature_bits(labels, t, H_TRAIN))
        for H in range(1, H_MAX + 1):
            sigs[H].append(future_signature_bits(labels, t, H))
    if not eligible:
        return None
    idx = np.asarray(eligible, dtype=int)
    return {
        "patient_id": patient_id,
        "X": Xall[idx],
        "target6": np.asarray(sig6, dtype=np.int16),
        "sigs": {H: np.asarray(v, dtype=np.int16) for H, v in sigs.items()},
        "n_states": len(idx),
        "has_future_positive": np.asarray([int(np.any(labels[t+1:t+H_MAX+1] == 1)) for t in idx], dtype=np.int8),
        "feature_names": colnames,
    }


def build_partition(source: Path):
    Xs, ys = [], []
    sig_blocks = {H: [] for H in range(1, H_MAX + 1)}
    patient_ids = []
    future_pos = []
    n_patients = 0
    n_with_states = 0
    feature_names = None
    for pid, df in iter_patient_frames(Path(source)):
        n_patients += 1
        rec = patient_rows(pid, df)
        if rec is None:
            continue
        n_with_states += 1
        Xs.append(rec["X"])
        ys.append(rec["target6"])
        for H in range(1, H_MAX + 1):
            sig_blocks[H].append(rec["sigs"][H])
        patient_ids.extend([pid] * rec["n_states"])
        future_pos.append(rec["has_future_positive"])
        feature_names = rec["feature_names"]
    if not Xs:
        raise RuntimeError(f"No eligible states found in {source}")
    return {
        "X": np.vstack(Xs).astype(np.float32),
        "target6": np.concatenate(ys),
        "sigs": {H: np.concatenate(sig_blocks[H]) for H in range(1, H_MAX + 1)},
        "patient_ids": np.asarray(patient_ids, dtype=object),
        "future_positive12": np.concatenate(future_pos),
        "n_patient_files": n_patients,
        "n_patients_with_eligible_states": n_with_states,
        "feature_names": feature_names,
    }


@dataclass
class Preprocessor:
    medians: np.ndarray
    scaler: StandardScaler
    def transform(self, X):
        X = np.asarray(X, dtype=np.float32)
        Xi = np.where(np.isnan(X), self.medians, X)
        return self.scaler.transform(Xi).astype(np.float32)


def fit_preprocessor(X):
    medians = np.nanmedian(X, axis=0).astype(np.float32)
    medians = np.where(np.isnan(medians), 0.0, medians).astype(np.float32)
    Xi = np.where(np.isnan(X), medians, X)
    scaler = StandardScaler()
    scaler.fit(Xi)
    return Preprocessor(medians=medians, scaler=scaler)


def comb2(n):
    return n * (n - 1) // 2


def exact_collision_metrics(codes, sigs):
    codes = np.asarray(codes)
    sigs = np.asarray(sigs)
    n = len(codes)
    all_pairs = comb2(n)
    if all_pairs == 0:
        return dict(M=0.0, V=0.0, Lambda=0.0, merged_pairs=0, bad_pairs=0, all_pairs=0)
    code_counts = Counter(codes.tolist())
    joint_counts = Counter(zip(codes.tolist(), sigs.tolist()))
    merged = sum(comb2(v) for v in code_counts.values())
    same_sig = sum(comb2(v) for v in joint_counts.values())
    bad = merged - same_sig
    return {
        "M": merged / all_pairs,
        "V": bad / merged if merged else 0.0,
        "Lambda": bad / all_pairs,
        "merged_pairs": int(merged),
        "bad_pairs": int(bad),
        "all_pairs": int(all_pairs),
    }


def fit_current(X_train, K):
    model = MiniBatchKMeans(
        n_clusters=K,
        random_state=SEED,
        batch_size=KMEANS_BATCH_SIZE,
        n_init=KMEANS_N_INIT,
        max_iter=KMEANS_MAX_ITER,
        reassignment_ratio=0.01,
    )
    codes = model.fit_predict(X_train)
    return model, codes, len(np.unique(codes))


def fit_preserve(X_train, y_train, K):
    model = DecisionTreeClassifier(
        max_leaf_nodes=K,
        min_samples_leaf=50,
        criterion="entropy",
        random_state=SEED,
    )
    model.fit(X_train, y_train)
    leaves = model.apply(X_train)
    return model, leaves, len(np.unique(leaves))


def fold_run(train, hold, train_name, hold_name, K):
    prep = fit_preprocessor(train["X"])
    Xtr = prep.transform(train["X"])
    Xho = prep.transform(hold["X"])
    current_model, current_train_codes, nc = fit_current(Xtr, K)
    preserve_model, preserve_train_codes, npres = fit_preserve(Xtr, train["target6"], K)
    result = {
        "train_partition": train_name,
        "holdout_partition": hold_name,
        "K": int(K),
        "current_train_codes": int(nc),
        "preserve_train_codes": int(npres),
        "capacity_valid": bool(nc == K and npres == K),
        "n_train_states": int(len(Xtr)),
        "n_holdout_states": int(len(Xho)),
        "n_train_patient_files": int(train["n_patient_files"]),
        "n_holdout_patient_files": int(hold["n_patient_files"]),
        "n_train_patients_with_eligible_states": int(train["n_patients_with_eligible_states"]),
        "n_holdout_patients_with_eligible_states": int(hold["n_patients_with_eligible_states"]),
        "holdout_future_positive12_states": int(hold["future_positive12"].sum()),
    }
    if not result["capacity_valid"]:
        return result
    current_hold_codes = current_model.predict(Xho)
    preserve_hold_codes = preserve_model.apply(Xho)
    rows = []
    phi_current = math.inf
    phi_preserve = math.inf
    for H in range(1, H_MAX + 1):
        mc = exact_collision_metrics(current_hold_codes, hold["sigs"][H])
        mp = exact_collision_metrics(preserve_hold_codes, hold["sigs"][H])
        if phi_current is math.inf and mc["bad_pairs"] > 0:
            phi_current = H
        if phi_preserve is math.inf and mp["bad_pairs"] > 0:
            phi_preserve = H
        rows.append({
            "H": H,
            "current": mc,
            "preserve": mp,
            "delta_V_current_minus_preserve": mc["V"] - mp["V"],
            "delta_Lambda_current_minus_preserve": mc["Lambda"] - mp["Lambda"],
        })
    result["metrics"] = rows
    result["phi_current"] = "infinity" if math.isinf(phi_current) else int(phi_current)
    result["phi_preserve"] = "infinity" if math.isinf(phi_preserve) else int(phi_preserve)
    result["mean_delta_V_H1_H12"] = float(np.mean([r["delta_V_current_minus_preserve"] for r in rows]))
    result["mean_delta_Lambda_H1_H12"] = float(np.mean([r["delta_Lambda_current_minus_preserve"] for r in rows]))
    result["pointwise_V_preserve_lower"] = int(sum(r["preserve"]["V"] < r["current"]["V"] for r in rows))
    result["pointwise_Lambda_preserve_lower"] = int(sum(r["preserve"]["Lambda"] < r["current"]["Lambda"] for r in rows))
    for eps in [0.005, 0.01, 0.025]:
        for rep in ["current", "preserve"]:
            hit = next((r["H"] for r in rows if r[rep]["Lambda"] > eps), None)
            result[f"phi_eps_{eps:g}_{rep}"] = ">12" if hit is None else int(hit)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--setA", required=True)
    ap.add_argument("--setB", required=True)
    ap.add_argument("--outdir", default=".")
    args = ap.parse_args()
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    print("Loading A...")
    A = build_partition(Path(args.setA))
    print("A eligible states:", len(A["X"]))
    print("Loading B...")
    B = build_partition(Path(args.setB))
    print("B eligible states:", len(B["X"]))
    all_results = []
    for K in [PRIMARY_K, ROBUST_K]:
        print(f"Running A -> B, K={K}...")
        all_results.append(fold_run(A, B, "A", "B", K))
        print(f"Running B -> A, K={K}...")
        all_results.append(fold_run(B, A, "B", "A", K))
    primary = [r for r in all_results if r["K"] == PRIMARY_K and r["capacity_valid"]]
    if len(primary) == 2:
        delta_v = float(np.mean([r["mean_delta_V_H1_H12"] for r in primary]))
        delta_l = float(np.mean([r["mean_delta_Lambda_H1_H12"] for r in primary]))
        v_count = sum(r["pointwise_V_preserve_lower"] for r in primary)
        l_count = sum(r["pointwise_Lambda_preserve_lower"] for r in primary)
        primary_status = "PASS" if delta_v > 0 else "FAIL_OR_TIE"
    else:
        delta_v = delta_l = None
        v_count = l_count = None
        primary_status = "CAPACITY_INVALID"
    receipt = {
        "name": "INSACERMO PHYSIONET2019 CROSS-HOSPITAL V1",
        "status": "PASS_EXECUTION",
        "protocol": {
            "folds": ["A->B", "B->A"],
            "H_train": H_TRAIN,
            "H_eval": [1, H_MAX],
            "primary_K": PRIMARY_K,
            "robustness_K": ROBUST_K,
            "seed": SEED,
            "implementation_freeze": {
                "MiniBatchKMeans_batch_size": KMEANS_BATCH_SIZE,
                "MiniBatchKMeans_n_init": KMEANS_N_INIT,
                "MiniBatchKMeans_max_iter": KMEANS_MAX_ITER,
            },
        },
        "results": all_results,
        "primary": {
            "status": primary_status,
            "Delta_V": delta_v,
            "Delta_Lambda": delta_l,
            "V_preserve_lower_pointwise": None if v_count is None else f"{v_count}/24",
            "Lambda_preserve_lower_pointwise": None if l_count is None else f"{l_count}/24",
        },
        "claim_discipline": [
            "Structural cross-hospital representation validation only.",
            "Not a diagnostic system or clinical decision support tool.",
            "No held-out hospital patient data used for fitting.",
            "Capacity-invalid folds/capacities are not retuned after holdout.",
        ],
    }
    receipt_path = outdir / "INSACERMO_PHYSIONET2019_CROSS_HOSPITAL_V1_RECEIPT.json"
    receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    metric_rows = []
    for r in all_results:
        if not r["capacity_valid"]:
            metric_rows.append({
                "train": r["train_partition"],
                "holdout": r["holdout_partition"],
                "K": r["K"],
                "capacity_valid": False,
                "current_train_codes": r["current_train_codes"],
                "preserve_train_codes": r["preserve_train_codes"],
            })
            continue
        for m in r["metrics"]:
            metric_rows.append({
                "train": r["train_partition"],
                "holdout": r["holdout_partition"],
                "K": r["K"],
                "capacity_valid": True,
                "H": m["H"],
                "V_current": m["current"]["V"],
                "V_preserve": m["preserve"]["V"],
                "Delta_V": m["delta_V_current_minus_preserve"],
                "Lambda_current": m["current"]["Lambda"],
                "Lambda_preserve": m["preserve"]["Lambda"],
                "Delta_Lambda": m["delta_Lambda_current_minus_preserve"],
                "M_current": m["current"]["M"],
                "M_preserve": m["preserve"]["M"],
            })
    pd.DataFrame(metric_rows).to_csv(outdir / "INSACERMO_PHYSIONET2019_CROSS_HOSPITAL_V1_METRICS.csv", index=False)
    print(json.dumps(receipt["primary"], indent=2))
    print("Receipt:", receipt_path)


if __name__ == "__main__":
    main()
