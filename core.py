"""
memguard.core
=============
Deux fonctions publiques :
    load(path)          → DataFrame aligné train/eval
    analyze(df)         → dict verdict
"""

import json
import math
import os
import re

import numpy as np
import pandas as pd

# ── Config ────────────────────────────────────────────────────────────────────

CFG = dict(
    EMA_ALPHA   = 0.35,
    W_SLOPE     = 4,
    SLOPE_SCALE = 0.03,
    GAP_MIN     = 0.10,
    MEM_WARN    = 0.80,
    MEM_ALERT   = 0.90,
    MIN_POINTS  = 8,
    PATIENCE    = 3,
    PRE_WIN     = 5,
    POST_WIN    = 10,
    MAX_LR_DROPS= 2,
)

# ── Helpers ───────────────────────────────────────────────────────────────────

def _sigmoid(z):
    return 1.0 / (1.0 + math.exp(-max(-50.0, min(50.0, float(z)))))


def _pick_col(cols, candidates):
    cols_l = {c.lower(): c for c in cols}
    for c in candidates:
        if c in cols_l:
            return cols_l[c]
    for c in candidates:
        for col in cols:
            if c in col.lower():
                return col
    return None


def _ema(series, alpha):
    out = []
    for i, x in enumerate(series):
        out.append(float(x) if i == 0 else alpha * float(x) + (1 - alpha) * out[-1])
    return np.array(out, dtype=float)


def _mem_score(gap_s, w, scale):
    n = len(gap_s)
    mem = np.zeros(n, dtype=float)
    for i in range(w, n):
        recent = gap_s[i - w + 1 : i + 1]
        slope  = (recent[-1] - recent[0]) / max(1, w - 1)
        mem[i] = _sigmoid(slope / (scale + 1e-9))
    return mem


def _detect_lr_drop(df):
    if "lr" not in df.columns:
        return None
    lr = df["lr"].astype(float).values
    drops = np.where(np.diff(lr) < 0)[0]
    return float(df["t"].iloc[drops[0] + 1]) if len(drops) else None


# ── Public : load ─────────────────────────────────────────────────────────────

def load(path):
    """
    Charge un fichier de log et retourne un DataFrame avec colonnes t, train, val [, lr].

    Formats acceptés :
      - CSV   : colonnes step/train_loss/eval_loss (noms flexibles)
      - JSON  : trainer_state.json HuggingFace (alignement strict train+eval même step)

    Parameters
    ----------
    path : str | Path | IO
        Chemin vers le fichier, ou objet file-like (StringIO).

    Returns
    -------
    pd.DataFrame  colonnes : t, train, val [, lr]
    """
    # StringIO ou file-like → CSV
    if hasattr(path, "read"):
        return _load_csv(path)

    path = str(path)
    if path.endswith(".json") or os.path.basename(path) == "trainer_state.json":
        return _load_hf_json(path)
    return _load_csv(path)


def _load_csv(path):
    df = pd.read_csv(path)
    if df.shape[0] == 0:
        raise ValueError("Fichier vide.")

    t_col     = _pick_col(df.columns, ["step", "global_step", "iteration", "iter", "epoch"])
    train_col = _pick_col(df.columns, ["train_loss", "loss_train", "training_loss", "train", "loss"])
    val_col   = _pick_col(df.columns, ["eval_loss", "val_loss", "validation_loss", "eval", "valid"])
    lr_col    = _pick_col(df.columns, ["learning_rate", "lr"])

    if t_col is None or train_col is None or val_col is None:
        raise ValueError(
            f"Colonnes introuvables — step={t_col} train={train_col} val={val_col}\n"
            f"Colonnes disponibles : {list(df.columns)}"
        )

    cols = [t_col, train_col, val_col] + ([lr_col] if lr_col else [])
    out  = df[cols].copy()
    out.columns = ["t", "train", "val"] + (["lr"] if lr_col else [])
    out = out.dropna(subset=["t", "train", "val"]).sort_values("t").reset_index(drop=True)
    return out


def _load_hf_json(path):
    """
    Lit un trainer_state.json HuggingFace.
    Alignement strict : conserve uniquement les steps où train_loss ET eval_loss
    sont tous les deux présents (inner join sur step).
    """
    with open(path) as f:
        data = json.load(f)

    history = data.get("log_history", [])
    if not history:
        raise ValueError("log_history vide dans le JSON.")

    df = pd.DataFrame(history)

    # Séparer train et eval
    train_rows = df[df["loss"].notna()][["step", "loss"]].copy() if "loss" in df.columns else pd.DataFrame()
    eval_rows  = df[df["eval_loss"].notna()][["step", "eval_loss"]].copy() if "eval_loss" in df.columns else pd.DataFrame()

    if train_rows.empty or eval_rows.empty:
        raise ValueError("trainer_state.json : colonnes 'loss' ou 'eval_loss' manquantes.")

    train_rows = train_rows.groupby("step").last()
    eval_rows  = eval_rows.groupby("step").last()

    merged = train_rows.join(eval_rows, how="inner").reset_index().sort_values("step")

    if merged.empty:
        raise ValueError(
            "Aucun step avec train_loss ET eval_loss simultanément.\n"
            "Astuce : utiliser logging_strategy='epoch' et evaluation_strategy='epoch' "
            "dans TrainingArguments pour aligner les logs."
        )

    # LR optionnel
    out = merged.rename(columns={"step": "t", "loss": "train", "eval_loss": "val"})

    if "learning_rate" in df.columns:
        lr_rows = df[df["learning_rate"].notna()][["step", "learning_rate"]].groupby("step").last()
        out = out.set_index("t").join(lr_rows.rename(columns={"learning_rate": "lr"}), how="left").reset_index()

    return out.reset_index(drop=True)


# ── Public : analyze ──────────────────────────────────────────────────────────

def analyze(df, cfg=None, total_steps_scheduled=None):
    """
    Analyse un DataFrame de logs et retourne un dict verdict.

    Parameters
    ----------
    df : pd.DataFrame
        Sortie de load().
    cfg : dict, optional
        Override des paramètres (CFG par défaut).
    total_steps_scheduled : float, optional
        Nombre total de steps prévus pour calculer compute_saved_pct.

    Returns
    -------
    dict avec les champs :
        recommended_action  : EARLY_STOP | MONITOR_CLOSELY | HEALTHY |
                              MONITOR | INSUFFICIENT_DATA
        risk_reason         : string machine-readable
        compute_saved_pct   : float ou None
        + métriques internes
    """
    cfg = {**CFG, **(cfg or {})}
    n   = len(df)

    if n < cfg["MIN_POINTS"]:
        return dict(
            n_points=n,
            recommended_action="INSUFFICIENT_DATA",
            risk_reason=None,
            compute_saved_pct=None,
            initial_gap_negative=None,
            early_warn_t=None,
            stop_t=None,
            gap_acceleration_index=None,
            gai_clipped=False,
        )

    t  = df["t"].astype(float).values
    tr = df["train"].astype(float).values
    va = df["val"].astype(float).values

    w_dyn = max(2, min(cfg["W_SLOPE"], n // 3))
    gap   = va - tr
    gap_s = _ema(gap, cfg["EMA_ALPHA"])
    mem   = _mem_score(gap_s, w_dyn, cfg["SLOPE_SCALE"])

    best_i = int(np.argmin(va))
    t_best = float(t[best_i])
    t_end  = float(t[-1])

    initial_gap_negative = bool(gap_s[0] < 0)

    pct_after_best = max(0.0, (t_end - t_best) / t_end * 100.0) if t_end > 0 else None

    # ── Détections ────────────────────────────────────────────────────────────

    ew_i = None
    for i in range(n):
        if gap_s[i] > cfg["GAP_MIN"] and mem[i] >= cfg["MEM_WARN"]:
            ew_i = i; break

    ha_i = None
    if ew_i is not None:
        for i in range(ew_i, n):
            if mem[i] >= cfg["MEM_ALERT"]:
                ha_i = i; break

    stop_i = None
    if ew_i is not None:
        best_v, worsen = float("inf"), 0
        for i in range(ew_i, n):
            if va[i] < best_v - 1e-6:
                best_v, worsen = va[i], 0
            else:
                worsen += 1
            if worsen >= cfg["PATIENCE"]:
                stop_i = i; break

    # ── GAI ───────────────────────────────────────────────────────────────────

    gai_val, gai_clipped = None, False
    if ew_i is not None:
        i0   = max(0, ew_i - cfg["PRE_WIN"])
        pre  = float(np.mean(gap_s[i0:ew_i])) if ew_i > 0 else float(gap_s[0])
        post = float(np.mean(gap_s[ew_i : min(n, ew_i + cfg["POST_WIN"])]))
        t_warn = float(t[ew_i])

        if abs(pre) > 0.03 and abs(post) > 1e-9:
            t_lr = _detect_lr_drop(df)
            if t_lr and t_lr > 0 and t_end > t_lr:
                tau = (t_end - t_lr) / t_lr
            else:
                tau = (t_end - t_warn) / max(1e-9, t_warn)

            if tau > 0.05:
                raw = abs(math.log(abs(post / pre))) / abs(math.log(tau + 1e-9))
                gai_clipped = raw > 3.0
                gai_val = round(float(np.clip(raw, 0.0, 3.0)), 4)

    # ── Action ────────────────────────────────────────────────────────────────

    _vit = (ew_i is None and mem[-1] >= 0.5
            and pct_after_best is not None and pct_after_best > 30.0)

    if gai_clipped or stop_i is not None:
        action = "EARLY_STOP"
    elif ha_i is not None:
        action = "MONITOR_CLOSELY"
    elif ew_i is not None:
        action = "MONITOR_CLOSELY"
    elif _vit:
        action = "MONITOR_CLOSELY"
    elif mem[-1] <= 0.5 and not initial_gap_negative:
        action = "HEALTHY"
    elif mem[-1] <= 0.5 and initial_gap_negative and n >= cfg["MIN_POINTS"]:
        action = "HEALTHY"   # P9 : dropout normal
    elif mem[-1] <= 0.5 and initial_gap_negative:
        action = "MONITOR_CLOSELY"
    else:
        action = "MONITOR"

    # ── risk_reason ───────────────────────────────────────────────────────────

    if gai_clipped:
        rr = "GAI_CLIPPED_NO_RETURN"
    elif stop_i is not None and initial_gap_negative:
        rr = "FLIP_TARDIF_STOP_TRIGGER"
    elif stop_i is not None:
        rr = "STOP_PATIENCE_TRIGGER"
    elif ha_i is not None:
        rr = "HARD_ALERT_LR_DROP_NEEDED"
    elif ew_i is not None and initial_gap_negative:
        rr = "FLIP_WARN_EARLY"
    elif ew_i is not None:
        rr = "OVERFIT_WARN_EARLY"
    elif initial_gap_negative and action == "MONITOR_CLOSELY":
        rr = "INITIAL_GAP_NEGATIVE_LOW_DATA"
    elif _vit:
        rr = "HIGH_MEM_STEPS_AFTER_BEST"
    elif action == "MONITOR":
        rr = "MEM_ELEVATED_WATCH"
    elif action == "HEALTHY" and initial_gap_negative:
        rr = "HEALTHY_DROPOUT_NORMAL"
    else:
        rr = "OK"

    # ── compute_saved ─────────────────────────────────────────────────────────

    saved = None
    ref   = float(total_steps_scheduled) if total_steps_scheduled else t_end
    if stop_i is not None and ref > 0:
        saved = round(max(0.0, (ref - float(t[stop_i])) / ref * 100.0), 2)

    return dict(
        n_points              = n,
        initial_gap_negative  = initial_gap_negative,
        early_warn_t          = float(t[ew_i]) if ew_i is not None else None,
        hard_alert_t          = float(t[ha_i]) if ha_i is not None else None,
        stop_t                = float(t[stop_i]) if stop_i is not None else None,
        best_val              = round(float(va[best_i]), 6),
        t_best                = t_best,
        final_val             = round(float(va[-1]), 6),
        final_gap             = round(float(gap[-1]), 6),
        final_mem             = round(float(mem[-1]), 4),
        gap_acceleration_index= gai_val,
        gai_clipped           = gai_clipped,
        compute_saved_pct     = saved,
        risk_reason           = rr,
        recommended_action    = action,
    )
