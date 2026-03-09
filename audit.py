"""
memguard.audit
==============
Scan automatisé de modèles HuggingFace Hub.

Usage CLI :
    memguard audit --limit 5000 --out results.csv
    memguard audit --limit 100 --filter tensorboard

Usage Python :
    from memguard.audit import run_audit
    df = run_audit(limit=5000)
"""

import json
import logging
import os
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

import numpy as np
import pandas as pd

from .core import analyze, CFG

log = logging.getLogger("memguard.audit")


# ── Chargement HF ─────────────────────────────────────────────────────────────

def _load_aligned(repo_id: str):
    """
    Télécharge trainer_state.json et retourne (DataFrame aligné, erreur|None).
    Alignement strict : inner join sur step où train_loss ET eval_loss sont présents.
    """
    try:
        from huggingface_hub import hf_hub_download
    except ImportError:
        raise ImportError("Installer huggingface_hub : pip install huggingface_hub")

    path = hf_hub_download(repo_id=repo_id, filename="trainer_state.json",
                           local_dir=tempfile.mkdtemp())
    with open(path) as f:
        data = json.load(f)

    df = pd.DataFrame(data.get("log_history", []))
    if df.empty:
        return None, "empty_log_history"
    if "step" not in df.columns:
        return None, "no_step_column"
    if "loss" not in df.columns or "eval_loss" not in df.columns:
        return None, "missing_loss_columns"

    tr = df[df["loss"].notna()][["step", "loss"]].groupby("step").last()
    ev = df[df["eval_loss"].notna()][["step", "eval_loss"]].groupby("step").last()
    aligned = tr.join(ev, how="inner").reset_index().sort_values("step")
    aligned = aligned.rename(columns={"step": "t", "loss": "train", "eval_loss": "val"})

    if len(aligned) < CFG["MIN_POINTS"]:
        return aligned, "insufficient_points"
    return aligned, None


# ── Analyse d'un repo ─────────────────────────────────────────────────────────

def analyze_repo(repo_id: str) -> dict | None:
    """
    Analyse un repo HuggingFace Hub.

    Returns
    -------
    dict avec champs repo, status, recommended_action, compute_saved_pct, ...
    None si erreur fatale (pas de trainer_state.json, timeout, etc.)
    """
    try:
        aligned, err = _load_aligned(repo_id)

        if aligned is None:
            return None  # erreur fatale, skip silencieux

        if err == "insufficient_points":
            return {
                "repo"              : repo_id,
                "status"            : "INSUFFICIENT_DATA",
                "n_points"          : len(aligned),
                "recommended_action": "INSUFFICIENT_DATA",
                "compute_saved_pct" : None,
            }

        rep = analyze(aligned)
        rep["repo"]   = repo_id
        rep["status"] = "OK"
        return rep

    except Exception as e:
        log.debug(f"[{repo_id}] erreur : {e}")
        return None


# ── Scan principal ────────────────────────────────────────────────────────────

def run_audit(
    limit     : int  = 5000,
    filter_tag: str  = "tensorboard",
    out_csv   : str  = None,
    verbose   : bool = True,
    workers   : int  = 4,
) -> pd.DataFrame:
    """
    Scanne les modèles HuggingFace Hub et applique MemGuard sur chaque
    trainer_state.json trouvé.

    Parameters
    ----------
    limit      : nombre max de modèles à scanner (trié par downloads)
    filter_tag : filtre HF Hub (défaut "tensorboard")
    out_csv    : chemin CSV de sortie (None = pas de sauvegarde)
    verbose    : affichage ligne par ligne
    workers    : threads parallèles pour les téléchargements

    Returns
    -------
    pd.DataFrame  une ligne par repo analysé
    """
    try:
        from huggingface_hub import HfApi
    except ImportError:
        raise ImportError("Installer huggingface_hub : pip install huggingface_hub")

    api = HfApi()
    log.info(f"Listing {limit} modèles (filter={filter_tag}, sort=downloads)...")
    models = list(api.list_models(
        filter=filter_tag, sort="downloads", direction=-1, limit=limit
    ))

    # Filtrer ceux qui ont trainer_state.json
    candidates = []
    log.info(f"Vérification trainer_state.json sur {len(models)} modèles...")
    for m in models:
        try:
            files = list(api.list_repo_files(m.id))
            if "trainer_state.json" in files:
                candidates.append(m.id)
        except Exception:
            pass

    if verbose:
        print(f"\n{len(candidates)} repos avec trainer_state.json sur {len(models)} scannés.")
        print(f"Analyse en cours ({workers} workers)...\n")

    rows = []

    def _process(repo_id):
        res = analyze_repo(repo_id)
        return repo_id, res

    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(_process, rid): rid for rid in candidates}
        for fut in as_completed(futures):
            repo_id, res = fut.result()
            if res is None:
                continue
            rows.append(res)
            if verbose:
                action = res.get("recommended_action", "?")
                saved  = res.get("compute_saved_pct")
                sym    = {"EARLY_STOP":"🔴","MONITOR_CLOSELY":"🟡",
                          "HEALTHY_OR_NEUTRAL":"🟢","HEALTHY":"🟢",
                          "INSUFFICIENT_DATA":"⚪"}.get(action, "❓")
                saved_str = f"  saved={saved:.1f}%" if saved else ""
                print(f"  {sym} {repo_id:<60} {action}{saved_str}")

    df = pd.DataFrame(rows)
    if df.empty:
        print("Aucun résultat exploitable.")
        return df

    # ── Résumé ──────────────────────────────────────────────────────────────
    ok  = df[df["status"] == "OK"]
    ins = df[df["status"] == "INSUFFICIENT_DATA"]

    stops   = ok[ok["recommended_action"] == "EARLY_STOP"]
    healthy = ok[ok["recommended_action"].isin(["HEALTHY", "HEALTHY_OR_NEUTRAL"])]
    monitor = ok[ok["recommended_action"] == "MONITOR_CLOSELY"]

    if verbose:
        print()
        print("=" * 60)
        print("  RÉSULTATS SCAN")
        print("=" * 60)
        print(f"  Total modèles avec trainer_state.json : {len(df)}")
        print(f"  Exploitables (≥ {CFG['MIN_POINTS']} points)  : {len(ok)}")
        print(f"  INSUFFICIENT_DATA              : {len(ins)}")
        print()
        print(f"  HEALTHY / NEUTRAL    : {len(healthy):>4}  ({len(healthy)/max(1,len(ok))*100:.1f}%)")
        print(f"  EARLY_STOP           : {len(stops):>4}  ({len(stops)/max(1,len(ok))*100:.1f}%)")
        print(f"  MONITOR_CLOSELY      : {len(monitor):>4}  ({len(monitor)/max(1,len(ok))*100:.1f}%)")
        if len(stops):
            saved_vals = stops["compute_saved_pct"].dropna()
            print()
            print(f"  Coverage (EARLY_STOP / OK)   : {len(stops)/max(1,len(ok))*100:.1f}%")
            print(f"  Compute saved moyen          : {saved_vals.mean():.2f}%")
            print(f"  Compute saved médiane        : {saved_vals.median():.2f}%")

    if out_csv:
        df.to_csv(out_csv, index=False)
        print(f"\n  Sauvegardé → {out_csv}")

    return df


# ── CLI entry point ───────────────────────────────────────────────────────────

def audit_main():
    import argparse, sys

    p = argparse.ArgumentParser(
        prog="memguard audit",
        description="Scan HuggingFace Hub — applique MemGuard sur les trainer_state.json."
    )
    p.add_argument("--limit",   type=int,  default=5000,         help="Nb modèles à scanner (défaut 5000)")
    p.add_argument("--filter",  type=str,  default="tensorboard", help="Filtre HF Hub (défaut tensorboard)")
    p.add_argument("--out",     type=str,  default="memguard_audit.csv", help="Fichier CSV de sortie")
    p.add_argument("--workers", type=int,  default=4,            help="Threads parallèles (défaut 4)")
    p.add_argument("--quiet",   action="store_true",             help="Pas d'affichage ligne par ligne")
    args = p.parse_args()

    df = run_audit(
        limit      = args.limit,
        filter_tag = args.filter,
        out_csv    = args.out,
        verbose    = not args.quiet,
        workers    = args.workers,
    )
    sys.exit(0 if not df.empty else 1)
