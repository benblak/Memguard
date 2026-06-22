"""Hugging Face repository audit and honest summary statistics."""

from __future__ import annotations

import json
import logging
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed

import pandas as pd

from .core import CFG, analyze

log = logging.getLogger("insacermo_memguard.audit")


def _load_aligned(repo_id: str):
    try:
        from huggingface_hub import hf_hub_download
    except ImportError as exc:
        raise ImportError('Install Hugging Face support with: pip install "insacermo-memguard[hf]"') from exc

    path = hf_hub_download(repo_id=repo_id, filename="trainer_state.json", local_dir=tempfile.mkdtemp())
    with open(path, encoding="utf-8") as handle:
        data = json.load(handle)
    history = pd.DataFrame(data.get("log_history", []))
    if history.empty or "step" not in history or "loss" not in history or "eval_loss" not in history:
        return None, "missing_or_empty_logs"

    train = history.loc[history["loss"].notna(), ["step", "loss"]].groupby("step", as_index=False).last()
    evaluation = history.loc[history["eval_loss"].notna(), ["step", "eval_loss"]].groupby("step", as_index=False).last()
    aligned = pd.merge_asof(
        evaluation.sort_values("step"),
        train.sort_values("step"),
        on="step",
        direction="backward",
    ).dropna()
    aligned = aligned.rename(columns={"step": "t", "loss": "train", "eval_loss": "val"})
    return aligned, None if len(aligned) >= CFG["MIN_POINTS"] else "insufficient_points"


def analyze_repo(repo_id: str) -> dict | None:
    try:
        aligned, error = _load_aligned(repo_id)
        if aligned is None:
            return None
        if error == "insufficient_points":
            return {
                "repo": repo_id,
                "status": "INSUFFICIENT_DATA",
                "n_points": len(aligned),
                "recommended_action": "INSUFFICIENT_DATA",
                "compute_saved_pct": None,
            }
        report = analyze(aligned)
        report.update({"repo": repo_id, "status": "OK"})
        return report
    except Exception as exc:  # pragma: no cover - network dependent
        log.debug("[%s] %s", repo_id, exc)
        return None


def summarize_audit(df: pd.DataFrame) -> dict:
    """Return both conditional and all-run compute-saving statistics."""
    if df.empty:
        return {
            "n_total": 0,
            "n_ok": 0,
            "n_early_stop": 0,
            "early_stop_coverage": 0.0,
            "compute_saved_conditional_mean": None,
            "compute_saved_unconditional_mean": None,
        }

    ok = df[df["status"] == "OK"].copy()
    stops = ok[ok["recommended_action"] == "EARLY_STOP"].copy()
    conditional = pd.to_numeric(stops.get("compute_saved_pct"), errors="coerce").dropna()
    all_run = pd.to_numeric(ok.get("compute_saved_pct"), errors="coerce").fillna(0.0)
    return {
        "n_total": int(len(df)),
        "n_ok": int(len(ok)),
        "n_early_stop": int(len(stops)),
        "early_stop_coverage": float(len(stops) / len(ok)) if len(ok) else 0.0,
        "compute_saved_conditional_mean": float(conditional.mean()) if len(conditional) else None,
        "compute_saved_conditional_median": float(conditional.median()) if len(conditional) else None,
        "compute_saved_unconditional_mean": float(all_run.mean()) if len(all_run) else None,
    }


def run_audit(limit=5000, filter_tag="tensorboard", out_csv=None, verbose=True, workers=4) -> pd.DataFrame:
    try:
        from huggingface_hub import HfApi
    except ImportError as exc:
        raise ImportError('Install Hugging Face support with: pip install "insacermo-memguard[hf]"') from exc

    api = HfApi()
    models = list(api.list_models(filter=filter_tag, sort="downloads", direction=-1, limit=limit))
    candidates = []
    for model in models:
        try:
            if "trainer_state.json" in api.list_repo_files(model.id):
                candidates.append(model.id)
        except Exception:
            continue

    rows = []
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(analyze_repo, repo): repo for repo in candidates}
        for future in as_completed(futures):
            result = future.result()
            if result is not None:
                rows.append(result)

    frame = pd.DataFrame(rows)
    if out_csv:
        frame.to_csv(out_csv, index=False)
    summary = summarize_audit(frame)
    if verbose:
        print(json.dumps(summary, indent=2))
        print("conditional = among EARLY_STOP runs only")
        print("unconditional = all analyzable runs, non-stops counted as 0% saved")
    return frame
