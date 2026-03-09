"""
memguard — Détection dynamique de la transition apprentissage → mémorisation.

Usage minimal :
    import memguard
    report = memguard.analyze_file("trainer_state.json")
    print(report["recommended_action"])   # EARLY_STOP | HEALTHY | ...
    print(report["risk_reason"])          # STOP_PATIENCE_TRIGGER | OK | ...
    print(report["compute_saved_pct"])    # 38.5  (% steps économisés si arrêt)

Avec un DataFrame existant :
    df  = memguard.load("trainer_state.json")
    rep = memguard.analyze(df)
"""

from .core import load, analyze, CFG
from .callback import MemGuardCallback
from .audit import analyze_repo, run_audit

__version__ = "0.1.0"
__all__      = ["load", "analyze", "analyze_file", "MemGuardCallback",
                "analyze_repo", "run_audit", "CFG"]


def analyze_file(path, total_steps_scheduled=None):
    """
    Raccourci : load + analyze en un appel.

    Parameters
    ----------
    path : str | Path
        trainer_state.json (HF) ou CSV (colonnes step/train_loss/eval_loss).
    total_steps_scheduled : int, optional
        Steps totaux prévus pour compute_saved_pct.

    Returns
    -------
    dict  verdict complet (recommended_action, risk_reason, compute_saved_pct, ...)
    """
    df = load(path)
    return analyze(df, total_steps_scheduled=total_steps_scheduled)
