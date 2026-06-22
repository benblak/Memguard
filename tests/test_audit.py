import pandas as pd

from insacermo_memguard.audit import summarize_audit


def test_conditional_and_unconditional_are_separate():
    frame = pd.DataFrame(
        [
            {"status": "OK", "recommended_action": "EARLY_STOP", "compute_saved_pct": 60.0},
            {"status": "OK", "recommended_action": "EARLY_STOP", "compute_saved_pct": 40.0},
            {"status": "OK", "recommended_action": "HEALTHY", "compute_saved_pct": None},
            {"status": "OK", "recommended_action": "MONITOR", "compute_saved_pct": None},
        ]
    )
    summary = summarize_audit(frame)
    assert summary["compute_saved_conditional_mean"] == 50.0
    assert summary["compute_saved_unconditional_mean"] == 25.0
    assert summary["early_stop_coverage"] == 0.5
