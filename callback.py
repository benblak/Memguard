"""
memguard.callback
=================
MemGuardCallback — s'intègre dans HuggingFace Trainer en une ligne.

Usage :
    from memguard import MemGuardCallback
    trainer = Trainer(..., callbacks=[MemGuardCallback()])
"""

import json
import logging
from pathlib import Path

from .core import CFG, analyze

log = logging.getLogger("memguard")

_ICONS = {
    "EARLY_STOP"      : "🔴",
    "MONITOR_CLOSELY" : "🟡",
    "HEALTHY"         : "🟢",
    "MONITOR"         : "🔵",
    "INSUFFICIENT_DATA": "⚪",
}

try:
    from transformers import TrainerCallback

    class MemGuardCallback(TrainerCallback):
        """
        Callback HuggingFace Trainer.

        Déclenche l'arrêt automatique si recommended_action == EARLY_STOP.

        Parameters
        ----------
        verbose     : affiche le rapport à chaque eval  (défaut True)
        save_report : chemin JSON pour sauvegarder le rapport final
        dry_run     : détecte sans jamais arrêter        (défaut False)
        cfg         : override des paramètres MemGuard
        """

        def __init__(self, verbose=True, save_report=None, dry_run=False, cfg=None):
            self.verbose      = verbose
            self.save_report  = save_report
            self.dry_run      = dry_run
            self.cfg          = cfg
            self._history     = []   # [(step, train_loss, eval_loss)]
            self._last_train  = None
            self.triggered    = False
            self.report       = {}

        def on_log(self, args, state, control, logs=None, **kwargs):
            if logs and "loss" in logs and "eval_loss" not in logs:
                self._last_train = (state.global_step, float(logs["loss"]))

        def on_evaluate(self, args, state, control, metrics=None, **kwargs):
            if not metrics or "eval_loss" not in metrics:
                return
            if self._last_train is None:
                return

            _, tl = self._last_train
            vl    = float(metrics["eval_loss"])
            self._history.append((state.global_step, tl, vl))

            import io, csv
            import pandas as pd
            buf = io.StringIO()
            w   = csv.writer(buf)
            w.writerow(["step", "train_loss", "eval_loss"])
            w.writerows(self._history)
            buf.seek(0)

            from .core import _load_csv
            df  = _load_csv(buf)
            rep = analyze(df, cfg=self.cfg)
            self.report = rep

            action = rep["recommended_action"]
            if self.verbose:
                icon = _ICONS.get(action, "❓")
                gap  = rep.get("final_gap") or 0.0
                mem  = rep.get("final_mem") or 0.0
                log.info(
                    f"[MemGuard] step={state.global_step:>7}  "
                    f"gap={gap:+.4f}  mem={mem:.3f}  "
                    f"n={rep['n_points']:>2}  "
                    f"{icon} {action}  [{rep.get('risk_reason', '?')}]"
                )

            if action == "EARLY_STOP" and not self.triggered:
                self.triggered = True
                if not self.dry_run:
                    log.warning(
                        f"[MemGuard] ⛔ EARLY_STOP → arrêt à step {state.global_step}  "
                        f"risk={rep.get('risk_reason')}"
                    )
                    control.should_training_stop = True
                else:
                    log.info(
                        f"[MemGuard] dry_run — EARLY_STOP détecté step={state.global_step} (non appliqué)"
                    )

        def on_train_end(self, args, state, control, **kwargs):
            if self.save_report and self.report:
                p = Path(self.save_report)
                p.parent.mkdir(parents=True, exist_ok=True)
                with open(p, "w") as f:
                    json.dump(
                        {"triggered": self.triggered, "dry_run": self.dry_run, **self.report},
                        f, indent=2, default=str,
                    )
                log.info(f"[MemGuard] Rapport → {self.save_report}")

except ImportError:

    class MemGuardCallback:  # type: ignore
        """Stub si transformers n'est pas installé."""

        def __init__(self, *args, **kwargs):
            raise ImportError(
                "MemGuardCallback nécessite transformers.\n"
                "  pip install transformers"
            )
