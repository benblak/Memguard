"""Hugging Face callback for INSACERMO MemGuard."""

from __future__ import annotations

import json
import logging
from pathlib import Path

import pandas as pd

from .core import analyze

log = logging.getLogger("insacermo_memguard")

try:
    from transformers import TrainerCallback

    class MemGuardCallback(TrainerCallback):
        """Conservative callback.

        ``dry_run=True`` is the safe default. Set ``dry_run=False`` only after
        validating the behavior on your own logs.
        """

        def __init__(self, verbose=True, save_report=None, dry_run=True, cfg=None):
            self.verbose = verbose
            self.save_report = save_report
            self.dry_run = dry_run
            self.cfg = cfg
            self._history: list[tuple[float, float, float]] = []
            self._last_train: tuple[float, float] | None = None
            self.triggered = False
            self.report: dict = {}

        def on_log(self, args, state, control, logs=None, **kwargs):
            if logs and "loss" in logs and "eval_loss" not in logs:
                self._last_train = (float(state.global_step), float(logs["loss"]))

        def on_evaluate(self, args, state, control, metrics=None, **kwargs):
            if not metrics or "eval_loss" not in metrics or self._last_train is None:
                return
            _, train_loss = self._last_train
            self._history.append((float(state.global_step), train_loss, float(metrics["eval_loss"])))
            frame = pd.DataFrame(self._history, columns=["t", "train", "val"])
            report = analyze(frame, cfg=self.cfg, total_steps_scheduled=getattr(state, "max_steps", None))
            self.report = report

            if self.verbose:
                log.info(
                    "[MemGuard] step=%s action=%s reason=%s val=%s gap=%s",
                    state.global_step,
                    report["recommended_action"],
                    report["risk_reason"],
                    report.get("final_val"),
                    report.get("final_gap"),
                )

            if report["recommended_action"] == "EARLY_STOP" and not self.triggered:
                self.triggered = True
                if self.dry_run:
                    log.warning("[MemGuard] dry-run: EARLY_STOP detected but not applied")
                else:
                    log.warning("[MemGuard] EARLY_STOP applied")
                    control.should_training_stop = True

        def on_train_end(self, args, state, control, **kwargs):
            if self.save_report and self.report:
                path = Path(self.save_report)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(
                    json.dumps({"triggered": self.triggered, "dry_run": self.dry_run, **self.report}, indent=2),
                    encoding="utf-8",
                )

except ImportError:

    class MemGuardCallback:  # type: ignore
        def __init__(self, *args, **kwargs):
            raise ImportError('MemGuardCallback requires transformers. Install with: pip install "insacermo-memguard[hf]"')
