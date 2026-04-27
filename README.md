le# MemGuard

**Early overfitting detection for LLM fine-tuning from logs only.**  
MemGuard detects the post-optimal degradation regime before standard visible metrics make it obvious.

- Hugging Face compatible
- No access to internal activations
- No model modification required
- Up to **56.4% compute saved**

**Stop fine-tuning at the right moment. Save 56% of compute.**

[![PyPI](https://img.shields.io/pypi/v/memguard)](https://pypi.org/project/memguard/)
[![Python](https://img.shields.io/pypi/pyversions/memguard)](https://pypi.org/project/memguard/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18675678.svg)](https://doi.org/10.5281/zenodo.18675678)

MemGuard detects the post-optimal degradation regime in LLM fine-tuning — before your metrics show it — and stops training automatically.



---

## The problem

Standard early stopping watches `eval_loss`. It reacts *after* the problem is visible.

MemGuard watches the **dynamics of the train/eval gap** — its slope and acceleration. It detects the transition from learning to memorisation before it appears in your metrics.

## Results on real HuggingFace runs

| Metric | Value |
|--------|-------|
| Compute saved (mean) | **56.4% ± 5.6%** |
| Regret MemGuard | **0.037** |
| Regret Standard | 0.077 |
| Improvement | **2.1× less regret** |

Validated on: `zephyr-7b-beta`, `mistral-7b-anthropic`, `argilla/notus-7b-v1`, `zephyr-7b-alpha`

---

## Install

```bash
pip install memguard
```

For HuggingFace Trainer integration:
```bash
pip install "memguard[hf]"
```

---

## Quick start

### Analyse an existing run
```python
import memguard

result = memguard.analyze_file("trainer_state.json")
print(result["recommended_action"])   # EARLY_STOP | MONITOR_CLOSELY | HEALTHY
print(result["compute_saved_pct"])    # 58.6
print(result["risk_reason"])          # STOP_PATIENCE_TRIGGER
```

### HuggingFace Trainer (live)
```python
from memguard import MemGuardCallback

trainer = Trainer(
    model=model,
    args=training_args,
    train_dataset=train_dataset,
    eval_dataset=eval_dataset,
    callbacks=[MemGuardCallback(verbose=True)]
)
trainer.train()
# MemGuard stops automatically when degradation is detected
```

### Predict optimal stopping point before training
```python
from memguard import predict_tc, measure_K, KNOWN_K

# Use cached complexity for known datasets
K = KNOWN_K["no_robots"]       # 0.787
tc = predict_tc(
    n_params=7e9,
    K=K,
    lr=2e-5,
    n_data=50_000,
    tokens_per_step=8192
)
print(f"Predicted optimal step: {tc:,.0f}")
```

### CLI
```bash
# Analyse a trainer_state.json
memguard analyze trainer_state.json

# Measure dataset complexity
memguard k HuggingFaceH4/no_robots --col prompt

# Predict optimal stopping point
memguard predict --n-params 7e9 --k 0.787 --lr 2e-5
```

---

## Three empirical laws

MemGuard is derived from three empirical laws validated on Pythia 70M → 12B and real HuggingFace runs:

**Law 1 — tc ~ N·log N** (r = 1.000, p < 0.001, n=8)
The optimal stopping step is proportional to model size times its logarithm.

**Law 2 — drift ~ log(overshoot)** (r = 0.979, bootstrap CI [0.891, 0.999], n=7)
Post-optimal degradation is predictable from the overshoot magnitude.

**Law 3 — K(D) predicts tc** (r = -0.622, p = 0.041, n=11)
Dataset algorithmic complexity predicts when overfitting begins.

---

## Known dataset complexity cache

```python
from memguard import KNOWN_K

# Pre-computed K values (zlib compression ratio)
print(KNOWN_K)
# {
#   "pile":         0.492,
#   "hh-rlhf":      0.621,
#   "UltraFeedback": 0.686,
#   "alpaca":       0.681,
#   "OpenHermes":   0.703,
#   "no_robots":    0.787,
#   "gsm8k":        0.821,
#   "flan-mini":    0.996,
# }
```

---

## API reference

### `memguard.analyze_file(path)`
Analyse a `trainer_state.json` or CSV log file.

Returns a dict with:
- `recommended_action`: `EARLY_STOP` | `MONITOR_CLOSELY` | `MONITOR` | `HEALTHY` | `INSUFFICIENT_DATA`
- `risk_reason`: machine-readable reason string
- `compute_saved_pct`: estimated compute saved if stopped now (float or None)
- `stop_t`, `t_best`, `final_val`, `final_gap`, `gap_acceleration_index`, ...

### `memguard.MemGuardCallback`
HuggingFace `TrainerCallback` that stops training automatically.

### `memguard.predict_tc(n_params, K, lr, n_data, tokens_per_step)`
Predict the optimal stopping step before training.

### `memguard.measure_K(dataset_name, column)`
Measure the algorithmic complexity K of a HuggingFace dataset column.

### `memguard.KNOWN_K`
Dict of pre-computed K values for common fine-tuning datasets.

---

## Citation

```bibtex
@misc{lenoir2025memguard,
  author    = {Lenoir, Benjamin},
  title     = {MemGuard: Empirical Laws of Post-Optimal Degradation in LLM Fine-Tuning},
  year      = {2025},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.18675678},
  url       = {https://doi.org/10.5281/zenodo.18675678}
}
```

---

## Related work

## Related research

MemGuard is one applied branch of the broader INSACERMO research program on memory, viability, regime transitions, and information-based dynamics.

The broader corpus includes core manuscripts, companion documents, and public reproducibility materials.

Main Zenodo entry:
- https://doi.org/10.5281/zenodo.19669211

- ## INSACERMO core law |K-G|

MemGuard implements the applied side. The theoretical core is the frozen criticality law:

$$|K-G| = 2.86 \frac{|\tau_c - 1.317|^{0.92}}{1 + 0.94 |\tau_c - 1.317|^{1.14}}$$

Validated on public MIT-BIH NSR record 16265:

- $\tau_c = 3.09$s, $K=0.85$, $G=2.15$
- $|K-G| = 1.30$, prediction $1.73$, $r=0.75$ → **PASS**

![ECG validation](https://raw.githubusercontent.com/benblak/Memguard/main/docs/figure_16265.png)

Reproducible notebook: [doi.org/10.5281/zenodo.19823276](https://doi.org/10.5281/zenodo.19823276)

INSACERMO is a state thermometer, a fragility sensor, and sometimes an early-warning signal — across heart, earthquake, climate, and LLM training.
---

## License

MIT — see [LICENSE](LICENSE)
