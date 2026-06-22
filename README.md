# INSACERMO MemGuard 0.3.0-rc1

**Noise-aware, conservative detection of persistent post-best degradation in fine-tuning logs.**

> **Release candidate.** Use in `dry_run` / shadow mode first. This version is not presented as a generally validated or production-ready automatic stopping system.

## Important correction notice

Earlier versions of this repository contained three public-facing problems:

1. `pip install memguard` pointed to an unrelated PyPI project;
2. the README documented functions and CLI commands that were not implemented;
3. the original stop logic was too sensitive to asymmetric convergence and noisy validation plateaus.

These points are corrected in the 0.3.0-rc1 source and documentation. Older copies should **not** be used for automatic stopping. See [`CORRECTION_NOTICE.md`](CORRECTION_NOTICE.md) and [`CHANGELOG.md`](CHANGELOG.md).

## Installation

The PyPI distribution named `memguard` belongs to an unrelated project. Do **not** use:

```bash
pip install memguard
```

This repository uses:

- distribution name: `insacermo-memguard`
- import name: `insacermo_memguard`

Install from this repository:

```bash
pip install "git+https://github.com/benblak/Memguard.git"
```

For Hugging Face integration:

```bash
pip install "insacermo-memguard[hf] @ git+https://github.com/benblak/Memguard.git"
```

## What changed in 0.3.0-rc1

Version 0.2 fixed a false positive caused by a widening train/eval gap while validation loss was still improving. Further stress testing then found a deeper issue: on a noisy plateau, the raw historical minimum can be an accidental low point, and later return toward the mean can look like degradation.

Version 0.3.0-rc1 changes the stop rule itself. `EARLY_STOP` now requires all of the following:

1. a prior widening-gap warning;
2. a robust post-best rise measured on a trailing rolling median;
3. degradation larger than both the configured minimum and three times an estimated validation-noise scale;
4. a positive recent validation trend with a sufficiently large noise-normalized slope score;
5. a positive shift between adjacent validation windows;
6. persistence over three consecutive candidate windows.

The train/eval gap remains a supporting signal only. A noisy plateau is reported as `MONITOR / NOISE_COMPATIBLE_PLATEAU`, not automatically as `EARLY_STOP`.

## Recalculated historical four-run benchmark

The original public README reported **56.4% ± 5.6%** compute saved. That number was a conditional mean from an older, more aggressive detector and is retired for the current version.

The four historical Hugging Face runs were recalculated with **MemGuard 0.3.0-rc1**, frozen thresholds, and no retuning:

| Run | v0.3 decision | Compute saved |
|---|---:|---:|
| `HuggingFaceH4/zephyr-7b-beta` | `EARLY_STOP` | 24.28% |
| `HuggingFaceH4/mistral-7b-anthropic` | `EARLY_STOP` | 29.40% |
| `argilla/notus-7b-v1` | `EARLY_STOP` | 10.00% |
| `HuggingFaceH4/zephyr-7b-alpha` | `HEALTHY` | 0.00% |

Summary:

- stop coverage: **3/4 runs (75%)**;
- mean compute saved among stopped runs: **21.23%**;
- median compute saved among stopped runs: **24.28%**;
- mean compute saved across all four runs, counting the healthy run as 0%: **15.92%**;
- change versus the former 56.4% conditional claim: **−35.17 percentage points**.

These figures describe this small named benchmark only. They are not a production guarantee or an enterprise-wide savings estimate.

## Safe quick start

```python
import insacermo_memguard as memguard

report = memguard.analyze_file("trainer_state.json")
print(report["recommended_action"])
print(report["risk_reason"])
```

CSV input must contain flexible equivalents of:

```text
step, train_loss, eval_loss
```

## Hugging Face callback

Safe default: detection only, no automatic stop.

```python
from insacermo_memguard import MemGuardCallback

callback = MemGuardCallback(dry_run=True, verbose=True)
```

Automatic stopping must be enabled explicitly only after validation on the target workload:

```python
callback = MemGuardCallback(dry_run=False, verbose=True)
```

## Interpretation

- `HEALTHY`: validation is still improving or no confirmed degradation exists.
- `MONITOR`: dynamics changed, or a noisy plateau is present, but stop evidence is absent.
- `MONITOR_CLOSELY`: the gap widened after the best region, but noise-aware confirmation is incomplete.
- `EARLY_STOP`: repeated noise-aware post-best degradation was confirmed.
- `INSUFFICIENT_DATA`: too few aligned evaluation points.

## Stress-regression suite

The suite includes:

- healthy asymmetric convergence with a widening gap;
- strong and moderate overfitting;
- purely noisy validation plateau;
- 100-seed noisy-plateau regression guard;
- structurally large but stable train/eval gap;
- one isolated late validation spike;
- Hugging Face logs where eval is more frequent than train (`merge_asof`);
- chronological invariant: `early_warn_t <= stop_t`.

Local result for this release candidate:

```text
11 tests passed
```

An additional synthetic stress sweep over 1,000 fixed noisy-plateau seeds produced 2 false stops for that one chosen generator. This is a regression diagnostic, not a general false-positive-rate estimate.

## Current public API

```python
load(path)
analyze(df, cfg=None, total_steps_scheduled=None)
analyze_file(path, total_steps_scheduled=None, cfg=None)
MemGuardCallback(...)
analyze_repo(repo_id)
run_audit(...)
summarize_audit(df)
CFG
```

The previously documented `predict_tc`, `measure_K`, `KNOWN_K`, `memguard k` and `memguard predict` are not part of this package because they are not implemented here.

## Tests

```bash
python -m pip install -e ".[dev]"
pytest
```

## Scope

MemGuard is an experimental log-only guard. It does not claim universal overfitting detection. Use it first in dry-run or shadow mode on the target workload, compare it with standard early stopping, and retain the best checkpoint.

## License

MIT. Benjamin Lenoir / INSACERMO.
