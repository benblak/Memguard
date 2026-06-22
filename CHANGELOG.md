# Changelog

## 0.3.0-rc1

Noise-aware release candidate responding to independent plateau-noise stress testing.

### Fixed

- Replaced raw-minimum-only stop confirmation with a noise-aware multi-condition rule.
- Added trailing rolling-median validation smoothing.
- Added robust validation-noise estimation from second differences and MAD.
- Added noise-normalized recent-slope and adjacent-window shift guards.
- Added three consecutive confirmation windows before `EARLY_STOP`.
- Fixed chronology so `stop_t` cannot precede `early_warn_t`.
- Added explicit `NOISE_COMPATIBLE_PLATEAU` reporting.

### Tests added

- purely noisy plateau;
- 100-seed plateau regression guard;
- stable structural train/eval gap;
- isolated late spike;
- eval-more-frequent-than-train `merge_asof` alignment;
- moderate overfitting;
- warning-before-stop invariant.


### Recalculated historical benchmark

Using frozen 0.3.0-rc1 thresholds on the four historical public runs:

- stop coverage: 3/4;
- mean saving among stopped runs: 21.23%;
- mean saving across all four runs: 15.92%;
- the former 56.4% conditional claim is retired for the current version.

### Status

Release candidate / alpha-quality research software. Not production validated.

## 0.2.0

- Corrected widening-gap false positives while validation was still improving.
- Renamed distribution to avoid the unrelated PyPI `memguard` package.
- Removed non-existent API and CLI promises from the README.
- Made the callback dry-run by default.
- Separated conditional and unconditional compute-saving statistics.
