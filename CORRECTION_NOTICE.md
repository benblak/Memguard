# Public correction notice — MemGuard

Date: 2026-06-22

This notice preserves the public audit trail. The repository history is not being rewritten or erased.

## What was wrong in the earlier public version

- The command `pip install memguard` installed an unrelated project because that distribution name was already occupied on PyPI.
- The README advertised `predict_tc`, `measure_K`, `KNOWN_K`, and CLI commands that were not present in the source package.
- The detector could react too strongly when the train loss converged faster than validation even while validation was still improving.
- A second stress test showed that a noisy validation plateau could be mistaken for degradation when the raw historical minimum was used as the main reference.
- The historical `56.4% ± 5.6%` compute-saving figure was conditional on older stop behavior and is not the current v0.3 result.

## What is corrected

- Distribution name changed to `insacermo-memguard`; import name changed to `insacermo_memguard`.
- Documentation now lists only implemented functions.
- `dry_run=True` is the callback default.
- `EARLY_STOP` requires persistent, noise-aware post-best degradation.
- Chronology is enforced: `early_warn_t <= stop_t`.
- Noisy plateaus and isolated spikes are handled conservatively.
- Conditional and all-run compute savings are reported separately.

## Current recalculated benchmark

Using frozen v0.3.0-rc1 thresholds on the four historical named runs:

- 3/4 runs stopped;
- 21.23% mean saving among stopped runs;
- 15.92% mean saving across all four runs;
- one run (`zephyr-7b-alpha`) classified as healthy and not stopped.

## Guidance for anyone who downloaded an older copy

Do not use an older copy for automatic stopping. Update to 0.3.0-rc1 or later, use `dry_run=True`, and validate on the target workload before enabling any automatic stop.

The older repository commits remain visible for transparency.
