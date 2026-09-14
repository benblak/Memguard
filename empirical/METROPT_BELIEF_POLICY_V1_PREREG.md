# INSACERMO — MetroPT-3 Belief-Policy Real-Data Audit V1

## Status

Pre-registered before the first full-data result is inspected.

This experiment is an empirical stress test of the recently Lean-verified future-state chain. It does **not** claim that a learned finite-dimensional representation equals the formal canonical future state. The formal theorem quantifies over all finite adaptive policies; this audit asks whether a richer belief representation empirically preserves more future-relevant distinctions than deliberately coarser summaries on real industrial telemetry.

## Data

Official UCI MetroPT-3 dataset, DOI `10.24432/C5VW3R`, CC BY 4.0.

Archive URL:

`https://archive.ics.uci.edu/static/public/791/metropt%2B3%2Bdataset.zip`

Pinned archive SHA256:

`aab991a970e58210de853bb8078ce0e63abb4d9412fdc5c79792dae3d8e1721a`

The published dataset contains 1,516,948 observations from an Air Production Unit compressor in metro operation. The raw CSV is not directly labelled, but UCI publishes four company failure-report intervals:

1. 2020-04-18 00:00 — 2020-04-18 23:59, air leak / high stress.
2. 2020-05-29 23:30 — 2020-05-30 06:00, air leak / high stress.
3. 2020-06-05 10:00 — 2020-06-07 14:30, air leak / high stress.
4. 2020-07-15 14:30 — 2020-07-15 19:00, air leak / high stress.

## Frozen chronology

No random train/test split.

- Representation learning: 2020-02-01 00:00 through 2020-03-31 23:59.
- Policy calibration: 2020-04-01 00:00 through 2020-05-31 23:59. This includes only failure reports #1 and #2.
- Untouched holdout: 2020-06-01 00:00 through 2020-09-01 03:59:50. This contains failure reports #3 and #4.

The holdout is not used to select the number of latent modes, aggregation width, prediction horizon, model class, warning horizon, alert burden, or success criteria.

## Frozen preprocessing

- Aggregate telemetry into 5-minute bins.
- Require at least 80% of the nominal 30 samples/bin.
- Numeric analogue channels: mean, standard deviation, minimum, maximum.
- Digital channels: mean occupancy.
- Standardization parameters are fitted only on representation-learning data.
- Latent operating model: diagonal-covariance Gaussian mixture with K=8, seed 20260914, fitted only on representation-learning data.

The GMM posterior vector is used as an empirical belief proxy.

## Representations compared

All downstream models have the same algorithm class within a task. Only the input representation changes.

1. `MAP_ONLY`: one-hot identity of the most likely latent mode.
2. `MAP_SCALAR`: MAP mode plus current negative log-likelihood anomaly score.
3. `FULL_BELIEF`: all 8 posterior mode probabilities plus anomaly score plus posterior entropy.
4. `RAW_SNAPSHOT`: standardized engineered telemetry features. This is an upper-information comparator, not an INSACERMO compression.

The primary comparison is `FULL_BELIEF` versus `MAP_SCALAR`.

## Test A — Future-trajectory sufficiency proxy

Target: engineered telemetry 30 minutes in the future (6 bins), standardized using representation-learning statistics.

Model: multi-output Ridge regression, alpha=1.0, fitted on policy-calibration data and evaluated on untouched holdout.

Primary metric: normalized mean squared error (NMSE), averaged across target dimensions.

Pre-registered structural-support criterion:

`FULL_BELIEF` must reduce holdout NMSE by at least 5% relative to `MAP_SCALAR`.

If it does not, this primary structural criterion fails. No post-hoc horizon or threshold substitution will be used to rescue V1.

## Test B — Real failure-warning proxy

Positive label: a valid 5-minute bin lies in the 24 hours immediately preceding the start of a published failure interval.

Bins inside a failure interval and for 12 hours after its end are excluded from classifier fitting/evaluation so that the task is early warning rather than trivial in-failure detection.

Model: class-weighted logistic regression, C=1.0, fitted only on the calibration period (#1 and #2 available there).

Metrics on untouched holdout (#3 and #4):

- average precision / PR-AUC,
- ROC-AUC,
- Brier score,
- recall of pre-failure bins at a frozen alert threshold,
- false-alert burden on holdout negatives,
- failure-episode hit count out of 2,
- earliest warning lead time per detected episode.

Alert threshold: the 99th percentile of predicted probabilities among calibration-period negative bins for each representation separately. Thus each method is calibrated to approximately 1% negative alert burden before seeing holdout.

Pre-registered operational-support criterion:

`FULL_BELIEF` must outperform `MAP_SCALAR` in holdout PR-AUC **and** either:

- detect at least one additional holdout failure episode at its frozen threshold, or
- improve positive-bin recall by at least 25% relative while holdout negative alert burden is no more than 1.5 percentage points worse.

If this criterion fails, V1 does not claim decisive operational support.

## Test C — Unsafe-merge witness audit

A deliberately coarse code is frozen as:

`(MAP latent mode, train-defined anomaly-score decile)`.

A coarse code is empirically future-mixed if, on untouched holdout, it contains both 24h pre-failure bins and safe negative bins.

Report:

- fraction of positive holdout bins falling in future-mixed coarse codes,
- number of mixed coarse codes,
- a reproducible witness pair chosen by a deterministic rule: among mixed codes, choose the positive/negative pair with the largest absolute difference in `FULL_BELIEF` warning probability, breaking ties chronologically.

This witness is an empirical analogue of a forbidden merge, not a proof that the formal canonical states differ.

## Overall interpretation frozen before results

- **Decisive empirical support V1:** Test A and Test B both pass their pre-registered criteria, and Test C exhibits at least one mixed coarse code.
- **Partial support:** Test A passes and Test C is nonempty, but Test B fails or is inconclusive.
- **No decisive support:** Test A fails, regardless of other exploratory patterns.
- **Falsifying evidence against this empirical instantiation:** `FULL_BELIEF` is no better than `MAP_SCALAR` on Test A and does not improve Test B.

No result from this empirical audit changes the logical validity of the Lean kernels; it tests whether this concrete learned belief proxy captures practically future-relevant distinctions on a real system.
