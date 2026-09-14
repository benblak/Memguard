# INSACERMO — MetroPT-3 Multi-Step PROBE Audit V3

Status: **FROZEN EXPLORATORY MECHANISM AUDIT — NOT BLIND CONFIRMATION**

V3 follows the completed V2 ACT / PROBE / REFUSE audit on the same MetroPT-3 holdout. Because this holdout has already been inspected, V3 is exploratory and mechanistic only. Its purpose is to test whether a non-myopic, multi-step value-of-information policy improves the choice of PROBE under the same contract.

## Dataset, chronology, and contract

Use exactly the same official UCI MetroPT-3 archive, SHA256, 5-minute feature engineering, chronological split, real failure windows, ACT thresholds, minimum-one-real-probe rule, 4-probe budget, and REPAIR exclusion as V2.

Terminal actions remain:
- `ACT_ALERT`
- `ACT_CONTINUE`
- `REFUSE`

Intermediate action:
- `PROBE(sensor_group)`

No ACT is permitted before at least one real sensor group has been observed.

## Main change from V2

V2 selected the next sensor by one-step immediate-resolution probability.

V3 selects the next sensor by **two-step contract value**. For a candidate first probe g, the policy estimates over calibration-only class-conditional evidence samples:

1. the probability that g immediately yields a terminal ACT;
2. if not terminal, the best achievable one-step terminal-ACT probability after a second probe h chosen adaptively from the remaining groups.

The V3 score is therefore:

`V2step(g | state) = P(immediate terminal after g) + P(nonterminal after g) * max_h P(terminal after h | resulting state)`

estimated by deterministic Monte Carlo from calibration-only evidence pools. The actual holdout sensor values are never used in the lookahead calculation.

Depth is fixed at **2 probes of lookahead**. Execution can still use up to **4 total probes** by replanning after every real observation.

## Deterministic Monte Carlo

- seed: `20260914`
- first-step samples per class and sensor: 48
- second-step samples per class and sensor: 32
- candidate shortlist per decision: top 6 groups by V2 one-step resolution score before two-step evaluation
- all tie breaks: lexicographic sensor-group name

These settings are frozen before V3 execution.

## Baselines

Compare:
1. `MULTISTEP_VOI_PROBE` — V3 two-step lookahead, replanned after each observation;
2. `MYOPIC_CONTRACT_PROBE` — exact V2 one-step adaptive rule;
3. `FIXED_ORDER_PROBE` — V2 calibration-only fixed order;
4. `NO_PROBE`;
5. `FULL_SENSOR` diagnostic upper reference.

## Primary direct PROBE diagnostics

For every adaptive PROBE event, retrospectively reveal the true held-out sensor values and record:

- chosen probe immediately produces a correct terminal ACT;
- any available probe could immediately produce a correct terminal ACT;
- random available-probe immediate-correct-resolution fraction;
- chosen probe produces a correct terminal ACT within **two real probes** when followed by the policy's next adaptive choice;
- random first probe followed by the same second-step policy produces a correct terminal ACT within two probes, averaged across all available first probes.

The last pair is the main V3 test. It directly asks whether multi-step planning chooses a better first measurement for eventual contract resolution than an arbitrary available first measurement.

## Policy outputs

For each policy report:
- ACT coverage;
- REFUSE rate;
- unsafe-ACT rate among ACTs;
- positive ALERT recall;
- negative false-alert burden;
- mean and median probes;
- failure episodes hit in the preceding 24 h.

## Frozen descriptive verdict labels

`MULTISTEP_PROBE_SUPPORT_V3` requires all of:
- V3 unsafe-ACT rate <= myopic unsafe-ACT rate + 0.005;
- V3 ACT coverage >= myopic ACT coverage - 0.005;
- V3 mean probes <= myopic mean probes + 0.10;
- V3 two-real-probe correct-resolution rate exceeds its random-first-probe reference by at least **5 percentage points**;
- and V3 two-real-probe correct-resolution rate exceeds the myopic policy's corresponding rate.

`PARTIAL_MULTISTEP_SUPPORT_V3` if at least one direct multi-step probe-selection advantage is positive and unsafe-ACT degradation is <= 2 percentage points.

Otherwise `NO_MULTISTEP_SUPPORT_V3`.

These labels are descriptive because the holdout is no longer blind.

## Interpretation boundary

A positive V3 result would support the specific claim that contract-directed multi-step sensing can outperform myopic sensing on real telemetry. It would not prove equivalence to the Lean canonical future state or validate REPAIR.

A negative V3 result would reject this concrete two-step VOI instantiation, not the abstract ACT / PROBE / REFUSE architecture.
