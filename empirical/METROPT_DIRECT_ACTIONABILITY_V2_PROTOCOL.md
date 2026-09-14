# INSACERMO — MetroPT-3 Direct Actionability Audit V2

Status: **FROZEN EXPLORATORY MECHANISM AUDIT — NOT A BLIND CONFIRMATORY TEST**

The MetroPT-3 June–September holdout has already been inspected in V1. Therefore V2 must not be described as an untouched or blind validation. Its purpose is narrower and more direct: test whether the operational INSACERMO roles ACT / PROBE / REFUSE behave coherently on real multi-sensor telemetry.

## Dataset and chronology

Use the same official UCI MetroPT-3 archive and verified SHA256 as V1.

- representation / scaling history: 2020-02-01 through 2020-03-31;
- policy calibration: 2020-04-01 through 2020-05-31;
- mechanism audit: 2020-06-01 through 2020-09-01;
- real 24 h pre-failure labels use the four published MetroPT failure windows already encoded in V1;
- failure intervals and 12 h post-failure windows remain excluded from action scoring.

## Contract

At each valid 5-minute bin, the system must choose one of:

- `ACT_ALERT`: act as if the machine is in the 24 h pre-failure class;
- `ACT_CONTINUE`: act as if it is not in the 24 h pre-failure class;
- `PROBE(sensor_group)`: acquire one previously unseen sensor group and continue;
- `REFUSE`: no sufficiently supported ACT is available within the allowed probe budget.

`REPAIR` is deliberately **not empirically scored in V2**. MetroPT is observational telemetry and does not contain counterfactual outcomes under a maintenance intervention. Claiming a validated REPAIR effect from this dataset would be unjustified.

## Sensor groups and belief score

Each original MetroPT sensor is one probe group. Its engineered 5-minute summaries (mean/std/min/max for analog sensors; mean for digital sensors) move together as one observation group.

A transparent train/calibration-only Gaussian naive-Bayes evidence model supplies an additive log-likelihood-ratio score over observed groups. The current belief proxy is the logistic transform of prior log-odds plus the accumulated group evidence.

This model is intentionally simple. V2 tests the **policy mechanism**, not state-of-the-art predictive performance.

## Decision thresholds

Thresholds are frozen from calibration data only:

- `ACT_CONTINUE` threshold = 5th percentile of the full-sensor score among calibration positives;
- `ACT_ALERT` threshold = 99th percentile of the full-sensor score among calibration negatives.

If these thresholds cross, the overlap is resolved conservatively by creating a no-ACT interval between their ordered values rather than allowing contradictory ACT decisions.

## PROBE rule

Maximum probe budget: **4 sensor groups**.

At a nonterminal state, every unobserved sensor group is scored using calibration-only class-conditional evidence samples. The chosen probe maximizes the model-estimated probability that observing that group will move the state into either ACT region after the probe. Ties are broken lexicographically by sensor-group name.

Thus PROBE is selected for **contract resolution**, not raw variance, reconstruction, or generic entropy reduction.

## REFUSE rule

If neither ACT region is reached after 4 probes, return `REFUSE`.

REFUSE is counted separately from an error. It is the explicit statement that the available evidence budget did not justify either ACT under the frozen contract.

## Baselines

Compare:

1. `ADAPTIVE_CONTRACT_PROBE`: chooses the next group from the current belief and remaining probes;
2. `FIXED_ORDER_PROBE`: fixed calibration-only order determined once at the prior state, then used for every bin;
3. `NO_PROBE`: no sensor acquisition; uncertain states REFUSE immediately;
4. `FULL_SENSOR`: diagnostic upper reference using all sensor groups at once, not a cost-matched policy.

No baseline is allowed to inspect the V2 audit labels when selecting its probe order or thresholds.

## Primary mechanism outputs

For each policy report:

- ACT coverage;
- REFUSE rate;
- unsafe-ACT rate among ACT decisions;
- positive ALERT recall;
- negative false-alert burden;
- mean and median number of probes;
- failure episodes with at least one ACT_ALERT in the preceding 24 h.

For every adaptive PROBE event additionally compute, using the hidden true sensor values only for retrospective audit:

- whether the chosen next probe immediately produces a **correct terminal ACT**;
- whether any available probe could have immediately produced a correct terminal ACT;
- the mean fraction of available probes that would have done so (random-probe reference).

The last comparison is the direct probe-selection diagnostic: the policy must choose useful probes more often than the average available probe if contract-directed sensing is doing nontrivial work.

## Mechanism-support labels

This is exploratory, not confirmatory. Still, the code will assign fixed descriptive labels:

- `DIRECT_MECHANISM_SUPPORT_V2` if adaptive probing has lower or equal unsafe-ACT rate than fixed order, strictly lower REFUSE rate or lower mean probe count at comparable ACT coverage, and chosen-probe immediate-correct-resolution rate exceeds the random available-probe reference by at least 5 percentage points;
- `PARTIAL_MECHANISM_SUPPORT_V2` if at least one of those direct mechanism advantages is present and adaptive probing does not increase unsafe-ACT rate by more than 2 percentage points;
- otherwise `NO_DIRECT_MECHANISM_SUPPORT_V2`.

These labels must not be promoted to blind empirical validation because the MetroPT holdout was already examined in V1.

## Interpretation boundary

A positive V2 result would show that an INSACERMO-style ACT / PROBE / REFUSE control rule can have measurable operational value on real telemetry. It would **not** prove that the learned score equals the Lean canonical future state.

A negative result would reject this concrete policy instantiation, not the abstract Lean theorem.
