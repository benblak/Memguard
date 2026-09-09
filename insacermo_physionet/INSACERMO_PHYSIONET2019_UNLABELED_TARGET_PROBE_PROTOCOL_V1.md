# INSACERMO — PhysioNet 2019 Unlabeled Target-PROBE Repair Protocol V1

Status: **POST-PRIMARY EXPLORATORY / FROZEN BEFORE RUN**

This protocol is written after the original cross-hospital outcome and after the first TRAIN-only compression-repair outcome were opened. It is therefore exploratory and cannot replace either earlier result.

## Question

The first repair matched PRESERVE's merged-pair mass to CURRENT on the source TRAIN hospital, but that mass did not transport to the target hospital. Can a strictly unlabeled target calibration step repair this mismatch without consulting any target SepsisLabel or future signature?

This operationalizes a PROBE step: inspect only the occupancy geometry of the target representation, refine if needed, and only then evaluate future safety.

## Frozen cross-hospital folds

- source TRAIN A -> target hospital B
- source TRAIN B -> target hospital A

Primary nominal representation capacity remains K=32 for the source-fitted CURRENT and PRESERVE models.

## Target split before repair

Target patients are partitioned deterministically by SHA-256(patient_id):

- CALIBRATION: hash integer mod 5 == 0 (approximately 20% of patients)
- EVALUATION: all remaining patients (approximately 80%)

The calibration/evaluation split depends only on patient_id, never on SepsisLabel, future trajectory, or measured physiology.

## Source fitting

Fit exactly the same source-hospital preprocessing and K=32 models as in the original cross-hospital run:

- CURRENT: MiniBatch K-means on source observable current/past features.
- PRESERVE: decision-tree leaf representation trained on the H_train=6 future contract signature.

Freeze both models before target calibration.

## Unlabeled target-PROBE repair

On TARGET-CAL only:

1. Apply CURRENT and PRESERVE to obtain codes.
2. Compute the CURRENT target-calibration merged-pair mass M_current_cal from code occupancy only.
3. Starting from PRESERVE codes, refine until M_repaired_cal <= M_current_cal or 256 codes are reached.
4. Each refinement step:
   - choose the currently largest PRESERVE block on TARGET-CAL;
   - within that block choose the observable feature with largest TARGET-CAL variance;
   - split at that feature's TARGET-CAL median;
   - create a new subcode for values above the median.
5. Record the resulting ordered split rules.
6. Apply those split rules unchanged to TARGET-EVAL.

Forbidden during calibration and repair:

- SepsisLabel on TARGET-CAL;
- any target future signature;
- V_H, Lambda_H, phi, or any future-collision statistic;
- any TARGET-EVAL feature or occupancy information when choosing splits or stopping.

Thus the target PROBE is label-free and uses only a disjoint 20% patient calibration partition.

## Evaluation

On TARGET-EVAL only, after repair is frozen, compute for H=1..12:

- CURRENT: M, V_H, Lambda_H, K_eff;
- original PRESERVE: M, V_H, Lambda_H, K_eff;
- PROBE-REPAIRED PRESERVE: M, V_H, Lambda_H, K_eff.

Primary exploratory diagnostic:

mean_H [Lambda_H(CURRENT) - Lambda_H(PROBE_REPAIRED)].

Secondary:

mean_H [V_H(CURRENT) - V_H(PROBE_REPAIRED)].

Also report pointwise directions across 2 folds x 12 horizons, calibration vs evaluation merged-pair masses, realized code counts, and number of split operations.

## Interpretation

A positive Lambda diagnostic together with a positive V diagnostic would show that the failure of fixed source-only PRESERVE can be repaired by a label-free target occupancy PROBE. It would support a three-stage empirical mechanism:

PRESERVE FUTURE STRUCTURE -> PROBE TARGET OCCUPANCY -> REFINE COMPRESSION -> EVALUATE ACTIONABILITY.

A negative Lambda diagnostic would show that occupancy calibration alone is still insufficient.

No result from this protocol is preregistered confirmatory evidence.
