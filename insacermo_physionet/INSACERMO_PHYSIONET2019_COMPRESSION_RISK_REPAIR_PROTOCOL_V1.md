# INSACERMO — PhysioNet 2019 Compression-Risk Repair Protocol V1

Status: **POST-PRIMARY EXPLORATORY / FROZEN BEFORE REPAIR RUN**

The original preregistered cross-hospital result has already been opened. Therefore this protocol is not confirmatory and does not replace the original result.

## Motivation

For a representation partition P on N held-out states with block sizes n_i,

M(P) = sum_i C(n_i,2) / C(N,2)

is the merged-pair mass and

Lambda_H(P) = M(P) V_H(P).

The original K=32 result used the same nominal number of codes for CURRENT and PRESERVE, but PRESERVE had substantially larger M. Thus equal K did not mean equal pairwise compression strength.

## Exact structural identity

Let p_i=n_i/N. Then

M(P) = (N sum_i p_i^2 - 1)/(N-1).

Define the collision-effective code count

K_eff(P)=1/sum_i p_i^2 = N/[1+(N-1)M(P)].

Balanced K-way partitions have K_eff=K; imbalanced K-way partitions can have K_eff far below K.

## Repair question

Can the already-fitted future-aligned PRESERVE representation be repaired only by refinement, using TRAIN observable features, until its TRAIN merged-pair mass is no larger than CURRENT's TRAIN merged-pair mass, while retaining its future-aligned parent structure?

## Frozen repair operator

For each cross-hospital fold A->B and B->A at K=32:

1. Fit the exact original CURRENT and PRESERVE models on TRAIN only.
2. Compute CURRENT TRAIN merged-pair mass M_current_train.
3. Start from PRESERVE leaf codes.
4. While PRESERVE TRAIN merged-pair mass exceeds M_current_train:
   - choose the currently largest PRESERVE block by TRAIN occupancy;
   - inside that block, select the observable feature with largest TRAIN variance;
   - split at that feature's TRAIN median;
   - keep the lower/equal side in the existing code and assign the upper side a new code;
   - apply the same frozen feature/threshold split to HOLDOUT states currently in that parent code.
5. Never merge blocks; every repair step is a refinement of the original PRESERVE partition.
6. Stop when M_repaired_train <= M_current_train or when 256 codes are reached.

No HOLDOUT labels, HOLDOUT future signatures, HOLDOUT collision rates, or HOLDOUT merge mass are used to choose a split or stopping point.

## Endpoints

Report, for H=1..12 on HOLDOUT:

- V_H for CURRENT, original PRESERVE, and REPAIRED-PRESERVE;
- Lambda_H for all three;
- merged-pair mass M;
- collision-effective code count K_eff;
- number of realized codes;
- strict empirical fracture depth phi.

Primary exploratory repair diagnostic:

mean_H [Lambda_H(CURRENT) - Lambda_H(REPAIRED-PRESERVE)].

Positive values mean the refinement repair crossed the global dangerous-pair-mass boundary on that fold.

Secondary exploratory diagnostic:

mean_H [V_H(CURRENT) - V_H(REPAIRED-PRESERVE)].

Positive values mean the repaired representation still retains the conditional future-coherence advantage.

## Interpretation discipline

This run is a mechanistic follow-up on already-opened PhysioNet holdouts. It may diagnose whether the negative Lambda result was caused by code-occupancy imbalance and whether existing INSACERMO refinement repair can correct it. It must not be relabeled as a preregistered replication.
