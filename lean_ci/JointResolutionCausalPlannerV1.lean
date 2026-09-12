import Mathlib
import LocalTemporalSeparationV1

namespace InsacermoJointResolutionCausalPlanner

/-!
INSACERMO Joint Resolution–Causal Planner V1

This file does not introduce a new INSACERMO engine law. It isolates a failure mode of a
two-stage planner that first minimizes intervention cost and only afterwards accounts for
PROBE/REPAIR interaction depth.

Family:
* the local plan is the already kernel-verified hidden-vector optimum `(PR)^k`;
* every local intervention has unit base cost, hence base cost `2k`;
* an added global repair capability U reaches the same contractual goal at base cost `2k+1`;
* U is a single REPAIR-like intervention, hence interaction depth zero;
* the contract may charge `lambda` per PROBE<->REPAIR role switch.

Consequences proved here:
* cost-only optimization strictly prefers the local plan by one unit;
* already at the minimal positive integer switch penalty lambda=1, joint optimization strictly
  prefers U for every k>=2;
* the additive regret of cost-first decomposition is unbounded at that fixed unit penalty;
* no multiplicative approximation factor independent of the contract's switch penalty exists
  for this two-stage choice, even already at k=1;
* one extra base-cost unit can buy an arbitrarily large reduction in interaction depth.
-/

open InsacermoProbeRepairMinimax
open InsacermoInteractionDepthBridge

inductive ResolutionPlan
  | local
  | globalRepair
  deriving DecidableEq, Repr

/-- Base intervention/resource cost. -/
def baseCost (k : Nat) : ResolutionPlan -> Nat
  | .local => 2 * k
  | .globalRepair => 2 * k + 1

/-- Interaction depth of the two candidate resolution programs. -/
def planDepth (k : Nat) : ResolutionPlan -> Nat
  | .local => interactionDepth (canonical k)
  | .globalRepair => 0

/-- Contract-relative scalarization: base resource cost plus lambda per role switch. -/
def objective (k lambda : Nat) (p : ResolutionPlan) : Nat :=
  baseCost k p + lambda * planDepth k p

/-- The decomposed "resolve cost first, sequence second" rule always selects the local plan. -/
def resolutionFirst (_k : Nat) : ResolutionPlan := .local

/-- Exact local interaction depth inherited from the verified minimax kernel. -/
theorem local_plan_depth_exact (k : Nat) (hk : 0 < k) :
    planDepth k .local = 2 * k - 1 := by
  unfold planDepth
  exact hidden_vector_exact_interaction_depth k hk

/-- The added global repair has exactly zero interaction depth. -/
@[simp] theorem global_repair_depth_zero (k : Nat) :
    planDepth k .globalRepair = 0 := by
  rfl

/-- Resolution/intervention cost alone prefers the local plan by exactly one unit. -/
theorem resolution_cost_only_strictly_prefers_local (k : Nat) :
    baseCost k .local < baseCost k .globalRepair := by
  simp [baseCost]

/-- The base-cost premium of the global repair is exactly one. -/
theorem global_repair_cost_premium_one (k : Nat) :
    baseCost k .globalRepair = baseCost k .local + 1 := by
  simp [baseCost]

/-- Already at unit switch penalty, joint optimization reverses the cost-only choice for k>=2. -/
theorem joint_objective_prefers_global_at_unit_penalty (k : Nat) (hk : 2 ≤ k) :
    objective k 1 .globalRepair < objective k 1 .local := by
  have hdepth : planDepth k .local = 2 * k - 1 := local_plan_depth_exact k (by omega)
  simp [objective, baseCost, planDepth, hdepth]
  omega

/-- The stronger lambda=2 statement also holds for every nonzero k. -/
theorem joint_objective_prefers_global_at_penalty_two (k : Nat) (hk : 0 < k) :
    objective k 2 .globalRepair < objective k 2 .local := by
  have hdepth : planDepth k .local = 2 * k - 1 := local_plan_depth_exact k hk
  simp [objective, baseCost, planDepth, hdepth]
  omega

/-- With only these two safe alternatives, the joint optimum at unit penalty is U for k>=2. -/
def jointBestAtOne (k : Nat) : Nat :=
  Nat.min (objective k 1 .local) (objective k 1 .globalRepair)

theorem joint_best_at_one_eq_global (k : Nat) (hk : 2 ≤ k) :
    jointBestAtOne k = objective k 1 .globalRepair := by
  unfold jointBestAtOne
  exact Nat.min_eq_right (Nat.le_of_lt (joint_objective_prefers_global_at_unit_penalty k hk))

/-- Cost-first decomposition regret at the smallest positive integer switch penalty. -/
def decouplingRegretAtOne (k : Nat) : Nat :=
  objective k 1 (resolutionFirst k) - jointBestAtOne k

/-- Exact unit-penalty regret formula: 2k-2 for k>=2. -/
theorem decoupling_regret_at_one_exact (k : Nat) (hk : 2 ≤ k) :
    decouplingRegretAtOne k = 2 * k - 2 := by
  have hdepth : planDepth k .local = 2 * k - 1 := local_plan_depth_exact k (by omega)
  unfold decouplingRegretAtOne resolutionFirst
  rw [joint_best_at_one_eq_global k hk]
  simp [objective, baseCost, planDepth, hdepth]
  omega

/-- Even with unit switch penalty and positive integer base costs, the additive loss of separating
resolution-cost optimization from interaction-aware planning is unbounded. -/
theorem unbounded_additive_decoupling_regret_at_unit_penalty (K : Nat) :
    ∃ k : Nat, 2 ≤ k ∧ K < decouplingRegretAtOne k := by
  refine ⟨K + 2, by omega, ?_⟩
  rw [decoupling_regret_at_one_exact (K + 2) (by omega)]
  omega

/-- One extra unit of base cost can eliminate arbitrarily many mandatory local role switches. -/
theorem one_extra_base_unit_buys_unbounded_depth_reduction (K : Nat) :
    ∃ k : Nat, 0 < k ∧
      baseCost k .globalRepair = baseCost k .local + 1 ∧
      K < planDepth k .local - planDepth k .globalRepair := by
  refine ⟨K + 1, by omega, global_repair_cost_premium_one (K + 1), ?_⟩
  rw [local_plan_depth_exact (K + 1) (by omega)]
  simp [planDepth]
  omega

/-- The contract's switch price matters essentially. At k=1, by increasing lambda, the cost-first
choice can exceed the globally available repair by more than any prescribed multiplicative factor B.
This is a no-contract-independent-factor statement; it does NOT say the ratio diverges for fixed
lambda. -/
theorem no_contract_independent_multiplicative_factor (B : Nat) :
    ∃ lambda : Nat,
      B * objective 1 lambda .globalRepair < objective 1 lambda (resolutionFirst 1) := by
  have hdepth : planDepth 1 .local = 1 := by
    simpa using local_plan_depth_exact 1 (by omega)
  refine ⟨3 * B + 2, ?_⟩
  simp [objective, baseCost, planDepth, resolutionFirst, hdepth]
  omega

/-- The two plans are Pareto-incomparable in (base cost, interaction depth) for k>0. -/
theorem local_global_pareto_tradeoff (k : Nat) (hk : 0 < k) :
    baseCost k .local < baseCost k .globalRepair ∧
    planDepth k .globalRepair < planDepth k .local := by
  constructor
  · exact resolution_cost_only_strictly_prefers_local k
  · rw [local_plan_depth_exact k hk]
    simp [planDepth]
    omega

/-- Consolidated unit-penalty separation theorem. -/
theorem joint_resolution_causal_separation (K : Nat) :
    ∃ k : Nat, 2 ≤ k ∧
      baseCost k .local < baseCost k .globalRepair ∧
      objective k 1 .globalRepair < objective k 1 .local ∧
      K < decouplingRegretAtOne k := by
  refine ⟨K + 2, by omega, resolution_cost_only_strictly_prefers_local (K + 2),
    joint_objective_prefers_global_at_unit_penalty (K + 2) (by omega), ?_⟩
  rw [decoupling_regret_at_one_exact (K + 2) (by omega)]
  omega

end InsacermoJointResolutionCausalPlanner
