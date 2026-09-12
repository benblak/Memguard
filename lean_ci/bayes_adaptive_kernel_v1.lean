import Mathlib

/-!
# INSACERMO — Bayes-Adaptive Kernel V1

Formal target for Lean 4.32.1 + mathlib v4.32.1.

This file kernel-checks the finite-alphabet structural layer used by the
INSACERMO Bayes-adaptive closure:

* BA-1: static-model augmented latent state;
* BA-2: finite normalized Bayes filter on positive-evidence branches;
* BA-3: posterior model-mass martingale, including zero-evidence branches;
* BA-4: monotonicity of the robust branchwise predecessor;
* BA-5: finite-horizon actionability recursion;
* BA-6: discounted greedy Bellman contraction in the finite sup norm;
* BA-7: existence and uniqueness of the Bellman fixed point by Banach;
* BA-8: an exact dual-effect PROBE+REPAIR witness and its two ablations;
* BA-9: a capability-only reversal showing model identity can become
        action-irrelevant without any new observation.

The classical ingredients (Bayesian filtering, dual control, Bellman
contraction, Banach fixed point) are not claimed as novel.  The purpose of the
formalization is to certify that they fit the same declared INSACERMO
CONTRACT -> ACTIONABILITY -> PLANNER interface.
-/

open scoped BigOperators
open Function

namespace Insacermo
namespace BayesAdaptiveKernel

/-! ## BA-1 — augmented latent state -/

section AugmentedLatent

variable {Theta S A : Type*} [DecidableEq Theta]

/-- Unknown static model plus physical state. -/
abbrev JointLatent (Theta S : Type*) := Theta × S

/-- Lift a model-indexed physical transition kernel to the joint latent state.
The latent model identity is static. -/
def staticThetaKernel
    (P : Theta → S → A → S → ℝ)
    (x : JointLatent Theta S) (a : A) (xp : JointLatent Theta S) : ℝ :=
  if xp.1 = x.1 then P x.1 x.2 a xp.2 else 0

theorem staticThetaKernel_zero_of_theta_ne
    (P : Theta → S → A → S → ℝ)
    (x xp : JointLatent Theta S) (a : A)
    (h : xp.1 ≠ x.1) :
    staticThetaKernel P x a xp = 0 := by
  simp [staticThetaKernel, h]

theorem staticThetaKernel_eq_of_theta_eq
    (P : Theta → S → A → S → ℝ)
    (x xp : JointLatent Theta S) (a : A)
    (h : xp.1 = x.1) :
    staticThetaKernel P x a xp = P x.1 x.2 a xp.2 := by
  simp [staticThetaKernel, h]

end AugmentedLatent

/-! ## BA-2 / BA-3 — exact finite Bayes filter -/

section FiniteBayes

variable {Theta S A O : Type*}
variable [Fintype Theta] [Fintype S] [Fintype O]

/-- A finite joint belief over model and physical state. -/
structure Belief (Theta S : Type*) [Fintype Theta] [Fintype S] where
  mass : Theta → S → ℝ
  nonneg : ∀ theta s, 0 ≤ mass theta s
  sum_eq_one : ∑ theta, ∑ s, mass theta s = 1

/-- Model-indexed physical transition kernel. -/
structure TransitionKernel (Theta S A : Type*) [Fintype S] where
  mass : Theta → S → A → S → ℝ
  nonneg : ∀ theta s a sp, 0 ≤ mass theta s a sp
  sum_eq_one : ∀ theta s a, ∑ sp, mass theta s a sp = 1

/-- Model-indexed observation kernel after transition. -/
structure ObservationKernel (Theta S A O : Type*) [Fintype O] where
  mass : Theta → S → A → O → ℝ
  nonneg : ∀ theta sp a o, 0 ≤ mass theta sp a o
  sum_eq_one : ∀ theta sp a, ∑ o, mass theta sp a o = 1

/-- Unnormalized joint posterior mass for one observation. -/
def predictMass
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) (theta : Theta) (sp : S) : ℝ :=
  Z.mass theta sp a o * ∑ s, b.mass theta s * P.mass theta s a sp

/-- Predictive probability of observation `o`. -/
def evidence
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) : ℝ :=
  ∑ theta, ∑ sp, predictMass b P Z a o theta sp

/-- Model-specific unnormalized posterior mass. -/
def unnormModelMass
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) (theta : Theta) : ℝ :=
  ∑ sp, predictMass b P Z a o theta sp

/-- Current posterior marginal on model identity. -/
def modelMarginal (b : Belief Theta S) (theta : Theta) : ℝ :=
  ∑ s, b.mass theta s

theorem predictMass_nonneg
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) (theta : Theta) (sp : S) :
    0 ≤ predictMass b P Z a o theta sp := by
  unfold predictMass
  apply mul_nonneg (Z.nonneg theta sp a o)
  exact Finset.sum_nonneg fun s _ =>
    mul_nonneg (b.nonneg theta s) (P.nonneg theta s a sp)

theorem unnormModelMass_nonneg
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) (theta : Theta) :
    0 ≤ unnormModelMass b P Z a o theta := by
  unfold unnormModelMass
  exact Finset.sum_nonneg fun sp _ => predictMass_nonneg b P Z a o theta sp

theorem evidence_nonneg
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) :
    0 ≤ evidence b P Z a o := by
  unfold evidence
  exact Finset.sum_nonneg fun theta _ =>
    Finset.sum_nonneg fun sp _ => predictMass_nonneg b P Z a o theta sp

theorem evidence_eq_sum_unnormModelMass
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) :
    evidence b P Z a o = ∑ theta, unnormModelMass b P Z a o theta := by
  rfl

theorem unnormModelMass_le_evidence
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) (theta : Theta) :
    unnormModelMass b P Z a o theta ≤ evidence b P Z a o := by
  rw [evidence_eq_sum_unnormModelMass]
  exact Finset.single_le_sum
    (fun t _ => unnormModelMass_nonneg b P Z a o t)
    (Finset.mem_univ theta)

theorem unnormModelMass_eq_zero_of_evidence_eq_zero
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) (theta : Theta)
    (he : evidence b P Z a o = 0) :
    unnormModelMass b P Z a o theta = 0 := by
  have h0 := unnormModelMass_nonneg b P Z a o theta
  have hle := unnormModelMass_le_evidence b P Z a o theta
  rw [he] at hle
  linarith

/-- Normalized posterior mass on a positive-evidence observation branch. -/
def posteriorMass
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) (theta : Theta) (sp : S) : ℝ :=
  predictMass b P Z a o theta sp / evidence b P Z a o

theorem posteriorMass_nonneg
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O)
    (he : 0 < evidence b P Z a o)
    (theta : Theta) (sp : S) :
    0 ≤ posteriorMass b P Z a o theta sp := by
  exact div_nonneg
    (predictMass_nonneg b P Z a o theta sp)
    (le_of_lt he)

theorem posteriorMass_sum_eq_one
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O)
    (he : evidence b P Z a o ≠ 0) :
    ∑ theta, ∑ sp, posteriorMass b P Z a o theta sp = 1 := by
  calc
    (∑ theta, ∑ sp, posteriorMass b P Z a o theta sp)
        = ∑ theta, (∑ sp, predictMass b P Z a o theta sp) /
            evidence b P Z a o := by
              apply Finset.sum_congr rfl
              intro theta htheta
              simp only [posteriorMass]
              rw [Finset.sum_div]
    _ = (∑ theta, ∑ sp, predictMass b P Z a o theta sp) /
          evidence b P Z a o := by
            rw [Finset.sum_div]
    _ = evidence b P Z a o / evidence b P Z a o := by rfl
    _ = 1 := div_self he

/-- The normalized positive-evidence Bayes update is again a belief. -/
def bayesUpdate
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O)
    (he : 0 < evidence b P Z a o) : Belief Theta S where
  mass := posteriorMass b P Z a o
  nonneg := posteriorMass_nonneg b P Z a o he
  sum_eq_one := posteriorMass_sum_eq_one b P Z a o (ne_of_gt he)

theorem modelMarginal_bayesUpdate
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O)
    (he : 0 < evidence b P Z a o)
    (theta : Theta) :
    modelMarginal (bayesUpdate b P Z a o he) theta =
      unnormModelMass b P Z a o theta / evidence b P Z a o := by
  simp only [modelMarginal, bayesUpdate, posteriorMass, unnormModelMass]
  rw [Finset.sum_div]

/-- Safe algebraic posterior used only to state expectations across all
observation labels.  Zero-evidence labels receive zero mass and therefore
contribute zero to any evidence-weighted expectation. -/
def safePosteriorMass
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) (theta : Theta) (sp : S) : ℝ :=
  if evidence b P Z a o = 0 then 0
  else posteriorMass b P Z a o theta sp

def safePosteriorModelMass
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) (theta : Theta) : ℝ :=
  ∑ sp, safePosteriorMass b P Z a o theta sp

theorem safePosteriorModelMass_eq_div_of_evidence_ne_zero
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) (theta : Theta)
    (he : evidence b P Z a o ≠ 0) :
    safePosteriorModelMass b P Z a o theta =
      unnormModelMass b P Z a o theta / evidence b P Z a o := by
  simp only [safePosteriorModelMass, safePosteriorMass, he, if_false,
    posteriorMass, unnormModelMass]
  rw [Finset.sum_div]

theorem evidence_mul_safePosteriorModelMass
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (o : O) (theta : Theta) :
    evidence b P Z a o * safePosteriorModelMass b P Z a o theta =
      unnormModelMass b P Z a o theta := by
  by_cases he : evidence b P Z a o = 0
  · rw [he, zero_mul]
    exact (unnormModelMass_eq_zero_of_evidence_eq_zero b P Z a o theta he).symm
  · rw [safePosteriorModelMass_eq_div_of_evidence_ne_zero b P Z a o theta he]
    exact mul_div_cancel₀ _ he

/-- Summing model-specific unnormalized posterior mass over observations
recovers the prior model marginal.  This is the algebraic heart of the
posterior martingale property. -/
theorem sum_unnormModelMass_eq_modelMarginal
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (theta : Theta) :
    ∑ o, unnormModelMass b P Z a o theta = modelMarginal b theta := by
  calc
    (∑ o, unnormModelMass b P Z a o theta)
        = ∑ o, ∑ sp, Z.mass theta sp a o *
            (∑ s, b.mass theta s * P.mass theta s a sp) := by rfl
    _ = ∑ sp, ∑ o, Z.mass theta sp a o *
            (∑ s, b.mass theta s * P.mass theta s a sp) := by
              rw [Finset.sum_comm]
    _ = ∑ sp, (∑ o, Z.mass theta sp a o) *
            (∑ s, b.mass theta s * P.mass theta s a sp) := by
              apply Finset.sum_congr rfl
              intro sp hsp
              rw [Finset.sum_mul]
    _ = ∑ sp, ∑ s, b.mass theta s * P.mass theta s a sp := by
              apply Finset.sum_congr rfl
              intro sp hsp
              rw [Z.sum_eq_one]
              simp
    _ = ∑ s, ∑ sp, b.mass theta s * P.mass theta s a sp := by
              rw [Finset.sum_comm]
    _ = ∑ s, b.mass theta s * (∑ sp, P.mass theta s a sp) := by
              apply Finset.sum_congr rfl
              intro s hs
              rw [Finset.mul_sum]
    _ = ∑ s, b.mass theta s := by
              apply Finset.sum_congr rfl
              intro s hs
              rw [P.sum_eq_one]
              simp
    _ = modelMarginal b theta := rfl

/-- BA-3: the posterior marginal on the static model is a martingale.  The
statement is valid without a full-support assumption because zero-evidence
observation labels are weighted by zero and are handled explicitly. -/
theorem modelPosterior_martingale
    (b : Belief Theta S)
    (P : TransitionKernel Theta S A)
    (Z : ObservationKernel Theta S A O)
    (a : A) (theta : Theta) :
    ∑ o, evidence b P Z a o * safePosteriorModelMass b P Z a o theta =
      modelMarginal b theta := by
  calc
    (∑ o, evidence b P Z a o * safePosteriorModelMass b P Z a o theta)
        = ∑ o, unnormModelMass b P Z a o theta := by
            apply Finset.sum_congr rfl
            intro o ho
            exact evidence_mul_safePosteriorModelMass b P Z a o theta
    _ = modelMarginal b theta :=
      sum_unnormModelMass_eq_modelMarginal b P Z a theta

end FiniteBayes

/-! ## BA-4 / BA-5 — contract-relative robust actionability -/

section RobustActionability

variable {B A O : Type*}

/-- A belief/information state is in `RobustPre K` when one legal action sends
every positive-probability observation branch into `K`. -/
def RobustPre
    (prob : B → A → O → ℝ)
    (next : B → A → O → B)
    (legal : B → A → Prop)
    (K : Set B) : Set B :=
  {b | ∃ a, legal b a ∧ ∀ o, 0 < prob b a o → next b a o ∈ K}

theorem robustPre_mono
    (prob : B → A → O → ℝ)
    (next : B → A → O → B)
    (legal : B → A → Prop)
    {K L : Set B}
    (hKL : K ⊆ L) :
    RobustPre prob next legal K ⊆ RobustPre prob next legal L := by
  intro b hb
  rcases hb with ⟨a, ha, hall⟩
  refine ⟨a, ha, ?_⟩
  intro o hpos
  exact hKL (hall o hpos)

/-- Finite-horizon robust actionability recursion. -/
def ActionableAt
    (prob : B → A → O → ℝ)
    (next : B → A → O → B)
    (legal : B → A → Prop)
    (terminal : Set B) : Nat → Set B
  | 0 => terminal
  | n + 1 => RobustPre prob next legal (ActionableAt prob next legal terminal n)

@[simp] theorem actionableAt_zero
    (prob : B → A → O → ℝ)
    (next : B → A → O → B)
    (legal : B → A → Prop)
    (terminal : Set B) :
    ActionableAt prob next legal terminal 0 = terminal := rfl

@[simp] theorem actionableAt_succ
    (prob : B → A → O → ℝ)
    (next : B → A → O → B)
    (legal : B → A → Prop)
    (terminal : Set B) (n : Nat) :
    ActionableAt prob next legal terminal (n + 1) =
      RobustPre prob next legal (ActionableAt prob next legal terminal n) := rfl

theorem actionableAt_mono_terminal
    (prob : B → A → O → ℝ)
    (next : B → A → O → B)
    (legal : B → A → Prop)
    {K L : Set B}
    (hKL : K ⊆ L) :
    ∀ n, ActionableAt prob next legal K n ⊆ ActionableAt prob next legal L n := by
  intro n
  induction n with
  | zero => simpa using hKL
  | succ n ih =>
      simpa [ActionableAt] using robustPre_mono prob next legal ih

end RobustActionability

/-! ## BA-6 / BA-7 — discounted Bellman contraction -/

section Bellman

variable {B A O : Type*}
variable [Fintype B] [Nonempty B]

/-- An abstract continuation evaluator.  The concrete finite-probability
expectation below is proved nonexpansive in the finite sup norm. -/
def ContinuationNonexpansive
    (E : (B → ℝ) → B → A → ℝ) : Prop :=
  ∀ V W b a, |E V b a - E W b a| ≤ ‖V - W‖

/-- One-step discounted action value. -/
def qValue
    (E : (B → ℝ) → B → A → ℝ)
    (reward : B → A → ℝ)
    (gamma : ℝ≥0)
    (V : B → ℝ) (b : B) (a : A) : ℝ :=
  reward b a + (gamma : ℝ) * E V b a

/-- A selector is greedy when it attains an action maximizing the one-step
backup for every value function and state. -/
def GreedySelector
    (E : (B → ℝ) → B → A → ℝ)
    (reward : B → A → ℝ)
    (gamma : ℝ≥0)
    (choose : (B → ℝ) → B → A) : Prop :=
  ∀ V b a, qValue E reward gamma V b a ≤
    qValue E reward gamma V b (choose V b)

/-- Restricted Bellman operator implemented through a certified greedy
selector over the declared legal action family. -/
def bellman
    (E : (B → ℝ) → B → A → ℝ)
    (reward : B → A → ℝ)
    (gamma : ℝ≥0)
    (choose : (B → ℝ) → B → A)
    (V : B → ℝ) : B → ℝ :=
  fun b => qValue E reward gamma V b (choose V b)

theorem qValue_difference_bound
    (E : (B → ℝ) → B → A → ℝ)
    (reward : B → A → ℝ)
    (gamma : ℝ≥0)
    (hE : ContinuationNonexpansive E)
    (V W : B → ℝ) (b : B) (a : A) :
    |qValue E reward gamma V b a - qValue E reward gamma W b a| ≤
      (gamma : ℝ) * ‖V - W‖ := by
  have hdiff :
      qValue E reward gamma V b a - qValue E reward gamma W b a =
        (gamma : ℝ) * (E V b a - E W b a) := by
    simp [qValue]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg gamma.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (hE V W b a) gamma.coe_nonneg

theorem bellman_pointwise_contraction
    (E : (B → ℝ) → B → A → ℝ)
    (reward : B → A → ℝ)
    (gamma : ℝ≥0)
    (choose : (B → ℝ) → B → A)
    (hE : ContinuationNonexpansive E)
    (hgreedy : GreedySelector E reward gamma choose)
    (V W : B → ℝ) (b : B) :
    |bellman E reward gamma choose V b - bellman E reward gamma choose W b| ≤
      (gamma : ℝ) * ‖V - W‖ := by
  let aV := choose V b
  let aW := choose W b
  have hVW := qValue_difference_bound E reward gamma hE V W b aV
  have hWV := qValue_difference_bound E reward gamma hE W V b aW
  have hupper :
      bellman E reward gamma choose V b - bellman E reward gamma choose W b ≤
        (gamma : ℝ) * ‖V - W‖ := by
    calc
      bellman E reward gamma choose V b - bellman E reward gamma choose W b
          ≤ qValue E reward gamma V b aV - qValue E reward gamma W b aV := by
              dsimp [bellman, aV, aW]
              linarith [hgreedy W b (choose V b)]
      _ ≤ |qValue E reward gamma V b aV - qValue E reward gamma W b aV| :=
          le_abs_self _
      _ ≤ (gamma : ℝ) * ‖V - W‖ := hVW
  have hreverse :
      bellman E reward gamma choose W b - bellman E reward gamma choose V b ≤
        (gamma : ℝ) * ‖W - V‖ := by
    calc
      bellman E reward gamma choose W b - bellman E reward gamma choose V b
          ≤ qValue E reward gamma W b aW - qValue E reward gamma V b aW := by
              dsimp [bellman, aV, aW]
              linarith [hgreedy V b (choose W b)]
      _ ≤ |qValue E reward gamma W b aW - qValue E reward gamma V b aW| :=
          le_abs_self _
      _ ≤ (gamma : ℝ) * ‖W - V‖ := hWV
  have hnorm : ‖W - V‖ = ‖V - W‖ := by
    rw [← norm_neg, neg_sub]
  rw [hnorm] at hreverse
  exact abs_le.2 ⟨by linarith, hupper⟩

/-- BA-6: the greedy restricted Bellman operator is gamma-Lipschitz in the
finite sup norm. -/
theorem bellman_lipschitz
    (E : (B → ℝ) → B → A → ℝ)
    (reward : B → A → ℝ)
    (gamma : ℝ≥0)
    (choose : (B → ℝ) → B → A)
    (hE : ContinuationNonexpansive E)
    (hgreedy : GreedySelector E reward gamma choose) :
    LipschitzWith gamma (bellman E reward gamma choose) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro V W
  rw [dist_eq_norm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonempty).2
  intro b
  simpa [Pi.sub_apply, Real.norm_eq_abs] using
    bellman_pointwise_contraction E reward gamma choose hE hgreedy V W b

/-- The Bellman operator is a contraction whenever `gamma < 1`. -/
theorem bellman_contracting
    (E : (B → ℝ) → B → A → ℝ)
    (reward : B → A → ℝ)
    (gamma : ℝ≥0)
    (choose : (B → ℝ) → B → A)
    (hE : ContinuationNonexpansive E)
    (hgreedy : GreedySelector E reward gamma choose)
    (hgamma : gamma < 1) :
    ContractingWith gamma (bellman E reward gamma choose) := by
  exact ⟨hgamma, bellman_lipschitz E reward gamma choose hE hgreedy⟩

/-- BA-7: Banach gives a unique discounted Bellman fixed point. -/
theorem bellman_exists_unique_fixedPoint
    (E : (B → ℝ) → B → A → ℝ)
    (reward : B → A → ℝ)
    (gamma : ℝ≥0)
    (choose : (B → ℝ) → B → A)
    (hE : ContinuationNonexpansive E)
    (hgreedy : GreedySelector E reward gamma choose)
    (hgamma : gamma < 1) :
    ∃! V : B → ℝ, IsFixedPt (bellman E reward gamma choose) V := by
  let hT : ContractingWith gamma (bellman E reward gamma choose) :=
    bellman_contracting E reward gamma choose hE hgreedy hgamma
  let Vstar : B → ℝ := ContractingWith.fixedPoint _ hT
  refine ⟨Vstar, ?_, ?_⟩
  · exact hT.fixedPoint_isFixedPt
  · intro W hW
    exact hT.fixedPoint_unique hW

end Bellman

/-! ### Concrete finite expectation is nonexpansive -/

section FiniteExpectation

variable {B A O : Type*}
variable [Fintype B] [Nonempty B] [Fintype O]

structure ObservationProbKernel (B A O : Type*) [Fintype O] where
  mass : B → A → O → ℝ
  nonneg : ∀ b a o, 0 ≤ mass b a o
  sum_eq_one : ∀ b a, ∑ o, mass b a o = 1

def expectedContinuation
    (K : ObservationProbKernel B A O)
    (next : B → A → O → B)
    (V : B → ℝ) (b : B) (a : A) : ℝ :=
  ∑ o, K.mass b a o * V (next b a o)

theorem component_difference_le_supNorm
    (V W : B → ℝ) (x : B) :
    |V x - W x| ≤ ‖V - W‖ := by
  have h := (pi_norm_le_iff_of_nonempty (f := V - W) (r := ‖V - W‖)).1 le_rfl x
  simpa [Pi.sub_apply, Real.norm_eq_abs] using h

theorem expectedContinuation_nonexpansive
    (K : ObservationProbKernel B A O)
    (next : B → A → O → B) :
    ContinuationNonexpansive (expectedContinuation K next) := by
  intro V W b a
  rw [expectedContinuation, expectedContinuation, Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    |∑ o, K.mass b a o * (V (next b a o) - W (next b a o))|
        ≤ ∑ o, |K.mass b a o * (V (next b a o) - W (next b a o))| :=
          abs_sum_le_sum_abs _
    _ = ∑ o, K.mass b a o * |V (next b a o) - W (next b a o)| := by
          apply Finset.sum_congr rfl
          intro o ho
          rw [abs_mul, abs_of_nonneg (K.nonneg b a o)]
    _ ≤ ∑ o, K.mass b a o * ‖V - W‖ := by
          apply Finset.sum_le_sum
          intro o ho
          exact mul_le_mul_of_nonneg_left
            (component_difference_le_supNorm V W (next b a o))
            (K.nonneg b a o)
    _ = ‖V - W‖ := by
          rw [← Finset.sum_mul, K.sum_eq_one]
          simp

end FiniteExpectation

/-! ## BA-8 — exact dual-effect witness -/

section DualEffectWitness

inductive Model2 where
  | m0 | m1
  deriving DecidableEq, Fintype, Repr

inductive Phys4 where
  | start | ready | goal | fail
  deriving DecidableEq, Fintype, Repr

inductive Act3 where
  | diagnosePrepare | act0 | act1
  deriving DecidableEq, Fintype, Repr

/-- Physical transition in the full witness. -/
def fullStep (theta : Model2) (s : Phys4) (a : Act3) : Phys4 :=
  match s, a with
  | .start, .diagnosePrepare => .ready
  | .ready, .act0 => if theta = .m0 then .goal else .fail
  | .ready, .act1 => if theta = .m1 then .goal else .fail
  | .goal, _ => .goal
  | _, _ => .fail

/-- The dual-effect action reveals the model identity. -/
def fullObservation (theta : Model2) (a : Act3) : Model2 :=
  match a with
  | .diagnosePrepare => theta
  | _ => .m0

/-- Second action selected from the observation produced by the first action. -/
def adaptiveCommit : Model2 → Act3
  | .m0 => .act0
  | .m1 => .act1

def fullFinal (theta : Model2) : Phys4 :=
  let s1 := fullStep theta .start .diagnosePrepare
  let o1 := fullObservation theta .diagnosePrepare
  fullStep theta s1 (adaptiveCommit o1)

theorem full_dual_effect_succeeds (theta : Model2) :
    fullFinal theta = .goal := by
  cases theta <;> rfl

/-- Information-only ablation: reveal theta but do not physically prepare the
system. -/
def infoOnlyStep (theta : Model2) (s : Phys4) (a : Act3) : Phys4 :=
  match s, a with
  | .start, .diagnosePrepare => .start
  | .ready, .act0 => if theta = .m0 then .goal else .fail
  | .ready, .act1 => if theta = .m1 then .goal else .fail
  | .goal, _ => .goal
  | _, _ => .fail

def infoOnlyFinal (theta : Model2) : Phys4 :=
  let s1 := infoOnlyStep theta .start .diagnosePrepare
  let o1 := fullObservation theta .diagnosePrepare
  infoOnlyStep theta s1 (adaptiveCommit o1)

theorem info_only_ablation_fails (theta : Model2) :
    infoOnlyFinal theta ≠ .goal := by
  cases theta <;> decide

/-- Control-only ablation: physically prepare, but emit an uninformative fixed
observation. -/
def controlOnlyObservation (_theta : Model2) (_a : Act3) : Model2 := .m0

def controlOnlyFinal (theta : Model2) : Phys4 :=
  let s1 := fullStep theta .start .diagnosePrepare
  let o1 := controlOnlyObservation theta .diagnosePrepare
  fullStep theta s1 (adaptiveCommit o1)

theorem control_only_ablation_fails_for_m1 :
    controlOnlyFinal .m1 ≠ .goal := by decide

/-- Functional intervention roles are not exclusive constructors. -/
structure InterventionRole where
  probe : Bool
  repair : Bool
  deriving DecidableEq, Repr

def probeRepair : InterventionRole := ⟨true, true⟩

@[simp] theorem probeRepair_is_both :
    probeRepair.probe = true ∧ probeRepair.repair = true := by
  exact ⟨rfl, rfl⟩

end DualEffectWitness

/-! ## BA-9 — capability can make model identity action-irrelevant -/

section CapabilityModelForgetting

inductive CapAction where
  | act0 | act1 | universal
  deriving DecidableEq, Fintype, Repr

/-- Success relation in the ready state. -/
def capSuccess : Model2 → CapAction → Bool
  | .m0, .act0 => true
  | .m1, .act1 => true
  | _, .universal => true
  | _, _ => false

/-- Base capability set has no action that succeeds for both possible models. -/
theorem base_capability_requires_model_distinction :
    ¬ ∃ a : CapAction,
      (a = .act0 ∨ a = .act1) ∧
      capSuccess .m0 a = true ∧ capSuccess .m1 a = true := by
  decide

/-- Adding one universal action makes the same coarse 50/50 model ambiguity
irrelevant to the terminal action choice. -/
theorem expanded_capability_erases_model_requirement :
    ∃ a : CapAction,
      capSuccess .m0 a = true ∧ capSuccess .m1 a = true := by
  exact ⟨.universal, rfl, rfl⟩

end CapabilityModelForgetting

end BayesAdaptiveKernel
end Insacermo
