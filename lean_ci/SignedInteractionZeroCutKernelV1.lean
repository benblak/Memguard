import Mathlib

namespace InsacermoSignedInteractionZeroCut

open Finset

/-- Signed interaction price: total Möbius/Harsanyi mass supported inside S. -/
def SignedInteractionPrice {Req : Type*} [DecidableEq Req]
    (c : Finset Req → Int) (S : Finset Req) : Int :=
  S.powerset.sum c

/-- Signed interaction mass omitted by S relative to the full finite contract. -/
def OmittedMass {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Int) (S : Finset Req) : Int :=
  ((Finset.univ : Finset Req).powerset.filter (fun T => ¬ T ⊆ S)).sum c

/-- The full powerset splits into terms supported in S and terms omitted by S. -/
theorem full_price_eq_price_add_omitted
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Int) (S : Finset Req) :
    SignedInteractionPrice c (Finset.univ : Finset Req) =
      SignedInteractionPrice c S + OmittedMass c S := by
  unfold SignedInteractionPrice OmittedMass
  let U : Finset (Finset Req) := (Finset.univ : Finset Req).powerset
  let A : Finset (Finset Req) := U.filter (fun T => T ⊆ S)
  let B : Finset (Finset Req) := U.filter (fun T => ¬ T ⊆ S)
  have hU : U = A ∪ B := by
    ext T
    simp [U, A, B]
  have hdis : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro T hTA hTB
    simp [A] at hTA
    simp [B] at hTB
    exact hTB hTA.2
  rw [hU, Finset.sum_union hdis]
  have hA : A = S.powerset := by
    ext T
    simp [A, U]
  have hB : B = (Finset.univ : Finset Req).powerset.filter (fun T => ¬ T ⊆ S) := by
    rfl
  simp [hA, hB]

/-- Exact zero-cut criterion: S has full global signed price iff all omitted
interaction mass cancels to zero. -/
theorem full_price_iff_zero_omitted_mass
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Int) (S : Finset Req) :
    SignedInteractionPrice c S = SignedInteractionPrice c (Finset.univ : Finset Req) ↔
      OmittedMass c S = 0 := by
  have h := full_price_eq_price_add_omitted c S
  constructor
  · intro hp
    rw [← hp] at h
    omega
  · intro hz
    rw [hz, add_zero] at h
    exact h.symm

/-- Minimal signed counterexample: two singleton interactions cancel globally. -/
def CancelCoeff : Finset (Fin 2) → Int := fun T =>
  if T = ({0} : Finset (Fin 2)) then 1
  else if T = ({1} : Finset (Fin 2)) then -1
  else 0

theorem cancelCoeff_singleton_zero : CancelCoeff ({0} : Finset (Fin 2)) = 1 := by
  simp [CancelCoeff]

theorem cancelCoeff_singleton_one : CancelCoeff ({1} : Finset (Fin 2)) = -1 := by
  simp [CancelCoeff]

theorem cancel_empty_price : SignedInteractionPrice CancelCoeff (∅ : Finset (Fin 2)) = 0 := by
  simp [SignedInteractionPrice, CancelCoeff]

theorem cancel_full_price :
    SignedInteractionPrice CancelCoeff (Finset.univ : Finset (Fin 2)) = 0 := by
  native_decide

/-- Cancellation destroys the unsigned carrier formula: the empty coalition
already has full price even though both singleton supports have nonzero
coefficients. -/
theorem signed_cancellation_breaks_active_union_rule :
    SignedInteractionPrice CancelCoeff (∅ : Finset (Fin 2)) =
      SignedInteractionPrice CancelCoeff (Finset.univ : Finset (Fin 2)) ∧
    CancelCoeff ({0} : Finset (Fin 2)) ≠ 0 ∧
    CancelCoeff ({1} : Finset (Fin 2)) ≠ 0 := by
  constructor
  · rw [cancel_empty_price, cancel_full_price]
  constructor
  · simp [cancelCoeff_singleton_zero]
  · simp [cancelCoeff_singleton_one]

/-- ZERO-CUT KERNEL V1.

In the signed interaction class, the exact full-price condition is zero omitted
mass, not containment of all nonzero supports. This is the cancellation-aware
replacement for the nonnegative carrier theorem. -/
theorem signed_interaction_zero_cut_v1
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Int) (S : Finset Req) :
    (SignedInteractionPrice c (Finset.univ : Finset Req) =
      SignedInteractionPrice c S + OmittedMass c S) ∧
    (SignedInteractionPrice c S = SignedInteractionPrice c (Finset.univ : Finset Req) ↔
      OmittedMass c S = 0) := by
  constructor
  · exact full_price_eq_price_add_omitted c S
  · exact full_price_iff_zero_omitted_mass c S

end InsacermoSignedInteractionZeroCut
