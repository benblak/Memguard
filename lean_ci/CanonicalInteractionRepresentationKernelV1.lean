import Mathlib
import SignedInteractionZeroCutKernelV1

namespace InsacermoCanonicalInteractionRepresentation

open Finset
open InsacermoSignedInteractionZeroCut

/-- A coefficient system represents a finite coalition-price function when every
price is the sum of coefficients supported inside that coalition. -/
def Represents {Req : Type*} [DecidableEq Req]
    (P : Finset Req → Int) (c : Finset Req → Int) : Prop :=
  ∀ S, P S = S.powerset.sum c

/-- Canonical triangular Möbius coefficients, defined recursively over strict
subset cardinality. -/
def CanonicalCoeff {Req : Type*} [DecidableEq Req]
    (P : Finset Req → Int) (S : Finset Req) : Int :=
  P S - S.ssubsets.sum (fun T => CanonicalCoeff P T)
termination_by S.card
decreasing_by
  simp_all only [Finset.mem_ssubsets]
  exact Finset.card_lt_card ‹_›

/-- The canonical coefficient closes the triangular reconstruction equation on
its own coalition. -/
theorem canonicalCoeff_add_strict_sum
    {Req : Type*} [DecidableEq Req]
    (P : Finset Req → Int) (S : Finset Req) :
    CanonicalCoeff P S + S.ssubsets.sum (CanonicalCoeff P) = P S := by
  rw [CanonicalCoeff]
  omega

/-- The powerset sum splits into the coefficient on S plus the sum over strict
subsets. -/
theorem powerset_sum_eq_self_add_strict
    {Req : Type*} [DecidableEq Req]
    (c : Finset Req → Int) (S : Finset Req) :
    S.powerset.sum c = c S + S.ssubsets.sum c := by
  rw [Finset.ssubsets]
  have h := Finset.sum_erase_add S.powerset c (Finset.mem_powerset_self S)
  simpa [add_comm] using h

/-- Existence: every finite integer-valued coalition-price function is exactly
reconstructed by its canonical triangular coefficients. -/
theorem canonicalCoeff_represents
    {Req : Type*} [DecidableEq Req]
    (P : Finset Req → Int) : Represents P (CanonicalCoeff P) := by
  intro S
  rw [powerset_sum_eq_self_add_strict]
  exact (canonicalCoeff_add_strict_sum P S).symm

/-- Local uniqueness step: if two coefficient systems reconstruct the same
price on S and already agree on every strict subset of S, then they agree on S. -/
theorem coefficient_eq_of_strict_agreement
    {Req : Type*} [DecidableEq Req]
    {P : Finset Req → Int} {a b : Finset Req → Int} {S : Finset Req}
    (ha : P S = S.powerset.sum a)
    (hb : P S = S.powerset.sum b)
    (hstrict : ∀ T ∈ S.ssubsets, a T = b T) :
    a S = b S := by
  rw [powerset_sum_eq_self_add_strict] at ha hb
  have hsums : S.ssubsets.sum a = S.ssubsets.sum b := by
    apply Finset.sum_congr rfl
    intro T hT
    exact hstrict T hT
  omega

/-- Global uniqueness of the interaction representation. -/
theorem representation_unique
    {Req : Type*} [DecidableEq Req]
    {P : Finset Req → Int} {a b : Finset Req → Int}
    (ha : Represents P a) (hb : Represents P b) :
    a = b := by
  funext S
  induction S using Finset.strongInductionOn with
  | h S ih =>
      apply coefficient_eq_of_strict_agreement (ha S) (hb S)
      intro T hT
      have hsub : T ⊂ S := Finset.mem_ssubsets.mp hT
      exact ih T hsub

/-- Canonicality: any coefficient system representing P is exactly the
canonical coefficient system. -/
theorem representing_coefficients_eq_canonical
    {Req : Type*} [DecidableEq Req]
    (P : Finset Req → Int) (c : Finset Req → Int)
    (hc : Represents P c) :
    c = CanonicalCoeff P := by
  exact representation_unique hc (canonicalCoeff_represents P)

/-- Every finite price has one and only one signed interaction representation. -/
theorem exists_unique_interaction_representation
    {Req : Type*} [DecidableEq Req]
    (P : Finset Req → Int) :
    ∃! c : Finset Req → Int, Represents P c := by
  refine ⟨CanonicalCoeff P, canonicalCoeff_represents P, ?_⟩
  intro c hc
  exact representing_coefficients_eq_canonical P c hc

/-- On a finite full contract Q, the canonical representation turns the signed
zero-cut theorem into an identity determined by P itself. -/
theorem canonical_zero_cut
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (P : Finset Req → Int) (S : Finset Req) :
    P S = P (Finset.univ : Finset Req) ↔
      OmittedMass (CanonicalCoeff P) S = 0 := by
  have hrep := canonicalCoeff_represents P
  rw [hrep S, hrep (Finset.univ : Finset Req)]
  exact full_price_iff_zero_omitted_mass (CanonicalCoeff P) S

/-- CANONICAL INTERACTION REPRESENTATION KERNEL V1.

Every integer-valued set function on finite coalitions has a unique signed
interaction decomposition. The coefficients are therefore not chosen modeling
features: they are determined uniquely by the price function. On finite full
contracts, equality with global price is canonically equivalent to zero omitted
interaction mass. -/
theorem canonical_interaction_representation_v1
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (P : Finset Req → Int) :
    Represents P (CanonicalCoeff P) ∧
    (∀ c : Finset Req → Int, Represents P c → c = CanonicalCoeff P) ∧
    (∀ S : Finset Req,
      P S = P (Finset.univ : Finset Req) ↔
        OmittedMass (CanonicalCoeff P) S = 0) := by
  constructor
  · exact canonicalCoeff_represents P
  constructor
  · intro c hc
    exact representing_coefficients_eq_canonical P c hc
  · intro S
    exact canonical_zero_cut P S

end InsacermoCanonicalInteractionRepresentation
