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

/-- For the subset order on finite coalitions, `Iic S` is exactly the powerset of `S`. -/
theorem powerset_eq_Iic
    {Req : Type*} [DecidableEq Req] (S : Finset Req) :
    S.powerset = Finset.Iic S := by
  ext T
  simp

/-- Canonical signed interaction coefficients: the Möbius transform of the price
function on the Boolean subset poset. -/
def CanonicalCoeff {Req : Type*} [DecidableEq Req]
    (P : Finset Req → Int) (S : Finset Req) : Int :=
  ∑ T ∈ Finset.Iic S, IncidenceAlgebra.mu Int T S * P T

/-- Möbius inversion reconstructs every price exactly from its canonical
interaction coefficients. -/
theorem canonicalCoeff_sum_Iic
    {Req : Type*} [DecidableEq Req]
    (P : Finset Req → Int) (S : Finset Req) :
    (Finset.Iic S).sum (CanonicalCoeff P) = P S := by
  classical
  calc
    ∑ y ∈ Finset.Iic S, CanonicalCoeff P y =
        ∑ y ∈ Finset.Iic S, ∑ z ∈ Finset.Iic y,
          IncidenceAlgebra.mu Int z y * P z := by
            simp_rw [CanonicalCoeff]
    _ = ∑ z ∈ Finset.Iic S, ∑ y ∈ Finset.Icc z S,
          IncidenceAlgebra.mu Int z y * P z := by
            rw [Finset.sum_sigma' (Finset.Iic S) fun y => Finset.Iic y]
            rw [Finset.sum_sigma' (Finset.Iic S) fun z => Finset.Icc z S]
            apply Finset.sum_nbij' (fun ⟨a, b⟩ => ⟨b, a⟩) (fun ⟨a, b⟩ => ⟨b, a⟩) <;>
              aesop (add simp mul_assoc) (add unsafe le_trans)
    _ = ∑ z ∈ Finset.Iic S,
          (IncidenceAlgebra.mu Int * IncidenceAlgebra.zeta Int :
            IncidenceAlgebra Int (Finset Req)) z S * P z := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [IncidenceAlgebra.mul_apply, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro y hy
            have hys : y ≤ S := (Finset.mem_Icc.mp hy).2
            rw [IncidenceAlgebra.zeta_of_le hys, mul_one]
    _ = P S := by
            rw [IncidenceAlgebra.mu_mul_zeta Int (Finset Req)]
            simp

/-- Existence: every integer-valued coalition-price function is exactly
reconstructed by its canonical Möbius coefficients. -/
theorem canonicalCoeff_represents
    {Req : Type*} [DecidableEq Req]
    (P : Finset Req → Int) : Represents P (CanonicalCoeff P) := by
  intro S
  rw [powerset_eq_Iic]
  exact (canonicalCoeff_sum_Iic P S).symm

/-- Canonicality: any coefficient system representing `P` is exactly its Möbius
transform. This is the uniqueness direction of Möbius inversion. -/
theorem representing_coefficients_eq_canonical
    {Req : Type*} [DecidableEq Req]
    (P : Finset Req → Int) (c : Finset Req → Int)
    (hc : Represents P c) :
    c = CanonicalCoeff P := by
  funext S
  have hrepr : ∀ x : Finset Req, P x = ∑ y ∈ Finset.Iic x, c y := by
    intro x
    rw [← powerset_eq_Iic x]
    exact hc x
  have hinv := IncidenceAlgebra.moebius_inversion_bot c P hrepr S
  simpa [CanonicalCoeff] using hinv

/-- Global uniqueness of the interaction representation. -/
theorem representation_unique
    {Req : Type*} [DecidableEq Req]
    {P : Finset Req → Int} {a b : Finset Req → Int}
    (ha : Represents P a) (hb : Represents P b) :
    a = b := by
  calc
    a = CanonicalCoeff P := representing_coefficients_eq_canonical P a ha
    _ = b := (representing_coefficients_eq_canonical P b hb).symm

/-- Every finite-coalition price has one and only one signed interaction representation. -/
theorem exists_unique_interaction_representation
    {Req : Type*} [DecidableEq Req]
    (P : Finset Req → Int) :
    ∃! c : Finset Req → Int, Represents P c := by
  refine ⟨CanonicalCoeff P, canonicalCoeff_represents P, ?_⟩
  intro c hc
  exact representing_coefficients_eq_canonical P c hc

/-- On a finite full contract, the canonical representation turns the signed
zero-cut theorem into an identity determined by `P` itself. -/
theorem canonical_zero_cut
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (P : Finset Req → Int) (S : Finset Req) :
    P S = P (Finset.univ : Finset Req) ↔
      OmittedMass (CanonicalCoeff P) S = 0 := by
  have hrep : Represents P (CanonicalCoeff P) := canonicalCoeff_represents P
  have hS := hrep S
  have hU := hrep (Finset.univ : Finset Req)
  rw [hS, hU]
  exact full_price_iff_zero_omitted_mass (CanonicalCoeff P) S

/-- CANONICAL INTERACTION REPRESENTATION KERNEL V1.

Every integer-valued set function on finite coalitions has a unique signed
interaction decomposition, namely its Möbius transform on the Boolean subset
poset. Thus the interaction coefficients are determined by the price function,
not chosen as modeling features. On finite full contracts, equality with global
price is canonically equivalent to zero omitted interaction mass. -/
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
