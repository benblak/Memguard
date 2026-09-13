import InteractionOrderBoundaryKernelV1

namespace InsacermoInteractionDiscrepancyDepth

open Finset
open InsacermoInteractionOrderBoundary

/-- Equality of interaction coefficients through order r. -/
def LocalCoeffEqThrough {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat) : Prop :=
  ∀ T : Finset Req, T.card ≤ r → cA T = cB T

/-- Equality of coefficients through order r implies equality of prices through
order r. -/
theorem local_prices_equal_of_local_coefficients_equal
    {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat)
    (hcoeff : LocalCoeffEqThrough r cA cB) :
    LocalPriceEqThrough r cA cB := by
  intro S hSr
  unfold InteractionPrice
  have hhead : cA S = cB S := hcoeff S hSr
  have hsum : S.ssubsets.sum cA = S.ssubsets.sum cB := by
    apply Finset.sum_congr rfl
    intro T hT
    have hsub : T ⊂ S := Finset.mem_ssubsets.mp hT
    have hlt : T.card < S.card := Finset.card_lt_card hsub
    exact hcoeff T (by omega)
  rw [hhead, hsum]

/-- Exact local inversion: price equality through order r is equivalent to
coefficient equality through order r. -/
theorem local_price_eq_iff_local_coeff_eq
    {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat) :
    LocalPriceEqThrough r cA cB ↔ LocalCoeffEqThrough r cA cB := by
  constructor
  · intro hprice
    exact coefficients_equal_through_order r cA cB hprice
  · intro hcoeff
    exact local_prices_equal_of_local_coefficients_equal r cA cB hcoeff

/-- The first exact order at which prices can differ: all smaller coalitions
agree, and some coalition of cardinality exactly r differs. -/
def FirstPriceDifferenceAt {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat) : Prop :=
  (∀ S : Finset Req, S.card < r → InteractionPrice cA S = InteractionPrice cB S) ∧
  (∃ S : Finset Req, S.card = r ∧ InteractionPrice cA S ≠ InteractionPrice cB S)

/-- The first exact order at which interaction coefficients differ. -/
def FirstCoeffDifferenceAt {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat) : Prop :=
  (∀ T : Finset Req, T.card < r → cA T = cB T) ∧
  (∃ T : Finset Req, T.card = r ∧ cA T ≠ cB T)

/-- If all lower-order prices agree, then all lower-order coefficients agree. -/
theorem lower_coefficients_equal_of_lower_prices_equal
    {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat)
    (hlow : ∀ S : Finset Req, S.card < r →
      InteractionPrice cA S = InteractionPrice cB S) :
    ∀ T : Finset Req, T.card < r → cA T = cB T := by
  intro T hTr
  have hlocal : LocalPriceEqThrough (r - 1) cA cB := by
    intro S hS
    by_cases hr0 : r = 0
    · subst hr0
      omega
    · have hslt : S.card < r := by omega
      exact hlow S hslt
  have hcoeff := (local_price_eq_iff_local_coeff_eq (r - 1) cA cB).mp hlocal
  exact hcoeff T (by omega)

/-- If all lower-order coefficients agree, then all lower-order prices agree. -/
theorem lower_prices_equal_of_lower_coefficients_equal
    {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat)
    (hlow : ∀ T : Finset Req, T.card < r → cA T = cB T) :
    ∀ S : Finset Req, S.card < r →
      InteractionPrice cA S = InteractionPrice cB S := by
  intro S hSr
  unfold InteractionPrice
  have hhead : cA S = cB S := hlow S hSr
  have hsum : S.ssubsets.sum cA = S.ssubsets.sum cB := by
    apply Finset.sum_congr rfl
    intro T hT
    have hsub : T ⊂ S := Finset.mem_ssubsets.mp hT
    have hlt : T.card < S.card := Finset.card_lt_card hsub
    exact hlow T (by omega)
  rw [hhead, hsum]

/-- At the first differing order r, once every proper subcoalition agrees, price
difference on a size-r coalition is equivalent to coefficient difference on
that coalition. -/
theorem price_diff_iff_coeff_diff_at_exact_order
    {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat)
    (hlow : ∀ T : Finset Req, T.card < r → cA T = cB T)
    (S : Finset Req) (hSr : S.card = r) :
    InteractionPrice cA S ≠ InteractionPrice cB S ↔ cA S ≠ cB S := by
  unfold InteractionPrice
  have hsum : S.ssubsets.sum cA = S.ssubsets.sum cB := by
    apply Finset.sum_congr rfl
    intro T hT
    have hsub : T ⊂ S := Finset.mem_ssubsets.mp hT
    have hlt : T.card < S.card := Finset.card_lt_card hsub
    exact hlow T (by omega)
  rw [hsum]
  constructor
  · intro hdiff hEq
    exact hdiff (by rw [hEq])
  · intro hdiff hEq
    apply hdiff
    exact Nat.add_right_cancel hEq

/-- EXACT DISCREPANCY DEPTH V1.

The first coalition size at which two interaction-price worlds become
distinguishable is exactly the first coalition size at which their interaction
coefficients differ. This requires no global order bound. -/
theorem interaction_discrepancy_depth_v1
    {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat) :
    FirstPriceDifferenceAt r cA cB ↔ FirstCoeffDifferenceAt r cA cB := by
  constructor
  · rintro ⟨hlowPrice, ⟨S, hSr, hSdiff⟩⟩
    have hlowCoeff := lower_coefficients_equal_of_lower_prices_equal r cA cB hlowPrice
    refine ⟨hlowCoeff, ?_⟩
    refine ⟨S, hSr, ?_⟩
    exact (price_diff_iff_coeff_diff_at_exact_order r cA cB hlowCoeff S hSr).mp hSdiff
  · rintro ⟨hlowCoeff, ⟨S, hSr, hSdiff⟩⟩
    have hlowPrice := lower_prices_equal_of_lower_coefficients_equal r cA cB hlowCoeff
    refine ⟨hlowPrice, ?_⟩
    refine ⟨S, hSr, ?_⟩
    exact (price_diff_iff_coeff_diff_at_exact_order r cA cB hlowCoeff S hSr).mpr hSdiff

end InsacermoInteractionDiscrepancyDepth
