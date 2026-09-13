import InteractionOrderBoundaryKernelV1

namespace InsacermoInteractionOrderSharpness

open Finset
open InsacermoInteractionOrderBoundary

/-- The completely flat zero-interaction world. -/
def ZeroCoeff {Req : Type*} : Finset Req → Nat := fun _ => 0

/-- A pure (r+1)-way interaction: the only nonzero coefficient is on a
coalition of cardinality r+1. On Fin (r+1), that coalition is necessarily the
full universe. -/
def PureTopCoeff (r M : Nat) : Finset (Fin (r + 1)) → Nat :=
  fun T => if T.card = r + 1 then M else 0

theorem zeroCoeff_orderBounded
    {Req : Type*} [DecidableEq Req] (r : Nat) :
    OrderBounded r (ZeroCoeff (Req := Req)) := by
  intro T hT
  rfl

theorem pureTopCoeff_orderBounded (r M : Nat) :
    OrderBounded (r + 1) (PureTopCoeff r M) := by
  intro T hT
  have hle : T.card ≤ r + 1 := by
    simpa using Finset.card_le_card (Finset.subset_univ T)
  omega

/-- The pure top-order coefficient vanishes on every coalition of size at most
r. -/
theorem pureTopCoeff_zero_through_r
    (r M : Nat) (T : Finset (Fin (r + 1)))
    (hT : T.card ≤ r) :
    PureTopCoeff r M T = 0 := by
  unfold PureTopCoeff
  split
  · rename_i hEq
    omega
  · rfl

/-- The zero world has zero price on every coalition. -/
theorem zeroPrice
    {Req : Type*} [DecidableEq Req] (S : Finset Req) :
    InteractionPrice (ZeroCoeff (Req := Req)) S = 0 := by
  simp [InteractionPrice, ZeroCoeff]

/-- A pure (r+1)-way interaction is completely invisible on all coalitions of
size at most r. -/
theorem pureTopPrice_zero_through_r
    (r M : Nat) (S : Finset (Fin (r + 1)))
    (hS : S.card ≤ r) :
    InteractionPrice (PureTopCoeff r M) S = 0 := by
  unfold InteractionPrice
  rw [pureTopCoeff_zero_through_r r M S hS]
  simp only [zero_add]
  apply Finset.sum_eq_zero
  intro T hT
  have hsub : T ⊂ S := Finset.mem_ssubsets.mp hT
  have hlt : T.card < S.card := Finset.card_lt_card hsub
  exact pureTopCoeff_zero_through_r r M T (by omega)

/-- Hence the flat world and the pure (r+1)-interaction world agree on the
entire audit profile through order r. -/
theorem pureTop_local_eq_through_r (r M : Nat) :
    LocalPriceEqThrough r
      (ZeroCoeff (Req := Fin (r + 1)))
      (PureTopCoeff r M) := by
  intro S hS
  rw [zeroPrice S, pureTopPrice_zero_through_r r M S hS]

/-- Every proper coalition is invisible to the pure top-order interaction. -/
theorem pureTop_equal_on_every_proper_coalition
    (r M : Nat) (S : Finset (Fin (r + 1)))
    (hproper : S ≠ Finset.univ) :
    InteractionPrice (ZeroCoeff (Req := Fin (r + 1))) S =
      InteractionPrice (PureTopCoeff r M) S := by
  have hss : S ⊂ (Finset.univ : Finset (Fin (r + 1))) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, hproper⟩
  have hlt : S.card < (Finset.univ : Finset (Fin (r + 1))).card :=
    Finset.card_lt_card hss
  have huniv : (Finset.univ : Finset (Fin (r + 1))).card = r + 1 := by
    simp
  have hS : S.card ≤ r := by
    omega
  rw [zeroPrice S, pureTopPrice_zero_through_r r M S hS]

/-- The pure top-order world has full-contract price exactly M. -/
theorem pureTop_full_price (r M : Nat) :
    InteractionPrice (PureTopCoeff r M)
      (Finset.univ : Finset (Fin (r + 1))) = M := by
  unfold InteractionPrice
  have hhead : PureTopCoeff r M
      (Finset.univ : Finset (Fin (r + 1))) = M := by
    simp [PureTopCoeff]
  rw [hhead]
  have hsum :
      (Finset.univ : Finset (Fin (r + 1))).ssubsets.sum
        (PureTopCoeff r M) = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    have hsub : T ⊂ (Finset.univ : Finset (Fin (r + 1))) :=
      Finset.mem_ssubsets.mp hT
    have hlt : T.card < (Finset.univ : Finset (Fin (r + 1))).card :=
      Finset.card_lt_card hsub
    have huniv : (Finset.univ : Finset (Fin (r + 1))).card = r + 1 := by
      simp
    have hTle : T.card ≤ r := by
      omega
    exact pureTopCoeff_zero_through_r r M T hTle
  simp [hsum]

/-- SHARPNESS V1.

For every audit order r and every positive M there are two order-(r+1)
interaction models on r+1 obligations which agree on every coalition of size
at most r -- indeed on every proper coalition -- but differ on the full
contract by M. Thus the order-r upper bound is sharp. -/
theorem interaction_order_sharpness_v1
    (r M : Nat) (hM : 0 < M) :
    ∃ cA cB : Finset (Fin (r + 1)) → Nat,
      OrderBounded (r + 1) cA ∧
      OrderBounded (r + 1) cB ∧
      LocalPriceEqThrough r cA cB ∧
      (∀ S : Finset (Fin (r + 1)), S ≠ Finset.univ →
        InteractionPrice cA S = InteractionPrice cB S) ∧
      InteractionPrice cA Finset.univ = 0 ∧
      InteractionPrice cB Finset.univ = M ∧
      InteractionPrice cA Finset.univ ≠ InteractionPrice cB Finset.univ := by
  refine ⟨ZeroCoeff (Req := Fin (r + 1)), PureTopCoeff r M, ?_⟩
  constructor
  · exact zeroCoeff_orderBounded (Req := Fin (r + 1)) (r + 1)
  constructor
  · exact pureTopCoeff_orderBounded r M
  constructor
  · exact pureTop_local_eq_through_r r M
  constructor
  · intro S hS
    exact pureTop_equal_on_every_proper_coalition r M S hS
  constructor
  · exact zeroPrice (Finset.univ : Finset (Fin (r + 1)))
  constructor
  · exact pureTop_full_price r M
  · rw [zeroPrice (Finset.univ : Finset (Fin (r + 1))), pureTop_full_price r M]
    omega

/-- EXACT WORST-CASE AUDIT ORDER V1.

Within order-(r+1) interaction models on Fin (r+1), audit through order r+1
always determines every coalition price, while audit only through order r can
fail. Therefore the worst-case exact audit order is r+1. -/
theorem exact_worst_case_audit_order_v1
    (r M : Nat) (hM : 0 < M) :
    (∀ cA cB : Finset (Fin (r + 1)) → Nat,
      OrderBounded (r + 1) cA →
      OrderBounded (r + 1) cB →
      LocalPriceEqThrough (r + 1) cA cB →
      ∀ S : Finset (Fin (r + 1)),
        InteractionPrice cA S = InteractionPrice cB S) ∧
    (∃ cA cB : Finset (Fin (r + 1)) → Nat,
      OrderBounded (r + 1) cA ∧
      OrderBounded (r + 1) cB ∧
      LocalPriceEqThrough r cA cB ∧
      InteractionPrice cA Finset.univ ≠ InteractionPrice cB Finset.univ) := by
  constructor
  · intro cA cB hA hB hlocal S
    exact all_prices_equal_of_order_r_local_equality
      (r + 1) cA cB hA hB hlocal S
  · obtain ⟨cA, cB, hA, hB, hlocal, hproper, hzero, hfull, hne⟩ :=
      interaction_order_sharpness_v1 r M hM
    exact ⟨cA, cB, hA, hB, hlocal, hne⟩

end InsacermoInteractionOrderSharpness
