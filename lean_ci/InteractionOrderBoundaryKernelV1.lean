import Mathlib

namespace InsacermoInteractionOrderBoundary

open Finset

/-- Coalition price obtained from nonnegative interaction coefficients over all
subcoalitions: the coefficient of S itself plus all proper-subset coefficients. -/
def InteractionPrice {Req : Type*} [DecidableEq Req]
    (c : Finset Req → Nat) (S : Finset Req) : Nat :=
  c S + S.ssubsets.sum c

/-- Interaction coefficients have order at most r when every coefficient above
cardinality r vanishes. -/
def OrderBounded {Req : Type*} [DecidableEq Req]
    (r : Nat) (c : Finset Req → Nat) : Prop :=
  ∀ T : Finset Req, r < T.card → c T = 0

/-- Equality of all coalition prices through order r. -/
def LocalPriceEqThrough {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat) : Prop :=
  ∀ S : Finset Req, S.card ≤ r → InteractionPrice cA S = InteractionPrice cB S

/-- Equality of prices through order r identifies every interaction coefficient
through order r. -/
theorem coefficients_equal_through_order
    {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat)
    (hlocal : LocalPriceEqThrough r cA cB) :
    ∀ T : Finset Req, T.card ≤ r → cA T = cB T := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
      intro hTr
      have hproper : T.ssubsets.sum cA = T.ssubsets.sum cB := by
        apply Finset.sum_congr rfl
        intro U hU
        have hsub : U ⊂ T := Finset.mem_ssubsets.mp hU
        have hcardlt : U.card < T.card := Finset.card_lt_card hsub
        have hUr : U.card ≤ r := le_trans (Nat.le_of_lt hcardlt) hTr
        exact ih U hsub hUr
      have hprice := hlocal T hTr
      unfold InteractionPrice at hprice
      rw [hproper] at hprice
      exact Nat.add_right_cancel hprice

/-- If both worlds have no interactions above order r, then agreement on all
coalitions of size at most r identifies every coefficient, including those
above r (which are zero in both worlds). -/
theorem all_coefficients_equal_of_local_prices_equal
    {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat)
    (hA : OrderBounded r cA) (hB : OrderBounded r cB)
    (hlocal : LocalPriceEqThrough r cA cB) :
    ∀ T : Finset Req, cA T = cB T := by
  intro T
  by_cases hTr : T.card ≤ r
  · exact coefficients_equal_through_order r cA cB hlocal T hTr
  · have hrT : r < T.card := Nat.lt_of_not_ge hTr
    rw [hA T hrT, hB T hrT]

/-- Consequently, in an order-r interaction model, the complete price function
is determined by its restriction to coalitions of cardinality at most r. -/
theorem all_prices_equal_of_order_r_local_equality
    {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Finset Req → Nat)
    (hA : OrderBounded r cA) (hB : OrderBounded r cB)
    (hlocal : LocalPriceEqThrough r cA cB) :
    ∀ S : Finset Req, InteractionPrice cA S = InteractionPrice cB S := by
  have hc := all_coefficients_equal_of_local_prices_equal r cA cB hA hB hlocal
  intro S
  have hproper : S.ssubsets.sum cA = S.ssubsets.sum cB := by
    apply Finset.sum_congr rfl
    intro T hT
    exact hc T
  unfold InteractionPrice
  rw [hc S, hproper]

/-- Time-indexed interaction coefficients. -/
def InteractionProcess {Req : Type*} [DecidableEq Req]
    (c : Nat → Finset Req → Nat) (t : Nat) (S : Finset Req) : Nat :=
  InteractionPrice (c t) S

/-- If two temporal worlds remain order-r at every time and their complete
order-r local traces agree forever, then their full coalition-price traces also
agree forever. -/
theorem infinite_full_trace_equal_of_order_r_local_trace_equal
    {Req : Type*} [DecidableEq Req]
    (r : Nat) (cA cB : Nat → Finset Req → Nat)
    (hA : ∀ t, OrderBounded r (cA t))
    (hB : ∀ t, OrderBounded r (cB t))
    (htrace : ∀ t S, S.card ≤ r →
      InteractionProcess cA t S = InteractionProcess cB t S) :
    ∀ t S, InteractionProcess cA t S = InteractionProcess cB t S := by
  intro t S
  unfold InteractionProcess
  exact all_prices_equal_of_order_r_local_equality
    r (cA t) (cB t) (hA t) (hB t)
    (fun U hUr => by simpa [InteractionProcess] using htrace t U hUr) S

/-- INTERACTION-ORDER BOUNDARY V1.

Inside the class of nonnegative interaction models with no coefficient above
order r, an audit containing every coalition of size at most r is complete.
Therefore two such worlds cannot have identical order-r local traces while
hiding any global price divergence at any time.

Equivalently, within this interaction representation, a hidden discrepancy
beyond audit order r requires interaction support above order r. -/
theorem interaction_order_boundary_v1
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (r : Nat) (cA cB : Nat → Finset Req → Nat)
    (hA : ∀ t, OrderBounded r (cA t))
    (hB : ∀ t, OrderBounded r (cB t))
    (htrace : ∀ t S, S.card ≤ r →
      InteractionProcess cA t S = InteractionProcess cB t S) :
    (∀ t S, InteractionProcess cA t S = InteractionProcess cB t S) ∧
    (∀ t,
      InteractionProcess cA t Finset.univ =
      InteractionProcess cB t Finset.univ) ∧
    ¬ (∃ t,
      InteractionProcess cA t Finset.univ ≠
      InteractionProcess cB t Finset.univ) := by
  have hall := infinite_full_trace_equal_of_order_r_local_trace_equal
    r cA cB hA hB htrace
  constructor
  · exact hall
  constructor
  · intro t
    exact hall t Finset.univ
  · intro hex
    rcases hex with ⟨t, ht⟩
    exact ht (hall t Finset.univ)

end InsacermoInteractionOrderBoundary
