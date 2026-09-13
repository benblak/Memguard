import InteractionOrderBoundaryKernelV1

namespace InsacermoInteractionCarrierDepth

open Finset
open InsacermoInteractionOrderBoundary

/-- In the nonnegative interaction representation, the interaction price of a
coalition is the sum of all coefficients supported inside that coalition. -/
theorem interactionPrice_eq_powerset_sum
    {Req : Type*} [DecidableEq Req]
    (c : Finset Req → Nat) (S : Finset Req) :
    InteractionPrice c S = S.powerset.sum c := by
  unfold InteractionPrice
  rw [Finset.ssubsets]
  have h := Finset.sum_erase_add S.powerset c (Finset.mem_powerset_self S)
  simpa [add_comm] using h

/-- Positive interaction supports inside the full finite contract. -/
def PositiveSupports
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Nat) : Finset (Finset Req) :=
  (Finset.univ : Finset Req).powerset.filter (fun T => 0 < c T)

/-- The active interaction carrier is the union of every positive interaction
support. -/
def ActiveUnion
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Nat) : Finset Req :=
  (PositiveSupports c).biUnion id

/-- A coalition carries every positive interaction support. -/
def ActiveCarrier
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Nat) (S : Finset Req) : Prop :=
  ∀ T : Finset Req, 0 < c T → T ⊆ S

/-- Carrying all positive supports is exactly the same as containing their
union. -/
theorem activeCarrier_iff_activeUnion_subset
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Nat) (S : Finset Req) :
    ActiveCarrier c S ↔ ActiveUnion c ⊆ S := by
  constructor
  · intro h x hx
    rw [ActiveUnion] at hx
    rcases Finset.mem_biUnion.mp hx with ⟨T, hT, hxT⟩
    have hpos : 0 < c T := (Finset.mem_filter.mp hT).2
    exact h T hpos hxT
  · intro h T hpos x hxT
    apply h
    rw [ActiveUnion]
    apply Finset.mem_biUnion.mpr
    refine ⟨T, ?_, hxT⟩
    simp [PositiveSupports, hpos]

/-- Exact carrier theorem: a coalition has the full global price iff it
contains every positive interaction support. -/
theorem full_price_iff_activeCarrier
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Nat) (S : Finset Req) :
    InteractionPrice c S = InteractionPrice c (Finset.univ : Finset Req) ↔
      ActiveCarrier c S := by
  rw [interactionPrice_eq_powerset_sum, interactionPrice_eq_powerset_sum]
  have hsub : S.powerset ⊆ (Finset.univ : Finset Req).powerset :=
    Finset.powerset_mono.mpr (Finset.subset_univ S)
  constructor
  · intro heq T hpos
    by_contra hnsub
    have hTmem : T ∈ (Finset.univ : Finset Req).powerset := by simp
    have hTnot : T ∉ S.powerset := by
      simpa using hnsub
    have hlt : S.powerset.sum c <
        (Finset.univ : Finset Req).powerset.sum c := by
      exact Finset.sum_lt_sum_of_subset hsub hTmem hTnot hpos
        (fun U hU hUnot => Nat.zero_le _)
    exact (Nat.ne_of_lt hlt) heq
  · intro hcarrier
    apply Finset.sum_subset hsub
    intro T hTuniv hTnot
    have hnsub : ¬ T ⊆ S := by
      simpa using hTnot
    have hnpos : ¬ 0 < c T := by
      intro hpos
      exact hnsub (hcarrier T hpos)
    exact Nat.eq_zero_of_not_pos hnpos

/-- Strong form: full price is equivalent to containing the active interaction
union. -/
theorem full_price_iff_activeUnion_subset
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Nat) (S : Finset Req) :
    InteractionPrice c S = InteractionPrice c (Finset.univ : Finset Req) ↔
      ActiveUnion c ⊆ S := by
  exact (full_price_iff_activeCarrier c S).trans
    (activeCarrier_iff_activeUnion_subset c S)

/-- The active union itself carries the full price. -/
theorem activeUnion_has_full_price
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Nat) :
    InteractionPrice c (ActiveUnion c) =
      InteractionPrice c (Finset.univ : Finset Req) := by
  exact (full_price_iff_activeUnion_subset c (ActiveUnion c)).2
    (Finset.Subset.rfl)

/-- Every full-price coalition contains the active union. Thus the active union
is the unique least full-price carrier under inclusion. -/
theorem activeUnion_least_full_price_carrier
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Nat) (S : Finset Req)
    (hfull : InteractionPrice c S =
      InteractionPrice c (Finset.univ : Finset Req)) :
    ActiveUnion c ⊆ S := by
  exact (full_price_iff_activeUnion_subset c S).1 hfull

/-- Carrier depth: the number of distinct obligations touched by at least one
positive interaction support. -/
def CarrierDepth
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Nat) : Nat :=
  (ActiveUnion c).card

/-- Every full-price coalition has cardinality at least the carrier depth. -/
theorem carrierDepth_lower_bound
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Nat) (S : Finset Req)
    (hfull : InteractionPrice c S =
      InteractionPrice c (Finset.univ : Finset Req)) :
    CarrierDepth c ≤ S.card := by
  unfold CarrierDepth
  exact Finset.card_le_card (activeUnion_least_full_price_carrier c S hfull)

/-- The lower bound is attained exactly by the active union. -/
theorem carrierDepth_attained
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Nat) :
    ∃ S : Finset Req,
      InteractionPrice c S =
        InteractionPrice c (Finset.univ : Finset Req) ∧
      S.card = CarrierDepth c := by
  refine ⟨ActiveUnion c, activeUnion_has_full_price c, ?_⟩
  rfl

/-- INTERACTION CARRIER DEPTH V1.

For nonnegative interaction coefficients, the unique least coalition carrying
the complete global interaction price is the union of all positive interaction
supports. Therefore the minimum cardinality of a full-price coalition is
exactly the cardinality of that active union.

This separates two structural notions:
* discrepancy depth: first interaction order on which two worlds differ;
* carrier depth: number of obligations collectively touched by all positive
  price-bearing interactions. -/
theorem interaction_carrier_depth_v1
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (c : Finset Req → Nat) :
    (InteractionPrice c (ActiveUnion c) =
      InteractionPrice c (Finset.univ : Finset Req)) ∧
    (∀ S : Finset Req,
      InteractionPrice c S =
        InteractionPrice c (Finset.univ : Finset Req) ↔
      ActiveUnion c ⊆ S) ∧
    (∀ S : Finset Req,
      InteractionPrice c S =
        InteractionPrice c (Finset.univ : Finset Req) →
      CarrierDepth c ≤ S.card) ∧
    (∃ S : Finset Req,
      InteractionPrice c S =
        InteractionPrice c (Finset.univ : Finset Req) ∧
      S.card = CarrierDepth c) := by
  constructor
  · exact activeUnion_has_full_price c
  constructor
  · intro S
    exact full_price_iff_activeUnion_subset c S
  constructor
  · intro S hfull
    exact carrierDepth_lower_bound c S hfull
  · exact carrierDepth_attained c

end InsacermoInteractionCarrierDepth
