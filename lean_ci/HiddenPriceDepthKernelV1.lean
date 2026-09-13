import Mathlib
import HigherOrderPriceInteractionKernelV1

namespace InsacermoHiddenPriceDepth

open Set
open InsacermoCausalPriceFactorization
open InsacermoHigherOrderPriceInteraction

universe u v

section HiddenDepth

variable {A : Type u} {Req : Type v}

/-- A coalition is a subcritical face at threshold p when one intervention of cost < p
satisfies every obligation in the coalition. -/
def SubcriticalFace
    (cost : A → Nat) (Sat : A → Req → Prop)
    (p : Nat) (S : Finset Req) : Prop :=
  ∃ a, cost a < p ∧ GoodFor Sat S a

/-- Subcritical faces are downward closed. -/
theorem subcriticalFace_downward
    (cost : A → Nat) (Sat : A → Req → Prop) (p : Nat)
    {S T : Finset Req} (hST : S ⊆ T)
    (hT : SubcriticalFace cost Sat p T) :
    SubcriticalFace cost Sat p S := by
  rcases hT with ⟨a, hcost, hgood⟩
  refine ⟨a, hcost, ?_⟩
  intro q hq
  exact hgood q (hST hq)

/-- Every subset of a feasible full contract is feasible. -/
theorem subset_feasible_of_full
    (cost : A → Nat) (Sat : A → Req → Prop)
    {S Q : Finset Req} (hSQ : S ⊆ Q)
    (hevQ : SetFeasible cost Sat Q) :
    SetFeasible cost Sat S := by
  rcases hevQ with ⟨B, a, hcost, hgood⟩
  refine ⟨B, a, hcost, ?_⟩
  intro q hq
  exact hgood q (hSQ hq)

/-- A subset contract cannot cost more than the full contract. -/
theorem subset_price_le_full_price
    (cost : A → Nat) (Sat : A → Req → Prop)
    {S Q : Finset Req} (hSQ : S ⊆ Q)
    (hevQ : SetFeasible cost Sat Q) :
    SetPrice cost Sat S (subset_feasible_of_full cost Sat hSQ hevQ) ≤
      SetPrice cost Sat Q hevQ := by
  unfold SetPrice
  apply price_minimal
  rcases price_affordable cost (GoodFor Sat Q) hevQ with ⟨a, hcost, hgood⟩
  refine ⟨a, hcost, ?_⟩
  intro q hq
  exact hgood q (hSQ hq)

/-- Exact bridge between price and the subcritical affordability complex:
a subset has price strictly below the full price iff it is a subcritical face. -/
theorem subcriticalFace_iff_subset_price_lt_full
    (cost : A → Nat) (Sat : A → Req → Prop)
    {S Q : Finset Req} (hSQ : S ⊆ Q)
    (hevQ : SetFeasible cost Sat Q) :
    SubcriticalFace cost Sat (SetPrice cost Sat Q hevQ) S ↔
      SetPrice cost Sat S (subset_feasible_of_full cost Sat hSQ hevQ) <
        SetPrice cost Sat Q hevQ := by
  constructor
  · rintro ⟨a, hcost, hgood⟩
    have hmin :
        SetPrice cost Sat S (subset_feasible_of_full cost Sat hSQ hevQ) ≤ cost a := by
      unfold SetPrice
      apply price_minimal
      exact ⟨a, le_rfl, hgood⟩
    exact lt_of_le_of_lt hmin hcost
  · intro hlt
    rcases exists_price_attainer
      cost (GoodFor Sat S) (subset_feasible_of_full cost Sat hSQ hevQ) with
      ⟨a, hcost, hgood⟩
    refine ⟨a, ?_, hgood⟩
    rw [hcost]
    exact hlt

/-- Since every subset price is bounded above by the full price, failure to be a
subcritical face is exactly equality with the full price. -/
theorem not_subcriticalFace_iff_subset_price_eq_full
    (cost : A → Nat) (Sat : A → Req → Prop)
    {S Q : Finset Req} (hSQ : S ⊆ Q)
    (hevQ : SetFeasible cost Sat Q) :
    (¬ SubcriticalFace cost Sat (SetPrice cost Sat Q hevQ) S) ↔
      SetPrice cost Sat S (subset_feasible_of_full cost Sat hSQ hevQ) =
        SetPrice cost Sat Q hevQ := by
  have hle := subset_price_le_full_price cost Sat hSQ hevQ
  constructor
  · intro hnf
    have hnlt :
        ¬ SetPrice cost Sat S (subset_feasible_of_full cost Sat hSQ hevQ) <
          SetPrice cost Sat Q hevQ := by
      intro hlt
      exact hnf ((subcriticalFace_iff_subset_price_lt_full cost Sat hSQ hevQ).2 hlt)
    exact Nat.le_antisymm hle (Nat.le_of_not_gt hnlt)
  · intro heq hface
    have hlt := (subcriticalFace_iff_subset_price_lt_full cost Sat hSQ hevQ).1 hface
    rw [heq] at hlt
    exact (Nat.lt_irrefl _ hlt)

/-- The full contract itself is never subcritical relative to its own minimum price. -/
theorem full_not_subcriticalFace
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    ¬ SubcriticalFace cost Sat (SetPrice cost Sat Q hevQ) Q := by
  rintro ⟨a, hcost, hgood⟩
  have hmin : SetPrice cost Sat Q hevQ ≤ cost a := by
    unfold SetPrice
    apply price_minimal
    exact ⟨a, le_rfl, hgood⟩
  exact (Nat.not_le_of_lt hcost) hmin

/-- There is a subcritical obstruction of size n when some n-obligation coalition inside Q
has no witness cheaper than the full-contract price. -/
def HasSubcriticalObstructionOfSize
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (p n : Nat) : Prop :=
  ∃ S : Finset Req,
    S ⊆ Q ∧ S.card = n ∧ ¬ SubcriticalFace cost Sat p S

/-- An obstruction always exists: the full contract Q is one. -/
theorem exists_subcritical_obstruction
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    ∃ n, HasSubcriticalObstructionOfSize
      cost Sat Q (SetPrice cost Sat Q hevQ) n := by
  refine ⟨Q.card, Q, Finset.Subset.rfl, rfl, ?_⟩
  exact full_not_subcriticalFace cost Sat Q hevQ

/-- Hidden price depth: the smallest cardinality of a coalition that already forces
full-contract price. Equivalently, the minimum non-face size of the subcritical complex. -/
noncomputable def HiddenPriceDepth
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) : Nat := by
  classical
  exact Nat.find (exists_subcritical_obstruction cost Sat Q hevQ)

/-- The hidden depth is realized by an actual obstruction. -/
theorem hiddenPriceDepth_spec
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    HasSubcriticalObstructionOfSize
      cost Sat Q (SetPrice cost Sat Q hevQ)
      (HiddenPriceDepth cost Sat Q hevQ) := by
  classical
  exact Nat.find_spec (exists_subcritical_obstruction cost Sat Q hevQ)

/-- No smaller cardinality can contain a subcritical obstruction. -/
theorem no_obstruction_below_hiddenDepth
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q)
    {n : Nat} (hn : n < HiddenPriceDepth cost Sat Q hevQ) :
    ¬ HasSubcriticalObstructionOfSize
      cost Sat Q (SetPrice cost Sat Q hevQ) n := by
  classical
  intro hobs
  have hle : HiddenPriceDepth cost Sat Q hevQ ≤ n := by
    exact Nat.find_min' (exists_subcritical_obstruction cost Sat Q hevQ) hobs
  omega

/-- Every coalition smaller than the hidden depth has a strictly subcritical witness. -/
theorem all_smaller_coalitions_are_subcritical_faces
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q)
    {S : Finset Req} (hSQ : S ⊆ Q)
    (hcard : S.card < HiddenPriceDepth cost Sat Q hevQ) :
    SubcriticalFace cost Sat (SetPrice cost Sat Q hevQ) S := by
  by_contra hnf
  have hobs : HasSubcriticalObstructionOfSize
      cost Sat Q (SetPrice cost Sat Q hevQ) S.card := by
    exact ⟨S, hSQ, rfl, hnf⟩
  exact (no_obstruction_below_hiddenDepth cost Sat Q hevQ hcard) hobs

/-- Every smaller coalition has price strictly below the full-contract price. -/
theorem all_smaller_coalitions_are_cheaper
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q)
    {S : Finset Req} (hSQ : S ⊆ Q)
    (hcard : S.card < HiddenPriceDepth cost Sat Q hevQ) :
    SetPrice cost Sat S (subset_feasible_of_full cost Sat hSQ hevQ) <
      SetPrice cost Sat Q hevQ := by
  apply (subcriticalFace_iff_subset_price_lt_full cost Sat hSQ hevQ).1
  exact all_smaller_coalitions_are_subcritical_faces cost Sat Q hevQ hSQ hcard

/-- At the hidden depth there exists a coalition whose price is already the full price. -/
theorem exists_hiddenDepth_coalition_at_full_price
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    ∃ S : Finset Req,
      S ⊆ Q ∧
      S.card = HiddenPriceDepth cost Sat Q hevQ ∧
      SetPrice cost Sat S (subset_feasible_of_full cost Sat ‹S ⊆ Q› hevQ) =
        SetPrice cost Sat Q hevQ := by
  classical
  rcases hiddenPriceDepth_spec cost Sat Q hevQ with ⟨S, hSQ, hcard, hnf⟩
  refine ⟨S, hSQ, hcard, ?_⟩
  exact (not_subcriticalFace_iff_subset_price_eq_full cost Sat hSQ hevQ).1 hnf

/-- Coverage through order k means every coalition of size at most k has a witness
strictly cheaper than the global price. -/
def CoveredThrough
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (p k : Nat) : Prop :=
  ∀ S : Finset Req, S ⊆ Q → S.card ≤ k → SubcriticalFace cost Sat p S

/-- Every audit order strictly below the hidden depth is fully covered. -/
theorem coveredThrough_below_hiddenDepth
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q)
    {k : Nat} (hk : k < HiddenPriceDepth cost Sat Q hevQ) :
    CoveredThrough cost Sat Q (SetPrice cost Sat Q hevQ) k := by
  intro S hSQ hcard
  apply all_smaller_coalitions_are_subcritical_faces cost Sat Q hevQ hSQ
  omega

/-- Coverage fails exactly when the audit reaches the hidden depth. -/
theorem not_coveredThrough_hiddenDepth
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    ¬ CoveredThrough cost Sat Q (SetPrice cost Sat Q hevQ)
      (HiddenPriceDepth cost Sat Q hevQ) := by
  intro hcov
  rcases hiddenPriceDepth_spec cost Sat Q hevQ with ⟨S, hSQ, hcard, hnf⟩
  apply hnf
  exact hcov S hSQ (by omega)

/-- The hidden depth never exceeds the number of obligations in the full contract. -/
theorem hiddenPriceDepth_le_card
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    HiddenPriceDepth cost Sat Q hevQ ≤ Q.card := by
  classical
  apply Nat.find_min'
  exact exists_subcritical_obstruction cost Sat Q hevQ
  exact ⟨Q, Finset.Subset.rfl, rfl, full_not_subcriticalFace cost Sat Q hevQ⟩

/-- Consolidated exact characterization: hidden price depth is the first interaction order
at which subcritical local coverage fails, equivalently the minimum non-face cardinality
of the subcritical affordability complex. -/
theorem hidden_price_depth_characterization_v1
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    (∀ k, k < HiddenPriceDepth cost Sat Q hevQ →
      CoveredThrough cost Sat Q (SetPrice cost Sat Q hevQ) k) ∧
    (¬ CoveredThrough cost Sat Q (SetPrice cost Sat Q hevQ)
      (HiddenPriceDepth cost Sat Q hevQ)) ∧
    (∃ S : Finset Req,
      S ⊆ Q ∧
      S.card = HiddenPriceDepth cost Sat Q hevQ ∧
      SetPrice cost Sat S (subset_feasible_of_full cost Sat ‹S ⊆ Q› hevQ) =
        SetPrice cost Sat Q hevQ) ∧
    (∀ S : Finset Req, ∀ hSQ : S ⊆ Q,
      S.card < HiddenPriceDepth cost Sat Q hevQ →
      SetPrice cost Sat S (subset_feasible_of_full cost Sat hSQ hevQ) <
        SetPrice cost Sat Q hevQ) := by
  constructor
  · intro k hk
    exact coveredThrough_below_hiddenDepth cost Sat Q hevQ hk
  constructor
  · exact not_coveredThrough_hiddenDepth cost Sat Q hevQ
  constructor
  · exact exists_hiddenDepth_coalition_at_full_price cost Sat Q hevQ
  · intro S hSQ hcard
    exact all_smaller_coalitions_are_cheaper cost Sat Q hevQ hSQ hcard

end HiddenDepth

end InsacermoHiddenPriceDepth
