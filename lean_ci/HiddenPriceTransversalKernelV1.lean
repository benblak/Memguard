import Mathlib
import HiddenPriceDepthKernelV1

namespace InsacermoHiddenPriceTransversal

open Set
open InsacermoCausalPriceFactorization
open InsacermoHigherOrderPriceInteraction
open InsacermoHiddenPriceDepth

universe u v

section TransversalGeometry

variable {A : Type u} {Req : Type v}

/-- A coalition eliminates all interventions cheaper than threshold p when every cheap
intervention misses at least one obligation in the coalition. -/
def EliminatesAllCheap
    (cost : A → Nat) (Sat : A → Req → Prop)
    (p : Nat) (S : Finset Req) : Prop :=
  ∀ a, cost a < p → ∃ q, q ∈ S ∧ ¬ Sat a q

/-- Failure of subcritical affordability is exactly elimination of every cheap intervention.
This is the hypergraph-transversal form of a hidden-price obstruction. -/
theorem not_subcriticalFace_iff_eliminatesAllCheap
    (cost : A → Nat) (Sat : A → Req → Prop)
    (p : Nat) (S : Finset Req) :
    (¬ SubcriticalFace cost Sat p S) ↔
      EliminatesAllCheap cost Sat p S := by
  constructor
  · intro hnf a hcost
    by_contra hnone
    apply hnf
    refine ⟨a, hcost, ?_⟩
    intro q hq
    by_contra hsat
    exact hnone ⟨q, hq, hsat⟩
  · intro helim hface
    rcases hface with ⟨a, hcost, hgood⟩
    rcases helim a hcost with ⟨q, hq, hnot⟩
    exact hnot (hgood q hq)

/-- At the true full-contract price, hidden depth is realized by a coalition that
eliminates every strictly cheaper intervention. -/
theorem hiddenPriceDepth_transversal_spec
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    ∃ S : Finset Req, ∃ hSQ : S ⊆ Q,
      S.card = HiddenPriceDepth cost Sat Q hevQ ∧
      EliminatesAllCheap cost Sat (SetPrice cost Sat Q hevQ) S := by
  rcases hiddenPriceDepth_spec cost Sat Q hevQ with ⟨S, hSQ, hcard, hnf⟩
  refine ⟨S, hSQ, hcard, ?_⟩
  exact (not_subcriticalFace_iff_eliminatesAllCheap
    cost Sat (SetPrice cost Sat Q hevQ) S).1 hnf

/-- No smaller coalition can eliminate all interventions cheaper than the true global price. -/
theorem no_smaller_transversal_than_hiddenPriceDepth
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q)
    (S : Finset Req) (hSQ : S ⊆ Q)
    (hcard : S.card < HiddenPriceDepth cost Sat Q hevQ) :
    ¬ EliminatesAllCheap cost Sat (SetPrice cost Sat Q hevQ) S := by
  intro helim
  have hnf : ¬ SubcriticalFace cost Sat (SetPrice cost Sat Q hevQ) S :=
    (not_subcriticalFace_iff_eliminatesAllCheap
      cost Sat (SetPrice cost Sat Q hevQ) S).2 helim
  have hobs : HasSubcriticalObstructionOfSize
      cost Sat Q (SetPrice cost Sat Q hevQ) S.card := by
    exact ⟨S, hSQ, rfl, hnf⟩
  exact (no_obstruction_below_hiddenDepth cost Sat Q hevQ hcard) hobs

/-- Exact transversal characterization: hidden depth is the minimum number of obligations
needed to rule out every intervention whose cost is strictly below the full-contract price. -/
theorem hidden_price_transversal_characterization_v1
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    (∃ S : Finset Req, ∃ hSQ : S ⊆ Q,
      S.card = HiddenPriceDepth cost Sat Q hevQ ∧
      EliminatesAllCheap cost Sat (SetPrice cost Sat Q hevQ) S) ∧
    (∀ S : Finset Req, ∀ hSQ : S ⊆ Q,
      S.card < HiddenPriceDepth cost Sat Q hevQ →
      ¬ EliminatesAllCheap cost Sat (SetPrice cost Sat Q hevQ) S) := by
  constructor
  · exact hiddenPriceDepth_transversal_spec cost Sat Q hevQ
  · intro S hSQ hcard
    exact no_smaller_transversal_than_hiddenPriceDepth
      cost Sat Q hevQ S hSQ hcard

end TransversalGeometry

/-! # Price magnitude and hidden depth are independent coordinates -/

section OrthogonalityWitness

/-- In the exact higher-order witness family, the hidden depth is exactly n whenever
local repairs of cost one are strictly cheaper than the global repair. -/
theorem ho_hiddenPriceDepth_eq_n
    (n M : Nat) (hM : 2 ≤ M) :
    HiddenPriceDepth
      (hoCost n M) (hoSat n) Finset.univ
      (ho_set_feasible n M Finset.univ) = n := by
  apply Nat.le_antisymm
  · simpa using
      (hiddenPriceDepth_le_card
        (hoCost n M) (hoSat n) Finset.univ
        (ho_set_feasible n M Finset.univ))
  · by_contra hnot
    have hlt :
        HiddenPriceDepth
          (hoCost n M) (hoSat n) Finset.univ
          (ho_set_feasible n M Finset.univ) < n := by
      omega
    rcases hiddenPriceDepth_spec
      (hoCost n M) (hoSat n) Finset.univ
      (ho_set_feasible n M Finset.univ) with
      ⟨S, hSQ, hcard, hnf⟩
    have hproper : S ≠ Finset.univ := by
      intro hEq
      have hSn : S.card = n := by
        rw [hEq]
        simp
      omega
    apply hnf
    refine ⟨HORepair.local S hproper, ?_, ?_⟩
    · rw [full_price_eq_M n M]
      simp [hoCost]
      omega
    · intro q hq
      simpa [hoSat] using hq

/-- For any n and any M≥2, one can realize global price exactly M and hidden depth exactly n.
Thus price magnitude and interaction depth are not determined by one another. -/
theorem arbitrary_price_arbitrary_hiddenDepth
    (n M : Nat) (hM : 2 ≤ M) :
    SetPrice (hoCost n M) (hoSat n) Finset.univ
      (ho_set_feasible n M Finset.univ) = M ∧
    HiddenPriceDepth
      (hoCost n M) (hoSat n) Finset.univ
      (ho_set_feasible n M Finset.univ) = n := by
  constructor
  · exact full_price_eq_M n M
  · exact ho_hiddenPriceDepth_eq_n n M hM

/-- Hidden depth can be arbitrarily large while the full price remains fixed at two. -/
theorem fixed_price_two_arbitrary_hiddenDepth
    (n : Nat) :
    SetPrice (hoCost n 2) (hoSat n) Finset.univ
      (ho_set_feasible n 2 Finset.univ) = 2 ∧
    HiddenPriceDepth
      (hoCost n 2) (hoSat n) Finset.univ
      (ho_set_feasible n 2 Finset.univ) = n := by
  exact arbitrary_price_arbitrary_hiddenDepth n 2 (by omega)

/-- Conversely, with hidden depth fixed at one, the full price can be arbitrarily large. -/
theorem fixed_hiddenDepth_one_arbitrary_price
    (M : Nat) (hM : 2 ≤ M) :
    SetPrice (hoCost 1 M) (hoSat 1) Finset.univ
      (ho_set_feasible 1 M Finset.univ) = M ∧
    HiddenPriceDepth
      (hoCost 1 M) (hoSat 1) Finset.univ
      (ho_set_feasible 1 M Finset.univ) = 1 := by
  exact arbitrary_price_arbitrary_hiddenDepth 1 M hM

/-- Consolidated orthogonality result: cost tells how expensive the future is; hidden depth
tells how many obligations must be combined before all cheaper alternatives are excluded. -/
theorem price_depth_orthogonality_v1
    (n M : Nat) (hM : 2 ≤ M) :
    SetPrice (hoCost n M) (hoSat n) Finset.univ
      (ho_set_feasible n M Finset.univ) = M ∧
    HiddenPriceDepth
      (hoCost n M) (hoSat n) Finset.univ
      (ho_set_feasible n M Finset.univ) = n := by
  exact arbitrary_price_arbitrary_hiddenDepth n M hM

end OrthogonalityWitness

end InsacermoHiddenPriceTransversal
