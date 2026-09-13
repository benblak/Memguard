import Mathlib
import CausalPriceFactorizationKernelV1

namespace InsacermoHigherOrderPriceInteraction

open Set
open InsacermoCausalPriceFactorization

universe u v

/-! # Requirement-indexed minimum-price geometry -/

section GenericSetPrice

variable {A : Type u} {Req : Type v}

/-- An intervention satisfies every requirement in a finite set. -/
def GoodFor (Sat : A → Req → Prop) (S : Finset Req) (a : A) : Prop :=
  ∀ q, q ∈ S → Sat a q

/-- Feasibility of a finite requirement set. -/
def SetFeasible (cost : A → Nat) (Sat : A → Req → Prop) (S : Finset Req) : Prop :=
  Feasible cost (GoodFor Sat S)

/-- Minimum price of satisfying a finite requirement set. -/
noncomputable def SetPrice
    (cost : A → Nat) (Sat : A → Req → Prop) (S : Finset Req)
    (hev : SetFeasible cost Sat S) : Nat :=
  Price cost (GoodFor Sat S) hev

/-- A larger requirement set cannot have a lower minimum price. -/
theorem setPrice_mono
    [DecidableEq Req]
    (cost : A → Nat) (Sat : A → Req → Prop)
    {S T : Finset Req} (hST : S ⊆ T)
    (hevS : SetFeasible cost Sat S)
    (hevT : SetFeasible cost Sat T) :
    SetPrice cost Sat S hevS ≤ SetPrice cost Sat T hevT := by
  unfold SetPrice
  apply price_minimal
  rcases price_affordable cost (GoodFor Sat T) hevT with ⟨a, hcost, hgood⟩
  refine ⟨a, hcost, ?_⟩
  intro q hq
  exact hgood q (hST hq)

end GenericSetPrice

/-! # Exact higher-order local/global separation -/

section LocalGlobalWitness

variable (n : Nat)

/-- A cheap local intervention may satisfy any proper subset of requirements.
The only intervention that satisfies all requirements is `global`. -/
inductive HORepair
  | local (S : Finset (Fin n)) (hproper : S ≠ Finset.univ)
  | global

/-- Every local intervention costs one. The global intervention costs M. -/
def hoCost (M : Nat) : HORepair n → Nat
  | HORepair.local _ _ => 1
  | HORepair.global => M

/-- A local intervention satisfies exactly its chosen proper subset; global satisfies all requirements. -/
def hoSat : HORepair n → Fin n → Prop
  | HORepair.local S _ => fun q => q ∈ S
  | HORepair.global => fun _ => True

/-- Every finite requirement set is feasible because `global` satisfies everything. -/
theorem ho_set_feasible (M : Nat) (S : Finset (Fin n)) :
    SetFeasible (hoCost n M) (hoSat n) S := by
  refine ⟨M, HORepair.global, le_rfl, ?_⟩
  intro q hq
  trivial

/-- Every proper subset has exact price one, provided the global intervention is not cheaper. -/
theorem proper_subset_price_eq_one
    (M : Nat) (hM : 1 ≤ M)
    (S : Finset (Fin n)) (hproper : S ≠ Finset.univ) :
    SetPrice (hoCost n M) (hoSat n) S (ho_set_feasible n M S) = 1 := by
  unfold SetPrice
  apply Nat.le_antisymm
  · apply price_minimal
    refine ⟨HORepair.local S hproper, le_rfl, ?_⟩
    intro q hq
    exact hq
  · rcases price_affordable
      (hoCost n M) (GoodFor (hoSat n) S) (ho_set_feasible n M S) with
      ⟨a, hcost, hgood⟩
    cases a
    next T hT =>
      simpa [hoCost] using hcost
    next =>
      have hMp : M ≤ Price (hoCost n M) (GoodFor (hoSat n) S)
          (ho_set_feasible n M S) := by
        simpa [hoCost] using hcost
      exact le_trans hM hMp

/-- Only the global intervention can satisfy the full requirement universe. -/
theorem full_good_forces_global
    (a : HORepair n)
    (hgood : GoodFor (hoSat n) Finset.univ a) :
    a = HORepair.global := by
  cases a
  next S hproper =>
    exfalso
    apply hproper
    apply Finset.eq_univ_of_forall
    intro q
    exact hgood q (by simp)
  next =>
    rfl

/-- The full requirement universe has exact price M. -/
theorem full_price_eq_M (M : Nat) :
    SetPrice (hoCost n M) (hoSat n) Finset.univ
      (ho_set_feasible n M Finset.univ) = M := by
  unfold SetPrice
  apply Nat.le_antisymm
  · apply price_minimal
    exact ⟨HORepair.global, le_rfl, by intro q hq; trivial⟩
  · rcases price_affordable
      (hoCost n M) (GoodFor (hoSat n) Finset.univ)
      (ho_set_feasible n M Finset.univ) with ⟨a, hcost, hgood⟩
    have ha : a = HORepair.global := full_good_forces_global n a hgood
    subst a
    simpa [hoCost] using hcost

/-- All proper subproblems can cost exactly one while the full problem costs an arbitrary M. -/
theorem all_proper_cheap_full_arbitrary
    (M : Nat) (hM : 1 ≤ M) :
    (∀ S : Finset (Fin n), S ≠ Finset.univ →
      SetPrice (hoCost n M) (hoSat n) S (ho_set_feasible n M S) = 1) ∧
    SetPrice (hoCost n M) (hoSat n) Finset.univ
      (ho_set_feasible n M Finset.univ) = M := by
  constructor
  · intro S hS
    exact proper_subset_price_eq_one n M hM S hS
  · exact full_price_eq_M n M

/-- No bound on the global price can be inferred even after auditing every proper subset.
For any proposed bound N, choose a system whose every proper subset costs one but whose
full requirement set costs strictly more than N. -/
theorem proper_subsets_do_not_bound_global
    (N : Nat) :
    ∃ M,
      N < M ∧
      (∀ S : Finset (Fin n), S ≠ Finset.univ →
        SetPrice (hoCost n M) (hoSat n) S (ho_set_feasible n M S) = 1) ∧
      SetPrice (hoCost n M) (hoSat n) Finset.univ
        (ho_set_feasible n M Finset.univ) = M := by
  refine ⟨N + 1, by omega, ?_, ?_⟩
  · intro S hS
    exact proper_subset_price_eq_one n (N + 1) (by omega) S hS
  · exact full_price_eq_M n (N + 1)

/-- Bounded-order audits are therefore powerless in the worst case: whenever k<n,
all coalitions of size at most k cost one, while the full n-way coalition may cost M. -/
theorem bounded_order_audits_can_miss_global
    (k M : Nat) (hkn : k < n) (hM : 1 ≤ M) :
    (∀ S : Finset (Fin n), S.card ≤ k →
      SetPrice (hoCost n M) (hoSat n) S (ho_set_feasible n M S) = 1) ∧
    SetPrice (hoCost n M) (hoSat n) Finset.univ
      (ho_set_feasible n M Finset.univ) = M := by
  constructor
  · intro S hcard
    apply proper_subset_price_eq_one n M hM S
    intro hEq
    have hcardUniv : S.card = n := by
      rw [hEq]
      simp
    omega
  · exact full_price_eq_M n M

/-- Unbounded higher-order surprise with all audits up to order k fixed at one. -/
theorem fixed_low_order_prices_unbounded_global
    (k N : Nat) (hkn : k < n) :
    ∃ M,
      N < M ∧
      (∀ S : Finset (Fin n), S.card ≤ k →
        SetPrice (hoCost n M) (hoSat n) S (ho_set_feasible n M S) = 1) ∧
      SetPrice (hoCost n M) (hoSat n) Finset.univ
        (ho_set_feasible n M Finset.univ) = M := by
  refine ⟨N + 1, by omega, ?_, ?_⟩
  · intro S hcard
    exact (bounded_order_audits_can_miss_global n k (N + 1) hkn (by omega)).1 S hcard
  · exact full_price_eq_M n (N + 1)

end LocalGlobalWitness

/-! # Consolidated higher-order theorem -/

/-- For every interaction order k there are larger systems where all prices visible up to order k
are identically one, yet the full joint price exceeds any prescribed bound. -/
theorem higher_order_price_separation_v1
    (k N : Nat) :
    ∃ n M,
      k < n ∧ N < M ∧
      (∀ S : Finset (Fin n), S.card ≤ k →
        SetPrice (hoCost n M) (hoSat n) S (ho_set_feasible n M S) = 1) ∧
      SetPrice (hoCost n M) (hoSat n) Finset.univ
        (ho_set_feasible n M Finset.univ) = M := by
  refine ⟨k + 1, N + 1, by omega, by omega, ?_, ?_⟩
  · intro S hcard
    exact (bounded_order_audits_can_miss_global (k + 1) k (N + 1)
      (by omega) (by omega)).1 S hcard
  · exact full_price_eq_M (k + 1) (N + 1)

end InsacermoHigherOrderPriceInteraction
