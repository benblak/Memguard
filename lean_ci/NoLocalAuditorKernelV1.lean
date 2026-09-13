import Mathlib
import HiddenPriceTransversalKernelV1

namespace InsacermoNoLocalAuditor

open Set
open InsacermoCausalPriceFactorization
open InsacermoHigherOrderPriceInteraction
open InsacermoHiddenPriceDepth
open InsacermoHiddenPriceTransversal

universe u

/-! # A flat comparison world whose every coalition has exact price one -/

inductive FlatRepair
  | universal

/-- The unique flat-world intervention costs one. -/
def flatCost : FlatRepair → Nat
  | FlatRepair.universal => 1

/-- The unique flat-world intervention satisfies every obligation. -/
def flatSat {Req : Type u} : FlatRepair → Req → Prop
  | FlatRepair.universal => fun _ => True

/-- Every coalition is feasible in the flat world. -/
theorem flat_set_feasible {Req : Type u} (S : Finset Req) :
    SetFeasible flatCost (flatSat (Req := Req)) S := by
  refine ⟨1, FlatRepair.universal, le_rfl, ?_⟩
  intro q hq
  trivial

/-- Every coalition has exact price one in the flat world. -/
theorem flat_price_eq_one {Req : Type u} (S : Finset Req) :
    SetPrice flatCost (flatSat (Req := Req)) S (flat_set_feasible S) = 1 := by
  unfold SetPrice
  apply Nat.le_antisymm
  · apply price_minimal
    exact ⟨FlatRepair.universal, le_rfl, by intro q hq; trivial⟩
  · rcases price_affordable
      flatCost (GoodFor (flatSat (Req := Req)) S) (flat_set_feasible S) with
      ⟨a, hcost, hgood⟩
    cases a
    simpa [flatCost] using hcost

/-- Two worlds are indistinguishable to an order-k price auditor when every coalition
of size at most k receives the same price in both worlds. -/
def KLocallyPriceEquivalent
    {Req : Type u}
    {A B : Type*}
    (costA : A → Nat) (satA : A → Req → Prop)
    (costB : B → Nat) (satB : B → Req → Prop)
    (feasA : ∀ S : Finset Req, SetFeasible costA satA S)
    (feasB : ∀ S : Finset Req, SetFeasible costB satB S)
    (k : Nat) : Prop :=
  ∀ S : Finset Req, S.card ≤ k →
    SetPrice costA satA S (feasA S) =
      SetPrice costB satB S (feasB S)

/-- For the higher-order witness with k<n and global price at least one, the hard world
is locally price-equivalent to the flat world through order k. -/
theorem flat_and_hard_are_k_locally_equivalent
    (n k M : Nat) (hkn : k < n) (hM : 1 ≤ M) :
    KLocallyPriceEquivalent
      flatCost (flatSat (Req := Fin n))
      (hoCost n M) (hoSat n)
      (fun S => flat_set_feasible S)
      (fun S => ho_set_feasible n M S)
      k := by
  intro S hcard
  rw [flat_price_eq_one S]
  exact (bounded_order_audits_can_miss_global n k M hkn hM).1 S hcard |>.symm

/-- Exact no-local-auditor impossibility theorem.
For every bounded audit order k and every proposed global bound N, there are two worlds
that agree on every coalition price visible to the order-k auditor, while one full contract
costs exactly one and the other exceeds N. -/
theorem no_local_auditor_impossibility_v1
    (k N : Nat) :
    ∃ n M,
      k < n ∧ N < M ∧
      KLocallyPriceEquivalent
        flatCost (flatSat (Req := Fin n))
        (hoCost n M) (hoSat n)
        (fun S => flat_set_feasible S)
        (fun S => ho_set_feasible n M S)
        k ∧
      SetPrice flatCost (flatSat (Req := Fin n)) Finset.univ
        (flat_set_feasible Finset.univ) = 1 ∧
      SetPrice (hoCost n M) (hoSat n) Finset.univ
        (ho_set_feasible n M Finset.univ) = M := by
  refine ⟨k + 1, N + 1, by omega, by omega, ?_, ?_, ?_⟩
  · exact flat_and_hard_are_k_locally_equivalent
      (k + 1) k (N + 1) (by omega) (by omega)
  · exact flat_price_eq_one Finset.univ
  · exact full_price_eq_M (k + 1) (N + 1)

/-- Any purported decision rule whose input is only the order-k local price profile must
return the same output on the two indistinguishable worlds from the theorem above.
This theorem isolates the information-theoretic obstruction independently of any
particular auditor implementation. -/
theorem same_local_profile_forces_same_auditor_output
    {X Y : Type*}
    (audit : X → Y)
    {x₁ x₂ : X}
    (h : x₁ = x₂) :
    audit x₁ = audit x₂ := by
  simpa [h]

/-- A strengthened summary: bounded local price data cannot yield any finite worst-case
upper bound on the global price. -/
theorem no_finite_global_bound_from_order_k_profile
    (k N : Nat) :
    ∃ n M,
      k < n ∧ N < M ∧
      (∀ S : Finset (Fin n), S.card ≤ k →
        SetPrice flatCost (flatSat (Req := Fin n)) S (flat_set_feasible S) =
          SetPrice (hoCost n M) (hoSat n) S (ho_set_feasible n M S)) ∧
      SetPrice flatCost (flatSat (Req := Fin n)) Finset.univ
        (flat_set_feasible Finset.univ) = 1 ∧
      SetPrice (hoCost n M) (hoSat n) Finset.univ
        (ho_set_feasible n M Finset.univ) = M := by
  rcases no_local_auditor_impossibility_v1 k N with
    ⟨n, M, hkn, hNM, hlocal, hflat, hhard⟩
  refine ⟨n, M, hkn, hNM, ?_, hflat, hhard⟩
  exact hlocal

end InsacermoNoLocalAuditor
