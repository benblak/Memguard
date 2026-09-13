import Mathlib
import NoLocalAuditorKernelV1
import CriticalHorizonKernelV1

namespace InsacermoSilentFuture

open Set
open InsacermoCausalPriceFactorization
open InsacermoHigherOrderPriceInteraction
open InsacermoNoLocalAuditor

universe u

/-- Temporal price profile: before the reveal horizon H, use a flat world;
from H onward, switch permanently to the higher-order hard world. -/
noncomputable def TemporalPrice
    (H n M : Nat) (h : Nat) (S : Finset (Fin n)) : Nat :=
  if h < H then
    SetPrice flatCost (flatSat (Req := Fin n)) S (flat_set_feasible S)
  else
    SetPrice (hoCost n M) (hoSat n) S (ho_set_feasible n M S)

/-- A permanently flat comparison world. -/
noncomputable def FlatTemporalPrice
    (n : Nat) (_h : Nat) (S : Finset (Fin n)) : Nat :=
  SetPrice flatCost (flatSat (Req := Fin n)) S (flat_set_feasible S)

/-- Through every horizon strictly before H, the temporal hard world is fully indistinguishable
from the permanently flat world on every coalition, not merely on bounded-order coalitions. -/
theorem pre_reveal_full_profile_indistinguishable
    (H n M h : Nat) (hh : h < H) :
    ∀ S : Finset (Fin n),
      TemporalPrice H n M h S = FlatTemporalPrice n h S := by
  intro S
  simp [TemporalPrice, FlatTemporalPrice, hh]

/-- After reveal, every coalition of size at most k still has price one whenever k<n and M≥1. -/
theorem post_reveal_local_profile_still_flat
    (H n M k h : Nat) (hh : H ≤ h) (hkn : k < n) (hM : 1 ≤ M) :
    ∀ S : Finset (Fin n), S.card ≤ k →
      TemporalPrice H n M h S = FlatTemporalPrice n h S := by
  intro S hcard
  simp [TemporalPrice, FlatTemporalPrice, Nat.not_lt.mpr hh]
  rw [flat_price_eq_one S]
  exact (bounded_order_audits_can_miss_global n k M hkn hM).1 S hcard

/-- Before reveal, both worlds have full-contract price one. -/
theorem pre_reveal_full_price_one
    (H n M h : Nat) (hh : h < H) :
    TemporalPrice H n M h Finset.univ = 1 := by
  simp [TemporalPrice, hh]
  exact flat_price_eq_one Finset.univ

/-- At and after reveal, the hard world's full-contract price is permanently M. -/
theorem post_reveal_full_price_M
    (H n M h : Nat) (hh : H ≤ h) :
    TemporalPrice H n M h Finset.univ = M := by
  simp [TemporalPrice, Nat.not_lt.mpr hh]
  exact full_price_eq_M n M

/-- The flat comparison world's full-contract price stays one forever. -/
theorem flat_full_price_one_forever
    (n h : Nat) :
    FlatTemporalPrice n h Finset.univ = 1 := by
  simp [FlatTemporalPrice]
  exact flat_price_eq_one Finset.univ

/-- A temporal world is globally safe under budget B at horizon h when its full-contract price
is at most B. -/
def GloballySafeAt
    (price : Nat → Finset (Fin n) → Nat) (B h : Nat) : Prop :=
  price h Finset.univ ≤ B

/-- In the permanently flat world, budget one is always globally safe. -/
theorem flat_safe_forever
    (n h : Nat) :
    GloballySafeAt (FlatTemporalPrice n) 1 h := by
  unfold GloballySafeAt
  rw [flat_full_price_one_forever n h]

/-- In the hard temporal world, budget one is safe before reveal. -/
theorem hard_safe_before_reveal
    (H n M h : Nat) (hh : h < H) :
    GloballySafeAt (TemporalPrice H n M) 1 h := by
  unfold GloballySafeAt
  rw [pre_reveal_full_price_one H n M h hh]

/-- If M>1, budget one is unsafe at every horizon at or after reveal. -/
theorem hard_unsafe_at_or_after_reveal
    (H n M h : Nat) (hM : 1 < M) (hh : H ≤ h) :
    ¬ GloballySafeAt (TemporalPrice H n M) 1 h := by
  unfold GloballySafeAt
  rw [post_reveal_full_price_M H n M h hh]
  omega

/-- Exact persistent failure threshold: before H the hard world is safe under budget one;
at and after H it is permanently unsafe, while the flat world remains safe forever. -/
theorem persistent_global_bifurcation_at_H
    (H n M : Nat) (hM : 1 < M) :
    (∀ h, h < H → GloballySafeAt (TemporalPrice H n M) 1 h) ∧
    (∀ h, H ≤ h → ¬ GloballySafeAt (TemporalPrice H n M) 1 h) ∧
    (∀ h, GloballySafeAt (FlatTemporalPrice n) 1 h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    exact hard_safe_before_reveal H n M h hh
  · intro h hh
    exact hard_unsafe_at_or_after_reveal H n M h hM hh
  · intro h
    exact flat_safe_forever n h

/-- SILENT FUTURE: for every observation horizon H, bounded audit order k, and target N,
there are two temporal worlds that are completely identical on every coalition before H;
after H one remains safe forever while the other becomes permanently unsafe under budget one,
its full price exceeds N, and yet every order-k local audit stays identical forever. -/
theorem silent_future_impossibility_v1
    (H k N : Nat) :
    ∃ n M,
      k < n ∧ N < M ∧ 1 < M ∧
      (∀ h, h < H → ∀ S : Finset (Fin n),
        TemporalPrice H n M h S = FlatTemporalPrice n h S) ∧
      (∀ h, H ≤ h →
        TemporalPrice H n M h Finset.univ = M ∧
        FlatTemporalPrice n h Finset.univ = 1) ∧
      (∀ h, ∀ S : Finset (Fin n), S.card ≤ k →
        TemporalPrice H n M h S = FlatTemporalPrice n h S) ∧
      (∀ h, GloballySafeAt (FlatTemporalPrice n) 1 h) ∧
      (∀ h, h < H → GloballySafeAt (TemporalPrice H n M) 1 h) ∧
      (∀ h, H ≤ h → ¬ GloballySafeAt (TemporalPrice H n M) 1 h) := by
  refine ⟨k + 1, max (N + 1) 2, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro h hh S
    exact pre_reveal_full_profile_indistinguishable H (k + 1) (max (N + 1) 2) h hh S
  · intro h hh
    constructor
    · exact post_reveal_full_price_M H (k + 1) (max (N + 1) 2) h hh
    · exact flat_full_price_one_forever (k + 1) h
  · intro h S hcard
    by_cases hh : h < H
    · exact pre_reveal_full_profile_indistinguishable
        H (k + 1) (max (N + 1) 2) h hh S
    · exact post_reveal_local_profile_still_flat
        H (k + 1) (max (N + 1) 2) k h (Nat.le_of_not_gt hh)
        (by omega) (by omega) S hcard
  · intro h
    exact flat_safe_forever (k + 1) h
  · intro h hh
    exact hard_safe_before_reveal H (k + 1) (max (N + 1) 2) h hh
  · intro h hh
    exact hard_unsafe_at_or_after_reveal
      H (k + 1) (max (N + 1) 2) h (by omega) hh

end InsacermoSilentFuture
