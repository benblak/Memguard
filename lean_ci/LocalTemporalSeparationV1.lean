import Mathlib
import InteractionDepthBridgeV1

namespace InsacermoLocalTemporalSeparation

open Set
open InsacermoProbeRepairMinimax
open InsacermoInteractionDepthBridge

/-- Every singleton belief admits its unique head-matching repair. -/
theorem singleton_has_common_repair {k : Nat} (w : Hidden (k + 1)) :
    CommonSafeRepair ({w} : Set (Hidden (k + 1))) := by
  refine ⟨head w, ?_⟩
  intro u hu
  simp only [Set.mem_singleton_iff] at hu
  subst u
  rfl

/-- Two worlds with different current heads form a non-actionable pair. -/
theorem opposite_heads_no_common_repair {k : Nat} (w₀ w₁ : Hidden (k + 1))
    (hne : head w₀ ≠ head w₁) :
    ¬ CommonSafeRepair ({w₀, w₁} : Set (Hidden (k + 1))) := by
  intro h
  rcases h with ⟨r, hr⟩
  have h₀ : head w₀ = r := hr w₀ (by simp)
  have h₁ : head w₁ = r := hr w₁ (by simp)
  exact hne (h₀.trans h₁.symm)

/-- Any non-actionable belief in this binary-head repair model contains two worlds with opposite
heads.  Thus every failure has a two-world certificate. -/
theorem nonactionable_has_opposite_pair {k : Nat} {F : Set (Hidden (k + 1))}
    (hbad : ¬ CommonSafeRepair F) :
    ∃ w₀, w₀ ∈ F ∧ ∃ w₁, w₁ ∈ F ∧ head w₀ ≠ head w₁ := by
  have hnonempty : F.Nonempty := by
    by_contra hne
    apply hbad
    refine ⟨false, ?_⟩
    intro w hw
    exact False.elim (hne ⟨w, hw⟩)
  rcases hnonempty with ⟨w₀, hw₀⟩
  by_cases hop : ∃ w₁, w₁ ∈ F ∧ head w₁ ≠ head w₀
  · rcases hop with ⟨w₁, hw₁, hdiff⟩
    exact ⟨w₀, hw₀, w₁, hw₁, hdiff.symm⟩
  · apply False.elim
    apply hbad
    refine ⟨head w₀, ?_⟩
    intro w hw
    have hsame : head w = head w₀ := by
      by_contra hdiff
      exact hop ⟨w, hw, hdiff⟩
    exact hsame

/-- Exact local certificate statement: every non-actionable belief contains a non-actionable pair,
and both singleton sub-beliefs are actionable. -/
theorem every_nonactionable_belief_has_binary_minimal_certificate
    {k : Nat} {F : Set (Hidden (k + 1))}
    (hbad : ¬ CommonSafeRepair F) :
    ∃ w₀, w₀ ∈ F ∧ ∃ w₁, w₁ ∈ F ∧
      (¬ CommonSafeRepair ({w₀, w₁} : Set (Hidden (k + 1)))) ∧
      CommonSafeRepair ({w₀} : Set (Hidden (k + 1))) ∧
      CommonSafeRepair ({w₁} : Set (Hidden (k + 1))) := by
  rcases nonactionable_has_opposite_pair hbad with ⟨w₀, hw₀, w₁, hw₁, hdiff⟩
  exact ⟨w₀, hw₀, w₁, hw₁,
    opposite_heads_no_common_repair w₀ w₁ hdiff,
    singleton_has_common_repair w₀,
    singleton_has_common_repair w₁⟩

/-- Local-vs-temporal separation.
The entire hidden-vector family has two-world certificates for every current non-actionability
failure, while its optimal PROBE/REPAIR interaction depth is not bounded by any finite K. -/
theorem binary_local_certificates_do_not_bound_optimal_interaction_depth (K : Nat) :
    (∀ (k : Nat) (F : Set (Hidden (k + 1))),
      ¬ CommonSafeRepair F →
      ∃ w₀, w₀ ∈ F ∧ ∃ w₁, w₁ ∈ F ∧
        (¬ CommonSafeRepair ({w₀, w₁} : Set (Hidden (k + 1)))) ∧
        CommonSafeRepair ({w₀} : Set (Hidden (k + 1))) ∧
        CommonSafeRepair ({w₁} : Set (Hidden (k + 1)))) ∧
    (∃ k : Nat, 0 < k ∧
      ∃ xs : List InsacermoProbeRepairMinimax.Role,
        run (initial k) xs = some goal ∧
        xs.length = 2 * k ∧
        K < interactionDepth xs) := by
  constructor
  · intro k F hbad
    exact every_nonactionable_belief_has_binary_minimal_certificate hbad
  · exact no_finite_universal_interaction_depth_bound K

end InsacermoLocalTemporalSeparation
