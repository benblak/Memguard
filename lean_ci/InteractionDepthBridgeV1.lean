import Mathlib
import ProbeRepairMinimaxKernelV1

namespace InsacermoInteractionDepthBridge

/-!
INSACERMO Interaction-Depth Bridge V1

This file does NOT claim novelty for precedence-constrained class sequencing itself.
It formalizes the INSACERMO semantic bridge from causal PROBE/REPAIR dependencies to a
lower bound on planner interaction depth.

The combinatorial core is deliberately small:
* a dependency witness is a subsequence of the executed role trace;
* deleting interventions cannot increase the number of adjacent role changes;
* therefore an alternating dependency witness of length m forces at least m-1 role changes;
* the hidden-vector minimax family from ProbeRepairMinimaxKernelV1 realizes witnesses
  of arbitrary length and attains the bound exactly on its unique optimal trace.
-/

abbrev Role := InsacermoProbeRepairMinimax.Role

open InsacermoProbeRepairMinimax
open Role

/-- Adjacent changes of intervention role. -/
def interactionDepth : List Role → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: xs => (if a = b then 0 else 1) + interactionDepth (b :: xs)

@[simp] theorem interactionDepth_eq_roleChanges (xs : List Role) :
    interactionDepth xs = roleChanges xs := by
  induction xs with
  | nil => rfl
  | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b ys =>
          simp [interactionDepth, roleChanges, *]

/-- Removing one interior role cannot increase adjacent-change count. -/
theorem erase_middle_le (a b : Role) (xs : List Role) :
    interactionDepth (a :: xs) ≤ interactionDepth (a :: b :: xs) := by
  rw [interactionDepth_eq_roleChanges, interactionDepth_eq_roleChanges]
  cases xs with
  | nil =>
      simp [roleChanges]
  | cons c ys =>
      cases a <;> cases b <;> cases c <;> simp [roleChanges] <;> omega

/-- Interaction depth is monotone under taking a list sublist (subsequence). -/
theorem interactionDepth_mono_sublist {ys xs : List Role} (h : ys <+ xs) :
    interactionDepth ys ≤ interactionDepth xs := by
  induction h with
  | slnil => simp [interactionDepth]
  | @cons a l₁ l₂ h ih =>
      cases l₁ with
      | nil => simp [interactionDepth]
      | cons b bs =>
          cases l₂ with
          | nil => cases h
          | cons c cs =>
              simp only [interactionDepth]
              have ht : interactionDepth (b :: bs) ≤ interactionDepth (c :: cs) := ih
              cases a <;> cases b <;> cases c <;> simp_all <;> omega
  | @cons₂ a l₁ l₂ h ih =>
      cases l₁ with
      | nil =>
          cases l₂ with
          | nil => simp [interactionDepth]
          | cons c cs => simp [interactionDepth]
      | cons b bs =>
          cases l₂ with
          | nil => cases h
          | cons c cs =>
              simp only [interactionDepth]
              have ht : interactionDepth (b :: bs) ≤ interactionDepth (c :: cs) := ih
              cases a <;> cases b <;> cases c <;> simp_all <;> omega

/-- A role trace alternates if every adjacent pair differs. -/
def Alternating : List Role → Prop
  | [] => True
  | [_] => True
  | a :: b :: xs => a ≠ b ∧ Alternating (b :: xs)

/-- An alternating trace changes role at every boundary. -/
theorem interactionDepth_eq_length_sub_one_of_alternating
    (xs : List Role) (h : Alternating xs) :
    interactionDepth xs = xs.length - 1 := by
  induction xs with
  | nil => simp [interactionDepth]
  | cons a xs ih =>
      cases xs with
      | nil => simp [interactionDepth]
      | cons b ys =>
          simp only [Alternating] at h
          rcases h with ⟨hab, htail⟩
          have hi := ih htail
          simp [interactionDepth, hab, hi]
          omega

/-- Causal-chain lower bound.
If a required alternating PROBE/REPAIR dependency chain occurs as a subsequence of a legal
execution, that execution needs at least one role change per chain boundary. -/
theorem alternating_dependency_chain_lower_bound
    {chain trace : List Role}
    (hsub : chain <+ trace)
    (halt : Alternating chain) :
    chain.length - 1 ≤ interactionDepth trace := by
  rw [← interactionDepth_eq_length_sub_one_of_alternating chain halt]
  exact interactionDepth_mono_sublist hsub

/-- Canonical hidden-vector optimal traces are alternating. -/
theorem canonical_alternating (k : Nat) : Alternating (canonical k) := by
  induction k with
  | zero => trivial
  | succ k ih =>
      simp [canonical, Alternating]
      exact ih

/-- The previous minimax family attains the causal-chain bound exactly. -/
theorem hidden_vector_exact_interaction_depth (k : Nat) (hk : 0 < k) :
    interactionDepth (canonical k) = 2 * k - 1 := by
  rw [interactionDepth_eq_roleChanges]
  exact optimal_trace_role_changes k (canonical k) hk (canonical_wins k) (canonical_length k)

/-- Every optimal trace in the hidden-vector family has the same exact interaction depth. -/
theorem every_hidden_vector_optimum_has_exact_depth
    (k : Nat) (hk : 0 < k) (xs : List Role)
    (hwin : run (initial k) xs = some goal)
    (hlen : xs.length = 2 * k) :
    interactionDepth xs = 2 * k - 1 := by
  rw [interactionDepth_eq_roleChanges]
  exact optimal_trace_role_changes k xs hk hwin hlen

/-- No finite universal bound exists on optimal PROBE/REPAIR interaction depth. -/
theorem no_finite_universal_interaction_depth_bound (K : Nat) :
    ∃ k : Nat, 0 < k ∧
      ∃ xs : List Role,
        run (initial k) xs = some goal ∧
        xs.length = 2 * k ∧
        K < interactionDepth xs := by
  rcases unbounded_optimal_interaction_depth K with ⟨k, hk, xs, hwin, hlen, hK⟩
  refine ⟨k, hk, xs, hwin, hlen, ?_⟩
  simpa [interactionDepth_eq_roleChanges] using hK

end InsacermoInteractionDepthBridge
