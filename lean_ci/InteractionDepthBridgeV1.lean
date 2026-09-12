import Mathlib
import ProbeRepairMinimaxKernelV1

namespace InsacermoInteractionDepthBridge

/-!
INSACERMO Interaction-Depth Bridge V1

This file does NOT claim novelty for precedence-constrained class sequencing itself.
It formalizes the INSACERMO semantic bridge from causal PROBE/REPAIR dependencies to a
lower bound on planner interaction depth.

Core statements:
* interaction depth is monotone under deleting interventions from a binary role trace;
* therefore any alternating causal dependency witness of length m forces at least m-1 switches;
* the hidden-vector minimax family realizes arbitrarily long such witnesses and attains the bound
  exactly on every optimal trace.
-/

abbrev Role := InsacermoProbeRepairMinimax.Role

open InsacermoProbeRepairMinimax
open Role

/-- Unit switching cost between two intervention roles. -/
def jump (a b : Role) : Nat := if a = b then 0 else 1

/-- Number of role switches when a trace is entered with previous role `prev`. -/
def switchesFrom : Role → List Role → Nat
  | _, [] => 0
  | prev, x :: xs => jump prev x + switchesFrom x xs

/-- Planner interaction depth: adjacent role switches, with no cost for the first role.  Taking the
minimum over the two possible virtual previous roles removes any artificial initial setup cost. -/
def interactionDepth (xs : List Role) : Nat :=
  Nat.min (switchesFrom probe xs) (switchesFrom repair xs)

/-- Existing minimax-kernel `roleChanges` agrees exactly with the bridge definition. -/
theorem switchesFrom_cons_self (x : Role) (xs : List Role) :
    switchesFrom x xs = roleChanges (x :: xs) := by
  induction xs generalizing x with
  | nil => simp [switchesFrom, roleChanges]
  | cons y ys ih =>
      simp [switchesFrom, roleChanges, jump, ih]

@[simp] theorem interactionDepth_eq_roleChanges (xs : List Role) :
    interactionDepth xs = roleChanges xs := by
  cases xs with
  | nil => simp [interactionDepth, switchesFrom, roleChanges]
  | cons x ys =>
      cases x with
      | probe =>
          simp [interactionDepth, switchesFrom, jump, switchesFrom_cons_self, roleChanges]
      | repair =>
          simp [interactionDepth, switchesFrom, jump, switchesFrom_cons_self, roleChanges]

/-- Triangle inequality for one skipped binary role. -/
theorem switchesFrom_triangle (p a : Role) (xs : List Role) :
    switchesFrom p xs ≤ jump p a + switchesFrom a xs := by
  cases xs with
  | nil => simp [switchesFrom, jump]
  | cons x ys =>
      cases p <;> cases a <;> cases x <;> simp [switchesFrom, jump] <;> omega

/-- With a fixed virtual previous role, deleting trace elements cannot increase switching cost. -/
theorem switchesFrom_mono_sublist {ys xs : List Role}
    (h : List.Sublist ys xs) (prev : Role) :
    switchesFrom prev ys ≤ switchesFrom prev xs := by
  induction h generalizing prev with
  | slnil => simp [switchesFrom]
  | @cons l₁ l₂ a h ih =>
      exact le_trans (ih prev) (switchesFrom_triangle prev a l₂)
  | @cons₂ l₁ l₂ a h ih =>
      simp only [switchesFrom]
      exact Nat.add_le_add_left (ih a) (jump prev a)

/-- Interaction depth is monotone under taking any subsequence. -/
theorem interactionDepth_mono_sublist {ys xs : List Role}
    (h : List.Sublist ys xs) :
    interactionDepth ys ≤ interactionDepth xs := by
  unfold interactionDepth
  have hp := switchesFrom_mono_sublist h probe
  have hr := switchesFrom_mono_sublist h repair
  omega

/-- Extensional definition of a fully alternating role trace: every possible boundary is a switch. -/
def Alternating (xs : List Role) : Prop :=
  interactionDepth xs = xs.length - 1

/-- Causal-chain lower bound.
If an alternating required PROBE/REPAIR dependency chain occurs as a subsequence of a legal
execution, the full execution pays at least one role switch per dependency-chain boundary. -/
theorem alternating_dependency_chain_lower_bound
    {chain trace : List Role}
    (hsub : List.Sublist chain trace)
    (halt : Alternating chain) :
    chain.length - 1 ≤ interactionDepth trace := by
  rw [← halt]
  exact interactionDepth_mono_sublist hsub

/-- The previous minimax family attains the causal-chain bound exactly. -/
theorem hidden_vector_exact_interaction_depth (k : Nat) (hk : 0 < k) :
    interactionDepth (canonical k) = 2 * k - 1 := by
  rw [interactionDepth_eq_roleChanges]
  exact optimal_trace_role_changes k (canonical k) hk (canonical_wins k) (canonical_length k)

/-- Canonical hidden-vector optimal traces are alternating in the bridge sense. -/
theorem canonical_alternating (k : Nat) : Alternating (canonical k) := by
  cases k with
  | zero => simp [Alternating, interactionDepth, switchesFrom, canonical]
  | succ k =>
      unfold Alternating
      rw [hidden_vector_exact_interaction_depth (k + 1) (by omega), canonical_length]
      omega

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
  rw [interactionDepth_eq_roleChanges]
  exact hK

end InsacermoInteractionDepthBridge
