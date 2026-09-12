import Mathlib

namespace InsacermoProbeRepairAlternation

/-!
INSACERMO Probe–Repair Alternation Kernel V1.

This file formalizes the belief-level quotient of a finite deterministic staged family:
at each unresolved stage a PROBE is required to learn the branch, then a branch-matched
REPAIR advances the physical stage and makes the next uncertainty relevant.

Targets:
T5a  PROBE then REPAIR advances one stage, while REPAIR before PROBE fails.
T5b  The canonical winning role trace is P,R,P,R,...,P,R.
T5c  Every winning trace is exactly that canonical trace.
T5d  Hence winning traces alternate and have length exactly 2k.
T5e  For k >= 2, every winning trace has prefix P,R,P.
T5f  Alternation depth is unbounded across the family.
-/

inductive Role
  | probe
  | repair
  deriving DecidableEq, Repr

open Role

/-- `remaining` is the number of physical stages still to close.
`informed = false` means the current stage's branch is still unresolved;
`informed = true` means the required branch information has been acquired. -/
structure ARState where
  remaining : Nat
  informed : Bool
  deriving DecidableEq, Repr

/-- The staged role dynamics.  At an unresolved nonterminal stage, only PROBE is legal.
After PROBE, only REPAIR is legal; REPAIR advances one physical stage and resets the next
stage to unresolved.  No action is legal after the terminal stage. -/
def step : ARState → Role → Option ARState
  | ⟨0, _⟩, _ => none
  | ⟨n + 1, false⟩, probe => some ⟨n + 1, true⟩
  | ⟨n + 1, true⟩, repair => some ⟨n, false⟩
  | _, _ => none

/-- Execute a role trace. -/
def run : ARState → List Role → Option ARState
  | s, [] => some s
  | s, a :: xs =>
      match step s a with
      | none => none
      | some s' => run s' xs

def initial (k : Nat) : ARState := ⟨k, false⟩
def goal : ARState := ⟨0, false⟩

/-- The forced alternating trace for `k` stages. -/
def canonical : Nat → List Role
  | 0 => []
  | k + 1 => probe :: repair :: canonical k

/-- T5a — PROBE followed by REPAIR advances exactly one stage. -/
theorem probe_then_repair_advances (k : Nat) :
    run (initial (k + 1)) [probe, repair] = some (initial k) := by
  rfl

/-- T5a — REPAIR before the required PROBE is illegal. -/
theorem repair_before_probe_fails (k : Nat) :
    run (initial (k + 1)) [repair, probe] = none := by
  rfl

/-- T5b — the canonical alternating trace reaches the contract goal. -/
theorem canonical_wins (k : Nat) :
    run (initial k) (canonical k) = some goal := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [canonical, run, initial, step, ih, goal]

/-- T5c — there is no other successful role ordering in this staged family. -/
theorem winning_trace_eq_canonical (k : Nat) (xs : List Role)
    (h : run (initial k) xs = some goal) :
    xs = canonical k := by
  induction k generalizing xs with
  | zero =>
      cases xs with
      | nil => rfl
      | cons a xs =>
          cases a <;> simp [run, initial, step, goal] at h
  | succ k ih =>
      cases xs with
      | nil =>
          simp [run, initial, goal] at h
      | cons a ys =>
          cases a with
          | repair =>
              simp [run, initial, step] at h
          | probe =>
              cases ys with
              | nil =>
                  simp [run, initial, step, goal] at h
              | cons b zs =>
                  cases b with
                  | probe =>
                      simp [run, initial, step] at h
                  | repair =>
                      have hz : run (initial k) zs = some goal := by
                        simpa [run, initial, step] using h
                      have hcanon : zs = canonical k := ih zs hz
                      simp [canonical, hcanon]

/-- Adjacent roles differ throughout the trace. -/
def Alternating : List Role → Prop
  | [] => True
  | [_] => True
  | a :: b :: xs => a ≠ b ∧ Alternating (b :: xs)

/-- The canonical trace alternates at every adjacent position. -/
theorem canonical_alternating (k : Nat) : Alternating (canonical k) := by
  induction k with
  | zero => simp [canonical, Alternating]
  | succ k ih =>
      cases k with
      | zero => simp [canonical, Alternating]
      | succ k =>
          simp [canonical, Alternating, ih]

/-- The canonical trace has exactly two roles per physical stage. -/
theorem canonical_length (k : Nat) : (canonical k).length = 2 * k := by
  induction k with
  | zero => simp [canonical]
  | succ k ih =>
      simp [canonical, ih]
      omega

/-- T5d — every winning trace alternates and has exact length 2k. -/
theorem winning_trace_alternates_and_length (k : Nat) (xs : List Role)
    (h : run (initial k) xs = some goal) :
    Alternating xs ∧ xs.length = 2 * k := by
  have hx : xs = canonical k := winning_trace_eq_canonical k xs h
  subst xs
  exact ⟨canonical_alternating k, canonical_length k⟩

/-- T5e — once two or more stages remain, every winning trace necessarily returns to PROBE
after the first REPAIR.  Thus a one-block `all probes, then all repairs` architecture cannot
realize this family. -/
theorem winning_two_plus_forces_PRP_prefix (k : Nat) (xs : List Role)
    (h : run (initial (k + 2)) xs = some goal) :
    xs.take 3 = [probe, repair, probe] := by
  rw [winning_trace_eq_canonical (k + 2) xs h]
  simp [canonical]

/-- T5f — there is no finite universal bound on the length of a forced alternating winning trace.
Since `Alternating xs` holds, every one of its `length - 1` adjacent boundaries is a role switch. -/
theorem unbounded_probe_repair_alternation (K : Nat) :
    ∃ k : Nat, ∃ xs : List Role,
      run (initial k) xs = some goal ∧
      Alternating xs ∧
      K < xs.length := by
  refine ⟨K + 1, canonical (K + 1), canonical_wins (K + 1), canonical_alternating (K + 1), ?_⟩
  rw [canonical_length]
  omega

end InsacermoProbeRepairAlternation
