import Mathlib
import DestructionAdmissibilityKernelV1

namespace InsacermoTemporalDestruction

open Set
open InsacermoDestructionAdmissibility

/-!
INSACERMO Temporal Destruction Kernel V1

Goal.
Show that preserving immediate one-step actionability is not sufficient to preserve a future
contract. A destructive transformation can leave the current state locally safe while removing the
only path to a later required goal.

This is a finite deterministic witness separating:
  * LocalSafe: an immediate legal action remains available;
  * FutureSafe: the declared future goal is still reachable;
  * temporal destruction admissibility: preserve FutureSafe, not merely LocalSafe.

The witness is intentionally minimal and does not claim that all planner results reduce to this one
example. It establishes the semantic need for horizon-sensitive preservation.
-/

inductive State
  | start
  | bridge
  | dead
  | goal
  deriving DecidableEq, Repr

inductive Act
  | wait
  | advance
  | destroy
  deriving DecidableEq, Repr

open State Act

/-- Legal actions. Dead remains locally operable through wait, so local safety is preserved even
though the future goal may already be impossible. -/
def Legal : State → Act → Prop
  | start, wait => True
  | start, advance => True
  | start, destroy => True
  | bridge, wait => True
  | bridge, advance => True
  | dead, wait => True
  | goal, wait => True
  | _, _ => False

/-- Deterministic transition relation. -/
def Step : State → Act → State
  | start, wait => start
  | start, advance => bridge
  | start, destroy => dead
  | bridge, wait => bridge
  | bridge, advance => goal
  | dead, wait => dead
  | goal, wait => goal
  | s, _ => s

/-- Immediate actionability: at least one legal action exists now. -/
def LocalSafe (s : State) : Prop := ∃ a, Legal s a

@[simp] theorem localSafe_start : LocalSafe start := by
  exact ⟨wait, by simp [Legal]⟩

@[simp] theorem localSafe_dead : LocalSafe dead := by
  exact ⟨wait, by simp [Legal]⟩

@[simp] theorem localSafe_goal : LocalSafe goal := by
  exact ⟨wait, by simp [Legal]⟩

/-- Reachability relation for finite traces. -/
inductive Reach : State → State → Prop
  | refl (s) : Reach s s
  | step {s t u a} : Reach s t → Legal t a → Step t a = u → Reach s u

/-- Future contract: the goal must remain reachable. -/
def FutureSafe (s : State) : Prop := Reach s goal

/-- Start satisfies the future contract via advance; advance. -/
theorem futureSafe_start : FutureSafe start := by
  unfold FutureSafe
  have h1 : Reach start bridge := by
    exact Reach.step (a := advance) (Reach.refl start) (by simp [Legal]) (by rfl)
  exact Reach.step (a := advance) h1 (by simp [Legal]) (by rfl)

/-- Goal trivially satisfies the future contract. -/
theorem futureSafe_goal : FutureSafe goal := by
  exact Reach.refl goal

/-- Every legal step from dead stays dead. -/
theorem legal_step_from_dead_stays_dead {a : Act} (h : Legal dead a) : Step dead a = dead := by
  cases a with
  | wait => rfl
  | advance => simp [Legal] at h
  | destroy => simp [Legal] at h

/-- Dead cannot reach goal, despite being locally safe. -/
theorem not_futureSafe_dead : ¬ FutureSafe dead := by
  intro h
  unfold FutureSafe at h
  have aux : ∀ {t}, Reach dead t → t = dead := by
    intro t hr
    induction hr with
    | refl => rfl
    | @step t u a hreach hlegal hstep ih =>
        have ht : t = dead := ih
        subst t
        have hs : Step dead a = dead := legal_step_from_dead_stays_dead hlegal
        calc
          u = Step dead a := hstep.symm
          _ = dead := hs
  have hgoal : goal = dead := aux h
  cases hgoal

/-- The destructive transition keeps immediate actionability. -/
theorem destroy_preserves_local_safety :
    LocalSafe start → LocalSafe (Step start destroy) := by
  intro _
  simpa [Step] using localSafe_dead

/-- But the same destructive transition destroys the future contract. -/
theorem destroy_breaks_future_safety :
    FutureSafe start ∧ ¬ FutureSafe (Step start destroy) := by
  constructor
  · exact futureSafe_start
  · simpa [Step] using not_futureSafe_dead

/-- One-step local preservation predicate. -/
def LocallyAdmissible (d : State → State) (s : State) : Prop :=
  LocalSafe s → LocalSafe (d s)

/-- Horizon-sensitive temporal preservation predicate. -/
def TemporallyAdmissible (d : State → State) (s : State) : Prop :=
  FutureSafe s → FutureSafe (d s)

/-- Destructive map used in the witness. -/
def destroyNow : State → State
  | start => dead
  | s => s

/-- Destruction is locally admissible at start. -/
theorem destroyNow_locally_admissible : LocallyAdmissible destroyNow start := by
  intro _
  exact localSafe_dead

/-- Yet the same destruction is temporally inadmissible at start. -/
theorem destroyNow_temporally_inadmissible : ¬ TemporallyAdmissible destroyNow start := by
  intro h
  have htarget : FutureSafe (destroyNow start) := h futureSafe_start
  exact not_futureSafe_dead (by simpa [destroyNow] using htarget)

/-- Separation theorem: immediate safety preservation does not imply future-contract preservation. -/
theorem local_admissibility_does_not_imply_temporal_admissibility :
    LocallyAdmissible destroyNow start ∧ ¬ TemporallyAdmissible destroyNow start := by
  exact ⟨destroyNow_locally_admissible, destroyNow_temporally_inadmissible⟩

/-- Recast in the generic destruction-admissibility framework using future reachability as Win. -/
def WinFuture (s : State) (_q : Unit) : Prop := FutureSafe s

def Contract : Set Unit := Set.univ

/-- Horizon-sensitive destruction is rejected by the generic preservation rule once the contract
requirement is taken to be future reachability. -/
theorem generic_future_preservation_rejects_destroyNow :
    ¬ AdmissibleDestruction WinFuture Contract destroyNow start := by
  intro h
  have htarget : WinFuture (destroyNow start) () :=
    h () (by simp [Contract]) futureSafe_start
  exact not_futureSafe_dead (by simpa [WinFuture, destroyNow] using htarget)

/-- Main consolidated result. -/
theorem temporal_destruction_separation_v1 :
    LocalSafe start ∧
    LocalSafe (destroyNow start) ∧
    FutureSafe start ∧
    ¬ FutureSafe (destroyNow start) ∧
    LocallyAdmissible destroyNow start ∧
    ¬ TemporallyAdmissible destroyNow start ∧
    ¬ AdmissibleDestruction WinFuture Contract destroyNow start := by
  exact ⟨localSafe_start,
    localSafe_dead,
    futureSafe_start,
    by simpa [destroyNow] using not_futureSafe_dead,
    destroyNow_locally_admissible,
    destroyNow_temporally_inadmissible,
    generic_future_preservation_rejects_destroyNow⟩

end InsacermoTemporalDestruction
