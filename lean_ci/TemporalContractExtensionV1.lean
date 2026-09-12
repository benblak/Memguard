import Mathlib
import DestructionAdmissibilityKernelV1
import TemporalDestructionKernelV1

namespace InsacermoTemporalContractExtension

open Set
open InsacermoDestructionAdmissibility
open InsacermoTemporalDestruction

/-!
INSACERMO Temporal Contract Extension V1

Purpose.
Unify immediate and future preservation inside one contract-relative admissibility relation.
The same destructive map can be admissible under a present-only contract and become inadmissible
when the contract is extended with a future reachability obligation.

This makes horizon dependence a property of the declared requirement set rather than a second,
unrelated notion of safety.
-/

inductive Requirement
  | immediate
  | futureGoal
  deriving DecidableEq, Repr

open Requirement

/-- One guarantee semantics for both present actionability and future reachability. -/
def WinTemporal : State → Requirement → Prop
  | s, immediate => LocalSafe s
  | s, futureGoal => FutureSafe s

/-- Present-only contract: preserve immediate actionability. -/
def PresentContract : Set Requirement := {immediate}

/-- Extended temporal contract: preserve both immediate actionability and future goal reachability. -/
def FutureContract : Set Requirement := Set.univ

/-- The future contract genuinely extends the present contract. -/
theorem presentContract_subset_futureContract : PresentContract ⊆ FutureContract := by
  intro q hq
  simp [FutureContract]

/-- The new future obligation was not already present in the local contract. -/
theorem futureGoal_added_by_extension :
    futureGoal ∉ PresentContract ∧ futureGoal ∈ FutureContract := by
  constructor <;> simp [PresentContract, FutureContract]

/-- Generic obstruction lemma: if a required guarantee exists before destruction and is lost after,
then that destruction is inadmissible. -/
theorem inadmissible_of_required_guarantee_destroyed
    {S R : Type*}
    (Win : S → R → Prop) (Γ : Set R) (d : S → S) (x : S) (q : R)
    (hq : q ∈ Γ) (hx : Win x q) (hlost : ¬ Win (d x) q) :
    ¬ AdmissibleDestruction Win Γ d x := by
  intro h
  exact hlost (h q hq hx)

/-- Under the present-only contract, destroyNow is admissible: local actionability survives. -/
theorem destroyNow_admissible_present :
    AdmissibleDestruction WinTemporal PresentContract destroyNow start := by
  intro q hq _hx
  have hqi : q = immediate := by
    simpa [PresentContract] using hq
  subst q
  simpa [WinTemporal, destroyNow] using localSafe_dead

/-- Under the extended temporal contract, the exact same destruction is inadmissible because the
futureGoal guarantee is lost. -/
theorem destroyNow_inadmissible_future :
    ¬ AdmissibleDestruction WinTemporal FutureContract destroyNow start := by
  apply inadmissible_of_required_guarantee_destroyed
    WinTemporal FutureContract destroyNow start futureGoal
  · simp [FutureContract]
  · simpa [WinTemporal] using futureSafe_start
  · intro h
    exact not_futureSafe_dead (by simpa [WinTemporal, destroyNow] using h)

/-- Contract strengthening can only reduce the admissible-destruction relation. -/
theorem future_admissible_implies_present_admissible
    (d : State → State) (s : State)
    (h : AdmissibleDestruction WinTemporal FutureContract d s) :
    AdmissibleDestruction WinTemporal PresentContract d s := by
  exact preserves_contract_antitone WinTemporal
    presentContract_subset_futureContract h

/-- Strictness witness: the implication cannot be reversed in general. -/
theorem present_admissibility_does_not_imply_future_admissibility :
    AdmissibleDestruction WinTemporal PresentContract destroyNow start ∧
    ¬ AdmissibleDestruction WinTemporal FutureContract destroyNow start := by
  exact ⟨destroyNow_admissible_present, destroyNow_inadmissible_future⟩

/-- Main result: adding a future obligation can revoke a previously valid right to destroy. -/
theorem contract_extension_can_revoke_destruction_right :
    PresentContract ⊆ FutureContract ∧
    futureGoal ∉ PresentContract ∧
    futureGoal ∈ FutureContract ∧
    AdmissibleDestruction WinTemporal PresentContract destroyNow start ∧
    ¬ AdmissibleDestruction WinTemporal FutureContract destroyNow start := by
  exact ⟨presentContract_subset_futureContract,
    futureGoal_added_by_extension.1,
    futureGoal_added_by_extension.2,
    destroyNow_admissible_present,
    destroyNow_inadmissible_future⟩

/-- Relation-level strictness: every future-admissible destruction is present-admissible,
but there exists a present-admissible destruction that is not future-admissible. -/
theorem admissibility_relation_strictly_shrinks_under_extension :
    (∀ (d : State → State) (s : State),
      AdmissibleDestruction WinTemporal FutureContract d s →
      AdmissibleDestruction WinTemporal PresentContract d s) ∧
    (∃ (d : State → State) (s : State),
      AdmissibleDestruction WinTemporal PresentContract d s ∧
      ¬ AdmissibleDestruction WinTemporal FutureContract d s) := by
  constructor
  · intro d s h
    exact future_admissible_implies_present_admissible d s h
  · exact ⟨destroyNow, start,
      destroyNow_admissible_present,
      destroyNow_inadmissible_future⟩

end InsacermoTemporalContractExtension
