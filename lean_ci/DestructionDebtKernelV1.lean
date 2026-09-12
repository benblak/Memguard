import Mathlib
import DestructionAdmissibilityKernelV1

namespace InsacermoDestructionDebt

open Set
open InsacermoDestructionAdmissibility

/-!
INSACERMO Capability-Induced Destruction Debt Kernel V1

This file tests whether the existing capability-induced information-debt phenomenon can be stated
as a dynamic failure of destruction admissibility.

The witness is deliberately minimal: two worlds, state-specific base actions, and one temporary
universal action. Fine information is safe with the base capability. Coarse information is unsafe
with the base capability, but becomes safe after adding the universal action. Therefore forgetting
is admissible while the extra capability is present and inadmissible without it. If the system
forgets while expanded and later loses the extra capability, it lands outside the contract-safe
region.

This is a finite witness theorem. It does not yet formalize entropy-valued debt or the unbounded
log2(n) family; those require an explicit quantitative restoration measure.
-/

inductive Action
  | left
  | right
  | universal
  deriving DecidableEq, Repr

open Action

/-- World-specific base actions plus a universal repair. -/
def Good : Bool → Action → Prop
  | false, left => True
  | true, right => True
  | _, universal => True
  | _, _ => False

/-- Base capability has only state-specific actions. -/
def baseCap : Set Action := {left, right}

/-- Expanded capability adds the universal action. -/
def expandedCap : Set Action := Set.univ

/-- Fine observation retains the world bit. -/
def fineObs : Bool → Bool := id

/-- Coarse observation forgets the world bit completely. -/
def coarseObs : Bool → Bool := fun _ => false

/-- Fine information is safe with only the base capability. -/
theorem fine_safe_base :
    FiberSafe Good Set.univ baseCap fineObs := by
  intro y hy
  cases y with
  | false =>
      refine ⟨left, by simp [baseCap], ?_⟩
      intro s hs
      cases s <;> simp [Fiber, fineObs, Good] at hs ⊢
  | true =>
      refine ⟨right, by simp [baseCap], ?_⟩
      intro s hs
      cases s <;> simp [Fiber, fineObs, Good] at hs ⊢

/-- Complete forgetting is safe while the universal capability is available. -/
theorem coarse_safe_expanded :
    FiberSafe Good Set.univ expandedCap coarseObs := by
  intro y hy
  refine ⟨universal, by simp [expandedCap], ?_⟩
  intro s hs
  cases s <;> simp [Good]

/-- Complete forgetting is unsafe under the original base capability. -/
theorem coarse_unsafe_base :
    ¬ FiberSafe Good Set.univ baseCap coarseObs := by
  intro hsafe
  have hy : (Fiber (B := Set.univ) coarseObs false).Nonempty := by
    refine ⟨false, ?_⟩
    simp [Fiber, coarseObs]
  rcases hsafe false hy with ⟨a, ha, hgood⟩
  cases a with
  | left =>
      have h := hgood true (by simp [Fiber, coarseObs])
      simp [Good] at h
  | right =>
      have h := hgood false (by simp [Fiber, coarseObs])
      simp [Good] at h
  | universal =>
      simp [baseCap] at ha

inductive CapMode
  | base
  | expanded
  deriving DecidableEq, Repr

inductive RepMode
  | fine
  | coarse
  deriving DecidableEq, Repr

structure Config where
  capMode : CapMode
  repMode : RepMode
  deriving DecidableEq, Repr

open CapMode RepMode

def capSet : CapMode → Set Action
  | base => baseCap
  | expanded => expandedCap

def obsFun : RepMode → Bool → Bool
  | fine => fineObs
  | coarse => coarseObs

/-- Contract-safe configuration in the one-shot common-action semantics. -/
def SafeConfig (x : Config) : Prop :=
  FiberSafe Good Set.univ (capSet x.capMode) (obsFun x.repMode)

/-- Single abstract future requirement: remain actionably safe. -/
def Win (x : Config) (_q : Unit) : Prop := SafeConfig x

def Contract : Set Unit := Set.univ

def baseFine : Config := ⟨base, fine⟩
def baseCoarse : Config := ⟨base, coarse⟩
def expandedFine : Config := ⟨expanded, fine⟩
def expandedCoarse : Config := ⟨expanded, coarse⟩

/-- Destructive memory operation: replace the representation by the coarse observation. -/
def forget (x : Config) : Config := { x with repMode := coarse }

/-- Capability-loss operation: remove the temporary universal action. -/
def loseCapability (x : Config) : Config := { x with capMode := base }

theorem safe_baseFine : SafeConfig baseFine := by
  simpa only [SafeConfig, baseFine, capSet, obsFun] using fine_safe_base

theorem safe_expandedFine : SafeConfig expandedFine := by
  have hsub : baseCap ⊆ expandedCap := by
    intro a ha
    simp only [expandedCap, Set.mem_univ]
  have hsafe : FiberSafe Good Set.univ expandedCap fineObs :=
    fiberSafe_of_capability_expansion Good Set.univ hsub fine_safe_base
  simpa only [SafeConfig, expandedFine, capSet, obsFun] using hsafe

theorem safe_expandedCoarse : SafeConfig expandedCoarse := by
  simpa only [SafeConfig, expandedCoarse, capSet, obsFun] using coarse_safe_expanded

theorem unsafe_baseCoarse : ¬ SafeConfig baseCoarse := by
  simpa only [SafeConfig, baseCoarse, capSet, obsFun] using coarse_unsafe_base

/-- With the temporary universal action, complete forgetting is destruction-admissible. -/
theorem forgetting_admissible_when_expanded :
    AdmissibleDestruction Win Contract forget expandedFine := by
  intro q hq hx
  have hs : SafeConfig expandedCoarse := safe_expandedCoarse
  simpa only [Win, forget, expandedFine, expandedCoarse] using hs

/-- The same forgetting operation is NOT destruction-admissible under the base capability. -/
theorem forgetting_inadmissible_when_base :
    ¬ AdmissibleDestruction Win Contract forget baseFine := by
  intro h
  have hsource : Win baseFine () := by
    exact safe_baseFine
  have htarget : Win (forget baseFine) () :=
    h () (by simp only [Contract, Set.mem_univ]) hsource
  have hbad : SafeConfig baseCoarse := by
    simpa only [Win, forget, baseFine, baseCoarse] using htarget
  exact unsafe_baseCoarse hbad

/-- After safe forgetting under expanded capability, losing that capability is itself inadmissible:
the target is the unsafe base/coarse configuration. -/
theorem capability_loss_after_forgetting_is_inadmissible :
    ¬ AdmissibleDestruction Win Contract loseCapability expandedCoarse := by
  intro h
  have hsource : Win expandedCoarse () := by
    exact safe_expandedCoarse
  have htarget : Win (loseCapability expandedCoarse) () :=
    h () (by simp only [Contract, Set.mem_univ]) hsource
  have hbad : SafeConfig baseCoarse := by
    simpa only [Win, loseCapability, expandedCoarse, baseCoarse] using htarget
  exact unsafe_baseCoarse hbad

/-- Consolidated dynamic witness: capability expansion buys the right to forget, but the resulting
coarsening becomes unsafe if the borrowed capability is later lost. -/
theorem capability_induced_destruction_debt :
    SafeConfig baseFine ∧
    AdmissibleDestruction Win Contract forget expandedFine ∧
    (¬ AdmissibleDestruction Win Contract forget baseFine) ∧
    SafeConfig expandedCoarse ∧
    (¬ SafeConfig baseCoarse) ∧
    (¬ AdmissibleDestruction Win Contract loseCapability expandedCoarse) := by
  exact ⟨safe_baseFine,
    forgetting_admissible_when_expanded,
    forgetting_inadmissible_when_base,
    safe_expandedCoarse,
    unsafe_baseCoarse,
    capability_loss_after_forgetting_is_inadmissible⟩

end InsacermoDestructionDebt
