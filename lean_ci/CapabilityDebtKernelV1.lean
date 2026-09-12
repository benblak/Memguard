import Mathlib
import TemporalHorizonKernelV1

namespace InsacermoCapabilityDebt

open Set

universe u v w

section GenericCapability

variable {State : Type u} {Req : Type v} {Cap : Type w} [Preorder Cap]

/-- Guarantee semantics depending jointly on state, available capability, and requirement. -/
def CapabilityMonotone (Win : State → Cap → Req → Prop) : Prop :=
  ∀ {x q cLow cHigh}, cLow ≤ cHigh → Win x cLow q → Win x cHigh q

/-- A destruction is admissible under capability `c` when every contracted guarantee available
before destruction under `c` remains available after destruction under that same capability. -/
def AdmissibleWithCapability
    (Win : State → Cap → Req → Prop) (Γ : Set Req) (c : Cap)
    (d : State → State) (x : State) : Prop :=
  ∀ q, q ∈ Γ → Win x c q → Win (d x) c q

/-- Contracted guarantees exposed as lost by a destruction at capability `c`. -/
def CapabilityDebt
    (Win : State → Cap → Req → Prop) (Γ : Set Req) (c : Cap)
    (d : State → State) (x : State) : Set Req :=
  {q | q ∈ Γ ∧ Win x c q ∧ ¬ Win (d x) c q}

/-- Capability-relative destruction is admissible exactly when its debt set is empty. -/
theorem admissibleWithCapability_iff_debt_empty
    (Win : State → Cap → Req → Prop) (Γ : Set Req) (c : Cap)
    (d : State → State) (x : State) :
    AdmissibleWithCapability Win Γ c d x ↔
      CapabilityDebt Win Γ c d x = ∅ := by
  constructor
  · intro h
    ext q
    constructor
    · intro hq
      exact False.elim (hq.2.2 (h q hq.1 hq.2.1))
    · intro hq
      simp at hq
  · intro h
    intro q hq hx
    by_contra hlost
    have hmem : q ∈ CapabilityDebt Win Γ c d x := ⟨hq, hx, hlost⟩
    rw [h] at hmem
    exact hmem

/-- Inadmissibility is witnessed by one precise contracted guarantee that survives in the source
but is lost after destruction at the same capability. -/
theorem not_admissibleWithCapability_iff_exists_witness
    (Win : State → Cap → Req → Prop) (Γ : Set Req) (c : Cap)
    (d : State → State) (x : State) :
    ¬ AdmissibleWithCapability Win Γ c d x ↔
      ∃ q, q ∈ Γ ∧ Win x c q ∧ ¬ Win (d x) c q := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro q hq hx
    by_contra hlost
    apply hnone
    exact ⟨q, hq, hx, hlost⟩
  · rintro ⟨q, hq, hx, hlost⟩ hadm
    exact hlost (hadm q hq hx)

/-- Main generic result. If a destruction is admissible with a stronger capability but becomes
inadmissible after capability loss, then there is an exact requirement whose post-destruction
availability was being supplied by the stronger capability. The original source still supports
that requirement after capability loss, so the lost capability exposes genuine destruction debt. -/
theorem capability_loss_revocation_has_compensation_witness
    (Win : State → Cap → Req → Prop) (Γ : Set Req)
    (hmono : CapabilityMonotone Win)
    {cLow cHigh : Cap} (hcap : cLow ≤ cHigh)
    (d : State → State) (x : State)
    (hadmHigh : AdmissibleWithCapability Win Γ cHigh d x)
    (hnotLow : ¬ AdmissibleWithCapability Win Γ cLow d x) :
    ∃ q,
      q ∈ Γ ∧
      Win x cLow q ∧
      Win (d x) cHigh q ∧
      ¬ Win (d x) cLow q := by
  rcases (not_admissibleWithCapability_iff_exists_witness Win Γ cLow d x).mp hnotLow with
    ⟨q, hq, hxLow, hlostLow⟩
  have hxHigh : Win x cHigh q := hmono hcap hxLow
  have hdHigh : Win (d x) cHigh q := hadmHigh q hq hxHigh
  exact ⟨q, hq, hxLow, hdHigh, hlostLow⟩

/-- Debt emergence formulation: high capability can leave the debt empty while lower capability
exposes a nonempty debt for the exact same destruction and contract. -/
theorem capability_loss_can_expose_destruction_debt
    (Win : State → Cap → Req → Prop) (Γ : Set Req)
    {cLow cHigh : Cap} (d : State → State) (x : State)
    (hadmHigh : AdmissibleWithCapability Win Γ cHigh d x)
    (hnotLow : ¬ AdmissibleWithCapability Win Γ cLow d x) :
    CapabilityDebt Win Γ cHigh d x = ∅ ∧
    CapabilityDebt Win Γ cLow d x ≠ ∅ := by
  constructor
  · exact (admissibleWithCapability_iff_debt_empty Win Γ cHigh d x).mp hadmHigh
  · intro hempty
    apply hnotLow
    exact (admissibleWithCapability_iff_debt_empty Win Γ cLow d x).mpr hempty

end GenericCapability

section CertifiedWitness

inductive MemoryState
  | rich
  | forgotten
  deriving DecidableEq, Repr

open MemoryState

/-- One contracted requirement. -/
def MemoryReq := Unit

/-- Rich memory can always satisfy the requirement. Forgotten memory can satisfy it only when
external capability is at least 1. -/
def WinMemory : MemoryState → Nat → MemoryReq → Prop
  | rich, _, _ => True
  | forgotten, c, _ => 1 ≤ c

/-- Forget the internal distinction/state resource. -/
def forgetNow : MemoryState → MemoryState
  | rich => forgotten
  | s => s

/-- The sole requirement remains contractually due. -/
def MemoryContract : Set MemoryReq := Set.univ

/-- More external capability never removes a guarantee in this witness. -/
theorem winMemory_capability_monotone : CapabilityMonotone WinMemory := by
  intro x q cLow cHigh hcap hwin
  cases x with
  | rich => trivial
  | forgotten =>
      exact le_trans hwin hcap

/-- With capability 1, forgetting is admissible: capability compensates for what memory lost. -/
theorem forgetNow_admissible_high_capability :
    AdmissibleWithCapability WinMemory MemoryContract 1 forgetNow rich := by
  intro q hq hx
  change 1 ≤ 1
  exact le_rfl

/-- With capability 0, the same forgetting is inadmissible: the source can still satisfy the
contract, but the forgotten state no longer can. -/
theorem forgetNow_inadmissible_low_capability :
    ¬ AdmissibleWithCapability WinMemory MemoryContract 0 forgetNow rich := by
  intro h
  have hsource : WinMemory rich 0 () := by trivial
  have htarget := h () (by simp [MemoryContract]) hsource
  change 1 ≤ 0 at htarget
  omega

/-- Finite certified phenomenon: capability can buy a right to forget which disappears when the
capability is removed. -/
theorem capability_can_buy_right_to_forget :
    AdmissibleWithCapability WinMemory MemoryContract 1 forgetNow rich ∧
    ¬ AdmissibleWithCapability WinMemory MemoryContract 0 forgetNow rich := by
  exact ⟨forgetNow_admissible_high_capability,
    forgetNow_inadmissible_low_capability⟩

/-- The generic theorem identifies exactly what the high capability had been compensating for. -/
theorem certified_capability_loss_exposes_compensated_debt :
    ∃ q,
      q ∈ MemoryContract ∧
      WinMemory rich 0 q ∧
      WinMemory (forgetNow rich) 1 q ∧
      ¬ WinMemory (forgetNow rich) 0 q := by
  exact capability_loss_revocation_has_compensation_witness
    WinMemory MemoryContract winMemory_capability_monotone
    (show (0 : Nat) ≤ 1 by omega)
    forgetNow rich
    forgetNow_admissible_high_capability
    forgetNow_inadmissible_low_capability

/-- In debt language: the same forgetting has zero debt while the compensating capability exists,
and nonzero debt after capability loss. -/
theorem certified_capability_loss_creates_visible_debt :
    CapabilityDebt WinMemory MemoryContract 1 forgetNow rich = ∅ ∧
    CapabilityDebt WinMemory MemoryContract 0 forgetNow rich ≠ ∅ := by
  exact capability_loss_can_expose_destruction_debt
    WinMemory MemoryContract forgetNow rich
    forgetNow_admissible_high_capability
    forgetNow_inadmissible_low_capability

end CertifiedWitness

end InsacermoCapabilityDebt
