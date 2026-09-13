import Mathlib
import JointHorizonCapabilityKernelV1

namespace InsacermoCriticalHorizon

open Set
open InsacermoCapabilityDebt
open InsacermoJointHorizonCapability

universe u v w

section GenericPersistence

variable {State : Type u} {Req : Type v} {Cap : Type w} [Preorder Cap]

/-- Source-side guarantee persistence along the horizon-capability path.
Even as horizon advances and available capability may fall, every guarantee that was both contracted
and realizable from the original source state remains realizable from that source state later. -/
def SourcePersistent
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (cap : Nat → Cap) (x : State) : Prop :=
  ∀ {h k q}, h ≤ k → q ∈ Γ h → Win x (cap h) q → Win x (cap k) q

/-- Under growing contracts, falling capability, capability-monotone guarantee semantics, and
source persistence, later admissibility implies earlier admissibility. Thus admissibility is an
initial segment in horizon. -/
theorem joint_admissible_antitone_under_source_persistence
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (cap : Nat → Cap)
    (hΓ : ContractMonotone Γ)
    (hcap : CapabilityAntitone cap)
    (hWin : CapabilityMonotone Win)
    (x : State) (hsrc : SourcePersistent Win Γ cap x)
    (d : State → State)
    {h k : Nat} (hhk : h ≤ k)
    (hadmLate : JointAdmissible Win Γ cap d x k) :
    JointAdmissible Win Γ cap d x h := by
  intro q hqh hxEarly
  have hqk : q ∈ Γ k := hΓ hhk hqh
  have hxLate : Win x (cap k) q := hsrc hhk hqh hxEarly
  have hdLate : Win (d x) (cap k) q := hadmLate q hqk hxLate
  have hcapkh : cap k ≤ cap h := hcap hhk
  exact hWin hcapkh hdLate

/-- Once revoked, a destruction right stays revoked at all later horizons, provided source-side
guarantees persist. -/
theorem revocation_persists_under_source_persistence
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (cap : Nat → Cap)
    (hΓ : ContractMonotone Γ)
    (hcap : CapabilityAntitone cap)
    (hWin : CapabilityMonotone Win)
    (x : State) (hsrc : SourcePersistent Win Γ cap x)
    (d : State → State)
    {h k : Nat} (hhk : h ≤ k)
    (hrev : ¬ JointAdmissible Win Γ cap d x h) :
    ¬ JointAdmissible Win Γ cap d x k := by
  intro hadmLate
  apply hrev
  exact joint_admissible_antitone_under_source_persistence
    Win Γ cap hΓ hcap hWin x hsrc d hhk hadmLate

/-- Revocation predicate for a fixed destruction and source state. -/
def RevokedAt
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (cap : Nat → Cap)
    (d : State → State) (x : State) (h : Nat) : Prop :=
  ¬ JointAdmissible Win Γ cap d x h

/-- Eventual revocation means that some finite horizon rejects the destruction. -/
def EverRevoked
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (cap : Nat → Cap)
    (d : State → State) (x : State) : Prop :=
  ∃ h, RevokedAt Win Γ cap d x h

/-- The first horizon at which the destruction right is revoked. -/
noncomputable def CriticalHorizon
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (cap : Nat → Cap)
    (d : State → State) (x : State)
    (hev : EverRevoked Win Γ cap d x) : Nat := by
  classical
  exact Nat.find hev

/-- The critical horizon is itself revoked. -/
theorem criticalHorizon_revoked
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (cap : Nat → Cap)
    (d : State → State) (x : State)
    (hev : EverRevoked Win Γ cap d x) :
    RevokedAt Win Γ cap d x (CriticalHorizon Win Γ cap d x hev) := by
  classical
  exact Nat.find_spec hev

/-- Every earlier horizon is admissible by minimality of the first revocation. -/
theorem admissible_before_criticalHorizon
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (cap : Nat → Cap)
    (d : State → State) (x : State)
    (hev : EverRevoked Win Γ cap d x)
    {h : Nat} (hlt : h < CriticalHorizon Win Γ cap d x hev) :
    JointAdmissible Win Γ cap d x h := by
  classical
  by_contra hrev
  have hmin : CriticalHorizon Win Γ cap d x hev ≤ h := by
    exact Nat.find_min' hev hrev
  omega

/-- With source persistence, revocation holds at and after the critical horizon. -/
theorem revoked_at_or_after_criticalHorizon
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (cap : Nat → Cap)
    (hΓ : ContractMonotone Γ)
    (hcap : CapabilityAntitone cap)
    (hWin : CapabilityMonotone Win)
    (x : State) (hsrc : SourcePersistent Win Γ cap x)
    (d : State → State)
    (hev : EverRevoked Win Γ cap d x)
    {k : Nat} (hcrit : CriticalHorizon Win Γ cap d x hev ≤ k) :
    RevokedAt Win Γ cap d x k := by
  exact revocation_persists_under_source_persistence
    Win Γ cap hΓ hcap hWin x hsrc d hcrit
    (criticalHorizon_revoked Win Γ cap d x hev)

/-- Exact threshold law: under source persistence, admissibility at horizon `h` is equivalent to
being strictly before the critical horizon. -/
theorem admissible_iff_before_criticalHorizon
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (cap : Nat → Cap)
    (hΓ : ContractMonotone Γ)
    (hcap : CapabilityAntitone cap)
    (hWin : CapabilityMonotone Win)
    (x : State) (hsrc : SourcePersistent Win Γ cap x)
    (d : State → State)
    (hev : EverRevoked Win Γ cap d x)
    (h : Nat) :
    JointAdmissible Win Γ cap d x h ↔
      h < CriticalHorizon Win Γ cap d x hev := by
  constructor
  · intro hadm
    by_contra hnotlt
    have hge : CriticalHorizon Win Γ cap d x hev ≤ h := by omega
    have hrev := revoked_at_or_after_criticalHorizon
      Win Γ cap hΓ hcap hWin x hsrc d hev hge
    exact hrev hadm
  · intro hlt
    exact admissible_before_criticalHorizon Win Γ cap d x hev hlt

/-- Consolidated lifetime theorem: the destruction right has a first expiry horizon, all earlier
horizons admit it, and all horizons at or after expiry reject it. -/
theorem critical_horizon_threshold_v1
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (cap : Nat → Cap)
    (hΓ : ContractMonotone Γ)
    (hcap : CapabilityAntitone cap)
    (hWin : CapabilityMonotone Win)
    (x : State) (hsrc : SourcePersistent Win Γ cap x)
    (d : State → State)
    (hev : EverRevoked Win Γ cap d x) :
    RevokedAt Win Γ cap d x (CriticalHorizon Win Γ cap d x hev) ∧
    (∀ h, h < CriticalHorizon Win Γ cap d x hev →
      JointAdmissible Win Γ cap d x h) ∧
    (∀ k, CriticalHorizon Win Γ cap d x hev ≤ k →
      RevokedAt Win Γ cap d x k) := by
  refine ⟨criticalHorizon_revoked Win Γ cap d x hev, ?_, ?_⟩
  · intro h hlt
    exact admissible_before_criticalHorizon Win Γ cap d x hev hlt
  · intro k hge
    exact revoked_at_or_after_criticalHorizon
      Win Γ cap hΓ hcap hWin x hsrc d hev hge

/-- If the first revocation occurs after horizon zero, the boundary itself has an exact localized
cause: either a newly added obligation or failure of capability compensation on an old obligation. -/
theorem criticalHorizon_has_localized_cause
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (cap : Nat → Cap)
    (hΓ : ContractMonotone Γ)
    (hcap : CapabilityAntitone cap)
    (hWin : CapabilityMonotone Win)
    (x : State) (hsrc : SourcePersistent Win Γ cap x)
    (d : State → State)
    (hev : EverRevoked Win Γ cap d x)
    (hpos : 0 < CriticalHorizon Win Γ cap d x hev) :
    ∃ q,
      q ∈ Γ (CriticalHorizon Win Γ cap d x hev) ∧
      Win x (cap (CriticalHorizon Win Γ cap d x hev)) q ∧
      ¬ Win (d x) (cap (CriticalHorizon Win Γ cap d x hev)) q ∧
      (
        q ∉ Γ (Nat.pred (CriticalHorizon Win Γ cap d x hev)) ∨
        (q ∈ Γ (Nat.pred (CriticalHorizon Win Γ cap d x hev)) ∧
         Win (d x) (cap (Nat.pred (CriticalHorizon Win Γ cap d x hev))) q ∧
         ¬ Win (d x) (cap (CriticalHorizon Win Γ cap d x hev)) q)
      ) := by
  let τ := CriticalHorizon Win Γ cap d x hev
  have hpredlt : Nat.pred τ < τ := by
    dsimp [τ]
    omega
  have hpredle : Nat.pred τ ≤ τ := Nat.le_of_lt hpredlt
  have hadmPrev : JointAdmissible Win Γ cap d x (Nat.pred τ) := by
    exact admissible_before_criticalHorizon Win Γ cap d x hev hpredlt
  have hrevτ : ¬ JointAdmissible Win Γ cap d x τ := by
    exact criticalHorizon_revoked Win Γ cap d x hev
  exact joint_revocation_has_localized_cause
    Win Γ cap hΓ hcap hWin d x hpredle hadmPrev hrevτ

end GenericPersistence

section NonPersistentCounterexample

inductive ToggleState
  | source
  | destroyed
  deriving DecidableEq, Repr

open ToggleState

/-- One fixed contracted requirement. -/
def ToggleReq := Unit

/-- Source needs capability at least 1; destroyed state needs capability at least 2. -/
def WinToggle : ToggleState → Nat → ToggleReq → Prop
  | source, c, _ => 1 ≤ c
  | destroyed, c, _ => 2 ≤ c

/-- Capability falls 2 → 1 → 0 and then stays at 0. -/
def ToggleCap (h : Nat) : Nat := 2 - h

/-- Contract does not change. -/
def ToggleContract (_h : Nat) : Set ToggleReq := Set.univ

/-- Destruction maps the source to the destroyed state. -/
def toggleDestroy : ToggleState → ToggleState
  | source => destroyed
  | destroyed => destroyed

/-- More capability never destroys a guarantee. -/
theorem winToggle_capability_monotone : CapabilityMonotone WinToggle := by
  intro x q cLow cHigh hle hwin
  cases x with
  | source => exact le_trans hwin hle
  | destroyed => exact le_trans hwin hle

/-- The fixed contract is monotone. -/
theorem toggleContract_monotone : ContractMonotone ToggleContract := by
  intro h k hhk q hq
  simp [ToggleContract]

/-- The capability path is antitone. -/
theorem toggleCap_antitone : CapabilityAntitone ToggleCap := by
  intro h k hhk
  simp [ToggleCap]
  omega

/-- At horizon 0, destruction is admissible: both source and destroyed states have enough capability. -/
theorem toggle_admissible_zero :
    JointAdmissible WinToggle ToggleContract ToggleCap toggleDestroy source 0 := by
  intro q hq hx
  change 2 ≤ ToggleCap 0
  simp [ToggleCap]

/-- At horizon 1, destruction is revoked: source still satisfies the requirement, destroyed state does not. -/
theorem toggle_revoked_one :
    ¬ JointAdmissible WinToggle ToggleContract ToggleCap toggleDestroy source 1 := by
  intro hadm
  have hx : WinToggle source (ToggleCap 1) () := by
    simp [WinToggle, ToggleCap]
  have hd := hadm () (by simp [ToggleContract]) hx
  change 2 ≤ 1 at hd
  omega

/-- At horizon 2, admissibility reappears vacuously because the source itself has lost the guarantee. -/
theorem toggle_admissible_two :
    JointAdmissible WinToggle ToggleContract ToggleCap toggleDestroy source 2 := by
  intro q hq hx
  simp [WinToggle, ToggleCap] at hx

/-- Without source persistence, revocation need not be permanent: admit → revoke → admit. -/
theorem revocation_can_reappear_without_source_persistence :
    JointAdmissible WinToggle ToggleContract ToggleCap toggleDestroy source 0 ∧
    ¬ JointAdmissible WinToggle ToggleContract ToggleCap toggleDestroy source 1 ∧
    JointAdmissible WinToggle ToggleContract ToggleCap toggleDestroy source 2 := by
  exact ⟨toggle_admissible_zero, toggle_revoked_one, toggle_admissible_two⟩

/-- The counterexample fails source persistence exactly where the source loses the requirement. -/
theorem toggle_source_not_persistent :
    ¬ SourcePersistent WinToggle ToggleContract ToggleCap source := by
  intro hsrc
  have hkeep := hsrc
    (h := 1) (k := 2) (q := ())
    (show (1 : Nat) ≤ 2 by omega)
    (by simp [ToggleContract])
    (by simp [WinToggle, ToggleCap])
  simp [WinToggle, ToggleCap] at hkeep

end NonPersistentCounterexample

section CertifiedCriticalHorizon

open InsacermoJointHorizonCapability
open InsacermoCapabilityDebt

/-- The previously certified joint witness has a source state whose guarantees persist forever. -/
theorem certified_joint_source_persistent :
    SourcePersistent WinJoint JointContract JointCap MemoryState.rich := by
  intro h k q hhk hq hwin
  trivial

/-- The previously certified witness is eventually revoked, already at horizon 1. -/
theorem certified_joint_ever_revoked :
    EverRevoked WinJoint JointContract JointCap forgetNow MemoryState.rich := by
  exact ⟨1, joint_forget_inadmissible_at_one⟩

/-- In the certified joint witness, the right to forget expires exactly at horizon 1. -/
theorem certified_criticalHorizon_eq_one :
    CriticalHorizon WinJoint JointContract JointCap forgetNow MemoryState.rich
      certified_joint_ever_revoked = 1 := by
  classical
  have hle :
      CriticalHorizon WinJoint JointContract JointCap forgetNow MemoryState.rich
        certified_joint_ever_revoked ≤ 1 := by
    exact Nat.find_min' certified_joint_ever_revoked joint_forget_inadmissible_at_one
  have hne0 :
      CriticalHorizon WinJoint JointContract JointCap forgetNow MemoryState.rich
        certified_joint_ever_revoked ≠ 0 := by
    intro hzero
    have hrev0 := criticalHorizon_revoked
      WinJoint JointContract JointCap forgetNow MemoryState.rich certified_joint_ever_revoked
    rw [hzero] at hrev0
    exact hrev0 joint_forget_admissible_at_zero
  omega

/-- Certified threshold instance: horizon 0 admits forgetting, horizon 1 and every later horizon reject it. -/
theorem certified_critical_horizon_threshold :
    (∀ h,
      JointAdmissible WinJoint JointContract JointCap forgetNow MemoryState.rich h ↔ h < 1) := by
  intro h
  rw [← certified_criticalHorizon_eq_one]
  exact admissible_iff_before_criticalHorizon
    WinJoint JointContract JointCap
    jointContract_monotone jointCap_antitone winJoint_capability_monotone
    MemoryState.rich certified_joint_source_persistent
    forgetNow certified_joint_ever_revoked h

end CertifiedCriticalHorizon

end InsacermoCriticalHorizon
