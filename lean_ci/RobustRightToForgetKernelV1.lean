import Mathlib
import CriticalHorizonKernelV1

namespace InsacermoRobustRightToForget

open Set
open InsacermoCapabilityDebt
open InsacermoJointHorizonCapability
open InsacermoCriticalHorizon

universe u v w

section GenericRobust

variable {State : Type u} {Req : Type v} {Cap : Type w}

/-- Contract obligations grow with horizon. -/
def ContractMonotoneNat (Γ : Nat → Set Req) : Prop := Monotone Γ

/-- The set of future capabilities considered possible may expand with horizon. -/
def EnvelopeMonotone (C : Nat → Set Cap) : Prop := Monotone C

/-- Absolute viability of a state against every obligation and every capability scenario still possible. -/
def ViableAt
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (x : State) (h : Nat) : Prop :=
  ∀ c, c ∈ C h → ∀ q, q ∈ Γ h → Win x c q

/-- Relative robust preservation: destruction loses no guarantee that the source can still deliver,
for any capability scenario still considered possible. This remains vulnerable to source-collapse vacuity. -/
def RelativeRobustAdmissibleAt
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State) (h : Nat) : Prop :=
  ∀ c, c ∈ C h → ∀ q, q ∈ Γ h → Win x c q → Win (d x) c q

/-- Strong robust right to forget: both the original state and the post-destruction state remain viable
for every contracted obligation under every capability scenario considered possible. -/
def RobustSafeAt
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State) (h : Nat) : Prop :=
  ViableAt Win Γ C x h ∧ ViableAt Win Γ C (d x) h

/-- Under source viability, relative robust admissibility is exactly target viability. -/
theorem relativeRobust_iff_targetViable_of_sourceViable
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State) (h : Nat)
    (hsrc : ViableAt Win Γ C x h) :
    RelativeRobustAdmissibleAt Win Γ C d x h ↔
      ViableAt Win Γ C (d x) h := by
  constructor
  · intro hrel c hc q hq
    exact hrel c hc q hq (hsrc c hc q hq)
  · intro htgt c hc q hq hx
    exact htgt c hc q hq

/-- Strong robust safety is source viability plus relative preservation. -/
theorem robustSafe_iff_sourceViable_and_relative
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State) (h : Nat) :
    RobustSafeAt Win Γ C d x h ↔
      ViableAt Win Γ C x h ∧ RelativeRobustAdmissibleAt Win Γ C d x h := by
  constructor
  · rintro ⟨hsrc, htgt⟩
    refine ⟨hsrc, ?_⟩
    intro c hc q hq hx
    exact htgt c hc q hq
  · rintro ⟨hsrc, hrel⟩
    refine ⟨hsrc, ?_⟩
    exact (relativeRobust_iff_targetViable_of_sourceViable
      Win Γ C d x h hsrc).mp hrel

/-- Viability is antitone in horizon when contracts and uncertainty envelopes expand. -/
theorem viable_antitone_in_horizon
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (x : State)
    {h k : Nat} (hhk : h ≤ k)
    (hvk : ViableAt Win Γ C x k) :
    ViableAt Win Γ C x h := by
  intro c hch q hqh
  exact hvk c (hC hhk hch) q (hΓ hhk hqh)

/-- Strong robust safety is an initial segment of the horizon. -/
theorem robustSafe_antitone_in_horizon
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    {h k : Nat} (hhk : h ≤ k)
    (hsafeK : RobustSafeAt Win Γ C d x k) :
    RobustSafeAt Win Γ C d x h := by
  rcases hsafeK with ⟨hsrcK, htgtK⟩
  exact ⟨
    viable_antitone_in_horizon Win Γ C hΓ hC x hhk hsrcK,
    viable_antitone_in_horizon Win Γ C hΓ hC (d x) hhk htgtK
  ⟩

/-- Once strong robust safety is lost, it cannot reappear under expanding contracts/scenarios. -/
theorem robust_revocation_persists
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    {h k : Nat} (hhk : h ≤ k)
    (hrev : ¬ RobustSafeAt Win Γ C d x h) :
    ¬ RobustSafeAt Win Γ C d x k := by
  intro hsafeK
  exact hrev (robustSafe_antitone_in_horizon Win Γ C hΓ hC d x hhk hsafeK)

/-- Failure of strong robust safety always has a concrete source-side or target-side witness. -/
theorem not_robustSafe_has_witness
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State) (h : Nat)
    (hnot : ¬ RobustSafeAt Win Γ C d x h) :
    (
      ∃ c q, c ∈ C h ∧ q ∈ Γ h ∧ ¬ Win x c q
    ) ∨
    (
      ∃ c q, c ∈ C h ∧ q ∈ Γ h ∧ ¬ Win (d x) c q
    ) := by
  unfold RobustSafeAt ViableAt at hnot
  push_neg at hnot
  rcases hnot with hsrc | htgt
  · left
    rcases hsrc with ⟨c, hc, q, hq, hfail⟩
    exact ⟨c, q, hc, hq, hfail⟩
  · right
    rcases htgt with ⟨c, hc, q, hq, hfail⟩
    exact ⟨c, q, hc, hq, hfail⟩

/-- If the source is robustly viable but strong safety fails, failure is necessarily destruction-side. -/
theorem sourceViable_not_robustSafe_has_destruction_witness
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State) (h : Nat)
    (hsrc : ViableAt Win Γ C x h)
    (hnot : ¬ RobustSafeAt Win Γ C d x h) :
    ∃ c q,
      c ∈ C h ∧ q ∈ Γ h ∧ Win x c q ∧ ¬ Win (d x) c q := by
  have htgt : ¬ ViableAt Win Γ C (d x) h := by
    intro htv
    exact hnot ⟨hsrc, htv⟩
  unfold ViableAt at htgt
  push_neg at htgt
  rcases htgt with ⟨c, hc, q, hq, hfail⟩
  exact ⟨c, q, hc, hq, hsrc c hc q hq, hfail⟩

/-- Eventual loss of strong robust safety. -/
def EverRobustRevoked
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State) : Prop :=
  ∃ h, ¬ RobustSafeAt Win Γ C d x h

/-- First horizon at which strong robust safety is lost. -/
noncomputable def RobustCriticalHorizon
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State)
    (hev : EverRobustRevoked Win Γ C d x) : Nat := by
  classical
  exact Nat.find hev

/-- The robust critical horizon is itself unsafe. -/
theorem robustCriticalHorizon_revoked
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State)
    (hev : EverRobustRevoked Win Γ C d x) :
    ¬ RobustSafeAt Win Γ C d x
      (RobustCriticalHorizon Win Γ C d x hev) := by
  classical
  exact Nat.find_spec hev

/-- Every horizon before the robust critical horizon is safe by minimality. -/
theorem robustSafe_before_critical
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State)
    (hev : EverRobustRevoked Win Γ C d x)
    {h : Nat} (hlt : h < RobustCriticalHorizon Win Γ C d x hev) :
    RobustSafeAt Win Γ C d x h := by
  classical
  by_contra hnot
  have hmin : RobustCriticalHorizon Win Γ C d x hev ≤ h := by
    exact Nat.find_min' hev hnot
  omega

/-- Exact robust threshold law under expanding contracts and expanding uncertainty envelopes. -/
theorem robustSafe_iff_before_critical
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    (hev : EverRobustRevoked Win Γ C d x)
    (h : Nat) :
    RobustSafeAt Win Γ C d x h ↔
      h < RobustCriticalHorizon Win Γ C d x hev := by
  constructor
  · intro hsafe
    by_contra hnotlt
    have hge : RobustCriticalHorizon Win Γ C d x hev ≤ h := by omega
    have hrev : ¬ RobustSafeAt Win Γ C d x h :=
      robust_revocation_persists Win Γ C hΓ hC d x hge
        (robustCriticalHorizon_revoked Win Γ C d x hev)
    exact hrev hsafe
  · intro hlt
    exact robustSafe_before_critical Win Γ C d x hev hlt

/-- Consolidated robust right-to-forget threshold theorem. -/
theorem robust_right_to_forget_threshold_v1
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    (hev : EverRobustRevoked Win Γ C d x) :
    (∀ h,
      RobustSafeAt Win Γ C d x h ↔
        h < RobustCriticalHorizon Win Γ C d x hev) ∧
    (∀ k,
      RobustCriticalHorizon Win Γ C d x hev ≤ k →
      ¬ RobustSafeAt Win Γ C d x k) := by
  constructor
  · intro h
    exact robustSafe_iff_before_critical Win Γ C hΓ hC d x hev h
  · intro k hge
    exact robust_revocation_persists Win Γ C hΓ hC d x hge
      (robustCriticalHorizon_revoked Win Γ C d x hev)

end GenericRobust

section AntiVacuityWitness

open InsacermoCriticalHorizon

/-- Singleton uncertainty envelope corresponding to the earlier 2→1→0 capability path. -/
def ToggleEnvelope (h : Nat) : Set Nat := {ToggleCap h}

/-- At horizon zero, both source and destroyed states are viable under the only possible capability. -/
theorem toggle_robustSafe_zero :
    RobustSafeAt WinToggle ToggleContract ToggleEnvelope toggleDestroy ToggleState.source 0 := by
  constructor <;> intro c hc q hq
  · simp [ToggleEnvelope] at hc
    subst c
    simp [WinToggle, ToggleCap]
  · simp [ToggleEnvelope] at hc
    subst c
    simp [WinToggle, ToggleCap, toggleDestroy]

/-- At horizon one, strong robust safety is lost because the destroyed state needs more capability. -/
theorem toggle_not_robustSafe_one :
    ¬ RobustSafeAt WinToggle ToggleContract ToggleEnvelope toggleDestroy ToggleState.source 1 := by
  rintro ⟨hsrc, htgt⟩
  have h := htgt 1 (by simp [ToggleEnvelope, ToggleCap]) () (by simp [ToggleContract])
  change 2 ≤ 1 at h
  omega

/-- At horizon two, strong robust safety remains lost: the source itself is no longer viable. -/
theorem toggle_not_robustSafe_two :
    ¬ RobustSafeAt WinToggle ToggleContract ToggleEnvelope toggleDestroy ToggleState.source 2 := by
  rintro ⟨hsrc, htgt⟩
  have h := hsrc 0 (by simp [ToggleEnvelope, ToggleCap]) () (by simp [ToggleContract])
  change 1 ≤ 0 at h
  omega

/-- Relative admissibility revives at horizon two, but strong robust safety does not. -/
theorem relative_can_revive_while_robust_remains_revoked :
    RelativeRobustAdmissibleAt WinToggle ToggleContract ToggleEnvelope
      toggleDestroy ToggleState.source 2 ∧
    ¬ RobustSafeAt WinToggle ToggleContract ToggleEnvelope
      toggleDestroy ToggleState.source 2 := by
  constructor
  · intro c hc q hq hx
    simp [ToggleEnvelope, ToggleCap] at hc
    subst c
    simp [WinToggle, ToggleCap] at hx
  · exact toggle_not_robustSafe_two

end AntiVacuityWitness

section UncertainFutureWitness

inductive UState
  | rich
  | forgotten
  deriving DecidableEq, Repr

open UState

abbrev UReq := Unit

/-- Source is always viable; forgotten state needs capability at least 1. -/
def WinU : UState → Nat → UReq → Prop
  | rich, _, _ => True
  | forgotten, c, _ => 1 ≤ c

/-- Fixed destruction. -/
def forgetU : UState → UState
  | rich => forgotten
  | forgotten => forgotten

/-- One fixed obligation. -/
def UContract (_h : Nat) : Set UReq := Set.univ

/-- Horizon 0 allows only capability 1; from horizon 1 onward capability 0 or 1 are both plausible. -/
def UEnvelope : Nat → Set Nat
  | 0 => {1}
  | _ + 1 => {0, 1}

/-- Contract is monotone. -/
theorem uContract_monotone : ContractMonotoneNat UContract := by
  intro h k hhk q hq
  simp [UContract]

/-- Future uncertainty expands with horizon. -/
theorem uEnvelope_monotone : EnvelopeMonotone UEnvelope := by
  intro h k hhk c hc
  cases h with
  | zero =>
      simp [UEnvelope] at hc
      subst c
      cases k with
      | zero => simp [UEnvelope]
      | succ k => simp [UEnvelope]
  | succ h =>
      have hkpos : 0 < k := by omega
      cases k with
      | zero => omega
      | succ k => simpa [UEnvelope] using hc

/-- Initially forgetting is robustly safe. -/
theorem uncertain_forget_safe_zero :
    RobustSafeAt WinU UContract UEnvelope forgetU rich 0 := by
  constructor <;> intro c hc q hq
  · trivial
  · simp [UEnvelope] at hc
    subst c
    simp [WinU, forgetU]

/-- Once capability 0 becomes a plausible future, the right to forget is robustly revoked. -/
theorem uncertain_forget_revoked_one :
    ¬ RobustSafeAt WinU UContract UEnvelope forgetU rich 1 := by
  rintro ⟨hsrc, htgt⟩
  have h := htgt 0 (by simp [UEnvelope]) () (by simp [UContract])
  change 1 ≤ 0 at h
  omega

/-- The uncertain-future witness is eventually robustly revoked. -/
theorem uncertain_ever_revoked :
    EverRobustRevoked WinU UContract UEnvelope forgetU rich := by
  exact ⟨1, uncertain_forget_revoked_one⟩

/-- Its robust critical horizon is exactly 1. -/
theorem uncertain_robustCriticalHorizon_eq_one :
    RobustCriticalHorizon WinU UContract UEnvelope forgetU rich
      uncertain_ever_revoked = 1 := by
  classical
  have hle :
      RobustCriticalHorizon WinU UContract UEnvelope forgetU rich
        uncertain_ever_revoked ≤ 1 := by
    exact Nat.find_min' uncertain_ever_revoked uncertain_forget_revoked_one
  have hne0 :
      RobustCriticalHorizon WinU UContract UEnvelope forgetU rich
        uncertain_ever_revoked ≠ 0 := by
    intro hzero
    have hrev := robustCriticalHorizon_revoked
      WinU UContract UEnvelope forgetU rich uncertain_ever_revoked
    rw [hzero] at hrev
    exact hrev uncertain_forget_safe_zero
  omega

/-- Certified threshold for uncertainty expansion: robustly safe exactly before horizon 1. -/
theorem uncertain_robust_threshold :
    ∀ h,
      RobustSafeAt WinU UContract UEnvelope forgetU rich h ↔ h < 1 := by
  intro h
  rw [← uncertain_robustCriticalHorizon_eq_one]
  exact robustSafe_iff_before_critical
    WinU UContract UEnvelope uContract_monotone uEnvelope_monotone
    forgetU rich uncertain_ever_revoked h

/-- A newly plausible capability scenario can revoke a destruction right even when the contract is unchanged. -/
theorem uncertainty_expansion_alone_can_revoke_forgetting :
    RobustSafeAt WinU UContract UEnvelope forgetU rich 0 ∧
    ¬ RobustSafeAt WinU UContract UEnvelope forgetU rich 1 := by
  exact ⟨uncertain_forget_safe_zero, uncertain_forget_revoked_one⟩

end UncertainFutureWitness

end InsacermoRobustRightToForget
