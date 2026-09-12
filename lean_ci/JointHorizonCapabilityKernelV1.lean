import Mathlib
import CapabilityDebtKernelV1

namespace InsacermoJointHorizonCapability

open Set
open InsacermoCapabilityDebt

universe u v w z

section GenericJoint

variable {State : Type u} {Req : Type v} {Cap : Type w} {Horizon : Type z}
variable [Preorder Cap] [Preorder Horizon]

/-- Contract family grows with horizon. -/
def ContractMonotone (Γ : Horizon → Set Req) : Prop := Monotone Γ

/-- Capability path decreases with horizon: later horizons may have less available capability. -/
def CapabilityAntitone (cap : Horizon → Cap) : Prop := Antitone cap

/-- Admissibility at horizon `h` under both the contract active at `h` and the capability available at `h`. -/
def JointAdmissible
    (Win : State → Cap → Req → Prop)
    (Γ : Horizon → Set Req) (cap : Horizon → Cap)
    (d : State → State) (x : State) (h : Horizon) : Prop :=
  AdmissibleWithCapability Win (Γ h) (cap h) d x

/-- Exact witness of late inadmissibility in the joint horizon-capability model. -/
theorem joint_not_admissible_has_witness
    (Win : State → Cap → Req → Prop)
    (Γ : Horizon → Set Req) (cap : Horizon → Cap)
    (d : State → State) (x : State) (h : Horizon)
    (hnot : ¬ JointAdmissible Win Γ cap d x h) :
    ∃ q, q ∈ Γ h ∧ Win x (cap h) q ∧ ¬ Win (d x) (cap h) q := by
  exact (not_admissibleWithCapability_iff_exists_witness
    Win (Γ h) (cap h) d x).mp hnot

/-- Core decomposition theorem.
If a destruction is admissible early and revoked later while the contract grows and capability falls,
then there is an exact late witness `q`. That witness is either:
1. newly introduced by the later contract, or
2. already owed early, in which case the stronger early capability kept the destroyed state able to
   satisfy it, while the weaker later capability does not.
Thus every strict revocation decomposes into contract growth or capability-loss compensation failure. -/
theorem joint_revocation_decomposes_into_contract_or_capability
    (Win : State → Cap → Req → Prop)
    (Γ : Horizon → Set Req) (cap : Horizon → Cap)
    (hΓ : ContractMonotone Γ)
    (hcap : CapabilityAntitone cap)
    (hWin : CapabilityMonotone Win)
    (d : State → State) (x : State)
    {h k : Horizon} (hhk : h ≤ k)
    (hadmEarly : JointAdmissible Win Γ cap d x h)
    (hnotLate : ¬ JointAdmissible Win Γ cap d x k) :
    ∃ q,
      q ∈ Γ k ∧
      Win x (cap k) q ∧
      ¬ Win (d x) (cap k) q ∧
      (
        q ∉ Γ h ∨
        (q ∈ Γ h ∧ Win (d x) (cap h) q)
      ) := by
  rcases joint_not_admissible_has_witness Win Γ cap d x k hnotLate with
    ⟨q, hqk, hxLate, hlostLate⟩
  refine ⟨q, hqk, hxLate, hlostLate, ?_⟩
  by_cases hqh : q ∈ Γ h
  · right
    have hcapkh : cap k ≤ cap h := hcap hhk
    have hxEarly : Win x (cap h) q := hWin hcapkh hxLate
    have hdEarly : Win (d x) (cap h) q := hadmEarly q hqh hxEarly
    exact ⟨hqh, hdEarly⟩
  · exact Or.inl hqh

/-- Stronger classifier: every strict joint revocation has a witness whose cause can be localized.
For an old obligation, we explicitly certify a capability compensation gap on the destroyed state. -/
theorem joint_revocation_has_localized_cause
    (Win : State → Cap → Req → Prop)
    (Γ : Horizon → Set Req) (cap : Horizon → Cap)
    (hΓ : ContractMonotone Γ)
    (hcap : CapabilityAntitone cap)
    (hWin : CapabilityMonotone Win)
    (d : State → State) (x : State)
    {h k : Horizon} (hhk : h ≤ k)
    (hadmEarly : JointAdmissible Win Γ cap d x h)
    (hnotLate : ¬ JointAdmissible Win Γ cap d x k) :
    ∃ q,
      q ∈ Γ k ∧
      Win x (cap k) q ∧
      ¬ Win (d x) (cap k) q ∧
      (
        q ∉ Γ h ∨
        (q ∈ Γ h ∧
         Win (d x) (cap h) q ∧
         ¬ Win (d x) (cap k) q)
      ) := by
  rcases joint_revocation_decomposes_into_contract_or_capability
    Win Γ cap hΓ hcap hWin d x hhk hadmEarly hnotLate with
    ⟨q, hqk, hxLate, hlostLate, hcause⟩
  refine ⟨q, hqk, hxLate, hlostLate, ?_⟩
  cases hcause with
  | inl hnew => exact Or.inl hnew
  | inr hold =>
      exact Or.inr ⟨hold.1, hold.2, hlostLate⟩

/-- If no genuinely new obligation appears between two horizons, then every new revocation is
necessarily caused by loss of compensating capability on an already-contracted requirement. -/
theorem pure_capability_loss_revocation
    (Win : State → Cap → Req → Prop)
    (Γ : Horizon → Set Req) (cap : Horizon → Cap)
    (hcap : CapabilityAntitone cap)
    (hWin : CapabilityMonotone Win)
    (d : State → State) (x : State)
    {h k : Horizon} (hhk : h ≤ k)
    (hsame : Γ h = Γ k)
    (hadmEarly : JointAdmissible Win Γ cap d x h)
    (hnotLate : ¬ JointAdmissible Win Γ cap d x k) :
    ∃ q,
      q ∈ Γ h ∧
      Win x (cap k) q ∧
      Win (d x) (cap h) q ∧
      ¬ Win (d x) (cap k) q := by
  rcases joint_not_admissible_has_witness Win Γ cap d x k hnotLate with
    ⟨q, hqk, hxLate, hlostLate⟩
  have hqh : q ∈ Γ h := by
    rw [hsame]
    exact hqk
  have hcapkh : cap k ≤ cap h := hcap hhk
  have hxEarly : Win x (cap h) q := hWin hcapkh hxLate
  have hdEarly : Win (d x) (cap h) q := hadmEarly q hqh hxEarly
  exact ⟨q, hqh, hxLate, hdEarly, hlostLate⟩

end GenericJoint

section FiniteCertifiedWitness

inductive Req2
  | base
  | future
  deriving DecidableEq, Repr

open Req2
open InsacermoCapabilityDebt

/-- Two horizons: 0 is present, 1 is later. -/
def H := Nat

/-- Contract grows from base-only to base+future. -/
def JointContract : H → Set Req2
  | 0 => {base}
  | _ + 1 => Set.univ

/-- Capability falls from 1 to 0 after horizon 0. -/
def JointCap : H → Nat
  | 0 => 1
  | _ + 1 => 0

/-- Base requirement is always satisfiable from rich memory and requires capability after forgetting.
Future requirement is only relevant at the later horizon and behaves the same way. -/
def WinJoint : MemoryState → Nat → Req2 → Prop
  | MemoryState.rich, _, _ => True
  | MemoryState.forgotten, c, _ => 1 ≤ c

/-- Capability monotonicity for the finite witness. -/
theorem winJoint_capability_monotone : CapabilityMonotone WinJoint := by
  intro x q cLow cHigh hle hwin
  cases x with
  | rich => trivial
  | forgotten => exact le_trans hwin hle

/-- Contract monotonicity for the finite witness. -/
theorem jointContract_monotone : ContractMonotone JointContract := by
  intro h k hhk
  cases h with
  | zero =>
      cases k with
      | zero => exact fun _ hq => hq
      | succ k =>
          intro q hq
          simp [JointContract]
  | succ h =>
      have hkpos : 0 < k := lt_of_lt_of_le (Nat.zero_lt_succ h) hhk
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
      exact fun _ hq => hq

/-- Capability antitonicity for the finite witness. -/
theorem jointCap_antitone : CapabilityAntitone JointCap := by
  intro h k hhk
  cases h with
  | zero =>
      cases k with
      | zero => exact le_rfl
      | succ k => simp [JointCap]
  | succ h =>
      have hkpos : 0 < k := lt_of_lt_of_le (Nat.zero_lt_succ h) hhk
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
      exact le_rfl

/-- At horizon 0, forgetting is admissible because capability 1 compensates. -/
theorem joint_forget_admissible_at_zero :
    JointAdmissible WinJoint JointContract JointCap forgetNow MemoryState.rich 0 := by
  intro q hq hx
  change 1 ≤ 1
  exact le_rfl

/-- At horizon 1, the same forgetting is inadmissible after both contract growth and capability loss. -/
theorem joint_forget_inadmissible_at_one :
    ¬ JointAdmissible WinJoint JointContract JointCap forgetNow MemoryState.rich 1 := by
  intro h
  have hx : WinJoint MemoryState.rich 0 base := by trivial
  have htarget := h base (by simp [JointContract]) hx
  change 1 ≤ 0 at htarget
  omega

/-- Certified finite witness of joint horizon/capability revocation. -/
theorem certified_joint_revocation :
    JointAdmissible WinJoint JointContract JointCap forgetNow MemoryState.rich 0 ∧
    ¬ JointAdmissible WinJoint JointContract JointCap forgetNow MemoryState.rich 1 := by
  exact ⟨joint_forget_admissible_at_zero, joint_forget_inadmissible_at_one⟩

/-- The generic decomposition theorem applies to the finite witness. -/
theorem certified_joint_revocation_has_localized_cause :
    ∃ q,
      q ∈ JointContract 1 ∧
      WinJoint MemoryState.rich (JointCap 1) q ∧
      ¬ WinJoint (forgetNow MemoryState.rich) (JointCap 1) q ∧
      (
        q ∉ JointContract 0 ∨
        (q ∈ JointContract 0 ∧
         WinJoint (forgetNow MemoryState.rich) (JointCap 0) q ∧
         ¬ WinJoint (forgetNow MemoryState.rich) (JointCap 1) q)
      ) := by
  exact joint_revocation_has_localized_cause
    WinJoint JointContract JointCap
    jointContract_monotone jointCap_antitone winJoint_capability_monotone
    forgetNow MemoryState.rich
    (show (0 : Nat) ≤ 1 by omega)
    joint_forget_admissible_at_zero
    joint_forget_inadmissible_at_one

end FiniteCertifiedWitness

end InsacermoJointHorizonCapability
