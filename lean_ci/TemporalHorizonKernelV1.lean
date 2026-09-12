import Mathlib
import DestructionAdmissibilityKernelV1
import TemporalContractExtensionV1

namespace InsacermoTemporalHorizon

open Set
open InsacermoDestructionAdmissibility

universe u v w

section GenericHorizon

variable {State : Type u} {Req : Type v} {Horizon : Type w} [Preorder Horizon]

/-- A horizon-indexed contract family. `Monotone Γ` means later horizons may only add
requirements, never silently remove earlier obligations. -/
def ContractChain (Γ : Horizon → Set Req) : Prop := Monotone Γ

/-- Admissibility of a fixed destruction at a particular contract horizon. -/
def AdmissibleAt
    (Win : State → Req → Prop) (Γ : Horizon → Set Req)
    (d : State → State) (x : State) (h : Horizon) : Prop :=
  AdmissibleDestruction Win (Γ h) d x

/-- The exact contract-relative obligations destroyed by `d` at `x`. -/
def DestructionDebt
    (Win : State → Req → Prop) (Γ : Set Req)
    (d : State → State) (x : State) : Set Req :=
  {q | q ∈ Γ ∧ Win x q ∧ ¬ Win (d x) q}

/-- A destruction is admissible exactly when it creates no destruction debt. -/
theorem admissible_iff_destructionDebt_empty
    (Win : State → Req → Prop) (Γ : Set Req)
    (d : State → State) (x : State) :
    AdmissibleDestruction Win Γ d x ↔
      DestructionDebt Win Γ d x = ∅ := by
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
    have hmem : q ∈ DestructionDebt Win Γ d x := ⟨hq, hx, hlost⟩
    rw [h] at hmem
    exact hmem

/-- Failure of admissibility always has an explicit destroyed required guarantee as witness. -/
theorem not_admissible_iff_exists_debt_witness
    (Win : State → Req → Prop) (Γ : Set Req)
    (d : State → State) (x : State) :
    ¬ AdmissibleDestruction Win Γ d x ↔
      ∃ q, q ∈ Γ ∧ Win x q ∧ ¬ Win (d x) q := by
  classical
  simp [AdmissibleDestruction, Preserves]

/-- Strengthening the contract can only enlarge destruction debt. -/
theorem destructionDebt_monotone_in_contract
    (Win : State → Req → Prop) {Γweak Γstrong : Set Req}
    (hsub : Γweak ⊆ Γstrong) (d : State → State) (x : State) :
    DestructionDebt Win Γweak d x ⊆
      DestructionDebt Win Γstrong d x := by
  intro q hq
  exact ⟨hsub hq.1, hq.2.1, hq.2.2⟩

/-- Along any increasing horizon family, destruction debt is monotone in the horizon. -/
theorem destructionDebt_monotone_in_horizon
    (Win : State → Req → Prop) (Γ : Horizon → Set Req)
    (hΓ : ContractChain Γ) (d : State → State) (x : State)
    {h k : Horizon} (hhk : h ≤ k) :
    DestructionDebt Win (Γ h) d x ⊆
      DestructionDebt Win (Γ k) d x := by
  exact destructionDebt_monotone_in_contract Win (hΓ hhk) d x

/-- Along any increasing contract horizon, admissibility is antitone: if destruction is still
allowed at a later horizon, it was already allowed at every earlier horizon. -/
theorem admissible_antitone_in_horizon
    (Win : State → Req → Prop) (Γ : Horizon → Set Req)
    (hΓ : ContractChain Γ) (d : State → State) (x : State)
    {h k : Horizon} (hhk : h ≤ k)
    (hadm : AdmissibleAt Win Γ d x k) :
    AdmissibleAt Win Γ d x h := by
  exact preserves_contract_antitone Win (hΓ hhk) hadm

/-- Once a destruction right has been revoked, a later horizon cannot restore it merely by adding
more obligations. -/
theorem revocation_persists_to_later_horizons
    (Win : State → Req → Prop) (Γ : Horizon → Set Req)
    (hΓ : ContractChain Γ) (d : State → State) (x : State)
    {h k : Horizon} (hhk : h ≤ k)
    (hrevoked : ¬ AdmissibleAt Win Γ d x h) :
    ¬ AdmissibleAt Win Γ d x k := by
  intro hadmLater
  exact hrevoked (admissible_antitone_in_horizon Win Γ hΓ d x hhk hadmLater)

/-- Exact localization of a strict revocation: if a destruction is admissible at an earlier horizon
but not at a later one, some requirement newly present at the later horizon is precisely a
preserved-before / destroyed-after guarantee. -/
theorem strict_revocation_has_new_layer_witness
    (Win : State → Req → Prop) (Γ : Horizon → Set Req)
    (d : State → State) (x : State)
    {h k : Horizon}
    (hadmEarly : AdmissibleAt Win Γ d x h)
    (hrevokedLater : ¬ AdmissibleAt Win Γ d x k) :
    ∃ q, q ∈ Γ k ∧ q ∉ Γ h ∧ Win x q ∧ ¬ Win (d x) q := by
  rcases (not_admissible_iff_exists_debt_witness Win (Γ k) d x).mp hrevokedLater with
    ⟨q, hqk, hxq, hlost⟩
  refine ⟨q, hqk, ?_, hxq, hlost⟩
  intro hqh
  exact hlost (hadmEarly q hqh hxq)

/-- Main generic temporal-horizon theorem: increasing horizons induce decreasing destruction rights,
increasing destruction debt, persistent revocation, and every strict revocation is witnessed by a
newly added obligation. -/
theorem temporal_horizon_kernel_v1
    (Win : State → Req → Prop) (Γ : Horizon → Set Req)
    (hΓ : ContractChain Γ) (d : State → State) (x : State)
    {h k : Horizon} (hhk : h ≤ k) :
    (AdmissibleAt Win Γ d x k → AdmissibleAt Win Γ d x h) ∧
    (DestructionDebt Win (Γ h) d x ⊆ DestructionDebt Win (Γ k) d x) ∧
    ((¬ AdmissibleAt Win Γ d x h) → ¬ AdmissibleAt Win Γ d x k) ∧
    ((AdmissibleAt Win Γ d x h ∧ ¬ AdmissibleAt Win Γ d x k) →
      ∃ q, q ∈ Γ k ∧ q ∉ Γ h ∧ Win x q ∧ ¬ Win (d x) q) := by
  constructor
  · exact admissible_antitone_in_horizon Win Γ hΓ d x hhk
  constructor
  · exact destructionDebt_monotone_in_horizon Win Γ hΓ d x hhk
  constructor
  · exact revocation_persists_to_later_horizons Win Γ hΓ d x hhk
  · rintro ⟨hadm, hnot⟩
    exact strict_revocation_has_new_layer_witness Win Γ d x hadm hnot

end GenericHorizon

section BridgeToTemporalContractExtension

open InsacermoTemporalContractExtension
open InsacermoTemporalDestruction

/-- Two-level horizon chain embedding the already certified present/future witness. -/
def CertifiedTemporalChain : Nat → Set Requirement
  | 0 => PresentContract
  | _ + 1 => FutureContract

/-- The two-level certified temporal chain is monotone. -/
theorem certifiedTemporalChain_monotone : Monotone CertifiedTemporalChain := by
  intro m n hmn
  cases m with
  | zero =>
      cases n with
      | zero => exact fun _ hq => hq
      | succ n => exact presentContract_subset_futureContract
  | succ m =>
      have hnpos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ m) hmn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
      exact fun _ hq => hq

/-- The certified destruction is allowed at horizon 0 and revoked at horizon 1. -/
theorem certified_destroyNow_revocation :
    AdmissibleAt WinTemporal CertifiedTemporalChain destroyNow State.start 0 ∧
    ¬ AdmissibleAt WinTemporal CertifiedTemporalChain destroyNow State.start 1 := by
  exact ⟨destroyNow_admissible_present, destroyNow_inadmissible_future⟩

/-- The generic new-layer witness theorem recovers the added `futureGoal` obligation from the
certified present/future example. -/
theorem certified_revocation_has_new_obligation_witness :
    ∃ q,
      q ∈ CertifiedTemporalChain 1 ∧
      q ∉ CertifiedTemporalChain 0 ∧
      WinTemporal State.start q ∧
      ¬ WinTemporal (destroyNow State.start) q := by
  exact strict_revocation_has_new_layer_witness
    WinTemporal CertifiedTemporalChain destroyNow State.start
    destroyNow_admissible_present destroyNow_inadmissible_future

end BridgeToTemporalContractExtension

end InsacermoTemporalHorizon
