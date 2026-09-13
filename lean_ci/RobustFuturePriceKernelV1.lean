import Mathlib
import RobustRightToForgetKernelV1

namespace InsacermoRobustFuturePrice

open Set
open InsacermoRobustRightToForget

universe u v w z

section GenericPrice

variable {State : Type u} {Req : Type v} {Cap : Type w} {Intervention : Type z}

/-- Robust safety after applying the same intervention to the retained source and to the post-destruction state. -/
def IntervenedSafeAt
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (d : State → State) (x : State)
    (a : Intervention) (h : Nat) : Prop :=
  ViableAt Win Γ C (apply a x) h ∧
  ViableAt Win Γ C (apply a (d x)) h

/-- An intervention buys robust safety through H when it works at every horizon up to H. -/
def SafeThrough
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (d : State → State) (x : State)
    (a : Intervention) (H : Nat) : Prop :=
  ∀ h, h ≤ H → IntervenedSafeAt Win Γ C apply d x a h

/-- A budget B can buy safety through H if some intervention of cost at most B does so. -/
def AffordableThrough
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    (B H : Nat) : Prop :=
  ∃ a, cost a ≤ B ∧ SafeThrough Win Γ C apply d x a H

/-- There is some finite budget that can buy robust safety through H. -/
def FeasibleThrough
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    (H : Nat) : Prop :=
  ∃ B, AffordableThrough Win Γ C apply cost d x B H

/-- Minimal budget that buys robust safety through H. -/
noncomputable def FuturePrice
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    (H : Nat)
    (hev : FeasibleThrough Win Γ C apply cost d x H) : Nat := by
  classical
  exact Nat.find hev

/-- Intervened robust safety is antitone in horizon under expanding contracts and uncertainty envelopes. -/
theorem intervenedSafe_antitone_in_horizon
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (apply : Intervention → State → State)
    (d : State → State) (x : State)
    (a : Intervention)
    {h k : Nat} (hhk : h ≤ k)
    (hsafeK : IntervenedSafeAt Win Γ C apply d x a k) :
    IntervenedSafeAt Win Γ C apply d x a h := by
  rcases hsafeK with ⟨hsrc, htgt⟩
  exact ⟨
    viable_antitone_in_horizon Win Γ C hΓ hC (apply a x) hhk hsrc,
    viable_antitone_in_horizon Win Γ C hΓ hC (apply a (d x)) hhk htgt
  ⟩

/-- Under monotone contracts and envelopes, buying safety through H is equivalent to being safe at endpoint H. -/
theorem safeThrough_iff_endpoint
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (apply : Intervention → State → State)
    (d : State → State) (x : State)
    (a : Intervention) (H : Nat) :
    SafeThrough Win Γ C apply d x a H ↔
      IntervenedSafeAt Win Γ C apply d x a H := by
  constructor
  · intro hs
    exact hs H le_rfl
  · intro hH h hle
    exact intervenedSafe_antitone_in_horizon Win Γ C hΓ hC apply d x a hle hH

/-- More budget never destroys affordability. -/
theorem affordableThrough_mono_budget
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    {B B' H : Nat} (hBB' : B ≤ B')
    (hB : AffordableThrough Win Γ C apply cost d x B H) :
    AffordableThrough Win Γ C apply cost d x B' H := by
  rcases hB with ⟨a, hcost, hsafe⟩
  exact ⟨a, le_trans hcost hBB', hsafe⟩

/-- Any intervention that buys a later horizon also buys every earlier horizon. -/
theorem affordableThrough_antitone_horizon
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    {B H K : Nat} (hHK : H ≤ K)
    (hK : AffordableThrough Win Γ C apply cost d x B K) :
    AffordableThrough Win Γ C apply cost d x B H := by
  rcases hK with ⟨a, hcost, hsafeK⟩
  refine ⟨a, hcost, ?_⟩
  intro h hh
  exact hsafeK h (le_trans hh hHK)

/-- The future price itself is affordable. -/
theorem futurePrice_affordable
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    (H : Nat)
    (hev : FeasibleThrough Win Γ C apply cost d x H) :
    AffordableThrough Win Γ C apply cost d x
      (FuturePrice Win Γ C apply cost d x H hev) H := by
  classical
  exact Nat.find_spec hev

/-- No smaller budget than FuturePrice can buy the requested horizon. -/
theorem futurePrice_minimal
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    (H : Nat)
    (hev : FeasibleThrough Win Γ C apply cost d x H)
    {B : Nat}
    (hB : AffordableThrough Win Γ C apply cost d x B H) :
    FuturePrice Win Γ C apply cost d x H hev ≤ B := by
  classical
  exact Nat.find_min' hev hB

/-- Exact budget threshold: a budget works exactly when it reaches the future price. -/
theorem affordableThrough_iff_futurePrice_le
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    (H : Nat)
    (hev : FeasibleThrough Win Γ C apply cost d x H)
    (B : Nat) :
    AffordableThrough Win Γ C apply cost d x B H ↔
      FuturePrice Win Γ C apply cost d x H hev ≤ B := by
  constructor
  · intro hB
    exact futurePrice_minimal Win Γ C apply cost d x H hev hB
  · intro hprice
    exact affordableThrough_mono_budget Win Γ C apply cost d x hprice
      (futurePrice_affordable Win Γ C apply cost d x H hev)

/-- Every feasible horizon has an intervention attaining exactly the minimal price. -/
theorem exists_optimal_intervention
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    (H : Nat)
    (hev : FeasibleThrough Win Γ C apply cost d x H) :
    ∃ a,
      cost a = FuturePrice Win Γ C apply cost d x H hev ∧
      SafeThrough Win Γ C apply d x a H := by
  rcases futurePrice_affordable Win Γ C apply cost d x H hev with
    ⟨a, hcost, hsafe⟩
  have hmin : FuturePrice Win Γ C apply cost d x H hev ≤ cost a := by
    apply futurePrice_minimal Win Γ C apply cost d x H hev
    exact ⟨a, le_rfl, hsafe⟩
  exact ⟨a, Nat.le_antisymm hcost hmin, hsafe⟩

/-- The minimal price of robust future safety cannot decrease when the demanded horizon increases. -/
theorem futurePrice_monotone_horizon
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    {H K : Nat} (hHK : H ≤ K)
    (hevH : FeasibleThrough Win Γ C apply cost d x H)
    (hevK : FeasibleThrough Win Γ C apply cost d x K) :
    FuturePrice Win Γ C apply cost d x H hevH ≤
      FuturePrice Win Γ C apply cost d x K hevK := by
  apply futurePrice_minimal Win Γ C apply cost d x H hevH
  exact affordableThrough_antitone_horizon Win Γ C apply cost d x hHK
    (futurePrice_affordable Win Γ C apply cost d x K hevK)

/-- Any budget strictly below the future price is impossible. -/
theorem budget_below_futurePrice_impossible
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    (H : Nat)
    (hev : FeasibleThrough Win Γ C apply cost d x H)
    {B : Nat}
    (hlt : B < FuturePrice Win Γ C apply cost d x H hev) :
    ¬ AffordableThrough Win Γ C apply cost d x B H := by
  intro hB
  have hmin := futurePrice_minimal Win Γ C apply cost d x H hev hB
  omega

end GenericPrice

section ExactPriceWitness

open InsacermoRobustRightToForget

inductive Repair
  | doNothing
  | restore
  deriving DecidableEq, Repr

/-- Restoring maps any memory state back to rich; doing nothing leaves it unchanged. -/
def repairApply : Repair → UState → UState
  | Repair.doNothing, s => s
  | Repair.restore, _ => UState.rich

/-- Restoration costs five units; doing nothing is free. -/
def repairCost : Repair → Nat
  | Repair.doNothing => 0
  | Repair.restore => 5

/-- The free intervention is safe through horizon zero. -/
theorem doNothing_safeThrough_zero :
    SafeThrough WinU UContract UEnvelope repairApply forgetU UState.rich
      Repair.doNothing 0 := by
  intro h hh
  have hz : h = 0 := by omega
  subst h
  change RobustSafeAt WinU UContract UEnvelope forgetU UState.rich 0
  exact uncertain_forget_safe_zero

/-- Horizon zero is feasible with zero budget. -/
theorem witness_feasible_zero :
    FeasibleThrough WinU UContract UEnvelope repairApply repairCost
      forgetU UState.rich 0 := by
  refine ⟨0, ?_⟩
  exact ⟨Repair.doNothing, by simp [repairCost], doNothing_safeThrough_zero⟩

/-- Restoration is robustly safe at every horizon. -/
theorem restore_safeAt_all (h : Nat) :
    IntervenedSafeAt WinU UContract UEnvelope repairApply
      forgetU UState.rich Repair.restore h := by
  constructor <;> intro c hc q hq <;> simp [repairApply, WinU]

/-- Therefore restoration buys safety through every finite horizon, in particular horizon one. -/
theorem restore_safeThrough_one :
    SafeThrough WinU UContract UEnvelope repairApply
      forgetU UState.rich Repair.restore 1 := by
  intro h hh
  exact restore_safeAt_all h

/-- Horizon one is feasible with budget five. -/
theorem witness_feasible_one :
    FeasibleThrough WinU UContract UEnvelope repairApply repairCost
      forgetU UState.rich 1 := by
  refine ⟨5, ?_⟩
  exact ⟨Repair.restore, by simp [repairCost], restore_safeThrough_one⟩

/-- Doing nothing cannot buy safety through horizon one. -/
theorem doNothing_not_safeThrough_one :
    ¬ SafeThrough WinU UContract UEnvelope repairApply
      forgetU UState.rich Repair.doNothing 1 := by
  intro hs
  have h1 := hs 1 le_rfl
  change RobustSafeAt WinU UContract UEnvelope forgetU UState.rich 1 at h1
  exact uncertain_forget_revoked_one h1

/-- Any budget below five is insufficient for horizon one. -/
theorem witness_not_affordable_below_five
    {B : Nat} (hB : B < 5) :
    ¬ AffordableThrough WinU UContract UEnvelope repairApply repairCost
      forgetU UState.rich B 1 := by
  rintro ⟨a, hcost, hsafe⟩
  cases a with
  | doNothing =>
      exact doNothing_not_safeThrough_one hsafe
  | restore =>
      simp [repairCost] at hcost
      omega

noncomputable def WitnessPrice0 : Nat :=
  FuturePrice WinU UContract UEnvelope repairApply repairCost
    forgetU UState.rich 0 witness_feasible_zero

noncomputable def WitnessPrice1 : Nat :=
  FuturePrice WinU UContract UEnvelope repairApply repairCost
    forgetU UState.rich 1 witness_feasible_one

/-- Exact price at horizon zero is zero. -/
theorem witness_price_zero : WitnessPrice0 = 0 := by
  unfold WitnessPrice0
  have hle :
      FuturePrice WinU UContract UEnvelope repairApply repairCost
        forgetU UState.rich 0 witness_feasible_zero ≤ 0 := by
    apply futurePrice_minimal WinU UContract UEnvelope repairApply repairCost
      forgetU UState.rich 0 witness_feasible_zero
    exact ⟨Repair.doNothing, by simp [repairCost], doNothing_safeThrough_zero⟩
  omega

/-- Exact price at horizon one is five. -/
theorem witness_price_one : WitnessPrice1 = 5 := by
  unfold WitnessPrice1
  let P := FuturePrice WinU UContract UEnvelope repairApply repairCost
    forgetU UState.rich 1 witness_feasible_one
  have hle : P ≤ 5 := by
    apply futurePrice_minimal WinU UContract UEnvelope repairApply repairCost
      forgetU UState.rich 1 witness_feasible_one
    exact ⟨Repair.restore, by simp [repairCost], restore_safeThrough_one⟩
  have hge : 5 ≤ P := by
    by_contra hnot
    have hlt : P < 5 := by omega
    have haff :
        AffordableThrough WinU UContract UEnvelope repairApply repairCost
          forgetU UState.rich P 1 := by
      exact futurePrice_affordable WinU UContract UEnvelope repairApply repairCost
        forgetU UState.rich 1 witness_feasible_one
    exact witness_not_affordable_below_five hlt haff
  omega

/-- The robust future price strictly jumps when the weak capability becomes plausible. -/
theorem exact_future_price_jump :
    WitnessPrice0 = 0 ∧ WitnessPrice1 = 5 ∧ WitnessPrice0 < WitnessPrice1 := by
  rw [witness_price_zero, witness_price_one]
  omega

/-- In the two-action witness, any intervention that buys horizon one must be restoration. -/
theorem horizon_one_forces_restore
    (a : Repair)
    (hsafe : SafeThrough WinU UContract UEnvelope repairApply
      forgetU UState.rich a 1) :
    a = Repair.restore := by
  cases a with
  | doNothing =>
      exact False.elim (doNothing_not_safeThrough_one hsafe)
  | restore =>
      rfl

/-- Restoration is an attained optimal intervention at the exact minimal price five. -/
theorem restore_is_exact_optimum :
    repairCost Repair.restore = WitnessPrice1 ∧
    SafeThrough WinU UContract UEnvelope repairApply
      forgetU UState.rich Repair.restore 1 := by
  rw [witness_price_one]
  exact ⟨by simp [repairCost], restore_safeThrough_one⟩

end ExactPriceWitness

end InsacermoRobustFuturePrice
