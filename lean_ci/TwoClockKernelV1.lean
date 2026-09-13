import Mathlib
import RobustRightToForgetKernelV1

namespace InsacermoTwoClock

open Set
open InsacermoRobustRightToForget

universe u v w

section GenericTwoClock

variable {State : Type u} {Req : Type v} {Cap : Type w}

/-- Destruction-specific robust debt: a capability/obligation pair still guaranteed by the
intact source but destroyed by the irreversible map. -/
def RobustDestructionDebtAt
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State) (h : Nat) : Prop :=
  ∃ c q,
    c ∈ C h ∧ q ∈ Γ h ∧ Win x c q ∧ ¬ Win (d x) c q

/-- Eventual destruction-specific debt. -/
def EverDestructionDebt
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State) : Prop :=
  ∃ h, RobustDestructionDebtAt Win Γ C d x h

/-- Eventual baseline failure of the intact source. -/
def EverSourceFailure
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (x : State) : Prop :=
  ∃ h, ¬ ViableAt Win Γ C x h

/-- First horizon where destruction creates robust debt. -/
noncomputable def DestructionCriticalHorizon
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State)
    (hev : EverDestructionDebt Win Γ C d x) : Nat := by
  classical
  exact Nat.find hev

/-- First horizon where the intact source itself ceases to satisfy the robust contract. -/
noncomputable def ViabilityCriticalHorizon
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (x : State)
    (hev : EverSourceFailure Win Γ C x) : Nat := by
  classical
  exact Nat.find hev

/-- Relative robust admissibility is exactly absence of destruction-specific debt. -/
theorem relativeRobust_iff_no_destructionDebt
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State) (h : Nat) :
    RelativeRobustAdmissibleAt Win Γ C d x h ↔
      ¬ RobustDestructionDebtAt Win Γ C d x h := by
  constructor
  · intro hrel hdebt
    rcases hdebt with ⟨c, q, hc, hq, hx, hnot⟩
    exact hnot (hrel c hc q hq hx)
  · intro hnodebt c hc q hq hx
    by_contra hnot
    exact hnodebt ⟨c, q, hc, hq, hx, hnot⟩

/-- Strong robust safety splits into baseline source viability and absence of destruction debt. -/
theorem robustSafe_iff_sourceViable_and_noDebt
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State) (h : Nat) :
    RobustSafeAt Win Γ C d x h ↔
      ViableAt Win Γ C x h ∧
      ¬ RobustDestructionDebtAt Win Γ C d x h := by
  constructor
  · rintro ⟨hsrc, htgt⟩
    refine ⟨hsrc, ?_⟩
    rintro ⟨c, q, hc, hq, hx, hnot⟩
    exact hnot (htgt c hc q hq)
  · rintro ⟨hsrc, hnodebt⟩
    refine ⟨hsrc, ?_⟩
    intro c hc q hq
    by_contra hnot
    exact hnodebt ⟨c, q, hc, hq, hsrc c hc q hq, hnot⟩

/-- Destruction-specific debt persists when contracts and uncertainty envelopes expand. -/
theorem destructionDebt_persists
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    {h k : Nat} (hhk : h ≤ k)
    (hdebt : RobustDestructionDebtAt Win Γ C d x h) :
    RobustDestructionDebtAt Win Γ C d x k := by
  rcases hdebt with ⟨c, q, hc, hq, hx, hnot⟩
  exact ⟨c, q, hC hhk hc, hΓ hhk hq, hx, hnot⟩

/-- Once the intact source becomes nonviable it remains nonviable under expanding contracts/scenarios. -/
theorem sourceFailure_persists
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (x : State)
    {h k : Nat} (hhk : h ≤ k)
    (hfail : ¬ ViableAt Win Γ C x h) :
    ¬ ViableAt Win Γ C x k := by
  intro hvk
  exact hfail (viable_antitone_in_horizon Win Γ C hΓ hC x hhk hvk)

/-- The destruction clock rings at an actual debt horizon. -/
theorem destructionCritical_hasDebt
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State)
    (hev : EverDestructionDebt Win Γ C d x) :
    RobustDestructionDebtAt Win Γ C d x
      (DestructionCriticalHorizon Win Γ C d x hev) := by
  classical
  exact Nat.find_spec hev

/-- No destruction debt exists before the destruction clock. -/
theorem noDebt_before_destructionCritical
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State)
    (hev : EverDestructionDebt Win Γ C d x)
    {h : Nat} (hlt : h < DestructionCriticalHorizon Win Γ C d x hev) :
    ¬ RobustDestructionDebtAt Win Γ C d x h := by
  classical
  intro hdebt
  have hmin : DestructionCriticalHorizon Win Γ C d x hev ≤ h := by
    exact Nat.find_min' hev hdebt
  omega

/-- Exact threshold law for destruction-specific debt. -/
theorem noDebt_iff_before_destructionCritical
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    (hev : EverDestructionDebt Win Γ C d x)
    (h : Nat) :
    (¬ RobustDestructionDebtAt Win Γ C d x h) ↔
      h < DestructionCriticalHorizon Win Γ C d x hev := by
  constructor
  · intro hnodebt
    by_contra hnotlt
    have hge : DestructionCriticalHorizon Win Γ C d x hev ≤ h := by omega
    exact hnodebt (destructionDebt_persists Win Γ C hΓ hC d x hge
      (destructionCritical_hasDebt Win Γ C d x hev))
  · intro hlt
    exact noDebt_before_destructionCritical Win Γ C d x hev hlt

/-- The viability clock rings at an actual baseline source failure. -/
theorem viabilityCritical_failed
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (x : State)
    (hev : EverSourceFailure Win Γ C x) :
    ¬ ViableAt Win Γ C x
      (ViabilityCriticalHorizon Win Γ C x hev) := by
  classical
  exact Nat.find_spec hev

/-- The intact source is viable before the viability clock. -/
theorem sourceViable_before_viabilityCritical
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (x : State)
    (hev : EverSourceFailure Win Γ C x)
    {h : Nat} (hlt : h < ViabilityCriticalHorizon Win Γ C x hev) :
    ViableAt Win Γ C x h := by
  classical
  by_contra hfail
  have hmin : ViabilityCriticalHorizon Win Γ C x hev ≤ h := by
    exact Nat.find_min' hev hfail
  omega

/-- Exact threshold law for intact-source viability. -/
theorem sourceViable_iff_before_viabilityCritical
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (x : State)
    (hev : EverSourceFailure Win Γ C x)
    (h : Nat) :
    ViableAt Win Γ C x h ↔
      h < ViabilityCriticalHorizon Win Γ C x hev := by
  constructor
  · intro hv
    by_contra hnotlt
    have hge : ViabilityCriticalHorizon Win Γ C x hev ≤ h := by omega
    have hfail := sourceFailure_persists Win Γ C hΓ hC x hge
      (viabilityCritical_failed Win Γ C x hev)
    exact hfail hv
  · intro hlt
    exact sourceViable_before_viabilityCritical Win Γ C x hev hlt

/-- The first loss of strong robust safety is the earlier of the destruction-debt clock
and the intact-source viability clock. -/
noncomputable def TwoClockBoundary
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State)
    (hevD : EverDestructionDebt Win Γ C d x)
    (hevV : EverSourceFailure Win Γ C x) : Nat :=
  Nat.min
    (DestructionCriticalHorizon Win Γ C d x hevD)
    (ViabilityCriticalHorizon Win Γ C x hevV)

/-- Before both clocks ring, and only then, strong robust safety holds. -/
theorem robustSafe_iff_before_both_clocks
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    (hevD : EverDestructionDebt Win Γ C d x)
    (hevV : EverSourceFailure Win Γ C x)
    (h : Nat) :
    RobustSafeAt Win Γ C d x h ↔
      h < ViabilityCriticalHorizon Win Γ C x hevV ∧
      h < DestructionCriticalHorizon Win Γ C d x hevD := by
  rw [robustSafe_iff_sourceViable_and_noDebt]
  constructor
  · rintro ⟨hsrc, hnodebt⟩
    exact ⟨
      (sourceViable_iff_before_viabilityCritical Win Γ C hΓ hC x hevV h).mp hsrc,
      (noDebt_iff_before_destructionCritical Win Γ C hΓ hC d x hevD h).mp hnodebt
    ⟩
  · rintro ⟨hv, hd⟩
    exact ⟨
      (sourceViable_iff_before_viabilityCritical Win Γ C hΓ hC x hevV h).mpr hv,
      (noDebt_iff_before_destructionCritical Win Γ C hΓ hC d x hevD h).mpr hd
    ⟩

/-- Exact two-clock threshold: robust safety lasts exactly until the earlier clock. -/
theorem robustSafe_iff_before_twoClockBoundary
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    (hevD : EverDestructionDebt Win Γ C d x)
    (hevV : EverSourceFailure Win Γ C x)
    (h : Nat) :
    RobustSafeAt Win Γ C d x h ↔
      h < TwoClockBoundary Win Γ C d x hevD hevV := by
  rw [robustSafe_iff_before_both_clocks Win Γ C hΓ hC d x hevD hevV h]
  unfold TwoClockBoundary
  let τD := DestructionCriticalHorizon Win Γ C d x hevD
  let τV := ViabilityCriticalHorizon Win Γ C x hevV
  change (h < τV ∧ h < τD) ↔ h < min τD τV
  rw [lt_min_iff]
  constructor
  · rintro ⟨hv, hd⟩
    exact ⟨hd, hv⟩
  · rintro ⟨hd, hv⟩
    exact ⟨hv, hd⟩

/-- If both clocks eventually ring, strong robust safety is eventually revoked. -/
theorem twoClock_everRobustRevoked
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State)
    (hevD : EverDestructionDebt Win Γ C d x)
    (hevV : EverSourceFailure Win Γ C x) :
    EverRobustRevoked Win Γ C d x := by
  refine ⟨ViabilityCriticalHorizon Win Γ C x hevV, ?_⟩
  intro hsafe
  exact (viabilityCritical_failed Win Γ C x hevV) hsafe.1

/-- The original robust critical horizon is exactly the minimum of the two causal clocks. -/
theorem robustCriticalHorizon_eq_twoClockBoundary
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    (hevD : EverDestructionDebt Win Γ C d x)
    (hevV : EverSourceFailure Win Γ C x)
    (hevR : EverRobustRevoked Win Γ C d x) :
    RobustCriticalHorizon Win Γ C d x hevR =
      TwoClockBoundary Win Γ C d x hevD hevV := by
  classical
  let B := TwoClockBoundary Win Γ C d x hevD hevV
  let R := RobustCriticalHorizon Win Γ C d x hevR
  have hnotB : ¬ RobustSafeAt Win Γ C d x B := by
    intro hs
    have hlt := (robustSafe_iff_before_twoClockBoundary
      Win Γ C hΓ hC d x hevD hevV B).mp hs
    omega
  have hle : R ≤ B := by
    exact Nat.find_min' hevR hnotB
  have hge : B ≤ R := by
    by_contra hnot
    have hlt : R < B := by omega
    have hsafeR : RobustSafeAt Win Γ C d x R :=
      (robustSafe_iff_before_twoClockBoundary
        Win Γ C hΓ hC d x hevD hevV R).mpr hlt
    have hrevR : ¬ RobustSafeAt Win Γ C d x R := by
      exact robustCriticalHorizon_revoked Win Γ C d x hevR
    exact hrevR hsafeR
  exact Nat.le_antisymm hle hge

/-- If destruction debt arrives first, the source is still viable at that boundary and the
first failure is genuinely destruction-caused. -/
theorem destruction_first_boundary_cause
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    (hevD : EverDestructionDebt Win Γ C d x)
    (hevV : EverSourceFailure Win Γ C x)
    (hfirst : DestructionCriticalHorizon Win Γ C d x hevD <
      ViabilityCriticalHorizon Win Γ C x hevV) :
    ViableAt Win Γ C x (DestructionCriticalHorizon Win Γ C d x hevD) ∧
    RobustDestructionDebtAt Win Γ C d x
      (DestructionCriticalHorizon Win Γ C d x hevD) := by
  exact ⟨
    (sourceViable_iff_before_viabilityCritical Win Γ C hΓ hC x hevV
      (DestructionCriticalHorizon Win Γ C d x hevD)).mpr hfirst,
    destructionCritical_hasDebt Win Γ C d x hevD
  ⟩

/-- If baseline viability fails first, no destruction-specific debt exists yet: the future
contract itself has become impossible before forgetting becomes the culprit. -/
theorem viability_first_boundary_cause
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    (hevD : EverDestructionDebt Win Γ C d x)
    (hevV : EverSourceFailure Win Γ C x)
    (hfirst : ViabilityCriticalHorizon Win Γ C x hevV <
      DestructionCriticalHorizon Win Γ C d x hevD) :
    (¬ ViableAt Win Γ C x (ViabilityCriticalHorizon Win Γ C x hevV)) ∧
    (¬ RobustDestructionDebtAt Win Γ C d x
      (ViabilityCriticalHorizon Win Γ C x hevV)) := by
  exact ⟨
    viabilityCritical_failed Win Γ C x hevV,
    (noDebt_iff_before_destructionCritical Win Γ C hΓ hC d x hevD
      (ViabilityCriticalHorizon Win Γ C x hevV)).mpr hfirst
  ⟩

/-- If the clocks coincide, both baseline impossibility and destruction-specific debt appear
at the same first boundary. -/
theorem simultaneous_boundary_cause
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (d : State → State) (x : State)
    (hevD : EverDestructionDebt Win Γ C d x)
    (hevV : EverSourceFailure Win Γ C x)
    (heq : DestructionCriticalHorizon Win Γ C d x hevD =
      ViabilityCriticalHorizon Win Γ C x hevV) :
    (¬ ViableAt Win Γ C x (DestructionCriticalHorizon Win Γ C d x hevD)) ∧
    RobustDestructionDebtAt Win Γ C d x
      (DestructionCriticalHorizon Win Γ C d x hevD) := by
  constructor
  · rw [heq]
    exact viabilityCritical_failed Win Γ C x hevV
  · exact destructionCritical_hasDebt Win Γ C d x hevD

/-- Causal trichotomy at the first robust boundary: destruction first, viability first, or both. -/
theorem twoClock_causal_trichotomy
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    (hevD : EverDestructionDebt Win Γ C d x)
    (hevV : EverSourceFailure Win Γ C x) :
    (
      DestructionCriticalHorizon Win Γ C d x hevD <
        ViabilityCriticalHorizon Win Γ C x hevV ∧
      ViableAt Win Γ C x (DestructionCriticalHorizon Win Γ C d x hevD) ∧
      RobustDestructionDebtAt Win Γ C d x
        (DestructionCriticalHorizon Win Γ C d x hevD)
    ) ∨
    (
      ViabilityCriticalHorizon Win Γ C x hevV <
        DestructionCriticalHorizon Win Γ C d x hevD ∧
      ¬ ViableAt Win Γ C x (ViabilityCriticalHorizon Win Γ C x hevV) ∧
      ¬ RobustDestructionDebtAt Win Γ C d x
        (ViabilityCriticalHorizon Win Γ C x hevV)
    ) ∨
    (
      DestructionCriticalHorizon Win Γ C d x hevD =
        ViabilityCriticalHorizon Win Γ C x hevV ∧
      ¬ ViableAt Win Γ C x (DestructionCriticalHorizon Win Γ C d x hevD) ∧
      RobustDestructionDebtAt Win Γ C d x
        (DestructionCriticalHorizon Win Γ C d x hevD)
    ) := by
  rcases lt_trichotomy
    (DestructionCriticalHorizon Win Γ C d x hevD)
    (ViabilityCriticalHorizon Win Γ C x hevV) with hlt | heq | hgt
  · left
    rcases destruction_first_boundary_cause Win Γ C hΓ hC d x hevD hevV hlt with
      ⟨hsrc, hdebt⟩
    exact ⟨hlt, hsrc, hdebt⟩
  · right
    right
    rcases simultaneous_boundary_cause Win Γ C d x hevD hevV heq with
      ⟨hfail, hdebt⟩
    exact ⟨heq, hfail, hdebt⟩
  · right
    left
    rcases viability_first_boundary_cause Win Γ C hΓ hC d x hevD hevV hgt with
      ⟨hfail, hnodebt⟩
    exact ⟨hgt, hfail, hnodebt⟩

/-- Consolidated theorem: the robust right-to-forget boundary is the minimum of two persistent,
causally distinct clocks, with an exact causal classification at the boundary. -/
theorem two_clock_decomposition_v1
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (hΓ : ContractMonotoneNat Γ)
    (hC : EnvelopeMonotone C)
    (d : State → State) (x : State)
    (hevD : EverDestructionDebt Win Γ C d x)
    (hevV : EverSourceFailure Win Γ C x) :
    (∀ h,
      RobustSafeAt Win Γ C d x h ↔
        h < TwoClockBoundary Win Γ C d x hevD hevV) ∧
    (
      DestructionCriticalHorizon Win Γ C d x hevD <
        ViabilityCriticalHorizon Win Γ C x hevV ∨
      ViabilityCriticalHorizon Win Γ C x hevV <
        DestructionCriticalHorizon Win Γ C d x hevD ∨
      DestructionCriticalHorizon Win Γ C d x hevD =
        ViabilityCriticalHorizon Win Γ C x hevV
    ) := by
  constructor
  · intro h
    exact robustSafe_iff_before_twoClockBoundary Win Γ C hΓ hC d x hevD hevV h
  · omega

end GenericTwoClock

section ExactDualWitnesses

inductive ClockState
  | intact
  | forgotten
  deriving DecidableEq, Repr

inductive ClockReq
  | preserve
  | impossible
  deriving DecidableEq, Repr

open ClockState ClockReq

/-- The intact state can always preserve the ordinary obligation but cannot satisfy the
intentionally impossible obligation. The forgotten state additionally needs capability ≥ 1. -/
def ClockWin : ClockState → Nat → ClockReq → Prop
  | intact, _, preserve => True
  | intact, _, impossible => False
  | forgotten, c, preserve => 1 ≤ c
  | forgotten, _, impossible => False

def clockDestroy : ClockState → ClockState
  | intact => forgotten
  | forgotten => forgotten

/-- Contract adds the impossible obligation at threshold t. -/
def ContractAt (t h : Nat) : Set ClockReq :=
  {q | q = preserve ∨ (t ≤ h ∧ q = impossible)}

/-- Capability uncertainty adds weak capability 0 at threshold t. -/
def EnvelopeAt (t h : Nat) : Set Nat :=
  {c | c = 1 ∨ (t ≤ h ∧ c = 0)}

theorem contractAt_monotone (t : Nat) : ContractMonotoneNat (ContractAt t) := by
  intro h k hhk q hq
  rcases hq with hpres | ⟨ht, himp⟩
  · exact Or.inl hpres
  · exact Or.inr ⟨le_trans ht hhk, himp⟩

theorem envelopeAt_monotone (t : Nat) : EnvelopeMonotone (EnvelopeAt t) := by
  intro h k hhk c hc
  rcases hc with hone | ⟨ht, hzero⟩
  · exact Or.inl hone
  · exact Or.inr ⟨le_trans ht hhk, hzero⟩

/-- Before the contract-impossibility threshold, the intact source is viable. -/
theorem clock_source_viable_before
    (capThreshold reqThreshold h : Nat)
    (hh : h < reqThreshold) :
    ViableAt ClockWin (ContractAt reqThreshold) (EnvelopeAt capThreshold) intact h := by
  intro c hc q hq
  rcases hq with hpres | ⟨hreq, himp⟩
  · subst q
    trivial
  · omega

/-- At the contract-impossibility threshold, the intact source fails. -/
theorem clock_source_fails_at
    (capThreshold reqThreshold : Nat) :
    ¬ ViableAt ClockWin (ContractAt reqThreshold) (EnvelopeAt capThreshold)
      intact reqThreshold := by
  intro hv
  have hbad := hv 1 (Or.inl rfl) impossible (Or.inr ⟨le_rfl, rfl⟩)
  exact hbad

/-- Before weak capability 0 becomes plausible, there is no destruction-specific debt. -/
theorem clock_no_debt_before
    (capThreshold reqThreshold h : Nat)
    (hh : h < capThreshold) :
    ¬ RobustDestructionDebtAt ClockWin (ContractAt reqThreshold)
      (EnvelopeAt capThreshold) clockDestroy intact h := by
  rintro ⟨c, q, hc, hq, hx, hnot⟩
  rcases hc with hone | ⟨hcap, hzero⟩
  · subst c
    cases q <;> simp [ClockWin, clockDestroy] at hx hnot
  · omega

/-- Exactly when weak capability 0 becomes plausible, forgetting creates debt for `preserve`. -/
theorem clock_debt_at
    (capThreshold reqThreshold : Nat) :
    RobustDestructionDebtAt ClockWin (ContractAt reqThreshold)
      (EnvelopeAt capThreshold) clockDestroy intact capThreshold := by
  refine ⟨0, preserve, ?_, ?_, ?_, ?_⟩
  · exact Or.inr ⟨le_rfl, rfl⟩
  · exact Or.inl rfl
  · trivial
  · simp [ClockWin, clockDestroy]

/-- Debt-first world: weak capability appears at 1; baseline impossibility appears at 2. -/
def DFContract := ContractAt 2
def DFEnvelope := EnvelopeAt 1

theorem df_contract_monotone : ContractMonotoneNat DFContract := contractAt_monotone 2
theorem df_envelope_monotone : EnvelopeMonotone DFEnvelope := envelopeAt_monotone 1

theorem df_ever_debt : EverDestructionDebt ClockWin DFContract DFEnvelope clockDestroy intact := by
  exact ⟨1, clock_debt_at 1 2⟩

theorem df_ever_source_failure : EverSourceFailure ClockWin DFContract DFEnvelope intact := by
  exact ⟨2, clock_source_fails_at 1 2⟩

theorem df_destructionCritical_eq_one :
    DestructionCriticalHorizon ClockWin DFContract DFEnvelope clockDestroy intact
      df_ever_debt = 1 := by
  classical
  have hle :
      DestructionCriticalHorizon ClockWin DFContract DFEnvelope clockDestroy intact
        df_ever_debt ≤ 1 := by
    exact Nat.find_min' df_ever_debt (clock_debt_at 1 2)
  have hge :
      1 ≤ DestructionCriticalHorizon ClockWin DFContract DFEnvelope clockDestroy intact
        df_ever_debt := by
    by_contra hnot
    have hzero :
        DestructionCriticalHorizon ClockWin DFContract DFEnvelope clockDestroy intact
          df_ever_debt = 0 := by omega
    have hcrit := destructionCritical_hasDebt ClockWin DFContract DFEnvelope
      clockDestroy intact df_ever_debt
    rw [hzero] at hcrit
    exact (clock_no_debt_before 1 2 0 (by omega)) hcrit
  omega

theorem df_viabilityCritical_eq_two :
    ViabilityCriticalHorizon ClockWin DFContract DFEnvelope intact
      df_ever_source_failure = 2 := by
  classical
  have hle :
      ViabilityCriticalHorizon ClockWin DFContract DFEnvelope intact
        df_ever_source_failure ≤ 2 := by
    exact Nat.find_min' df_ever_source_failure (clock_source_fails_at 1 2)
  have hge :
      2 ≤ ViabilityCriticalHorizon ClockWin DFContract DFEnvelope intact
        df_ever_source_failure := by
    by_contra hnot
    have hlt :
        ViabilityCriticalHorizon ClockWin DFContract DFEnvelope intact
          df_ever_source_failure < 2 := by omega
    have hviable := clock_source_viable_before 1 2
      (ViabilityCriticalHorizon ClockWin DFContract DFEnvelope intact df_ever_source_failure) hlt
    exact (viabilityCritical_failed ClockWin DFContract DFEnvelope intact
      df_ever_source_failure) hviable
  omega

theorem df_twoClockBoundary_eq_one :
    TwoClockBoundary ClockWin DFContract DFEnvelope clockDestroy intact
      df_ever_debt df_ever_source_failure = 1 := by
  unfold TwoClockBoundary
  rw [df_destructionCritical_eq_one, df_viabilityCritical_eq_two]
  decide

theorem df_destruction_really_first :
    ViableAt ClockWin DFContract DFEnvelope intact 1 ∧
    RobustDestructionDebtAt ClockWin DFContract DFEnvelope clockDestroy intact 1 := by
  have hfirst :
      DestructionCriticalHorizon ClockWin DFContract DFEnvelope clockDestroy intact df_ever_debt <
      ViabilityCriticalHorizon ClockWin DFContract DFEnvelope intact df_ever_source_failure := by
    rw [df_destructionCritical_eq_one, df_viabilityCritical_eq_two]
    omega
  simpa [df_destructionCritical_eq_one] using
    (destruction_first_boundary_cause ClockWin DFContract DFEnvelope
      df_contract_monotone df_envelope_monotone clockDestroy intact
      df_ever_debt df_ever_source_failure hfirst)

/-- Viability-first world: baseline impossibility appears at 1; destruction debt only at 2. -/
def VFContract := ContractAt 1
def VFEnvelope := EnvelopeAt 2

theorem vf_contract_monotone : ContractMonotoneNat VFContract := contractAt_monotone 1
theorem vf_envelope_monotone : EnvelopeMonotone VFEnvelope := envelopeAt_monotone 2

theorem vf_ever_debt : EverDestructionDebt ClockWin VFContract VFEnvelope clockDestroy intact := by
  exact ⟨2, clock_debt_at 2 1⟩

theorem vf_ever_source_failure : EverSourceFailure ClockWin VFContract VFEnvelope intact := by
  exact ⟨1, clock_source_fails_at 2 1⟩

theorem vf_destructionCritical_eq_two :
    DestructionCriticalHorizon ClockWin VFContract VFEnvelope clockDestroy intact
      vf_ever_debt = 2 := by
  classical
  have hle :
      DestructionCriticalHorizon ClockWin VFContract VFEnvelope clockDestroy intact
        vf_ever_debt ≤ 2 := by
    exact Nat.find_min' vf_ever_debt (clock_debt_at 2 1)
  have hge :
      2 ≤ DestructionCriticalHorizon ClockWin VFContract VFEnvelope clockDestroy intact
        vf_ever_debt := by
    by_contra hnot
    have hlt :
        DestructionCriticalHorizon ClockWin VFContract VFEnvelope clockDestroy intact
          vf_ever_debt < 2 := by omega
    have hnodebt := clock_no_debt_before 2 1
      (DestructionCriticalHorizon ClockWin VFContract VFEnvelope clockDestroy intact vf_ever_debt) hlt
    exact hnodebt (destructionCritical_hasDebt ClockWin VFContract VFEnvelope
      clockDestroy intact vf_ever_debt)
  omega

theorem vf_viabilityCritical_eq_one :
    ViabilityCriticalHorizon ClockWin VFContract VFEnvelope intact
      vf_ever_source_failure = 1 := by
  classical
  have hle :
      ViabilityCriticalHorizon ClockWin VFContract VFEnvelope intact
        vf_ever_source_failure ≤ 1 := by
    exact Nat.find_min' vf_ever_source_failure (clock_source_fails_at 2 1)
  have hge :
      1 ≤ ViabilityCriticalHorizon ClockWin VFContract VFEnvelope intact
        vf_ever_source_failure := by
    by_contra hnot
    have hzero :
        ViabilityCriticalHorizon ClockWin VFContract VFEnvelope intact
          vf_ever_source_failure = 0 := by omega
    have hviable := clock_source_viable_before 2 1 0 (by omega)
    have hfail := viabilityCritical_failed ClockWin VFContract VFEnvelope intact
      vf_ever_source_failure
    rw [hzero] at hfail
    exact hfail hviable
  omega

theorem vf_twoClockBoundary_eq_one :
    TwoClockBoundary ClockWin VFContract VFEnvelope clockDestroy intact
      vf_ever_debt vf_ever_source_failure = 1 := by
  unfold TwoClockBoundary
  rw [vf_destructionCritical_eq_two, vf_viabilityCritical_eq_one]
  decide

theorem vf_viability_really_first :
    (¬ ViableAt ClockWin VFContract VFEnvelope intact 1) ∧
    (¬ RobustDestructionDebtAt ClockWin VFContract VFEnvelope clockDestroy intact 1) := by
  have hfirst :
      ViabilityCriticalHorizon ClockWin VFContract VFEnvelope intact vf_ever_source_failure <
      DestructionCriticalHorizon ClockWin VFContract VFEnvelope clockDestroy intact vf_ever_debt := by
    rw [vf_viabilityCritical_eq_one, vf_destructionCritical_eq_two]
    omega
  simpa [vf_viabilityCritical_eq_one] using
    (viability_first_boundary_cause ClockWin VFContract VFEnvelope
      vf_contract_monotone vf_envelope_monotone clockDestroy intact
      vf_ever_debt vf_ever_source_failure hfirst)

/-- Dual exact witnesses: the same robust boundary can be caused by destruction debt first
or by baseline viability failure first. -/
theorem dual_clock_separation_witnesses :
    (
      DestructionCriticalHorizon ClockWin DFContract DFEnvelope clockDestroy intact df_ever_debt = 1 ∧
      ViabilityCriticalHorizon ClockWin DFContract DFEnvelope intact df_ever_source_failure = 2 ∧
      TwoClockBoundary ClockWin DFContract DFEnvelope clockDestroy intact
        df_ever_debt df_ever_source_failure = 1
    ) ∧
    (
      DestructionCriticalHorizon ClockWin VFContract VFEnvelope clockDestroy intact vf_ever_debt = 2 ∧
      ViabilityCriticalHorizon ClockWin VFContract VFEnvelope intact vf_ever_source_failure = 1 ∧
      TwoClockBoundary ClockWin VFContract VFEnvelope clockDestroy intact
        vf_ever_debt vf_ever_source_failure = 1
    ) := by
  exact ⟨
    ⟨df_destructionCritical_eq_one, df_viabilityCritical_eq_two, df_twoClockBoundary_eq_one⟩,
    ⟨vf_destructionCritical_eq_two, vf_viabilityCritical_eq_one, vf_twoClockBoundary_eq_one⟩
  ⟩

end ExactDualWitnesses

end InsacermoTwoClock
