import Mathlib

namespace InsacermoProbeRepair

open Set
open scoped BigOperators

/-!
INSACERMO Probe–Repair Duality Kernel V1.

Targets:
T1  Obstruction Resolution Cover Theorem.
T2W Fractional probe–repair weak duality.
T3  Minimal-obstruction insufficiency under variable repair.
T4  Unbounded hybrid PROBE+REPAIR advantage.

Strong LP duality is deliberately not asserted here: mathlib v4.32.1 contains Farkas/separation
machinery but no ready-made linear-programming strong-duality API. The structural reduction and
universal weak-duality inequality are proved without added axioms.
-/

section StructuralCore

variable {W A Y Q : Type*}

def FinalFiber (h : W → Y) (out : Q → W → Bool) (P : Set Q) (s : W) : Set W :=
  {t | h t = h s ∧ ∀ q, q ∈ P → out q t = out q s}

def SafeAfter (Good : W → A → Prop) (C : Set A) (h : W → Y)
    (out : Q → W → Bool) (P : Set Q) : Prop :=
  ∀ s, ∃ a, a ∈ C ∧ ∀ t, t ∈ FinalFiber h out P s → Good t a

def HasCommonAction (Good : W → A → Prop) (C : Set A) (O : Set W) : Prop :=
  ∃ a, a ∈ C ∧ ∀ t, t ∈ O → Good t a

def InitialObstruction (Good : W → A → Prop) (C : Set A) (h : W → Y)
    (O : Set W) : Prop :=
  O.Nonempty ∧ (∃ s₀, O ⊆ {t | h t = h s₀}) ∧ ¬ HasCommonAction Good C O

def Separated (out : Q → W → Bool) (P : Set Q) (O : Set W) : Prop :=
  ∃ q, q ∈ P ∧ ∃ s, s ∈ O ∧ ∃ t, t ∈ O ∧ out q s ≠ out q t

def CoveredBy (Good : W → A → Prop) (R : Set A) (O : Set W) : Prop :=
  HasCommonAction Good R O

/-- T1 — Obstruction Resolution Cover Theorem. -/
theorem obstruction_resolution_cover
    (Good : W → A → Prop) (C R : Set A) (h : W → Y)
    (out : Q → W → Bool) (P : Set Q) :
    SafeAfter Good (C ∪ R) h out P ↔
      ∀ O, InitialObstruction Good C h O → Separated out P O ∨ CoveredBy Good R O := by
  classical
  constructor
  · intro hsafe O hO
    by_cases hsep : Separated out P O
    · exact Or.inl hsep
    · right
      rcases hO with ⟨hneO, ⟨b, hb⟩, hnoOld⟩
      rcases hneO with ⟨s₀, hs₀O⟩
      rcases hsafe s₀ with ⟨a, haCR, haSafe⟩
      have hs₀h : h s₀ = h b := hb hs₀O
      have hsameH : ∀ t, t ∈ O → h t = h s₀ := by
        intro t ht
        exact (hb ht).trans hs₀h.symm
      have hsameQ : ∀ t, t ∈ O → ∀ q, q ∈ P → out q t = out q s₀ := by
        intro t ht q hq
        by_contra hne
        apply hsep
        exact ⟨q, hq, t, ht, s₀, hs₀O, hne⟩
      have hGoodO : ∀ t, t ∈ O → Good t a := by
        intro t ht
        exact haSafe t ⟨hsameH t ht, hsameQ t ht⟩
      rcases haCR with haC | haR
      · exact False.elim (hnoOld ⟨a, haC, hGoodO⟩)
      · exact ⟨a, haR, hGoodO⟩
  · intro hresolve s
    let O : Set W := FinalFiber h out P s
    by_cases hOld : HasCommonAction Good C O
    · rcases hOld with ⟨a, haC, haGood⟩
      exact ⟨a, Or.inl haC, by simpa [O] using haGood⟩
    · have hOb : InitialObstruction Good C h O := by
        refine ⟨⟨s, ?_⟩, ⟨s, ?_⟩, hOld⟩
        · simp [O, FinalFiber]
        · intro t ht
          exact ht.1
      have hNoSep : ¬ Separated out P O := by
        intro hsep
        rcases hsep with ⟨q, hq, u, hu, v, hv, huv⟩
        exact huv ((hu.2 q hq).trans (hv.2 q hq).symm)
      rcases hresolve O hOb with hsep | hnew
      · exact False.elim (hNoSep hsep)
      · rcases hnew with ⟨a, haR, haGood⟩
        exact ⟨a, Or.inr haR, by simpa [O] using haGood⟩

end StructuralCore

section FractionalDuality

variable {Obs Intv : Type*} [Fintype Obs] [Fintype Intv]

/-- T2W — weak duality for the fractional obstruction-cover relaxation. -/
theorem fractional_probe_repair_weak_duality
    (M : Obs → Intv → ℝ) (c : Intv → ℝ) (x : Intv → ℝ) (y : Obs → ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (hy : ∀ o, 0 ≤ y o)
    (hPrimal : ∀ o, 1 ≤ ∑ i, M o i * x i)
    (hDual : ∀ i, (∑ o, M o i * y o) ≤ c i) :
    (∑ o, y o) ≤ ∑ i, c i * x i := by
  classical
  have hrow : ∀ o, y o ≤ y o * (∑ i, M o i * x i) := by
    intro o
    have hm := mul_le_mul_of_nonneg_left (hPrimal o) (hy o)
    simpa using hm
  calc
    (∑ o, y o) ≤ ∑ o, y o * (∑ i, M o i * x i) := by
      exact Finset.sum_le_sum (fun o _ => hrow o)
    _ = ∑ i, x i * (∑ o, M o i * y o) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro o ho
      ring
    _ ≤ ∑ i, x i * c i := by
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hDual i) (hx i))
    _ = ∑ i, c i * x i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

end FractionalDuality

section MinimalObstructionCounterexample

inductive W3
  | w1 | w2 | w3
  deriving DecidableEq, Fintype

inductive A6
  | a1 | a2 | a3 | r12 | r13 | r23
  deriving DecidableEq, Fintype

open W3 A6

def good3 : W3 → A6 → Bool
  | w1, a1 => true
  | w2, a2 => true
  | w3, a3 => true
  | w1, r12 => true
  | w2, r12 => true
  | w1, r13 => true
  | w3, r13 => true
  | w2, r23 => true
  | w3, r23 => true
  | _, _ => false

def old3 : Finset A6 := {a1, a2, a3}
def repairs3 : Finset A6 := {r12, r13, r23}
def pair12 : Finset W3 := {w1, w2}
def pair13 : Finset W3 := {w1, w3}
def pair23 : Finset W3 := {w2, w3}
def triple3 : Finset W3 := {w1, w2, w3}

/-- Boolean executable version of “some capability is common to all worlds in O”. -/
def commonFSB (Caps : Finset A6) (O : Finset W3) : Bool :=
  Caps.any (fun a => O.all (fun w => good3 w a))

/-- Boolean executable minimal-old-obstruction predicate. -/
def minimalOldObstructionFSB (O : Finset W3) : Bool :=
  (!O.isEmpty) &&
  !(commonFSB old3 O) &&
  ((Finset.univ : Finset W3).powerset.all fun T =>
    if T ⊂ O ∧ T.Nonempty then commonFSB old3 T else true)

/-- T3 — all three old minimal pair obstructions are individually repairable while the unchanged
three-world fiber still has no single common action after all pair repairs are added. -/
theorem minimal_obstructions_insufficient_under_repair :
    minimalOldObstructionFSB pair12 = true ∧
    minimalOldObstructionFSB pair13 = true ∧
    minimalOldObstructionFSB pair23 = true ∧
    commonFSB repairs3 pair12 = true ∧
    commonFSB repairs3 pair13 = true ∧
    commonFSB repairs3 pair23 = true ∧
    commonFSB (old3 ∪ repairs3) triple3 = false := by
  native_decide

end MinimalObstructionCounterexample

section HybridAdvantage

inductive Ob2
  | x | y
  deriving DecidableEq, Fintype

inductive Intervention
  | probeX | probeY | repairX | repairY
  deriving DecidableEq, Fintype

open Ob2 Intervention

def resolves : Intervention → Ob2 → Bool
  | probeX, x => true
  | repairX, x => true
  | probeY, y => true
  | repairY, y => true
  | _, _ => false

def isProbe : Intervention → Bool
  | probeX | probeY => true
  | _ => false

def isRepair : Intervention → Bool
  | repairX | repairY => true
  | _ => false

def CoversAll (S : Finset Intervention) : Prop :=
  ∀ o : Ob2, ∃ i ∈ S, resolves i o = true

def ProbeOnly (S : Finset Intervention) : Prop :=
  ∀ i ∈ S, isProbe i = true

def RepairOnly (S : Finset Intervention) : Prop :=
  ∀ i ∈ S, isRepair i = true

def interventionCost (M : ℝ) : Intervention → ℝ
  | probeX => 1
  | probeY => M
  | repairX => M
  | repairY => 1

def planCost (M : ℝ) (S : Finset Intervention) : ℝ :=
  S.sum (fun i => interventionCost M i)

def mixedPlan : Finset Intervention := {probeX, repairY}

lemma mixedPlan_covers : CoversAll mixedPlan := by
  intro o
  cases o
  · exact ⟨probeX, by simp [mixedPlan], by simp [resolves]⟩
  · exact ⟨repairY, by simp [mixedPlan], by simp [resolves]⟩

lemma mixedPlan_cost (M : ℝ) : planCost M mixedPlan = 2 := by
  simp [planCost, mixedPlan, interventionCost]

lemma probeOnly_cover_eq (S : Finset Intervention) (hp : ProbeOnly S) (hc : CoversAll S) :
    S = {probeX, probeY} := by
  have hx : probeX ∈ S := by
    obtain ⟨i, hiS, hiR⟩ := hc x
    have hiP := hp i hiS
    cases i <;> simp_all [resolves, isProbe]
  have hy : probeY ∈ S := by
    obtain ⟨i, hiS, hiR⟩ := hc y
    have hiP := hp i hiS
    cases i <;> simp_all [resolves, isProbe]
  ext i
  constructor
  · intro hi
    have hiP := hp i hi
    cases i <;> simp_all [isProbe]
  · intro hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hx
    · exact hy

lemma repairOnly_cover_eq (S : Finset Intervention) (hr : RepairOnly S) (hc : CoversAll S) :
    S = {repairX, repairY} := by
  have hx : repairX ∈ S := by
    obtain ⟨i, hiS, hiR⟩ := hc x
    have hiP := hr i hiS
    cases i <;> simp_all [resolves, isRepair]
  have hy : repairY ∈ S := by
    obtain ⟨i, hiS, hiR⟩ := hc y
    have hiP := hr i hiS
    cases i <;> simp_all [resolves, isRepair]
  ext i
  constructor
  · intro hi
    have hiP := hr i hi
    cases i <;> simp_all [isRepair]
  · intro hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hx
    · exact hy

lemma probeOnly_cover_cost (M : ℝ) (S : Finset Intervention)
    (hp : ProbeOnly S) (hc : CoversAll S) :
    planCost M S = M + 1 := by
  rw [probeOnly_cover_eq S hp hc]
  simp [planCost, interventionCost]
  ring

lemma repairOnly_cover_cost (M : ℝ) (S : Finset Intervention)
    (hr : RepairOnly S) (hc : CoversAll S) :
    planCost M S = M + 1 := by
  rw [repairOnly_cover_eq S hr hc]
  simp [planCost, interventionCost]
  ring

/-- T4 — mixed PROBE+REPAIR can beat either pure family by an arbitrarily large factor. -/
theorem unbounded_hybrid_advantage (K : ℕ) :
    ∃ M : ℝ,
      1 ≤ M ∧
      (∀ S : Finset Intervention, ProbeOnly S → CoversAll S → planCost M S = M + 1) ∧
      (∀ S : Finset Intervention, RepairOnly S → CoversAll S → planCost M S = M + 1) ∧
      CoversAll mixedPlan ∧
      planCost M mixedPlan = 2 ∧
      (K : ℝ) * planCost M mixedPlan < M + 1 := by
  refine ⟨2 * (K : ℝ) + 1, ?_, ?_, ?_, mixedPlan_covers, mixedPlan_cost _, ?_⟩
  · have hK : 0 ≤ (K : ℝ) := by positivity
    linarith
  · intro S hp hc
    exact probeOnly_cover_cost _ S hp hc
  · intro S hr hc
    exact repairOnly_cover_cost _ S hr hc
  · rw [mixedPlan_cost]
    norm_num

end HybridAdvantage

end InsacermoProbeRepair
