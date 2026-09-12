import Mathlib

namespace InsacermoProbeRepair

open Set
open scoped BigOperators

/-!
INSACERMO Probe–Repair Duality Kernel V1.

Targets:
T1  Obstruction Resolution Cover Theorem.
T2W Fractional probe–repair weak duality (the weak-duality half of the LP duality claim).
T3  Minimal-obstruction insufficiency under variable repair.
T4  Unbounded hybrid PROBE+REPAIR advantage.

The general strong LP equality for T2 is deliberately not asserted here: mathlib v4.32.1 does
not yet expose a ready-made linear-programming strong-duality theorem.  This file kernel-checks
the structural reduction and the universal weak-duality inequality without adding axioms.
-/

section StructuralCore

variable {W A Y Q : Type*}

/-- Worlds that remain indistinguishable from `s` after the current representation `h` and all
selected probes `P`.  Probes are taken Boolean only to keep the formal interface minimal; the
cover theorem uses only equality/inequality of probe outputs. -/
def FinalFiber (h : W → Y) (out : Q → W → Bool) (P : Set Q) (s : W) : Set W :=
  {t | h t = h s ∧ ∀ q, q ∈ P → out q t = out q s}

/-- Safety/actionability after adding capabilities in `C` and selecting probes `P`. -/
def SafeAfter (Good : W → A → Prop) (C : Set A) (h : W → Y)
    (out : Q → W → Bool) (P : Set Q) : Prop :=
  ∀ s, ∃ a, a ∈ C ∧ ∀ t, t ∈ FinalFiber h out P s → Good t a

/-- A common action for all worlds in `O`. -/
def HasCommonAction (Good : W → A → Prop) (C : Set A) (O : Set W) : Prop :=
  ∃ a, a ∈ C ∧ ∀ t, t ∈ O → Good t a

/-- A nonempty subset of one current information fiber with no common old action. -/
def InitialObstruction (Good : W → A → Prop) (C : Set A) (h : W → Y)
    (O : Set W) : Prop :=
  O.Nonempty ∧ (∃ s₀, O ⊆ {t | h t = h s₀}) ∧ ¬ HasCommonAction Good C O

/-- A selected probe resolves `O` by splitting at least two worlds in it. -/
def Separated (out : Q → W → Bool) (P : Set Q) (O : Set W) : Prop :=
  ∃ q, q ∈ P ∧ ∃ s, s ∈ O ∧ ∃ t, t ∈ O ∧ out q s ≠ out q t

/-- A newly available capability resolves `O` by covering all of it with one common action. -/
def CoveredBy (Good : W → A → Prop) (R : Set A) (O : Set W) : Prop :=
  HasCommonAction Good R O

/-- T1 — Obstruction Resolution Cover Theorem.

After choosing probes `P` and adding capabilities `R`, safety is equivalent to the statement that
every subset of a current fiber that lacks an old common action is either split by a chosen probe
or covered by one newly added common action.
-/
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
      rcases hO.1 with ⟨s₀, hs₀O⟩
      rcases hO.2.1 with ⟨b, hb⟩
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
      · exfalso
        apply hO.2.2
        exact ⟨a, haC, hGoodO⟩
      · exact ⟨a, haR, hGoodO⟩
  · intro hresolve s
    let O : Set W := FinalFiber h out P s
    by_cases hOld : HasCommonAction Good C O
    · rcases hOld with ⟨a, haC, haGood⟩
      exact ⟨a, Or.inl haC, by simpa [O] using haGood⟩
    · have hOb : InitialObstruction Good C h O := by
        refine ⟨?_, ?_, hOld⟩
        · exact ⟨s, by simp [O, FinalFiber]⟩
        · refine ⟨s, ?_⟩
          intro t ht
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

/-- T2W — universal weak duality for the fractional obstruction-cover relaxation.
`M o i` is the nonnegative incidence/coverage matrix, `c i` is intervention cost, `x` is a
fractional intervention vector and `y` an obstruction-price vector. -/
theorem fractional_probe_repair_weak_duality
    (M : Obs → Intv → ℝ) (c : Intv → ℝ) (x : Intv → ℝ) (y : Obs → ℝ)
    (hM : ∀ o i, 0 ≤ M o i)
    (hx : ∀ i, 0 ≤ x i)
    (hy : ∀ o, 0 ≤ y o)
    (hPrimal : ∀ o, 1 ≤ ∑ i, M o i * x i)
    (hDual : ∀ i, (∑ o, M o i * y o) ≤ c i) :
    (∑ o, y o) ≤ ∑ i, c i * x i := by
  classical
  have hrow : ∀ o, y o ≤ y o * (∑ i, M o i * x i) := by
    intro o
    have := mul_le_mul_of_nonneg_left (hPrimal o) (hy o)
    simpa using this
  calc
    (∑ o, y o) ≤ ∑ o, y o * (∑ i, M o i * x i) :=
      Finset.sum_le_sum fun o _ => hrow o
    _ = ∑ i, x i * (∑ o, M o i * y o) := by
      simp_rw [mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro o ho
      ring
    _ ≤ ∑ i, x i * c i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hDual i) (hx i)
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

/-- Old singleton actions and new pair-repair actions. -/
def good3 : W3 → A6 → Prop
  | w1, a1 => True
  | w2, a2 => True
  | w3, a3 => True
  | w1, r12 => True
  | w2, r12 => True
  | w1, r13 => True
  | w3, r13 => True
  | w2, r23 => True
  | w3, r23 => True
  | _, _ => False

instance good3Decidable (w : W3) (a : A6) : Decidable (good3 w a) := by
  cases w <;> cases a <;> simp [good3] <;> infer_instance

def old3 : Set A6 := {a | a = a1 ∨ a = a2 ∨ a = a3}
def repairs3 : Set A6 := {a | a = r12 ∨ a = r13 ∨ a = r23}
def h3 : W3 → Unit := fun _ => ()

def pair12 : Set W3 := {w | w = w1 ∨ w = w2}
def pair13 : Set W3 := {w | w = w1 ∨ w = w3}
def pair23 : Set W3 := {w | w = w2 ∨ w = w3}

/-- Minimality relative to the current representation and old capability set. -/
def MinimalInitialObstruction
    (Good : W3 → A6 → Prop) (C : Set A6) (h : W3 → Unit) (O : Set W3) : Prop :=
  InitialObstruction Good C h O ∧
    ∀ T : Set W3, T ⊂ O → T.Nonempty → HasCommonAction Good C T

theorem t3_pair12_minimal : MinimalInitialObstruction good3 old3 h3 pair12 := by
  native_decide

theorem t3_pair13_minimal : MinimalInitialObstruction good3 old3 h3 pair13 := by
  native_decide

theorem t3_pair23_minimal : MinimalInitialObstruction good3 old3 h3 pair23 := by
  native_decide

theorem t3_each_minimal_pair_is_repaired :
    CoveredBy good3 repairs3 pair12 ∧
    CoveredBy good3 repairs3 pair13 ∧
    CoveredBy good3 repairs3 pair23 := by
  native_decide

/-- Yet no single old-or-new action covers all three worlds. -/
theorem t3_triple_still_has_no_common_action :
    ¬ HasCommonAction good3 (old3 ∪ repairs3) (Set.univ : Set W3) := by
  native_decide

/-- T3 — the minimal old obstructions can all be repaired individually while the unchanged
three-world fiber remains unsafe under the enlarged capability set. -/
theorem minimal_obstructions_insufficient_under_repair :
    (MinimalInitialObstruction good3 old3 h3 pair12 ∧
      MinimalInitialObstruction good3 old3 h3 pair13 ∧
      MinimalInitialObstruction good3 old3 h3 pair23) ∧
    (CoveredBy good3 repairs3 pair12 ∧
      CoveredBy good3 repairs3 pair13 ∧
      CoveredBy good3 repairs3 pair23) ∧
    ¬ HasCommonAction good3 (old3 ∪ repairs3) (Set.univ : Set W3) := by
  exact ⟨⟨t3_pair12_minimal, t3_pair13_minimal, t3_pair23_minimal⟩,
    t3_each_minimal_pair_is_repaired, t3_triple_still_has_no_common_action⟩

end MinimalObstructionCounterexample

section HybridAdvantage

inductive Ob2
  | x | y
  deriving DecidableEq, Fintype

inductive Intervention
  | probeX | probeY | repairX | repairY
  deriving DecidableEq, Fintype

open Ob2 Intervention

/-- Incidence pattern: each intervention resolves exactly one of the two independent obstructions. -/
def resolves : Intervention → Ob2 → Prop
  | probeX, x => True
  | repairX, x => True
  | probeY, y => True
  | repairY, y => True
  | _, _ => False

instance resolvesDecidable (i : Intervention) (o : Ob2) : Decidable (resolves i o) := by
  cases i <;> cases o <;> simp [resolves] <;> infer_instance

def isProbe : Intervention → Prop
  | probeX | probeY => True
  | _ => False

instance isProbeDecidable (i : Intervention) : Decidable (isProbe i) := by
  cases i <;> simp [isProbe] <;> infer_instance

def isRepair : Intervention → Prop
  | repairX | repairY => True
  | _ => False

instance isRepairDecidable (i : Intervention) : Decidable (isRepair i) := by
  cases i <;> simp [isRepair] <;> infer_instance

def CoversAll (S : Finset Intervention) : Prop :=
  ∀ o : Ob2, ∃ i ∈ S, resolves i o

def ProbeOnly (S : Finset Intervention) : Prop :=
  ∀ i ∈ S, isProbe i

def RepairOnly (S : Finset Intervention) : Prop :=
  ∀ i ∈ S, isRepair i

/-- `probeX` and `repairY` are cheap; their pure-type counterparts are expensive. -/
def interventionCost (M : ℝ) : Intervention → ℝ
  | probeX => 1
  | probeY => M
  | repairX => M
  | repairY => 1

def planCost (M : ℝ) (S : Finset Intervention) : ℝ :=
  ∑ i in S, interventionCost M i

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

/-- T4 — for every requested factor `K`, there is a two-obstruction instance in which every
pure-PROBE or pure-REPAIR solution costs `M+1`, while a mixed solution costs exactly two and the
pure/mixed cost ratio exceeds `K`. -/
theorem unbounded_hybrid_advantage (K : ℕ) :
    ∃ M : ℝ,
      1 ≤ M ∧
      (∀ S : Finset Intervention, ProbeOnly S → CoversAll S → planCost M S = M + 1) ∧
      (∀ S : Finset Intervention, RepairOnly S → CoversAll S → planCost M S = M + 1) ∧
      CoversAll mixedPlan ∧
      planCost M mixedPlan = 2 ∧
      (K : ℝ) * planCost M mixedPlan < M + 1 := by
  refine ⟨2 * (K : ℝ) + 1, ?_, ?_, ?_, mixedPlan_covers, ?_, ?_⟩
  · positivity
  · intro S hp hc
    exact probeOnly_cover_cost _ S hp hc
  · intro S hr hc
    exact repairOnly_cover_cost _ S hr hc
  · exact mixedPlan_cost _
  · rw [mixedPlan_cost]
    norm_num

end HybridAdvantage

end InsacermoProbeRepair
