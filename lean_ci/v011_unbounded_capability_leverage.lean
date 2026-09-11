-- INSACERMO V0.11 — UNBOUNDED CAPABILITY LEVERAGE FAMILY
-- A single added, non-universal capability can collapse the safe information
-- requirement from n distinct state codes to a binary code, for arbitrary n.
namespace Insacermo

/-- Predicate-level representation safety.  For every true state, the whole
    representation fiber containing that state must admit one available plan. -/
def CapRepSafe {S Plan Code : Type*}
    (cap : Plan → Prop) (good : S → Plan → Prop) (h : S → Code) : Prop :=
  ∀ s : S, ∃ π : Plan, cap π ∧ ∀ t : S, h t = h s → good t π

/-- Plans consist of one state-specific action for every state, plus one
    additional bulk capability. -/
abbrev LeveragePlan (n : Nat) := Sum (Fin n) Unit

/-- State-specific actions work only on their indexed state.  The added bulk
    action works on every state except state 0, so it is explicitly NOT
    universal. -/
def leverageGood {n : Nat} (s : Fin n) : LeveragePlan n → Prop
  | Sum.inl j => s = j
  | Sum.inr _ => s.val ≠ 0

/-- Initial capability set: only state-specific actions are available. -/
def leverageBaseCap {n : Nat} : LeveragePlan n → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- Expanded capability set: add exactly the one bulk action. -/
def leverageExpandedCap {n : Nat} : LeveragePlan n → Prop := fun _ => True

/-- The post-expansion binary representation remembers only whether the state
    is the exceptional state 0 or one of all remaining states. -/
def leverageBinaryCode {n : Nat} (s : Fin n) : Nat :=
  if s.val = 0 then 0 else 1

/-- Under the original capabilities, every safe representation must be
    injective: any two worlds sharing a code would have to share one
    state-specific action, which is impossible unless they are the same world. -/
theorem leverage_base_safe_implies_injective
    {n : Nat} {Code : Type*} {h : Fin n → Code}
    (hsafe : CapRepSafe leverageBaseCap leverageGood h) :
    Function.Injective h := by
  intro x y hxy
  rcases hsafe x with ⟨π, hcap, hgood⟩
  cases π with
  | inl j =>
      have hx : x = j := by
        simpa [leverageGood] using hgood x rfl
      have hy : y = j := by
        simpa [leverageGood] using hgood y hxy.symm
      exact hx.trans hy.symm
  | inr u =>
      simp [leverageBaseCap] at hcap

/-- After adding the single bulk capability, the binary exceptional/non-
    exceptional representation is safe for every finite n. -/
theorem leverage_binary_safe_after {n : Nat} :
    CapRepSafe (@leverageExpandedCap n) (@leverageGood n)
      (@leverageBinaryCode n) := by
  intro s
  by_cases hs0 : s.val = 0
  · refine ⟨Sum.inl s, trivial, ?_⟩
    intro t hcode
    change t = s
    by_cases ht0 : t.val = 0
    · apply Fin.ext
      exact ht0.trans hs0.symm
    · have hbad : (1 : Nat) = 0 := by
        simpa [leverageBinaryCode, ht0, hs0] using hcode
      exact False.elim ((by decide : (1 : Nat) ≠ 0) hbad)
  · refine ⟨Sum.inr (), trivial, ?_⟩
    intro t hcode
    change t.val ≠ 0
    intro ht0
    have hbad : (0 : Nat) = 1 := by
      simpa [leverageBinaryCode, ht0, hs0] using hcode
    exact (by decide : (0 : Nat) ≠ 1) hbad

/-- The added bulk action is genuinely non-universal whenever a state 0
    exists: it fails on that state. -/
theorem leverage_bulk_is_not_universal {n : Nat} (hn : 0 < n) :
    ∃ s : Fin n, ¬ leverageGood s (Sum.inr ()) := by
  refine ⟨⟨0, hn⟩, ?_⟩
  simp [leverageGood]

/-- For n ≥ 3, the binary representation is not safe before expansion,
    because at least two distinct nonzero states share code 1 while base-safe
    representations are forced to be injective. -/
theorem leverage_binary_not_safe_before {n : Nat} (hn : 3 ≤ n) :
    ¬ CapRepSafe (@leverageBaseCap n) (@leverageGood n)
      (@leverageBinaryCode n) := by
  intro hsafe
  have hinj : Function.Injective (@leverageBinaryCode n) :=
    leverage_base_safe_implies_injective hsafe
  have h1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 3) hn
  have h2 : 2 < n := lt_of_lt_of_le (by decide : 2 < 3) hn
  let s1 : Fin n := ⟨1, h1⟩
  let s2 : Fin n := ⟨2, h2⟩
  have hcode : leverageBinaryCode s1 = leverageBinaryCode s2 := by
    simp [leverageBinaryCode, s1, s2]
  have heq : s1 = s2 := hinj hcode
  have hval : (1 : Nat) = 2 := by
    exact congrArg Fin.val heq
  exact (by decide : (1 : Nat) ≠ 2) hval

/-- Every output of the post-expansion representation is one of only two
    codes, 0 or 1. -/
theorem leverage_binary_has_only_two_codes {n : Nat} (s : Fin n) :
    leverageBinaryCode s = 0 ∨ leverageBinaryCode s = 1 := by
  by_cases hs0 : s.val = 0
  · left
    simp [leverageBinaryCode, hs0]
  · right
    simp [leverageBinaryCode, hs0]

/-- PARAMETRIC LEVERAGE THEOREM.
    For every n ≥ 3:
      (i) every safe representation before expansion is injective on n worlds;
      (ii) one added non-universal capability makes a binary representation safe;
      (iii) that same binary representation was unsafe before expansion.
    Since n is arbitrary, the compression leverage of one added capability has
    no finite cardinality bound. -/
theorem unbounded_capability_leverage_family (n : Nat) (hn : 3 ≤ n) :
    (∀ (Code : Type*) (h : Fin n → Code),
      CapRepSafe (@leverageBaseCap n) (@leverageGood n) h →
        Function.Injective h) ∧
    CapRepSafe (@leverageExpandedCap n) (@leverageGood n)
      (@leverageBinaryCode n) ∧
    ¬ CapRepSafe (@leverageBaseCap n) (@leverageGood n)
      (@leverageBinaryCode n) ∧
    (∃ s : Fin n, ¬ leverageGood s (Sum.inr ())) := by
  refine ⟨?_, leverage_binary_safe_after,
    leverage_binary_not_safe_before hn, ?_⟩
  · intro Code h hsafe
    exact leverage_base_safe_implies_injective hsafe
  · exact leverage_bulk_is_not_universal (lt_of_lt_of_le (by decide : 0 < 3) hn)

/-- Concrete sanity checks: the same theorem instantiates at small and large n. -/
example :
    CapRepSafe (@leverageExpandedCap 8) (@leverageGood 8)
      (@leverageBinaryCode 8) := leverage_binary_safe_after

example :
    ¬ CapRepSafe (@leverageBaseCap 1024) (@leverageGood 1024)
      (@leverageBinaryCode 1024) := by
  exact leverage_binary_not_safe_before (by decide)

end Insacermo
