-- INSACERMO V0.11 — CAPABILITY-INDUCED INFORMATION DEBT
-- A temporary capability can make aggressive compression safe; after that
-- capability is removed, no deterministic post-processing of the compressed
-- memory can recover a representation that is safe under the old capability.
namespace Insacermo

/-- Before capability expansion, retaining the exact state is safe. -/
theorem leverage_identity_safe_before {n : Nat} :
    CapRepSafe (@leverageBaseCap n) (@leverageGood n) (fun s : Fin n => s) := by
  intro s
  refine ⟨Sum.inl s, trivial, ?_⟩
  intro t hts
  simpa [leverageGood] using hts

/-- Once the binary compression has happened, any deterministic recoding of
    that stored binary code still identifies states 1 and 2.  Therefore, for
    n ≥ 3, no such recoding can be safe after the bulk capability is removed,
    because base-safe representations must be injective. -/
theorem no_deterministic_recovery_after_capability_loss
    {n : Nat} (hn : 3 ≤ n) (Code : Type*) (g : Nat → Code) :
    ¬ CapRepSafe (@leverageBaseCap n) (@leverageGood n)
      (fun s : Fin n => g (leverageBinaryCode s)) := by
  intro hsafe
  have hinj : Function.Injective (fun s : Fin n => g (leverageBinaryCode s)) :=
    leverage_base_safe_implies_injective hsafe
  have h1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 3) hn
  have h2 : 2 < n := lt_of_lt_of_le (by decide : 2 < 3) hn
  let s1 : Fin n := ⟨1, h1⟩
  let s2 : Fin n := ⟨2, h2⟩
  have hbin : leverageBinaryCode s1 = leverageBinaryCode s2 := by
    simp [leverageBinaryCode, s1, s2]
  have hcode : g (leverageBinaryCode s1) = g (leverageBinaryCode s2) := by
    exact congrArg g hbin
  have heq : s1 = s2 := hinj hcode
  have hval : (1 : Nat) = 2 := congrArg Fin.val heq
  exact (by decide : (1 : Nat) ≠ 2) hval

/-- CAPABILITY-INDUCED INFORMATION DEBT THEOREM.
    For every n ≥ 3, there is a reversible capability cycle C -> C' -> C but
    an information path that is not recoverable by deterministic processing:

      exact identity memory --safe under C
             |
             | add one non-universal capability
             v
      binary memory         --safe under C'
             |
             | remove that capability
             v
      no deterministic recoding of the binary memory is safe under C.

    Thus capability can be reversible while the forgetting it authorized is
    operationally irreversible without acquiring new information. -/
theorem capability_induced_information_debt
    (n : Nat) (hn : 3 ≤ n) :
    CapRepSafe (@leverageBaseCap n) (@leverageGood n) (fun s : Fin n => s) ∧
    CapRepSafe (@leverageExpandedCap n) (@leverageGood n)
      (@leverageBinaryCode n) ∧
    (∀ (Code : Type*) (g : Nat → Code),
      ¬ CapRepSafe (@leverageBaseCap n) (@leverageGood n)
        (fun s : Fin n => g (leverageBinaryCode s))) ∧
    (∃ s : Fin n, ¬ leverageGood s (Sum.inr ())) := by
  refine ⟨leverage_identity_safe_before, leverage_binary_safe_after, ?_, ?_⟩
  · intro Code g
    exact no_deterministic_recovery_after_capability_loss hn Code g
  · exact leverage_bulk_is_not_universal
      (lt_of_lt_of_le (by decide : 0 < 3) hn)

/-- Concrete illustration at 1024 worlds: after safe binary compression under
    the expanded capability, removing that capability leaves no deterministic
    recoding of the stored binary memory that is safe for the base system. -/
example (Code : Type*) (g : Nat → Code) :
    ¬ CapRepSafe (@leverageBaseCap 1024) (@leverageGood 1024)
      (fun s : Fin 1024 => g (leverageBinaryCode s)) := by
  exact no_deterministic_recovery_after_capability_loss (by decide) Code g

end Insacermo
