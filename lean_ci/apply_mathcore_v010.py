from pathlib import Path

p = Path('InsacermoFlat.lean')
s = p.read_text()

repls = [
("""    refine ⟨d z, ?_, ?_⟩
    · have hc := (hd s0).1
      simpa [hs0] using hc
    · intro s hs
      have hg := (hd s).2
      simpa [hs] using hg
""", """    change h s0 = z at hs0
    subst z
    refine ⟨d (h s0), (hd s0).1, ?_⟩
    intro s hs
    change h s = h s0 at hs
    have hg := (hd s).2
    rw [hs] at hg
    exact hg
"""),
("""    refine ⟨s0, ?_⟩
    simp [Function.comp_apply, hs0]
""", """    refine ⟨s0, ?_⟩
    change h s0 = z at hs0
    change g (h s0) = g z
    exact congrArg g hs0
"""),
("""  · intro s hs
    simp only [Set.mem_setOf_eq] at hs ⊢
    simp [Function.comp_apply, hs]
""", """  · intro s hs
    change h s = z at hs
    change g (h s) = g z
    exact congrArg g hs
"""),
("""  have hbtop : (b : WithTop Nat) < ⊤ := by simp
""", """  have hbtop : (b : WithTop Nat) < ⊤ := WithTop.coe_lt_top b
"""),
("""    · refine ⟨π, ?_, hgood⟩
      simpa [candidateCost, hgood] using hcost
    · simp [candidateCost, hgood] at hcost
""", """    · refine ⟨π, ?_, hgood⟩
      unfold candidateCost at hcost
      rw [if_pos hgood] at hcost
      exact WithTop.coe_le_coe.mp hcost
    · unfold candidateCost at hcost
      rw [if_neg hgood] at hcost
      exact False.elim ((not_le_of_gt hbtop) hcost)
"""),
("""    simpa [candidateCost, hgood] using hcost
""", """    unfold candidateCost
    rw [if_pos hgood]
    exact WithTop.coe_le_coe.mpr hcost
"""),
("""  by_cases hB : ∀ s ∈ B, sys.good s π
  · have hA : ∀ s ∈ A, sys.good s π := by
      intro s hs
      exact hB s (hAB hs)
    simp [candidateCost, hA, hB]
  · simp [candidateCost, hB]
""", """  unfold candidateCost
  by_cases hB : ∀ s ∈ B, sys.good s π
  · have hA : ∀ s ∈ A, sys.good s π := by
      intro s hs
      exact hB s (hAB hs)
    rw [if_pos hA, if_pos hB]
  · rw [if_neg hB]
    exact le_top
"""),
("""  simpa [InSublevel] using beta_triple_not_le_one
""", """  change ¬ beta ternarySystem (Set.univ : Set TState) ≤ (1 : WithTop Nat)
  exact beta_triple_not_le_one
"""),
("""    change h s = z₁
    apply Fin.ext
    have hc : Fin.castLE hkk (h s) = Fin.castLE hkk (h s₀) := by
      calc
        Fin.castLE hkk (h s) = z₂ := hs
        _ = Fin.castLE hkk (h s₀) := hs₀.symm
    exact congrArg Fin.val hc
""", """    change h s = z₁
    apply Fin.ext
    change (h s).val = (h s₀).val
    have hc : Fin.castLE hkk (h s) = Fin.castLE hkk (h s₀) := by
      calc
        Fin.castLE hkk (h s) = z₂ := hs
        _ = Fin.castLE hkk (h s₀) := hs₀.symm
    have hvals : (Fin.castLE hkk (h s)).val = (Fin.castLE hkk (h s₀)).val :=
      congrArg (fun x : Fin k₂ => x.val) hc
    exact hvals
"""),
("""    intro t ht
    simpa using ht
""", """    intro t ht
    have hts : t = s := by simpa using ht
    exact congrArg h hts
"""),
]

for old, new in repls:
    if old not in s:
        print('MISSING REPLACEMENT BLOCK:', old.splitlines()[0][:80])
    s = s.replace(old, new)

s = s.replace('import Mathlib.Tactic.FinCases\n', '')
p.write_text(s)
print('WROTE', p, 'chars=', len(s))
