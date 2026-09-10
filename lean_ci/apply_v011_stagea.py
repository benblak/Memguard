from pathlib import Path

p = Path('InsacermoV011StageA.lean')
s = p.read_text()

repls = [
    ('theorem ternary_probe_certificate :\n    ProbeCertificate ternarySystem 1 (Set.univ : Set TState) TObs := by',
     'def ternary_probe_certificate :\n    ProbeCertificate ternarySystem 1 (Set.univ : Set TState) TObs := by'),
    ('theorem ternary_repair_certificate :\n    RepairCertificate ternarySystem ternaryRepairedSystem 1\n      (Set.univ : Set TState) := by',
     'def ternary_repair_certificate :\n    RepairCertificate ternarySystem ternaryRepairedSystem 1\n      (Set.univ : Set TState) := by'),
    ('''theorem ternaryFine_betaSafe :
    BetaSafe ternarySystem 1 ternaryFine := by
  intro z hz
  fin_cases z
  · have hsub : {s : TState | ternaryFine s = 0} ⊆ AB := by
      intro s hs
      cases s with
      | a => simp [AB]
      | b => simp [AB]
      | c => simp [ternaryFine] at hs
    exact le_trans (beta_mono_ambiguity ternarySystem hsub) beta_AB_le_one
  · have hc : beta ternarySystem ({c} : Set TState) ≤ (1 : WithTop Nat) := by
      apply (beta_le_iff_admissible ternarySystem ({c} : Set TState) 1).2
      refine ⟨ac, by decide, ?_⟩
      intro s hs
      have hsc : s = c := by simpa using hs
      subst s
      trivial
    have hsub : {s : TState | ternaryFine s = 1} ⊆ ({c} : Set TState) := by
      intro s hs
      cases s with
      | a => simp [ternaryFine] at hs
      | b => simp [ternaryFine] at hs
      | c => simp
    exact le_trans (beta_mono_ambiguity ternarySystem hsub) hc
''',
     '''theorem ternaryFine_betaSafe :
    BetaSafe ternarySystem 1 ternaryFine := by
  intro z hz
  have h0 : beta ternarySystem {s : TState | ternaryFine s = 0} ≤ (1 : WithTop Nat) := by
    have hsub : {s : TState | ternaryFine s = 0} ⊆ AB := by
      intro s hs
      cases s with
      | a => simp [AB]
      | b => simp [AB]
      | c => simp [ternaryFine] at hs
    exact le_trans (beta_mono_ambiguity ternarySystem hsub) beta_AB_le_one
  have h1 : beta ternarySystem {s : TState | ternaryFine s = 1} ≤ (1 : WithTop Nat) := by
    have hc : beta ternarySystem ({c} : Set TState) ≤ (1 : WithTop Nat) := by
      apply (beta_le_iff_admissible ternarySystem ({c} : Set TState) 1).2
      refine ⟨ac, by decide, ?_⟩
      intro s hs
      have hsc : s = c := by simpa using hs
      subst s
      trivial
    have hsub : {s : TState | ternaryFine s = 1} ⊆ ({c} : Set TState) := by
      intro s hs
      cases s with
      | a => simp [ternaryFine] at hs
      | b => simp [ternaryFine] at hs
      | c => simp
    exact le_trans (beta_mono_ambiguity ternarySystem hsub) hc
  rcases hz with ⟨s₀, hs₀⟩
  change ternaryFine s₀ = z at hs₀
  cases s₀ with
  | a =>
      have hz0 : z = 0 := by simpa [ternaryFine] using hs₀.symm
      subst z
      exact h0
  | b =>
      have hz0 : z = 0 := by simpa [ternaryFine] using hs₀.symm
      subst z
      exact h0
  | c =>
      have hz1 : z = 1 := by simpa [ternaryFine] using hs₀.symm
      subst z
      exact h1
'''),
    ('''  have : beta ternarySystem (Set.univ : Set TState) ≤ (1 : WithTop Nat) := by
    simpa [hEq] using hb
  exact beta_triple_not_le_one this
''',
     '''  rw [hEq] at hb
  exact beta_triple_not_le_one hb
'''),
]

for old, new in repls:
    if old not in s:
        raise SystemExit('MISSING V0.11 REPLACEMENT: ' + old.splitlines()[0])
    s = s.replace(old, new)

p.write_text(s)
print('PATCHED', p, 'chars=', len(s))
