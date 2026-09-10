from pathlib import Path

p = Path('InsacermoV011StageA.lean')
s = p.read_text()

# Stage A needs fin_cases for the explicit ternary Fin 2 witness.
if 'import Mathlib.Tactic.FinCases\n' not in s:
    s = s.replace('import Mathlib.Data.Nat.Find\n', 'import Mathlib.Data.Nat.Find\nimport Mathlib.Tactic.FinCases\n')

repls = [
    ('theorem ternary_probe_certificate :\n    ProbeCertificate ternarySystem 1 (Set.univ : Set TState) TObs := by',
     'def ternary_probe_certificate :\n    ProbeCertificate ternarySystem 1 (Set.univ : Set TState) TObs := by'),
    ('theorem ternary_repair_certificate :\n    RepairCertificate ternarySystem ternaryRepairedSystem 1\n      (Set.univ : Set TState) := by',
     'def ternary_repair_certificate :\n    RepairCertificate ternarySystem ternaryRepairedSystem 1\n      (Set.univ : Set TState) := by'),
    ('''  have : beta ternarySystem (Set.univ : Set TState) ≤ (1 : WithTop Nat) := by\n    simpa [hEq] using hb\n  exact beta_triple_not_le_one this\n''',
     '''  rw [hEq] at hb\n  exact beta_triple_not_le_one hb\n'''),
]

for old, new in repls:
    if old not in s:
        raise SystemExit('MISSING V0.11 REPLACEMENT: ' + old.splitlines()[0])
    s = s.replace(old, new)

p.write_text(s)
print('PATCHED', p, 'chars=', len(s))
