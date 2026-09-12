from pathlib import Path

p = Path('bayes_adaptive_kernel_v1.lean')
s = p.read_text(encoding='utf-8')
repls = [
    ('def posteriorMass\n', 'noncomputable def posteriorMass\n'),
    ('def bayesUpdate\n', 'noncomputable def bayesUpdate\n'),
    ('def safePosteriorMass\n', 'noncomputable def safePosteriorMass\n'),
    ('def safePosteriorModelMass\n', 'noncomputable def safePosteriorModelMass\n'),
    ('ℝ≥0', 'NNReal'),
    ('have h := (pi_norm_le_iff_of_nonempty (f := V - W) (r := ‖V - W‖)).1 le_rfl x',
     'have h := (pi_norm_le_iff_of_nonempty (V - W)).1 le_rfl x'),
    ('  apply (pi_norm_le_iff_of_nonempty).2\n  intro b',
     '  rw [pi_norm_le_iff_of_nonempty]\n  intro b'),
    ('rw [expectedContinuation, expectedContinuation, Finset.sum_sub_distrib]',
     'rw [expectedContinuation, expectedContinuation, ← Finset.sum_sub_distrib]'),
    ('          abs_sum_le_sum_abs _',
     '          Finset.abs_sum_le_sum_abs _ _'),
]
for old, new in repls:
    if old not in s:
        raise SystemExit(f'expected source fragment not found: {old!r}')
    s = s.replace(old, new)
p.write_text(s, encoding='utf-8')
print('Patched Bayes-adaptive kernel source deterministically.')
