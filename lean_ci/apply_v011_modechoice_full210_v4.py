from pathlib import Path
import re

p = Path('v011_modechoice_full210_bridge.lean')
s = p.read_text()

# Give only this large integration harness a bounded larger elaboration budget.
if 'set_option maxHeartbeats 2000000' not in s:
    s = s.replace('set_option maxRecDepth 10000\n', 'set_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n', 1)

# Replace the expensive 210-way simp completeness proof by native evaluation.
pat = re.compile(
    r'(instance : Fintype MC210World where\n  elems := \{.*?\}\n)  complete := by intro x; cases x <;> simp',
    re.S,
)
s, n = pat.subn(r'\1  complete := by intro x; cases x <;> native_decide', s, count=1)
if n != 1:
    raise SystemExit(f'world Fintype patch count={n}')

# Ensure pair audit stays entirely in the executable Bool layer.
pat2 = re.compile(
    r'def mc210PairActionable \(xy : MC210World × MC210World\) : Bool :=\n\s*mc210Available\.any \(fun p =>\s*decide \(mc210Good xy\.1 p ∧ mc210Good xy\.2 p\)\)',
    re.S,
)
s, n2 = pat2.subn(
    'def mc210PairActionable (xy : MC210World × MC210World) : Bool :=\n  mc210Available.any (fun p => mc210Accepts xy.1 p && mc210Accepts xy.2 p)',
    s,
    count=1,
)
if n2 != 1:
    raise SystemExit(f'pair-actionable patch count={n2}')

p.write_text(s)
print('PATCHED full-210 V4 harness; V0.11 engine untouched')
