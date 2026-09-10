from pathlib import Path
import re

p = Path('v011_modechoice_full210_bridge.lean')
s = p.read_text()

# Use Lean's generated finite enumeration instead of a 210-way simp completeness proof.
s = re.sub(
    r'inductive MC210World where\n(.*?)\n  deriving DecidableEq, Repr\n\ninstance : Fintype MC210World where\n  elems := \{.*?\}\n  complete := by intro x; cases x <;> simp\n\ninductive MC210Plan where',
    lambda m: 'inductive MC210World where\n' + m.group(1) + '\n  deriving DecidableEq, Repr, Fintype\n\ninductive MC210Plan where',
    s,
    flags=re.S,
)
s = re.sub(
    r'(inductive MC210Plan where\n.*?\n)  deriving DecidableEq, Repr\n\ninstance : Fintype MC210Plan where\n  elems := \{.*?\}\n  complete := by intro x; cases x <;> simp\n\n',
    r'\1  deriving DecidableEq, Repr, Fintype\n\n',
    s,
    flags=re.S,
)

old = '''def mc210Good : MC210World → MC210Plan → Prop
  | w, .mode1 => mc210Profile w / 8 % 2 = 1
  | w, .mode2 => mc210Profile w / 4 % 2 = 1
  | w, .mode3 => mc210Profile w / 2 % 2 = 1
  | w, .mode4 => mc210Profile w % 2 = 1
  | _, .r30_180 => True
  | _, .r56_137 => True
  | _, .r58_90 => True
  | _, .r76_85 => True
  | _, .r92_80 => True
'''
new = '''def mc210Accepts : MC210World → MC210Plan → Bool
  | w, .mode1 => mc210Profile w / 8 % 2 == 1
  | w, .mode2 => mc210Profile w / 4 % 2 == 1
  | w, .mode3 => mc210Profile w / 2 % 2 == 1
  | w, .mode4 => mc210Profile w % 2 == 1
  | _, .r30_180 => true
  | _, .r56_137 => true
  | _, .r58_90 => true
  | _, .r76_85 => true
  | _, .r92_80 => true

def mc210Good (w : MC210World) (p : MC210Plan) : Prop :=
  mc210Accepts w p = true
'''
if old not in s:
    raise SystemExit('mc210Good block not found')
s = s.replace(old, new)

old_inst = '''instance mc210GoodDecidable : DecidableRel mc210System.good := by
  intro s p
  change Decidable (mc210Good s p)
  infer_instance
'''
new_inst = '''instance mc210GoodDecidable : DecidableRel mc210System.good := by
  intro s p
  change Decidable (mc210Accepts s p = true)
  infer_instance
'''
if old_inst not in s:
    raise SystemExit('decidability block not found')
s = s.replace(old_inst, new_inst)

# This affects only elaboration/evaluation of this 210-world test file.
s = s.replace('namespace Insacermo\n', 'namespace Insacermo\n\nset_option maxRecDepth 10000\n', 1)

p.write_text(s)
print('PATCHED full-210 harness only')
