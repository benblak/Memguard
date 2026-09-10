from pathlib import Path

p = Path('v011_modechoice_full210_bridge.lean')
s = p.read_text()

# Raise elaborator recursion only for this large 210-world test harness.
s = s.replace('namespace Insacermo\n', 'namespace Insacermo\n\nset_option maxRecDepth 10000\n', 1)

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

# Avoid asking typeclass synthesis to unfold the proposition in helper computations.
s = s.replace(
    '(mc210AllWorlds.filter (fun w => decide (mc210Good w p))).length',
    '(mc210AllWorlds.filter (fun w => mc210Accepts w p)).length'
)
s = s.replace(
    'mc210Available.any (fun p =>\n    decide (mc210Good xy.1 p ∧ mc210Good xy.2 p))',
    'mc210Available.any (fun p =>\n    mc210Accepts xy.1 p && mc210Accepts xy.2 p)'
)

p.write_text(s)
print('PATCHED full-210 V3 harness; engine untouched')
