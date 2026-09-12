from pathlib import Path

p = Path('ProbeRepairDualityKernelV1.lean')
s = p.read_text()
old = '''def planCost (M : ℝ) (S : Finset Intervention) : ℝ :=
  S.sum (fun i => interventionCost M i)
'''
new = '''def planCost (M : ℝ) (S : Finset Intervention) : ℝ :=
  (if probeX ∈ S then 1 else 0) +
  (if probeY ∈ S then M else 0) +
  (if repairX ∈ S then M else 0) +
  (if repairY ∈ S then 1 else 0)
'''
if old not in s:
    raise SystemExit('planCost target not found')
s = s.replace(old, new, 1)
p.write_text(s)
