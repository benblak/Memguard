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

old = '''lemma mixedPlan_cost (M : ℝ) : planCost M mixedPlan = 2 := by
  norm_num [planCost, mixedPlan, interventionCost]
'''
new = '''lemma mixedPlan_cost (M : ℝ) : planCost M mixedPlan = 2 := by
  have h1 : probeY ≠ probeX := by decide
  have h2 : probeY ≠ repairY := by decide
  have h3 : repairX ≠ probeX := by decide
  have h4 : repairX ≠ repairY := by decide
  simp [planCost, mixedPlan, h1, h2, h3, h4]
'''
if old not in s:
    raise SystemExit('mixedPlan_cost target not found')
s = s.replace(old, new, 1)

old = '''lemma probeOnly_cover_cost (M : ℝ) (S : Finset Intervention)
    (hp : ProbeOnly S) (hc : CoversAll S) :
    planCost M S = M + 1 := by
  rw [probeOnly_cover_eq S hp hc]
  norm_num [planCost, interventionCost] <;> ring
'''
new = '''lemma probeOnly_cover_cost (M : ℝ) (S : Finset Intervention)
    (hp : ProbeOnly S) (hc : CoversAll S) :
    planCost M S = M + 1 := by
  rw [probeOnly_cover_eq S hp hc]
  have h1 : repairX ≠ probeX := by decide
  have h2 : repairX ≠ probeY := by decide
  have h3 : repairY ≠ probeX := by decide
  have h4 : repairY ≠ probeY := by decide
  simp [planCost, h1, h2, h3, h4]
  ring
'''
if old not in s:
    raise SystemExit('probeOnly_cover_cost target not found')
s = s.replace(old, new, 1)

old = '''lemma repairOnly_cover_cost (M : ℝ) (S : Finset Intervention)
    (hr : RepairOnly S) (hc : CoversAll S) :
    planCost M S = M + 1 := by
  rw [repairOnly_cover_eq S hr hc]
  norm_num [planCost, interventionCost] <;> ring
'''
new = '''lemma repairOnly_cover_cost (M : ℝ) (S : Finset Intervention)
    (hr : RepairOnly S) (hc : CoversAll S) :
    planCost M S = M + 1 := by
  rw [repairOnly_cover_eq S hr hc]
  have h1 : probeX ≠ repairX := by decide
  have h2 : probeX ≠ repairY := by decide
  have h3 : probeY ≠ repairX := by decide
  have h4 : probeY ≠ repairY := by decide
  simp [planCost, h1, h2, h3, h4]
  ring
'''
if old not in s:
    raise SystemExit('repairOnly_cover_cost target not found')
s = s.replace(old, new, 1)

p.write_text(s)
