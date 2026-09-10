from pathlib import Path

p = Path('InsacermoV011StageB.lean')
s = p.read_text()

start = s.index('-- ===== ExecutableCompiler.lean =====')
end = s.index('-- ===== OperationalSemantics.lean =====') if '-- ===== OperationalSemantics.lean =====' in s else len(s)
prefix, body, suffix = s[:start], s[start:end], s[end:]

repls = [
    ('  ambiguity : Finset S\n  available : Finset Plan\n  budget : Nat\n  probes : List (S → Nat) := []\n  repairs : List (Finset Plan) := []\n  forgets : List (Finset S) := []\n',
     '  /-- Ordered finite ambiguity list. Order is computational data only;\n      semantic feasibility remains permutation-invariant. -/\n  ambiguity : List S\n  /-- Ordered capability list. Order determines the first returned witness,\n      making ACT search genuinely executable rather than choice-based. -/\n  available : List Plan\n  budget : Nat\n  probes : List (S → Nat) := []\n  repairs : List (List Plan) := []\n  forgets : List (List S) := []\n'),
    ('    (sys : ContractSystem S Plan) (available : Finset Plan)\n    (b : Nat) (B : Finset S) (π : Plan) : Prop :=\n',
     '    (sys : ContractSystem S Plan) (available : List Plan)\n    (b : Nat) (B : List S) (π : Plan) : Prop :=\n'),
    ('  π ∈ available ∧ sys.cost π ≤ b ∧ ∀ s : S, s ∈ B → sys.good s π\n\n/-- Search a finite list',
     '  π ∈ available ∧ sys.cost π ≤ b ∧ ∀ s : S, s ∈ B → sys.good s π\n\n/-- Decidability required by the executable search. -/\ninstance execFeasibleDecidable\n    [Fintype S] [DecidableEq S] [DecidableEq Plan]\n    (sys : ContractSystem S Plan) [DecidableRel sys.good]\n    (available : List Plan) (b : Nat) (B : List S) (π : Plan) :\n    Decidable (ExecFeasible sys available b B π) := by\n  unfold ExecFeasible\n  infer_instance\n\n/-- Search a finite list'),
    ('    (available : Finset Plan) (b : Nat) (B : Finset S) :\n    List Plan → Option Plan\n',
     '    (available : List Plan) (b : Nat) (B : List S) :\n    List Plan → Option Plan\n'),
    ('    (available : Finset Plan) (b : Nat) (B : Finset S) : Option Plan :=\n  findFeasibleAux sys available b B available.toList\n',
     '    (available : List Plan) (b : Nat) (B : List S) : Option Plan :=\n  findFeasibleAux sys available b B available\n'),
    ('    (available : Finset Plan) (b : Nat) (B : Finset S)\n    {L : List Plan} {π : Plan}\n',
     '    (available : List Plan) (b : Nat) (B : List S)\n    {L : List Plan} {π : Plan}\n'),
    ('    (available : Finset Plan) (b : Nat) (B : Finset S)\n    {π : Plan} (h : findAct?',
     '    (available : List Plan) (b : Nat) (B : List S)\n    {π : Plan} (h : findAct?'),
    ('def observationFiber\n    [DecidableEq S]\n    (B : Finset S) (observe : S → Nat) (y : Nat) : Finset S :=\n  B.filter (fun s => observe s = y)\n',
     'def observationFiber\n    [DecidableEq S]\n    (B : List S) (observe : S → Nat) (y : Nat) : List S :=\n  B.filter (fun s => observe s = y)\n'),
    ('def observationLabels\n    [DecidableEq S]\n    (B : Finset S) (observe : S → Nat) : Finset Nat :=\n  B.image observe\n',
     'def observationLabels\n    [DecidableEq S]\n    (B : List S) (observe : S → Nat) : List Nat :=\n  (B.map observe).eraseDups\n'),
    ('    (available : Finset Plan) (b : Nat) (B : Finset S)\n    (observe : S → Nat) : List Nat → Bool\n',
     '    (available : List Plan) (b : Nat) (B : List S)\n    (observe : S → Nat) : List Nat → Bool\n'),
    ('    (available : Finset Plan) (b : Nat) (B : Finset S)\n    (observe : S → Nat) : Bool :=\n  probeLabelsResolve sys available b B observe\n    (observationLabels B observe).toList\n',
     '    (available : List Plan) (b : Nat) (B : List S)\n    (observe : S → Nat) : Bool :=\n  probeLabelsResolve sys available b B observe\n    (observationLabels B observe)\n'),
    ('    (available : Finset Plan) (b : Nat) (B : Finset S)\n    (probes : List (S → Nat)) : Option Nat :=\n',
     '    (available : List Plan) (b : Nat) (B : List S)\n    (probes : List (S → Nat)) : Option Nat :=\n'),
    ('    (available : Finset Plan) (b : Nat) (B : Finset S) :\n    Nat → List (Finset Plan) → Option (Nat × Plan)\n',
     '    (available : List Plan) (b : Nat) (B : List S) :\n    Nat → List (List Plan) → Option (Nat × Plan)\n'),
    ('      match findAct? sys (available ∪ added) b B with\n',
     '      match findAct? sys (available ++ added) b B with\n'),
    ('    (available : Finset Plan) (b : Nat) (B : Finset S)\n    (repairs : List (Finset Plan)) : Option (Nat × Plan) :=\n',
     '    (available : List Plan) (b : Nat) (B : List S)\n    (repairs : List (List Plan)) : Option (Nat × Plan) :=\n'),
    ('    (available : Finset Plan) (b : Nat) (B proposed : Finset S) : Bool :=\n  decide (B ⊆ proposed) &&\n',
     '    (available : List Plan) (b : Nat) (B proposed : List S) : Bool :=\n  decide (∀ s : S, s ∈ B → s ∈ proposed) &&\n'),
    ('    (available : Finset Plan) (b : Nat) (B : Finset S)\n    (forgets : List (Finset S)) : Option Nat :=\n',
     '    (available : List Plan) (b : Nat) (B : List S)\n    (forgets : List (List S)) : Option Nat :=\n'),
    ('instance executableTernaryGoodDecidable :\n    DecidableRel executableTernarySystem.good := by\n  intro s π\n  cases s <;> cases π <;> simp [executableTernarySystem, eGood]\n',
     'instance executableTernaryGoodDecidable :\n    DecidableRel executableTernarySystem.good := by\n  intro s π\n  change Decidable (eGood s π)\n  cases s <;> cases π <;> exact inferInstance\n'),
    ('def ternaryWorlds : Finset TState := {.a, .b, .c}\n',
     'def ternaryWorlds : List TState := [.a, .b, .c]\n'),
    ('def ternaryAvailable : Finset EPlan := {.ab, .ac, .bc}\n',
     'def ternaryAvailable : List EPlan := [.ab, .ac, .bc]\n'),
    ('def execTernaryRepair : Finset EPlan := {.universalOne}\n',
     'def execTernaryRepair : List EPlan := [.universalOne]\n'),
    ('def ternaryAB : Finset TState := {.a, .b}\n',
     'def ternaryAB : List TState := [.a, .b]\n'),
]

for old, new in repls:
    if old not in body:
        raise SystemExit('MISSING STAGE B REPLACEMENT: ' + old.splitlines()[0])
    body = body.replace(old, new)

p.write_text(prefix + body + suffix)
print('PATCHED', p, 'chars=', len(prefix + body + suffix))
