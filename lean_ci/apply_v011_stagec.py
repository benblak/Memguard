from pathlib import Path

p = Path('InsacermoV011StageC.lean')
s = p.read_text()

start = s.index('-- ===== OperationalSemantics.lean =====')
end = s.index('-- ===== ExecutableSoundness.lean =====') if '-- ===== ExecutableSoundness.lean =====' in s else len(s)

replacement = r'''-- ===== OperationalSemantics.lean =====

namespace Insacermo

variable {S Plan : Type*}

/-- Operational admissibility relative to the strategies that are *currently
    available*.  The ordered-list representation is computational data; the
    proposition depends only on membership. -/
def FiniteAdmissible
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) (available : List Plan)
    (b : Nat) (B : List S) : Prop :=
  ∃ π : Plan, ExecFeasible sys available b B π

/-- Restricted feasibility always implies the unrestricted semantics on the
    set represented by the ambiguity list. -/
theorem finiteAdmissible_implies_admissible
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) (available : List Plan)
    (b : Nat) (B : List S) :
    FiniteAdmissible sys available b B →
      Admissible sys b {s : S | s ∈ B} := by
  rintro ⟨π, hmem, hcost, hgood⟩
  refine ⟨π, hcost, ?_⟩
  intro s hs
  exact hgood s hs

/-- If the declared ordered capability list contains every strategy, then
    operational and unrestricted admissibility coincide.  This avoids any
    noncomputable enumeration of a finite type while expressing the same
    semantic bridge. -/
theorem finiteAdmissible_all_available_iff_admissible
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) (available : List Plan)
    (hall : ∀ π : Plan, π ∈ available)
    (b : Nat) (B : List S) :
    FiniteAdmissible sys available b B ↔
      Admissible sys b {s : S | s ∈ B} := by
  constructor
  · exact finiteAdmissible_implies_admissible sys available b B
  · rintro ⟨π, hcost, hgood⟩
    refine ⟨π, hall π, hcost, ?_⟩
    intro s hs
    exact hgood s hs

/-- Semantic meaning of each executable label.  REFUSE is explicitly relative
    to the declared candidate search: `searchComplete = true` is a trusted
    declaration that the listed candidates exhaust the allowed intervention
    class.  INCOMPLETE records the same failed finite search without that
    declaration. -/
def OperationalSound
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (input : ExecInput S Plan) [DecidableRel input.sys.good]
    (out : ExecResult Plan) : Prop :=
  match out.label with
  | .act =>
      FiniteAdmissible input.sys input.available input.budget input.ambiguity
  | .preserve =>
      FiniteAdmissible input.sys input.available input.budget input.ambiguity ∧
      ∃ proposed ∈ input.forgets,
        (∀ s : S, s ∈ input.ambiguity → s ∈ proposed) ∧
        ¬ FiniteAdmissible input.sys input.available input.budget proposed
  | .probe =>
      ¬ FiniteAdmissible input.sys input.available input.budget input.ambiguity ∧
      ∃ observe ∈ input.probes,
        ∀ y ∈ observationLabels input.ambiguity observe,
          FiniteAdmissible input.sys input.available input.budget
            (observationFiber input.ambiguity observe y)
  | .repair =>
      ¬ FiniteAdmissible input.sys input.available input.budget input.ambiguity ∧
      ∃ added ∈ input.repairs,
        FiniteAdmissible input.sys (input.available ++ added)
          input.budget input.ambiguity
  | .refuse =>
      ¬ FiniteAdmissible input.sys input.available input.budget input.ambiguity ∧
      input.searchComplete = true ∧
      findProbe? input.sys input.available input.budget input.ambiguity
        input.probes = none ∧
      findRepair? input.sys input.available input.budget input.ambiguity
        input.repairs = none
  | .incomplete =>
      ¬ FiniteAdmissible input.sys input.available input.budget input.ambiguity ∧
      input.searchComplete = false ∧
      findProbe? input.sys input.available input.budget input.ambiguity
        input.probes = none ∧
      findRepair? input.sys input.available input.budget input.ambiguity
        input.repairs = none

end Insacermo

'''

p.write_text(s[:start] + replacement + s[end:])
print('PATCHED', p, 'chars=', len(s[:start] + replacement + s[end:]))
