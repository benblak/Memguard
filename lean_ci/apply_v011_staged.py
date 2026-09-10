from pathlib import Path

p = Path('InsacermoV011StageD.lean')
s = p.read_text()
start = s.index('-- ===== ExecutableSoundness.lean =====')

replacement = r'''-- ===== ExecutableSoundness.lean =====

namespace Insacermo

variable {S Plan : Type*}

/-- Failure of the recursive ACT search means that no strategy appearing in the
    searched list is feasible. -/
theorem findFeasibleAux_none_iff
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) [DecidableRel sys.good]
    (available : List Plan) (b : Nat) (B : List S)
    (L : List Plan) :
    findFeasibleAux sys available b B L = none ↔
      ∀ π ∈ L, ¬ ExecFeasible sys available b B π := by
  induction L with
  | nil =>
      simp [findFeasibleAux]
  | cons a rest ih =>
      by_cases ha : ExecFeasible sys available b B a
      · simp [findFeasibleAux, ha]
      · simp [findFeasibleAux, ha, ih]

/-- The finite ACT search is complete for the explicitly available ordered
    capability list. -/
theorem findAct_none_iff_not_finiteAdmissible
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) [DecidableRel sys.good]
    (available : List Plan) (b : Nat) (B : List S) :
    findAct? sys available b B = none ↔
      ¬ FiniteAdmissible sys available b B := by
  unfold findAct?
  rw [findFeasibleAux_none_iff]
  constructor
  · intro hnone hAdm
    rcases hAdm with ⟨π, hπ⟩
    exact hnone π hπ.1 hπ
  · intro hnot π hmem hfeas
    exact hnot ⟨π, hfeas⟩

/-- A successful ACT search yields operational admissibility. -/
theorem findAct_some_finiteAdmissible
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) [DecidableRel sys.good]
    (available : List Plan) (b : Nat) (B : List S)
    {π : Plan} (h : findAct? sys available b B = some π) :
    FiniteAdmissible sys available b B := by
  exact ⟨π, findAct_sound sys available b B h⟩

/-- Boolean probe checking is sound: every listed observation fiber has a
    genuine finite ACT witness. -/
theorem probeLabelsResolve_sound
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) [DecidableRel sys.good]
    (available : List Plan) (b : Nat) (B : List S)
    (observe : S → Nat) (L : List Nat)
    (h : probeLabelsResolve sys available b B observe L = true) :
    ∀ y ∈ L,
      FiniteAdmissible sys available b (observationFiber B observe y) := by
  induction L with
  | nil =>
      simp
  | cons y rest ih =>
      cases hact : findAct? sys available b (observationFiber B observe y) with
      | none =>
          simp [probeLabelsResolve, hact] at h
      | some π =>
          have hy : FiniteAdmissible sys available b
              (observationFiber B observe y) :=
            findAct_some_finiteAdmissible sys available b
              (observationFiber B observe y) hact
          have hrest : probeLabelsResolve sys available b B observe rest = true := by
            simpa [probeLabelsResolve, hact] using h
          have iht := ih hrest
          intro y' hy'
          simp only [List.mem_cons] at hy'
          rcases hy' with rfl | hyrest
          · exact hy
          · exact iht y' hyrest

/-- A successful executable probe resolves every observation label actually
    produced on the current ambiguity list. -/
theorem probeResolves_sound
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) [DecidableRel sys.good]
    (available : List Plan) (b : Nat) (B : List S)
    (observe : S → Nat)
    (h : probeResolves sys available b B observe = true) :
    ∀ y ∈ observationLabels B observe,
      FiniteAdmissible sys available b (observationFiber B observe y) := by
  unfold probeResolves at h
  intro y hy
  exact probeLabelsResolve_sound sys available b B observe
    (observationLabels B observe) h y hy

/-- Any successful indexed-list search identifies a real listed candidate whose
    executable predicate is true. -/
theorem firstIndexWhere_sound_mem
    {α : Type*} (p : α → Bool) (i : Nat) (L : List α) {j : Nat}
    (h : firstIndexWhere p i L = some j) :
    ∃ x ∈ L, p x = true := by
  induction L generalizing i with
  | nil =>
      simp [firstIndexWhere] at h
  | cons a rest ih =>
      cases hpa : p a with
      | false =>
          simp [firstIndexWhere, hpa] at h
          rcases ih (i := i + 1) h with ⟨x, hx, hpx⟩
          exact ⟨x, by simp [hx], hpx⟩
      | true =>
          exact ⟨a, by simp, hpa⟩

/-- A returned PROBE index corresponds to an actually resolving candidate. -/
theorem findProbe_sound_exists
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) [DecidableRel sys.good]
    (available : List Plan) (b : Nat) (B : List S)
    (probes : List (S → Nat)) {i : Nat}
    (h : findProbe? sys available b B probes = some i) :
    ∃ observe ∈ probes,
      ∀ y ∈ observationLabels B observe,
        FiniteAdmissible sys available b (observationFiber B observe y) := by
  unfold findProbe? at h
  rcases firstIndexWhere_sound_mem
      (fun q => probeResolves sys available b B q) 0 probes h with
    ⟨observe, hmem, htrue⟩
  refine ⟨observe, hmem, ?_⟩
  exact probeResolves_sound sys available b B observe htrue

/-- A returned REPAIR candidate really makes the unchanged ambiguity list
    feasible after adding the corresponding ordered capability list. -/
theorem findRepairAux_sound_exists
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) [DecidableRel sys.good]
    (available : List Plan) (b : Nat) (B : List S)
    (i0 : Nat) (repairs : List (List Plan)) {out : Nat × Plan}
    (h : findRepairAux sys available b B i0 repairs = some out) :
    ∃ added ∈ repairs,
      FiniteAdmissible sys (available ++ added) b B := by
  induction repairs generalizing i0 with
  | nil =>
      simp [findRepairAux] at h
  | cons added rest ih =>
      cases hact : findAct? sys (available ++ added) b B with
      | some π =>
          refine ⟨added, by simp, ?_⟩
          exact findAct_some_finiteAdmissible sys (available ++ added) b B hact
      | none =>
          simp [findRepairAux, hact] at h
          rcases ih (i0 := i0 + 1) h with ⟨added', hmem, hAdm⟩
          exact ⟨added', by simp [hmem], hAdm⟩

/-- Soundness of the top-level REPAIR search. -/
theorem findRepair_sound_exists
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) [DecidableRel sys.good]
    (available : List Plan) (b : Nat) (B : List S)
    (repairs : List (List Plan)) {out : Nat × Plan}
    (h : findRepair? sys available b B repairs = some out) :
    ∃ added ∈ repairs,
      FiniteAdmissible sys (available ++ added) b B := by
  exact findRepairAux_sound_exists sys available b B 0 repairs h

/-- A positive PRESERVE predicate is a genuine safe-to-unsafe ambiguity
    enlargement relative to the current available capabilities. -/
theorem preserveThreat_sound
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) [DecidableRel sys.good]
    (available : List Plan) (b : Nat) (B proposed : List S)
    (h : preserveThreat sys available b B proposed = true) :
    (∀ s : S, s ∈ B → s ∈ proposed) ∧
      ¬ FiniteAdmissible sys available b proposed := by
  by_cases hsub : ∀ s : S, s ∈ B → s ∈ proposed
  · cases hact : findAct? sys available b proposed with
    | some π =>
        simp [preserveThreat, hsub, hact] at h
    | none =>
        refine ⟨hsub, ?_⟩
        exact (findAct_none_iff_not_finiteAdmissible
          sys available b proposed).1 hact
  · simp [preserveThreat, hsub] at h

/-- A returned PRESERVE index corresponds to a listed unsafe coarsening. -/
theorem findPreserve_sound_exists
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) [DecidableRel sys.good]
    (available : List Plan) (b : Nat) (B : List S)
    (forgets : List (List S)) {i : Nat}
    (h : findPreserve? sys available b B forgets = some i) :
    ∃ proposed ∈ forgets,
      (∀ s : S, s ∈ B → s ∈ proposed) ∧
      ¬ FiniteAdmissible sys available b proposed := by
  unfold findPreserve? at h
  rcases firstIndexWhere_sound_mem
      (fun proposed => preserveThreat sys available b B proposed)
      0 forgets h with ⟨proposed, hmem, htrue⟩
  rcases preserveThreat_sound sys available b B proposed htrue with
    ⟨hsub, hbad⟩
  exact ⟨proposed, hmem, hsub, hbad⟩

/-- Main executable soundness theorem: every label produced by the executable
    compiler has its declared operational semantics. REFUSE remains relative to
    the trusted `searchComplete` declaration; INCOMPLETE is used otherwise. -/
theorem compile_operational_sound
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (input : ExecInput S Plan) [DecidableRel input.sys.good] :
    OperationalSound input (compile input) := by
  unfold compile
  cases hact : findAct? input.sys input.available input.budget input.ambiguity with
  | some π =>
      have hcurrent : FiniteAdmissible input.sys input.available
          input.budget input.ambiguity :=
        findAct_some_finiteAdmissible input.sys input.available
          input.budget input.ambiguity hact
      cases hpres : findPreserve? input.sys input.available input.budget
          input.ambiguity input.forgets with
      | some i =>
          rcases findPreserve_sound_exists input.sys input.available
              input.budget input.ambiguity input.forgets hpres with
            ⟨proposed, hmem, hsub, hbad⟩
          simp [OperationalSound, hact, hpres]
          exact ⟨hcurrent, proposed, hmem, hsub, hbad⟩
      | none =>
          simp [OperationalSound, hact, hpres]
          exact hcurrent
  | none =>
      have hcurrent : ¬ FiniteAdmissible input.sys input.available
          input.budget input.ambiguity :=
        (findAct_none_iff_not_finiteAdmissible input.sys input.available
          input.budget input.ambiguity).1 hact
      cases hprobe : findProbe? input.sys input.available input.budget
          input.ambiguity input.probes with
      | some i =>
          rcases findProbe_sound_exists input.sys input.available input.budget
              input.ambiguity input.probes hprobe with
            ⟨observe, hmem, hfibers⟩
          simp [OperationalSound, hact, hprobe]
          exact ⟨hcurrent, observe, hmem, hfibers⟩
      | none =>
          cases hrepair : findRepair? input.sys input.available input.budget
              input.ambiguity input.repairs with
          | some out =>
              rcases findRepair_sound_exists input.sys input.available input.budget
                  input.ambiguity input.repairs hrepair with
                ⟨added, hmem, hafter⟩
              simp [OperationalSound, hact, hprobe, hrepair]
              exact ⟨hcurrent, added, hmem, hafter⟩
          | none =>
              cases hcomplete : input.searchComplete with
              | false =>
                  simp [OperationalSound, hact, hprobe, hrepair, hcomplete]
                  exact ⟨hcurrent, hcomplete, hprobe, hrepair⟩
              | true =>
                  simp [OperationalSound, hact, hprobe, hrepair, hcomplete]
                  exact ⟨hcurrent, hcomplete, hprobe, hrepair⟩

end Insacermo
'''

p.write_text(s[:start] + replacement)
print('PATCHED', p, 'chars=', len(s[:start] + replacement))
