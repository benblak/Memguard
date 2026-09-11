-- INSACERMO V0.11 — CAPABILITY / INFORMATION MONOTONICITY LAW
-- General law: enlarging the available capability set cannot make a previously
-- safe representation unsafe. A strict witness shows that the inclusion can be
-- proper: more capability can make the same coarse representation safe.
namespace Insacermo

variable {S Plan : Type*}

/-- A representation is operationally safe on ambiguity list B when every
    actually occurring observation fiber is actionable with the currently
    available capabilities. -/
def OperationalRepSafe
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) (available : List Plan)
    (b : Nat) (B : List S) (h : S → Nat) : Prop :=
  ∀ y ∈ observationLabels B h,
    FiniteAdmissible sys available b (observationFiber B h y)

/-- Capability monotonicity of finite admissibility: adding available actions
    cannot destroy an already valid common action. -/
theorem finiteAdmissible_mono_capability
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan)
    (available expanded : List Plan)
    (hsub : ∀ π : Plan, π ∈ available → π ∈ expanded)
    (b : Nat) (B : List S) :
    FiniteAdmissible sys available b B →
      FiniteAdmissible sys expanded b B := by
  rintro ⟨π, hmem, hcost, hgood⟩
  exact ⟨π, hsub π hmem, hcost, hgood⟩

/-- CAPABILITY-INFORMATION LAW.
    For a fixed contract, budget, ambiguity set and representation h,
    capability expansion preserves representation safety. -/
theorem operationalRepSafe_mono_capability
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan)
    (available expanded : List Plan)
    (hsub : ∀ π : Plan, π ∈ available → π ∈ expanded)
    (b : Nat) (B : List S) (h : S → Nat) :
    OperationalRepSafe sys available b B h →
      OperationalRepSafe sys expanded b B h := by
  intro hsafe y hy
  exact finiteAdmissible_mono_capability
    sys available expanded hsub b (observationFiber B h y) (hsafe y hy)

/-- The safe-representation family induced by a capability list. -/
def OperationalSafeReps
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan) (available : List Plan)
    (b : Nat) (B : List S) : Set (S → Nat) :=
  {h | OperationalRepSafe sys available b B h}

/-- Set form of the law: C ⊆ C' implies SafeRep(C) ⊆ SafeRep(C'). -/
theorem operationalSafeReps_mono_capability
    [Fintype S] [DecidableEq S] [DecidableEq Plan]
    (sys : ContractSystem S Plan)
    (available expanded : List Plan)
    (hsub : ∀ π : Plan, π ∈ available → π ∈ expanded)
    (b : Nat) (B : List S) :
    OperationalSafeReps sys available b B ⊆
      OperationalSafeReps sys expanded b B := by
  intro h hh
  exact operationalRepSafe_mono_capability
    sys available expanded hsub b B h hh

-- ===== Strict finite witness in the canonical ternary system =====

open TState EPlan

/-- Maximal forgetting: all three worlds receive the same code. -/
def capabilityCoarseCode : TState → Nat := fun _ => 0

/-- Original capabilities are contained in the expanded list. -/
theorem ternaryAvailable_subset_expanded :
    ∀ π : EPlan, π ∈ ternaryAvailable →
      π ∈ (ternaryAvailable ++ execTernaryRepair) := by
  intro π hπ
  exact List.mem_append_left _ hπ

/-- Under the original capabilities, the constant representation is unsafe:
    its unique nonempty fiber is the full ternary ambiguity, which has no
    common available action at budget 1. -/
theorem coarseCode_not_safe_before :
    ¬ OperationalRepSafe executableTernarySystem ternaryAvailable 1
      ternaryWorlds capabilityCoarseCode := by
  intro hsafe
  have hlabel : 0 ∈ observationLabels ternaryWorlds capabilityCoarseCode := by
    simp [observationLabels, ternaryWorlds, capabilityCoarseCode]
  have hfiber := hsafe 0 hlabel
  have hfull : observationFiber ternaryWorlds capabilityCoarseCode 0 = ternaryWorlds := by
    simp [observationFiber, ternaryWorlds, capabilityCoarseCode]
  rw [hfull] at hfiber
  have hnone : findAct? executableTernarySystem ternaryAvailable 1 ternaryWorlds = none := by
    native_decide
  have hnot := (findAct_none_iff_not_finiteAdmissible
    executableTernarySystem ternaryAvailable 1 ternaryWorlds).1 hnone
  exact hnot hfiber

/-- After capability expansion, without changing the representation or
    ambiguity at all, the exact same constant code becomes safe. -/
theorem coarseCode_safe_after :
    OperationalRepSafe executableTernarySystem
      (ternaryAvailable ++ execTernaryRepair) 1
      ternaryWorlds capabilityCoarseCode := by
  intro y hy
  have hy0 : y = 0 := by
    simpa [observationLabels, ternaryWorlds, capabilityCoarseCode] using hy
  subst y
  have hfull : observationFiber ternaryWorlds capabilityCoarseCode 0 = ternaryWorlds := by
    simp [observationFiber, ternaryWorlds, capabilityCoarseCode]
  rw [hfull]
  refine ⟨EPlan.universalOne, ?_, ?_, ?_⟩
  · simp [ternaryAvailable, execTernaryRepair]
  · rfl
  · intro s hs
    cases s <;> simp [executableTernarySystem, eGood]

/-- Strictness certificate: capability expansion can strictly enlarge the set
    of safe representations. This is the formal version of
    'capability can buy the right to forget'. -/
theorem capability_can_strictly_expand_safe_representations :
    OperationalSafeReps executableTernarySystem ternaryAvailable 1 ternaryWorlds ⊆
      OperationalSafeReps executableTernarySystem
        (ternaryAvailable ++ execTernaryRepair) 1 ternaryWorlds ∧
    capabilityCoarseCode ∉
      OperationalSafeReps executableTernarySystem ternaryAvailable 1 ternaryWorlds ∧
    capabilityCoarseCode ∈
      OperationalSafeReps executableTernarySystem
        (ternaryAvailable ++ execTernaryRepair) 1 ternaryWorlds := by
  refine ⟨operationalSafeReps_mono_capability
    executableTernarySystem ternaryAvailable
      (ternaryAvailable ++ execTernaryRepair)
      ternaryAvailable_subset_expanded 1 ternaryWorlds, ?_, ?_⟩
  · exact coarseCode_not_safe_before
  · exact coarseCode_safe_after

end Insacermo
