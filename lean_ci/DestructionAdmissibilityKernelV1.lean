import Mathlib

namespace InsacermoDestructionAdmissibility

/-!
INSACERMO Destruction Admissibility Kernel V1

This file tests a proposed deeper formulation of the existing INSACERMO architecture.
It does NOT replace CONTRACT -> ACTIONABILITY -> PLANNER and does not claim that every
previous theorem follows from one axiom.

The abstract object is a contract-relative guarantee profile.  A transformation may be lossy in
raw information, capability, resources, or plan options; it is contract-admissible at a state when
it does not destroy any guarantee that the declared contract can still require and that the source
state can still provide.

The kernel proves:
* guarantee-profile preservation is exactly set inclusion;
* the induced relation is a preorder (identity and transitive composition);
* strengthening the contract can only reduce the set of admissible destructions;
* from a contract-safe source, preservation is equivalent to contract safety of the target;
* therefore PRESERVE is exactly the gate that rejects a lossy transition whose target would
  leave the safe region;
* in the one-shot common-action model, actionability is equivalent to the absence of an
  obstructive realized fiber;
* finer information preserves safety;
* capability expansion preserves safety.

The last two are the local order laws behind the existing safe-representation and
capability-information monotonicity results.  Information debt, factorization, and causal planning
need additional structure (restoration cost, joint representation, and temporal transitions); they
are not silently identified with this abstract preorder.
-/

open Set

universe u v

section AbstractGuarantees

variable {State : Type u} {Req : Type v}

/-- `Win x q` means that state `x` can still guarantee future requirement `q`. -/
def GuaranteeProfile (Win : State → Req → Prop) (Γ : Set Req) (x : State) : Set Req :=
  {q | q ∈ Γ ∧ Win x q}

/-- `y` preserves `x` relative to the declared future contract Γ when every contract requirement
still guaranteeable from `x` remains guaranteeable from `y`. -/
def Preserves (Win : State → Req → Prop) (Γ : Set Req) (x y : State) : Prop :=
  ∀ q, q ∈ Γ → Win x q → Win y q

/-- A state is contract-safe when it can guarantee every declared requirement. -/
def ContractSafe (Win : State → Req → Prop) (Γ : Set Req) (x : State) : Prop :=
  ∀ q, q ∈ Γ → Win x q

/-- A transformation is admissible at x iff applying it preserves the contract-relative guarantee
profile of x. -/
def AdmissibleDestruction (Win : State → Req → Prop) (Γ : Set Req)
    (d : State → State) (x : State) : Prop :=
  Preserves Win Γ x (d x)

/-- Profile inclusion is exactly guarantee preservation. -/
theorem preserves_iff_profile_subset (Win : State → Req → Prop) (Γ : Set Req)
    (x y : State) :
    Preserves Win Γ x y ↔ GuaranteeProfile Win Γ x ⊆ GuaranteeProfile Win Γ y := by
  constructor
  · intro h q hq
    exact ⟨hq.1, h q hq.1 hq.2⟩
  · intro h q hq hx
    exact (h ⟨hq, hx⟩).2

/-- Contract-relative preservation is reflexive. -/
theorem preserves_refl (Win : State → Req → Prop) (Γ : Set Req) (x : State) :
    Preserves Win Γ x x := by
  intro q hq hx
  exact hx

/-- Contract-relative preservation is transitive. -/
theorem preserves_trans (Win : State → Req → Prop) (Γ : Set Req)
    {x y z : State}
    (hxy : Preserves Win Γ x y) (hyz : Preserves Win Γ y z) :
    Preserves Win Γ x z := by
  intro q hq hx
  exact hyz q hq (hxy q hq hx)

/-- Identity is always an admissible destruction. -/
theorem admissible_id (Win : State → Req → Prop) (Γ : Set Req) (x : State) :
    AdmissibleDestruction Win Γ id x := by
  exact preserves_refl Win Γ x

/-- Sequentially admissible destructions compose. -/
theorem admissible_comp (Win : State → Req → Prop) (Γ : Set Req)
    (d e : State → State) (x : State)
    (hd : AdmissibleDestruction Win Γ d x)
    (he : AdmissibleDestruction Win Γ e (d x)) :
    AdmissibleDestruction Win Γ (e ∘ d) x := by
  exact preserves_trans Win Γ hd he

/-- A stronger declared contract can only make preservation harder. -/
theorem preserves_contract_antitone (Win : State → Req → Prop)
    {Γstrong Γweak : Set Req} (hsub : Γweak ⊆ Γstrong)
    {x y : State} (h : Preserves Win Γstrong x y) :
    Preserves Win Γweak x y := by
  intro q hq hx
  exact h q (hsub hq) hx

/-- Preservation from a safe source keeps the target safe. -/
theorem contractSafe_of_preserves (Win : State → Req → Prop) (Γ : Set Req)
    {x y : State} (hx : ContractSafe Win Γ x)
    (hxy : Preserves Win Γ x y) :
    ContractSafe Win Γ y := by
  intro q hq
  exact hxy q hq (hx q hq)

/-- From a safe source, preservation is equivalent to target safety. -/
theorem preserves_iff_target_safe_of_source_safe (Win : State → Req → Prop) (Γ : Set Req)
    {x y : State} (hx : ContractSafe Win Γ x) :
    Preserves Win Γ x y ↔ ContractSafe Win Γ y := by
  constructor
  · intro h
    exact contractSafe_of_preserves Win Γ hx h
  · intro hy q hq _
    exact hy q hq

/-- Exact PRESERVE gate: if the source is safe, rejecting a lossy transformation as inadmissible
is equivalent to saying that its target leaves the contract-safe region. -/
theorem preserve_gate_exact (Win : State → Req → Prop) (Γ : Set Req)
    (d : State → State) {x : State} (hx : ContractSafe Win Γ x) :
    (¬ AdmissibleDestruction Win Γ d x) ↔ ¬ ContractSafe Win Γ (d x) := by
  rw [AdmissibleDestruction, preserves_iff_target_safe_of_source_safe Win Γ hx]

/-- Exact-future equivalence: two states expose the same guarantee profile on the declared contract. -/
def FutureEq (Win : State → Req → Prop) (Γ : Set Req) (x y : State) : Prop :=
  ∀ q, q ∈ Γ → (Win x q ↔ Win y q)

/-- Exact future equivalence is mutual preservation. -/
theorem futureEq_iff_mutual_preservation (Win : State → Req → Prop) (Γ : Set Req)
    (x y : State) :
    FutureEq Win Γ x y ↔ Preserves Win Γ x y ∧ Preserves Win Γ y x := by
  constructor
  · intro h
    constructor
    · intro q hq hx
      exact (h q hq).mp hx
    · intro q hq hy
      exact (h q hq).mpr hy
  · rintro ⟨hxy, hyx⟩ q hq
    constructor
    · exact hxy q hq
    · exact hyx q hq

end AbstractGuarantees

section OneShotActionability

variable {World : Type u} {Act : Type v} {Obs : Type*}

/-- A fiber is jointly actionable when one available action is good for every world in it. -/
def CommonAction (Good : World → Act → Prop) (C : Set Act) (F : Set World) : Prop :=
  ∃ a, a ∈ C ∧ ∀ s, s ∈ F → Good s a

/-- An obstruction is a set of worlds with no common available action. -/
def Obstructive (Good : World → Act → Prop) (C : Set Act) (F : Set World) : Prop :=
  ¬ CommonAction Good C F

/-- Realized observation fiber inside the current ambiguity set. -/
def Fiber (B : Set World) (h : World → Obs) (y : Obs) : Set World :=
  {s | s ∈ B ∧ h s = y}

/-- One-shot SafeRep semantics: every realized observation fiber has a common available action. -/
def FiberSafe (Good : World → Act → Prop) (B : Set World) (C : Set Act)
    (h : World → Obs) : Prop :=
  ∀ y, (Fiber B h y).Nonempty → CommonAction Good C (Fiber B h y)

/-- One-shot actionability is exactly absence of an obstructive realized fiber. -/
theorem fiberSafe_iff_no_obstructive_realized_fiber
    (Good : World → Act → Prop) (B : Set World) (C : Set Act)
    (h : World → Obs) :
    FiberSafe Good B C h ↔
      ∀ y, (Fiber B h y).Nonempty → ¬ Obstructive Good C (Fiber B h y) := by
  constructor
  · intro hsafe y hy hobs
    exact hobs (hsafe y hy)
  · intro hno y hy
    by_contra hca
    exact hno y hy hca

/-- `fine` refines `coarse` when equality under the fine observation implies equality under the
coarse observation. -/
def Refines (fine coarse : World → Obs) : Prop :=
  ∀ s t, fine s = fine t → coarse s = coarse t

/-- More information cannot destroy one-shot actionability. -/
theorem fiberSafe_of_refinement
    (Good : World → Act → Prop) (B : Set World) (C : Set Act)
    {fine coarse : World → Obs}
    (href : Refines fine coarse)
    (hsafe : FiberSafe Good B C coarse) :
    FiberSafe Good B C fine := by
  intro y hy
  rcases hy with ⟨s0, hs0B, hs0y⟩
  have hcoarseNonempty : (Fiber B coarse (coarse s0)).Nonempty := by
    exact ⟨s0, hs0B, rfl⟩
  rcases hsafe (coarse s0) hcoarseNonempty with ⟨a, haC, hgood⟩
  refine ⟨a, haC, ?_⟩
  intro s hs
  have hFineEq : fine s = fine s0 := by
    calc
      fine s = y := hs.2
      _ = fine s0 := hs0y.symm
  have hCoarseEq : coarse s = coarse s0 := href s s0 hFineEq
  exact hgood s ⟨hs.1, hCoarseEq⟩

/-- More capability cannot destroy one-shot actionability. -/
theorem fiberSafe_of_capability_expansion
    (Good : World → Act → Prop) (B : Set World)
    {C C' : Set Act} (hcap : C ⊆ C')
    {h : World → Obs}
    (hsafe : FiberSafe Good B C h) :
    FiberSafe Good B C' h := by
  intro y hy
  rcases hsafe y hy with ⟨a, haC, hgood⟩
  exact ⟨a, hcap haC, hgood⟩

/-- If a realized fiber is obstructive, the representation is not safe. -/
theorem not_fiberSafe_of_obstruction
    (Good : World → Act → Prop) (B : Set World) (C : Set Act)
    (h : World → Obs) {y : Obs}
    (hy : (Fiber B h y).Nonempty)
    (hobs : Obstructive Good C (Fiber B h y)) :
    ¬ FiberSafe Good B C h := by
  intro hsafe
  exact hobs (hsafe y hy)

/-- A probe-style refinement and a repair-style capability expansion are two orthogonal ways of
re-entering the same FiberSafe region.  This theorem records the common target semantics without
claiming that the interventions are otherwise identical. -/
theorem probe_or_repair_restore_same_safety_predicate
    (Good : World → Act → Prop) (B : Set World)
    {C C' : Set Act} {fine coarse : World → Obs}
    (_hProbe : Refines fine coarse)
    (hFineSafe : FiberSafe Good B C fine)
    (_hRepair : C ⊆ C')
    (hCoarseRepairedSafe : FiberSafe Good B C' coarse) :
    FiberSafe Good B C fine ∧ FiberSafe Good B C' coarse := by
  exact ⟨hFineSafe, hCoarseRepairedSafe⟩

end OneShotActionability

end InsacermoDestructionAdmissibility
