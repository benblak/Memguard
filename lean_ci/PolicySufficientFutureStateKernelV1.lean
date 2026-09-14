import Mathlib
import MinimalSufficientFutureStateKernelV1

namespace InsacermoPolicySufficientFutureState

open InsacermoMinimalSufficientFutureState

universe u o a r

/-- Terminal contractual outcomes exposed by a policy execution. -/
inductive TerminalResult (Act : Type a) (Obs : Type o)
  | acted (a : Act)
  | refused
  | probed (obs : Obs)
  deriving DecidableEq, Repr

/-- Finite contingent policy language with the operational INSACERMO roles:
ACT, REFUSE, PROBE, and REPAIR. `PROBE` branches on the observation returned by
`observe`; `REPAIR` changes the state and continues. -/
inductive Policy (State : Type u) (Obs : Type o) (Act : Type a)
  | act (a : Act)
  | refuse
  | probe (next : Obs → Policy State Obs Act)
  | repair (step : State → State) (next : Policy State Obs Act)

/-- Environment semantics used to execute one finite policy. ACT is admissible
only when `legalAct` holds. A rejected ACT produces REFUSE, making refusal part
of the externally visible contractual behavior. The final field supplies only
the decidability witness needed to execute that same proposition. -/
structure Semantics (State : Type u) (Obs : Type o) (Act : Type a) where
  observe : State → Obs
  legalAct : State → Act → Prop
  legalActDecidable : ∀ s a, Decidable (legalAct s a)

/-- Execute a finite contingent policy from a present state. The result records
whether the policy ACTed, REFUSEd, or performed a PROBE and what it observed.
REPAIR is internal state change and execution continues. -/
def runPolicy
    {State : Type u} {Obs : Type o} {Act : Type a}
    [DecidableEq Obs]
    (sem : Semantics State Obs Act) :
    State → Policy State Obs Act → TerminalResult Act Obs
  | s, .act a => by
      letI : Decidable (sem.legalAct s a) := sem.legalActDecidable s a
      exact if sem.legalAct s a then .acted a else .refused
  | _, .refuse => .refused
  | s, .probe next =>
      let o := sem.observe s
      match next o with
      | .act a => by
          letI : Decidable (sem.legalAct s a) := sem.legalActDecidable s a
          exact if sem.legalAct s a then .acted a else .refused
      | .refuse => .refused
      | p => .probed o
  | s, .repair step next => runPolicy sem (step s) next
termination_by
  s p => p

/-- Policy equivalence: no finite ACT/PROBE/REPAIR/REFUSE continuation can
contractually distinguish the two present states. -/
def PolicyEq
    {State : Type u} {Obs : Type o} {Act : Type a}
    [DecidableEq Obs]
    (sem : Semantics State Obs Act) (x y : State) : Prop :=
  FutureEq (fun s p => runPolicy sem s p) x y

/-- Canonical policy-future state: the complete behavior signature against every
finite contingent policy. -/
def CanonicalPolicyState
    {State : Type u} {Obs : Type o} {Act : Type a}
    [DecidableEq Obs]
    (sem : Semantics State Obs Act) (x : State) :
    Policy State Obs Act → TerminalResult Act Obs :=
  CanonicalFutureState (fun s p => runPolicy sem s p) x

/-- Equality of canonical policy states is exactly policy equivalence. -/
theorem canonicalPolicyState_eq_iff_policyEq
    {State : Type u} {Obs : Type o} {Act : Type a}
    [DecidableEq Obs]
    (sem : Semantics State Obs Act) (x y : State) :
    CanonicalPolicyState sem x = CanonicalPolicyState sem y ↔
      PolicyEq sem x y := by
  exact canonicalFutureState_eq_iff_futureEq (fun s p => runPolicy sem s p) x y

/-- Any representation safe for all policies must refine the canonical policy
kernel. -/
theorem policySafe_iff_kernel_refines_canonical
    {State : Type u} {Obs : Type o} {Act : Type a} {Rep : Type r}
    [DecidableEq Obs]
    (sem : Semantics State Obs Act) (h : State → Rep) :
    FutureSafeRepresentation (fun s p => runPolicy sem s p) h ↔
      ∀ x y, h x = h y → CanonicalPolicyState sem x = CanonicalPolicyState sem y := by
  exact futureSafe_iff_kernel_refines_canonical (fun s p => runPolicy sem s p) h

/-- Universal factorization: the canonical policy state decodes from every
representation that is safe for all ACT/PROBE/REPAIR/REFUSE continuations. -/
theorem canonical_policy_factors_through_every_safe_representation
    {State : Type u} {Obs : Type o} {Act : Type a} {Rep : Type r}
    [DecidableEq Obs]
    (sem : Semantics State Obs Act) (h : State → Rep)
    (hsafe : FutureSafeRepresentation (fun s p => runPolicy sem s p) h)
    (x : State) :
    DecodeCanonicalOnRange (fun s p => runPolicy sem s p) h
      ⟨h x, ⟨x, rfl⟩⟩ = CanonicalPolicyState sem x := by
  exact canonical_factors_through_every_safe_representation
    (fun s p => runPolicy sem s p) h hsafe x

/-- Explicit no-merge theorem: if one admissible finite policy distinguishes two
states, no representation safe for all such policies may merge them. -/
theorem distinguishing_policy_forbids_safe_merge
    {State : Type u} {Obs : Type o} {Act : Type a} {Rep : Type r}
    [DecidableEq Obs]
    (sem : Semantics State Obs Act) (h : State → Rep)
    (hsafe : FutureSafeRepresentation (fun s p => runPolicy sem s p) h)
    {x y : State} (p : Policy State Obs Act)
    (hdiff : runPolicy sem x p ≠ runPolicy sem y p) :
    h x ≠ h y := by
  intro hxy
  have heq := hsafe x y hxy p
  exact hdiff heq

/-- Policy-preserving destruction is exactly pointwise invariance of the
canonical policy state. -/
def PolicyPreservingMap
    {State : Type u} {Obs : Type o} {Act : Type a}
    [DecidableEq Obs]
    (sem : Semantics State Obs Act) (d : State → State) : Prop :=
  FuturePreservingMap (fun s p => runPolicy sem s p) d

theorem policyPreservingMap_iff_canonical_unchanged
    {State : Type u} {Obs : Type o} {Act : Type a}
    [DecidableEq Obs]
    (sem : Semantics State Obs Act) (d : State → State) :
    PolicyPreservingMap sem d ↔
      ∀ x, CanonicalPolicyState sem x = CanonicalPolicyState sem (d x) := by
  exact futurePreservingMap_iff_canonical_unchanged
    (fun s p => runPolicy sem s p) d

/-- POLICY-SUFFICIENT FUTURE STATE KERNEL V1.

The minimal sufficient future-state theorem lifts from abstract futures to an
explicit finite planner language containing ACT, REFUSE, PROBE, and REPAIR.
The complete policy-behavior signature is canonical; every representation safe
for all such policies factors through it; one distinguishing policy forbids a
safe merge; and irreversible destruction is admissible exactly when the
canonical policy state is unchanged. -/
theorem policy_sufficient_future_state_v1
    {State : Type u} {Obs : Type o} {Act : Type a}
    [DecidableEq Obs]
    (sem : Semantics State Obs Act) :
    FutureSafeRepresentation
      (fun s p => runPolicy sem s p) (CanonicalPolicyState sem) ∧
    FutureCompleteRepresentation
      (fun s p => runPolicy sem s p) (CanonicalPolicyState sem) ∧
    (∀ {Rep : Type r} (h : State → Rep),
      FutureSafeRepresentation (fun s p => runPolicy sem s p) h →
      ∀ x,
        DecodeCanonicalOnRange (fun s p => runPolicy sem s p) h
          ⟨h x, ⟨x, rfl⟩⟩ = CanonicalPolicyState sem x) ∧
    (∀ d : State → State,
      PolicyPreservingMap sem d ↔
        ∀ x, CanonicalPolicyState sem x = CanonicalPolicyState sem (d x)) := by
  exact minimal_sufficient_future_state_v1 (fun s p => runPolicy sem s p)

end InsacermoPolicySufficientFutureState
