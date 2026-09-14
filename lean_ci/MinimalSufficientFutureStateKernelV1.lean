import Mathlib

namespace InsacermoMinimalSufficientFutureState

universe u v w r

/-- Two present states are future-equivalent when every still-admissible future
test/continuation gives exactly the same outcome from both states. -/
def FutureEq {State : Type u} {Future : Type v} {Outcome : Type w}
    (eval : State → Future → Outcome) (x y : State) : Prop :=
  ∀ f, eval x f = eval y f

/-- Future equivalence is an equivalence relation. -/
theorem futureEq_refl
    {State : Type u} {Future : Type v} {Outcome : Type w}
    (eval : State → Future → Outcome) (x : State) :
    FutureEq eval x x := by
  intro f
  rfl

theorem futureEq_symm
    {State : Type u} {Future : Type v} {Outcome : Type w}
    (eval : State → Future → Outcome) {x y : State}
    (h : FutureEq eval x y) :
    FutureEq eval y x := by
  intro f
  exact (h f).symm

theorem futureEq_trans
    {State : Type u} {Future : Type v} {Outcome : Type w}
    (eval : State → Future → Outcome) {x y z : State}
    (hxy : FutureEq eval x y) (hyz : FutureEq eval y z) :
    FutureEq eval x z := by
  intro f
  exact (hxy f).trans (hyz f)

/-- The canonical future state is the complete outcome signature against every
still-admissible future continuation. -/
def CanonicalFutureState
    {State : Type u} {Future : Type v} {Outcome : Type w}
    (eval : State → Future → Outcome) (x : State) : Future → Outcome :=
  fun f => eval x f

/-- Equality of canonical future states is exactly future equivalence. -/
theorem canonicalFutureState_eq_iff_futureEq
    {State : Type u} {Future : Type v} {Outcome : Type w}
    (eval : State → Future → Outcome) (x y : State) :
    CanonicalFutureState eval x = CanonicalFutureState eval y ↔
      FutureEq eval x y := by
  constructor
  · intro h f
    exact congrFun h f
  · intro h
    funext f
    exact h f

/-- A representation is future-safe when any pair it merges is indistinguishable
for every future that is still owed. -/
def FutureSafeRepresentation
    {State : Type u} {Future : Type v} {Outcome : Type w} {Rep : Type r}
    (eval : State → Future → Outcome) (h : State → Rep) : Prop :=
  ∀ x y, h x = h y → FutureEq eval x y

/-- A representation is future-complete when it makes no distinction inside a
canonical future-equivalence class. -/
def FutureCompleteRepresentation
    {State : Type u} {Future : Type v} {Outcome : Type w} {Rep : Type r}
    (eval : State → Future → Outcome) (h : State → Rep) : Prop :=
  ∀ x y, FutureEq eval x y → h x = h y

/-- The canonical future-state representation is safe. -/
theorem canonicalFutureState_safe
    {State : Type u} {Future : Type v} {Outcome : Type w}
    (eval : State → Future → Outcome) :
    FutureSafeRepresentation eval (CanonicalFutureState eval) := by
  intro x y hxy
  exact (canonicalFutureState_eq_iff_futureEq eval x y).1 hxy

/-- The canonical future-state representation is complete. -/
theorem canonicalFutureState_complete
    {State : Type u} {Future : Type v} {Outcome : Type w}
    (eval : State → Future → Outcome) :
    FutureCompleteRepresentation eval (CanonicalFutureState eval) := by
  intro x y hxy
  exact (canonicalFutureState_eq_iff_futureEq eval x y).2 hxy

/-- Safety is exactly kernel refinement of the canonical future state: every
merge made by h must also be a merge of the canonical representation. -/
theorem futureSafe_iff_kernel_refines_canonical
    {State : Type u} {Future : Type v} {Outcome : Type w} {Rep : Type r}
    (eval : State → Future → Outcome) (h : State → Rep) :
    FutureSafeRepresentation eval h ↔
      ∀ x y, h x = h y →
        CanonicalFutureState eval x = CanonicalFutureState eval y := by
  constructor
  · intro hs x y hxy
    exact (canonicalFutureState_eq_iff_futureEq eval x y).2 (hs x y hxy)
  · intro hk x y hxy
    exact (canonicalFutureState_eq_iff_futureEq eval x y).1 (hk x y hxy)

/-- On the actually realized codes of h, every future-safe representation
canonically decodes to the minimal future state. -/
noncomputable def DecodeCanonicalOnRange
    {State : Type u} {Future : Type v} {Outcome : Type w} {Rep : Type r}
    (eval : State → Future → Outcome) (h : State → Rep) :
    Set.range h → (Future → Outcome) :=
  fun r => CanonicalFutureState eval (Classical.choose r.property)

/-- Universal factorization property: the canonical future state factors through
any future-safe representation, on every code that the representation actually
realizes. -/
theorem canonical_factors_through_every_safe_representation
    {State : Type u} {Future : Type v} {Outcome : Type w} {Rep : Type r}
    (eval : State → Future → Outcome) (h : State → Rep)
    (hsafe : FutureSafeRepresentation eval h) (x : State) :
    DecodeCanonicalOnRange eval h ⟨h x, ⟨x, rfl⟩⟩ =
      CanonicalFutureState eval x := by
  apply (canonicalFutureState_eq_iff_futureEq eval _ x).2
  apply hsafe
  exact (Classical.choose_spec (show ∃ y, h y = h x from ⟨x, rfl⟩))

/-- A representation is exact for future actionability precisely when its kernel
is exactly future equivalence. -/
theorem safe_and_complete_iff_exact_kernel
    {State : Type u} {Future : Type v} {Outcome : Type w} {Rep : Type r}
    (eval : State → Future → Outcome) (h : State → Rep) :
    (FutureSafeRepresentation eval h ∧ FutureCompleteRepresentation eval h) ↔
      ∀ x y, h x = h y ↔ FutureEq eval x y := by
  constructor
  · rintro ⟨hsafe, hcomplete⟩ x y
    exact ⟨hsafe x y, hcomplete x y⟩
  · intro hexact
    constructor
    · intro x y hxy
      exact (hexact x y).1 hxy
    · intro x y hxy
      exact (hexact x y).2 hxy

/-- An irreversible map is future-preserving when applying it never changes any
outcome for any still-owed future continuation. -/
def FuturePreservingMap
    {State : Type u} {Future : Type v} {Outcome : Type w}
    (eval : State → Future → Outcome) (d : State → State) : Prop :=
  ∀ x, FutureEq eval x (d x)

/-- Exact destruction criterion: an irreversible map is future-preserving iff it
leaves the canonical future state unchanged pointwise. -/
theorem futurePreservingMap_iff_canonical_unchanged
    {State : Type u} {Future : Type v} {Outcome : Type w}
    (eval : State → Future → Outcome) (d : State → State) :
    FuturePreservingMap eval d ↔
      ∀ x, CanonicalFutureState eval x = CanonicalFutureState eval (d x) := by
  constructor
  · intro hd x
    exact (canonicalFutureState_eq_iff_futureEq eval x (d x)).2 (hd x)
  · intro hd x
    exact (canonicalFutureState_eq_iff_futureEq eval x (d x)).1 (hd x)

/-- MINIMAL SUFFICIENT FUTURE STATE KERNEL V1.

The complete future-outcome signature is safe and complete; every future-safe
representation refines its kernel and canonically factors to it on realized
codes; and irreversible destruction is admissible exactly when this canonical
future state is unchanged. -/
theorem minimal_sufficient_future_state_v1
    {State : Type u} {Future : Type v} {Outcome : Type w}
    (eval : State → Future → Outcome) :
    FutureSafeRepresentation eval (CanonicalFutureState eval) ∧
    FutureCompleteRepresentation eval (CanonicalFutureState eval) ∧
    (∀ {Rep : Type r} (h : State → Rep),
      FutureSafeRepresentation eval h →
      ∀ x,
        DecodeCanonicalOnRange eval h ⟨h x, ⟨x, rfl⟩⟩ =
          CanonicalFutureState eval x) ∧
    (∀ d : State → State,
      FuturePreservingMap eval d ↔
        ∀ x, CanonicalFutureState eval x = CanonicalFutureState eval (d x)) := by
  constructor
  · exact canonicalFutureState_safe eval
  constructor
  · exact canonicalFutureState_complete eval
  constructor
  · intro Rep h hsafe x
    exact canonical_factors_through_every_safe_representation eval h hsafe x
  · intro d
    exact futurePreservingMap_iff_canonical_unchanged eval d

end InsacermoMinimalSufficientFutureState
