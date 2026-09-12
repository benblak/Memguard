import Mathlib
import DestructionAdmissibilityKernelV1

namespace InsacermoDestructionFactorizationBoundary

open Set
open InsacermoDestructionAdmissibility

/-!
INSACERMO Destruction–Factorization Boundary Kernel V1

Purpose.
This kernel tests whether contract-relative destruction admissibility can, in general, be decided
from separate information/capability marginals.  The answer is no, already in a 2×2 finite witness.

Two joint couplings have exactly the same information marginal and exactly the same capability
marginal.  One coupling aligns information and capability; the other anti-aligns them.  A genuinely
joint contract score distinguishes the two.  Consequently, from a safe source state, a destructive
transition to the aligned coupling is admissible while an otherwise marginally indistinguishable
transition to the anti-aligned coupling is not.

The file also exposes the binary cross-difference identity: the diagonal-vs-antidiagonal value gap
is exactly the cross difference of the joint score.  Thus a nonzero interaction term is precisely
what allows fixed marginals to conceal different contract values in this binary witness.

This is a bridge theorem, not a replacement for the full INSACERMO Factorization Boundary theory.
It proves a concrete impossibility of marginal-only destruction certification.
-/

/-- Integer-valued 2×2 joint coupling, represented by four cell masses/counts. -/
structure Coupling where
  ff : Int
  ft : Int
  tf : Int
  tt : Int
  deriving DecidableEq, Repr

/-- Row marginal for information=false. -/
def rowFalse (K : Coupling) : Int := K.ff + K.ft
/-- Row marginal for information=true. -/
def rowTrue (K : Coupling) : Int := K.tf + K.tt
/-- Column marginal for capability=false. -/
def colFalse (K : Coupling) : Int := K.ff + K.tf
/-- Column marginal for capability=true. -/
def colTrue (K : Coupling) : Int := K.ft + K.tt

/-- Complete separate-marginal signature. -/
def marginalSignature (K : Coupling) : Int × Int × Int × Int :=
  (rowFalse K, rowTrue K, colFalse K, colTrue K)

/-- Perfectly aligned coupling. -/
def diagonal : Coupling := ⟨1, 0, 0, 1⟩
/-- Perfectly anti-aligned coupling. -/
def antiDiagonal : Coupling := ⟨0, 1, 1, 0⟩

/-- The two couplings have identical separate marginals. -/
theorem same_separate_marginals :
    marginalSignature diagonal = marginalSignature antiDiagonal := by
  rfl

/-- A joint score on an information bit and a capability bit. -/
abbrev JointScore := Bool → Bool → Int

/-- Contract value of a score on an integer coupling. -/
def contractValue (H : JointScore) (K : Coupling) : Int :=
  K.ff * H false false +
  K.ft * H false true +
  K.tf * H true false +
  K.tt * H true true

/-- Binary cross difference, the elementary interaction term. -/
def crossDiff (H : JointScore) : Int :=
  H false false + H true true - H false true - H true false

/-- The diagonal-vs-antidiagonal value gap equals the score's cross difference. -/
theorem diagonal_anti_gap_is_crossDiff (H : JointScore) :
    contractValue H diagonal - contractValue H antiDiagonal = crossDiff H := by
  simp [contractValue, diagonal, antiDiagonal, crossDiff]
  ring

/-- Hence the two fixed-marginal couplings have equal value iff this binary interaction vanishes. -/
theorem diagonal_value_eq_anti_iff_crossDiff_zero (H : JointScore) :
    contractValue H diagonal = contractValue H antiDiagonal ↔ crossDiff H = 0 := by
  constructor
  · intro h
    have hgap : contractValue H diagonal - contractValue H antiDiagonal = 0 := sub_eq_zero.mpr h
    simpa [diagonal_anti_gap_is_crossDiff] using hgap
  · intro h
    apply sub_eq_zero.mp
    rw [diagonal_anti_gap_is_crossDiff H, h]

/-- Interaction score: one unit exactly when information and capability are aligned. -/
def alignScore : JointScore
  | false, false => 1
  | true, true => 1
  | _, _ => 0

@[simp] theorem alignScore_crossDiff : crossDiff alignScore = 2 := by
  rfl

@[simp] theorem diagonal_value : contractValue alignScore diagonal = 2 := by
  rfl

@[simp] theorem antiDiagonal_value : contractValue alignScore antiDiagonal = 0 := by
  rfl

/-- Contract-safe joint state: at least one aligned unit remains. -/
def JointSafe (K : Coupling) : Prop := contractValue alignScore K ≥ 1

@[simp] theorem diagonal_safe : JointSafe diagonal := by
  norm_num [JointSafe]

@[simp] theorem antiDiagonal_unsafe : ¬ JointSafe antiDiagonal := by
  norm_num [JointSafe]

/-- Abstract contract used to import the generic DestructionAdmissibility semantics. -/
def Win (K : Coupling) (_q : Unit) : Prop := JointSafe K

def Contract : Set Unit := Set.univ

/-- Constant destructive transitions to a chosen target joint structure. -/
def destroyTo (target : Coupling) : Coupling → Coupling := fun _ => target

/-- From a safe source, destruction to the aligned target is admissible. -/
theorem destruction_to_diagonal_admissible :
    AdmissibleDestruction Win Contract (destroyTo diagonal) diagonal := by
  intro q hq hsource
  exact diagonal_safe

/-- From the same safe source, destruction to the anti-aligned target is not admissible. -/
theorem destruction_to_antiDiagonal_inadmissible :
    ¬ AdmissibleDestruction Win Contract (destroyTo antiDiagonal) diagonal := by
  intro h
  have hsource : Win diagonal () := diagonal_safe
  have htarget : Win antiDiagonal () := h () (by simp [Contract]) hsource
  exact antiDiagonal_unsafe htarget

/-- Core bridge: two targets with identical separate information/capability marginals can have
opposite destruction-admissibility verdicts. -/
theorem same_marginals_opposite_destruction_verdicts :
    marginalSignature diagonal = marginalSignature antiDiagonal ∧
    AdmissibleDestruction Win Contract (destroyTo diagonal) diagonal ∧
    ¬ AdmissibleDestruction Win Contract (destroyTo antiDiagonal) diagonal := by
  exact ⟨same_separate_marginals,
    destruction_to_diagonal_admissible,
    destruction_to_antiDiagonal_inadmissible⟩

/-- No exact classifier of destruction admissibility can depend only on the separate marginal
signature, even in this tiny finite witness. -/
theorem no_marginal_only_destruction_classifier :
    ¬ ∃ classify : (Int × Int × Int × Int) → Prop,
      ∀ target : Coupling,
        classify (marginalSignature target) ↔
          AdmissibleDestruction Win Contract (destroyTo target) diagonal := by
  rintro ⟨classify, hclass⟩
  have hdiagAdm :
      AdmissibleDestruction Win Contract (destroyTo diagonal) diagonal :=
    destruction_to_diagonal_admissible
  have hdiagClass : classify (marginalSignature diagonal) :=
    (hclass diagonal).2 hdiagAdm
  have hantiClass : classify (marginalSignature antiDiagonal) := by
    simpa [same_separate_marginals] using hdiagClass
  have hantiAdm :
      AdmissibleDestruction Win Contract (destroyTo antiDiagonal) diagonal :=
    (hclass antiDiagonal).1 hantiClass
  exact destruction_to_antiDiagonal_inadmissible hantiAdm

/-- Consolidated factorization-boundary witness for destruction admissibility. -/
theorem destruction_factorization_boundary_v1 :
    crossDiff alignScore ≠ 0 ∧
    marginalSignature diagonal = marginalSignature antiDiagonal ∧
    contractValue alignScore diagonal ≠ contractValue alignScore antiDiagonal ∧
    AdmissibleDestruction Win Contract (destroyTo diagonal) diagonal ∧
    (¬ AdmissibleDestruction Win Contract (destroyTo antiDiagonal) diagonal) ∧
    (¬ ∃ classify : (Int × Int × Int × Int) → Prop,
      ∀ target : Coupling,
        classify (marginalSignature target) ↔
          AdmissibleDestruction Win Contract (destroyTo target) diagonal) := by
  constructor
  · norm_num
  constructor
  · exact same_separate_marginals
  constructor
  · norm_num
  constructor
  · exact destruction_to_diagonal_admissible
  constructor
  · exact destruction_to_antiDiagonal_inadmissible
  · exact no_marginal_only_destruction_classifier

end InsacermoDestructionFactorizationBoundary
