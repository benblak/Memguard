import SignedInteractionZeroCutKernelV1

namespace InsacermoMonotoneSignedCancellation

open Finset
open InsacermoSignedInteractionZeroCut

/-- Signed Möbius coefficients on a two-obligation contract.

Singletons contribute +1 each, while the joint interaction contributes -1.
The induced price remains nonnegative and monotone even though cancellation
makes the raw nonzero-support union nonminimal. -/
def MonotoneCancelCoeff : Finset (Fin 2) → Int := fun T =>
  if T = ({0} : Finset (Fin 2)) then 1
  else if T = ({1} : Finset (Fin 2)) then 1
  else if T = ({0, 1} : Finset (Fin 2)) then -1
  else 0

abbrev MCP (S : Finset (Fin 2)) : Int :=
  SignedInteractionPrice MonotoneCancelCoeff S

/-- Every coalition price in the witness is nonnegative. -/
theorem witness_price_nonnegative :
    ∀ S : Finset (Fin 2), 0 ≤ MCP S := by
  native_decide

/-- The witness price is monotone under inclusion. -/
theorem witness_price_monotone :
    ∀ S T : Finset (Fin 2), S ⊆ T → MCP S ≤ MCP T := by
  native_decide

/-- Exact price profile of the witness. -/
theorem witness_empty_price : MCP (∅ : Finset (Fin 2)) = 0 := by
  native_decide

theorem witness_zero_price : MCP ({0} : Finset (Fin 2)) = 1 := by
  native_decide

theorem witness_one_price : MCP ({1} : Finset (Fin 2)) = 1 := by
  native_decide

theorem witness_full_price : MCP (Finset.univ : Finset (Fin 2)) = 1 := by
  native_decide

/-- Both singleton and pair coefficients are genuinely active. -/
theorem witness_coeff_zero_nonzero :
    MonotoneCancelCoeff ({0} : Finset (Fin 2)) ≠ 0 := by
  native_decide

theorem witness_coeff_one_nonzero :
    MonotoneCancelCoeff ({1} : Finset (Fin 2)) ≠ 0 := by
  native_decide

theorem witness_coeff_pair_nonzero :
    MonotoneCancelCoeff ({0, 1} : Finset (Fin 2)) ≠ 0 := by
  native_decide

/-- Raw union of all nonzero interaction supports. -/
def NonzeroSupportUnion : Finset (Fin 2) :=
  ((Finset.univ : Finset (Fin 2)).powerset.filter
    (fun T => MonotoneCancelCoeff T ≠ 0)).biUnion id

/-- In this witness, the raw support union is the whole two-obligation contract. -/
theorem nonzeroSupportUnion_eq_univ :
    NonzeroSupportUnion = (Finset.univ : Finset (Fin 2)) := by
  native_decide

/-- Yet a proper singleton already has the complete global price. -/
theorem proper_singleton_has_full_price :
    MCP ({0} : Finset (Fin 2)) = MCP (Finset.univ : Finset (Fin 2)) ∧
    ({0} : Finset (Fin 2)) ⊂ (Finset.univ : Finset (Fin 2)) := by
  native_decide

/-- The raw nonzero-support union is therefore not necessary for full price,
even under nonnegativity and monotonicity of the induced price. -/
theorem monotonicity_does_not_restore_raw_carrier :
    MCP ({0} : Finset (Fin 2)) = MCP (Finset.univ : Finset (Fin 2)) ∧
    ¬ NonzeroSupportUnion ⊆ ({0} : Finset (Fin 2)) := by
  native_decide

/-- The mechanism is exactly zero omitted mass: omitting obligation 1 drops
its +1 singleton term and the -1 pair term together, so the net omitted mass
is zero. -/
theorem singleton_zero_cut :
    OmittedMass MonotoneCancelCoeff ({0} : Finset (Fin 2)) = 0 := by
  native_decide

/-- MONOTONE SIGNED CANCELLATION KERNEL V1.

There exists a finite signed interaction price that is everywhere nonnegative
and monotone under coalition inclusion, yet a proper coalition has the full
global price while failing to contain the union of all nonzero interaction
supports. Thus monotonicity of the induced price does not recover the unsigned
carrier rule; the exact signed criterion remains zero omitted mass. -/
theorem monotone_signed_cancellation_v1 :
    (∀ S : Finset (Fin 2), 0 ≤ MCP S) ∧
    (∀ S T : Finset (Fin 2), S ⊆ T → MCP S ≤ MCP T) ∧
    (MCP ({0} : Finset (Fin 2)) = MCP (Finset.univ : Finset (Fin 2))) ∧
    (¬ NonzeroSupportUnion ⊆ ({0} : Finset (Fin 2))) ∧
    (OmittedMass MonotoneCancelCoeff ({0} : Finset (Fin 2)) = 0) := by
  refine ⟨witness_price_nonnegative, witness_price_monotone, ?_, ?_, singleton_zero_cut⟩
  · exact witness_zero_price.trans witness_full_price.symm
  · exact monotonicity_does_not_restore_raw_carrier.2

end InsacermoMonotoneSignedCancellation
