import HiddenPriceDepthKernelV1
import CanonicalInteractionRepresentationKernelV1

namespace InsacermoHiddenDepthMobiusBridge

open Finset
open InsacermoHiddenPriceDepth
open InsacermoCausalPriceFactorization
open InsacermoCanonicalInteractionRepresentation

universe u v

/-- Signed interaction mass omitted by `S`, but only relative to the declared
contract `Q`. This is the arbitrary-contract version of the full-universe
`OmittedMass` used by the signed zero-cut kernel. -/
def RelativeOmittedMass {Req : Type v} [DecidableEq Req]
    (c : Finset Req → Int) (Q S : Finset Req) : Int :=
  (Q.powerset.filter (fun T => ¬ T ⊆ S)).sum c

/-- Exact relative zero-cut identity for any represented price function. -/
theorem represented_price_eq_price_add_relative_omitted
    {Req : Type v} [DecidableEq Req]
    (P c : Finset Req → Int)
    (hrep : Represents P c)
    {S Q : Finset Req} (hSQ : S ⊆ Q) :
    P Q = P S + RelativeOmittedMass c Q S := by
  unfold RelativeOmittedMass
  have hsplit := Finset.sum_filter_add_sum_filter_not
    Q.powerset (fun T => T ⊆ S) c
  have hfilter :
      Q.powerset.filter (fun T => T ⊆ S) = S.powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨_, hTS⟩
      exact hTS
    · intro hTS
      exact ⟨fun x hx => hSQ (hTS hx), hTS⟩
  rw [hfilter] at hsplit
  have hQ := hrep Q
  have hS := hrep S
  rw [hQ, hS]
  exact hsplit.symm

/-- A represented subset has the same price as `Q` iff the interaction mass
omitted relative to `Q` is exactly zero. -/
theorem represented_full_price_iff_relative_zero_cut
    {Req : Type v} [DecidableEq Req]
    (P c : Finset Req → Int)
    (hrep : Represents P c)
    {S Q : Finset Req} (hSQ : S ⊆ Q) :
    P S = P Q ↔ RelativeOmittedMass c Q S = 0 := by
  have h := represented_price_eq_price_add_relative_omitted P c hrep hSQ
  constructor
  · intro hp
    rw [← hp] at h
    omega
  · intro hz
    rw [hz, add_zero] at h
    exact h.symm

/-- Total integer-valued extension of the original INSACERMO set-price on one
declared contract `Q`. Outside `Q` we assign zero; coefficients on subsets of
`Q` depend only on values inside `Q`, so this extension does not alter the
relative bridge. -/
noncomputable def ContractPrice
    {A : Type u} {Req : Type v} [DecidableEq Req]
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q)
    (S : Finset Req) : Int := by
  classical
  exact if h : S ⊆ Q then
    Int.ofNat (SetPrice cost Sat S
      (subset_feasible_of_full cost Sat h hevQ))
  else 0

/-- On every subcoalition of `Q`, `ContractPrice` is exactly the original
`SetPrice`, embedded into the integers. -/
theorem contractPrice_of_subset
    {A : Type u} {Req : Type v} [DecidableEq Req]
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q)
    {S : Finset Req} (hSQ : S ⊆ Q) :
    ContractPrice cost Sat Q hevQ S =
      Int.ofNat (SetPrice cost Sat S
        (subset_feasible_of_full cost Sat hSQ hevQ)) := by
  classical
  simp [ContractPrice, hSQ]

/-- Equality with the full original set-price is exactly equality with the full
integer contract-price. -/
theorem contractPrice_eq_full_iff_setPrice_eq_full
    {A : Type u} {Req : Type v} [DecidableEq Req]
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q)
    {S : Finset Req} (hSQ : S ⊆ Q) :
    ContractPrice cost Sat Q hevQ S = ContractPrice cost Sat Q hevQ Q ↔
      SetPrice cost Sat S
          (subset_feasible_of_full cost Sat hSQ hevQ) =
        SetPrice cost Sat Q hevQ := by
  rw [contractPrice_of_subset cost Sat Q hevQ hSQ,
      contractPrice_of_subset cost Sat Q hevQ Finset.Subset.rfl]
  norm_cast

/-- Canonical Möbius zero-cut criterion for the original contract-relative price. -/
theorem setPrice_eq_full_iff_canonical_relative_zero_cut
    {A : Type u} {Req : Type v} [DecidableEq Req]
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q)
    {S : Finset Req} (hSQ : S ⊆ Q) :
    SetPrice cost Sat S
        (subset_feasible_of_full cost Sat hSQ hevQ) =
      SetPrice cost Sat Q hevQ ↔
    RelativeOmittedMass
      (CanonicalCoeff (ContractPrice cost Sat Q hevQ)) Q S = 0 := by
  rw [← contractPrice_eq_full_iff_setPrice_eq_full cost Sat Q hevQ hSQ]
  exact represented_full_price_iff_relative_zero_cut
    (ContractPrice cost Sat Q hevQ)
    (CanonicalCoeff (ContractPrice cost Sat Q hevQ))
    (canonicalCoeff_represents (ContractPrice cost Sat Q hevQ)) hSQ

/-- There is a canonical zero-cut of size `n` inside the declared contract. -/
def HasCanonicalZeroCutOfSize
    {A : Type u} {Req : Type v} [DecidableEq Req]
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q)
    (n : Nat) : Prop :=
  ∃ S : Finset Req,
    S ⊆ Q ∧ S.card = n ∧
    RelativeOmittedMass
      (CanonicalCoeff (ContractPrice cost Sat Q hevQ)) Q S = 0

/-- At every cardinality, the old subcritical obstruction predicate and the new
canonical zero-cut predicate are exactly the same predicate. -/
theorem subcritical_obstruction_iff_canonical_zero_cut
    {A : Type u} {Req : Type v} [DecidableEq Req]
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q)
    (n : Nat) :
    HasSubcriticalObstructionOfSize
      cost Sat Q (SetPrice cost Sat Q hevQ) n ↔
    HasCanonicalZeroCutOfSize cost Sat Q hevQ n := by
  constructor
  · rintro ⟨S, hSQ, hcard, hnot⟩
    refine ⟨S, hSQ, hcard, ?_⟩
    have hprice :=
      (not_subcriticalFace_iff_subset_price_eq_full cost Sat hSQ hevQ).1 hnot
    exact
      (setPrice_eq_full_iff_canonical_relative_zero_cut
        cost Sat Q hevQ hSQ).1 hprice
  · rintro ⟨S, hSQ, hcard, hzero⟩
    refine ⟨S, hSQ, hcard, ?_⟩
    have hprice :=
      (setPrice_eq_full_iff_canonical_relative_zero_cut
        cost Sat Q hevQ hSQ).2 hzero
    exact
      (not_subcriticalFace_iff_subset_price_eq_full cost Sat hSQ hevQ).2 hprice

/-- A canonical zero-cut always exists: the full contract itself omits no
interaction mass. -/
theorem exists_canonical_zero_cut
    {A : Type u} {Req : Type v} [DecidableEq Req]
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    ∃ n, HasCanonicalZeroCutOfSize cost Sat Q hevQ n := by
  refine ⟨Q.card, Q, Finset.Subset.rfl, rfl, ?_⟩
  simp [RelativeOmittedMass]

/-- Canonical zero-cut depth: the least coalition cardinality whose omitted
canonical Möbius mass is zero relative to `Q`. -/
noncomputable def CanonicalZeroCutDepth
    {A : Type u} {Req : Type v} [DecidableEq Req]
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) : Nat := by
  classical
  exact Nat.find (exists_canonical_zero_cut cost Sat Q hevQ)

/-- The canonical zero-cut depth is attained. -/
theorem canonicalZeroCutDepth_spec
    {A : Type u} {Req : Type v} [DecidableEq Req]
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    HasCanonicalZeroCutOfSize cost Sat Q hevQ
      (CanonicalZeroCutDepth cost Sat Q hevQ) := by
  classical
  exact Nat.find_spec (exists_canonical_zero_cut cost Sat Q hevQ)

/-- Exact bridge: the historical INSACERMO hidden price depth is identical to
the least canonical Möbius zero-cut depth. -/
theorem hiddenPriceDepth_eq_canonicalZeroCutDepth
    {A : Type u} {Req : Type v} [DecidableEq Req]
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    HiddenPriceDepth cost Sat Q hevQ =
      CanonicalZeroCutDepth cost Sat Q hevQ := by
  apply Nat.le_antisymm
  · unfold HiddenPriceDepth
    apply Nat.find_min' (exists_subcritical_obstruction cost Sat Q hevQ)
    exact
      (subcritical_obstruction_iff_canonical_zero_cut
        cost Sat Q hevQ (CanonicalZeroCutDepth cost Sat Q hevQ)).2
        (canonicalZeroCutDepth_spec cost Sat Q hevQ)
  · unfold CanonicalZeroCutDepth
    apply Nat.find_min' (exists_canonical_zero_cut cost Sat Q hevQ)
    exact
      (subcritical_obstruction_iff_canonical_zero_cut
        cost Sat Q hevQ (HiddenPriceDepth cost Sat Q hevQ)).1
        (hiddenPriceDepth_spec cost Sat Q hevQ)

/-- HIDDEN DEPTH ↔ MÖBIUS ZERO-CUT BRIDGE KERNEL V1.

The old contract-relative hidden price depth and the new canonical interaction
geometry are not merely analogous: they minimize equivalent predicates at every
cardinality. Therefore the historical `HiddenPriceDepth` is exactly the minimum
size of a coalition with zero omitted canonical Möbius mass relative to `Q`. -/
theorem hidden_depth_mobius_bridge_v1
    {A : Type u} {Req : Type v} [DecidableEq Req]
    (cost : A → Nat) (Sat : A → Req → Prop)
    (Q : Finset Req) (hevQ : SetFeasible cost Sat Q) :
    HiddenPriceDepth cost Sat Q hevQ =
      CanonicalZeroCutDepth cost Sat Q hevQ ∧
    (∀ S : Finset Req, ∀ hSQ : S ⊆ Q,
      (SetPrice cost Sat S
          (subset_feasible_of_full cost Sat hSQ hevQ) =
        SetPrice cost Sat Q hevQ ↔
       RelativeOmittedMass
         (CanonicalCoeff (ContractPrice cost Sat Q hevQ)) Q S = 0)) := by
  constructor
  · exact hiddenPriceDepth_eq_canonicalZeroCutDepth cost Sat Q hevQ
  · intro S hSQ
    exact setPrice_eq_full_iff_canonical_relative_zero_cut
      cost Sat Q hevQ hSQ

end InsacermoHiddenDepthMobiusBridge
