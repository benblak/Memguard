import Mathlib

namespace InsacermoRigidityStress

open Finset
open scoped BigOperators

/-- A maximally rigid price law: every coalition price is exactly the sum of
its singleton weights. There are no higher-order interaction terms. -/
def ModularPrice {Req : Type*} [DecidableEq Req]
    (w : Req → Nat) (S : Finset Req) : Nat :=
  ∑ q in S, w q

/-- A time-indexed modular process. The weights may evolve with time, but the
price law remains modular at every time. -/
def ModularProcess {Req : Type*} [DecidableEq Req]
    (w : Nat → Req → Nat) (t : Nat) (S : Finset Req) : Nat :=
  ModularPrice (w t) S

/-- Singleton prices expose the underlying modular weights exactly. -/
theorem modularPrice_singleton {Req : Type*} [DecidableEq Req]
    (w : Req → Nat) (q : Req) :
    ModularPrice w {q} = w q := by
  simp [ModularPrice]

/-- In a modular system, equality on every singleton forces equality on every
coalition. There is no room for a hidden higher-order discrepancy. -/
theorem all_coalitions_equal_of_singletons_equal
    {Req : Type*} [DecidableEq Req]
    (wA wB : Req → Nat)
    (h₁ : ∀ q, ModularPrice wA {q} = ModularPrice wB {q}) :
    ∀ S : Finset Req, ModularPrice wA S = ModularPrice wB S := by
  have hw : ∀ q, wA q = wB q := by
    intro q
    simpa [ModularPrice] using h₁ q
  intro S
  simp [ModularPrice, hw]

/-- Contrapositive form: a global modular discrepancy must already be visible
on at least one singleton. -/
theorem global_divergence_has_singleton_witness
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (wA wB : Req → Nat)
    (hfull : ModularPrice wA Finset.univ ≠ ModularPrice wB Finset.univ) :
    ∃ q : Req, ModularPrice wA {q} ≠ ModularPrice wB {q} := by
  by_contra h
  push_neg at h
  apply hfull
  exact all_coalitions_equal_of_singletons_equal wA wB h Finset.univ

/-- Equality of the complete singleton trace over time forces equality of the
complete coalition-price trace over time, even though the weights themselves
may evolve arbitrarily with time. -/
theorem infinite_full_trace_equal_of_singleton_trace_equal
    {Req : Type*} [DecidableEq Req]
    (wA wB : Nat → Req → Nat)
    (htrace : ∀ t q,
      ModularProcess wA t {q} = ModularProcess wB t {q}) :
    ∀ t, ∀ S : Finset Req,
      ModularProcess wA t S = ModularProcess wB t S := by
  intro t S
  unfold ModularProcess
  exact all_coalitions_equal_of_singletons_equal
    (wA t) (wB t) (fun q => htrace t q) S

/-- Budget safety on the full contract. -/
def GloballyBudgetSafe
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (price : Nat → Finset Req → Nat) (B t : Nat) : Prop :=
  price t Finset.univ ≤ B

/-- Under modularity, identical singleton traces imply identical global safety
judgements for every budget and every time. -/
theorem same_global_safety_of_singleton_trace_equal
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (wA wB : Nat → Req → Nat)
    (htrace : ∀ t q,
      ModularProcess wA t {q} = ModularProcess wB t {q})
    (B t : Nat) :
    GloballyBudgetSafe (ModularProcess wA) B t ↔
      GloballyBudgetSafe (ModularProcess wB) B t := by
  unfold GloballyBudgetSafe
  rw [infinite_full_trace_equal_of_singleton_trace_equal wA wB htrace t Finset.univ]

/-- RIGIDITY STRESS BOUNDARY V1.

For modular price processes, an order-1 local auditor is complete: if two
worlds have the same singleton prices for all time, then they have the same
price for every coalition for all time, the same full-contract price for all
time, and there cannot exist any hidden global divergence.

Thus the No-Local-Auditor / Silent-Future / Dynamical-Hidden-Debt phenomenon
cannot occur inside the purely modular class. Higher-order non-separability is
necessary for that kind of local/global concealment. -/
theorem rigidity_stress_modular_boundary_v1
    {Req : Type*} [Fintype Req] [DecidableEq Req]
    (wA wB : Nat → Req → Nat)
    (htrace : ∀ t q,
      ModularProcess wA t {q} = ModularProcess wB t {q}) :
    (∀ t, ∀ S : Finset Req,
      ModularProcess wA t S = ModularProcess wB t S) ∧
    (∀ t,
      ModularProcess wA t Finset.univ = ModularProcess wB t Finset.univ) ∧
    ¬ (∃ t,
      ModularProcess wA t Finset.univ ≠ ModularProcess wB t Finset.univ) := by
  have hall := infinite_full_trace_equal_of_singleton_trace_equal wA wB htrace
  constructor
  · exact hall
  constructor
  · intro t
    exact hall t Finset.univ
  · push_neg
    intro t
    exact hall t Finset.univ

end InsacermoRigidityStress
