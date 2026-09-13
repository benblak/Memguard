import Mathlib
import RobustFuturePriceKernelV1
import TwoClockKernelV1

namespace InsacermoCausalPriceFactorization

open Set
open InsacermoRobustRightToForget
open InsacermoRobustFuturePrice
open InsacermoTwoClock

universe u v w z u₁ u₂

/-! # Abstract minimum-price geometry -/

section AbstractPrice

variable {A : Type u}

/-- Budget B can buy property Good when some intervention of cost at most B satisfies it. -/
def Affordable (cost : A → Nat) (Good : A → Prop) (B : Nat) : Prop :=
  ∃ a, cost a ≤ B ∧ Good a

/-- A property is feasible when some finite budget buys it. -/
def Feasible (cost : A → Nat) (Good : A → Prop) : Prop :=
  ∃ B, Affordable cost Good B

/-- Minimum budget buying a feasible intervention property. -/
noncomputable def Price
    (cost : A → Nat) (Good : A → Prop)
    (hev : Feasible cost Good) : Nat := by
  classical
  exact Nat.find hev

/-- The minimum price is itself affordable. -/
theorem price_affordable
    (cost : A → Nat) (Good : A → Prop)
    (hev : Feasible cost Good) :
    Affordable cost Good (Price cost Good hev) := by
  classical
  exact Nat.find_spec hev

/-- Every affordable budget is at least the minimum price. -/
theorem price_minimal
    (cost : A → Nat) (Good : A → Prop)
    (hev : Feasible cost Good)
    {B : Nat} (hB : Affordable cost Good B) :
    Price cost Good hev ≤ B := by
  classical
  exact Nat.find_min' hev hB

/-- A feasible property has an intervention attaining exactly the minimum price. -/
theorem exists_price_attainer
    (cost : A → Nat) (Good : A → Prop)
    (hev : Feasible cost Good) :
    ∃ a, cost a = Price cost Good hev ∧ Good a := by
  rcases price_affordable cost Good hev with ⟨a, hcost, hgood⟩
  have hmin : Price cost Good hev ≤ cost a := by
    apply price_minimal cost Good hev
    exact ⟨a, le_rfl, hgood⟩
  exact ⟨a, Nat.le_antisymm hcost hmin, hgood⟩

/-- Joint causal repair means satisfying both component obligations with the same intervention. -/
def JointGood (GoodV GoodD : A → Prop) (a : A) : Prop :=
  GoodV a ∧ GoodD a

/-- A joint-safe price dominates the viability-component price. -/
theorem viability_price_le_joint_price
    (cost : A → Nat) (GoodV GoodD : A → Prop)
    (hevV : Feasible cost GoodV)
    (hevJ : Feasible cost (JointGood GoodV GoodD)) :
    Price cost GoodV hevV ≤ Price cost (JointGood GoodV GoodD) hevJ := by
  apply price_minimal cost GoodV hevV
  rcases price_affordable cost (JointGood GoodV GoodD) hevJ with
    ⟨a, hcost, hgood⟩
  exact ⟨a, hcost, hgood.1⟩

/-- A joint-safe price dominates the destruction-component price. -/
theorem destruction_price_le_joint_price
    (cost : A → Nat) (GoodV GoodD : A → Prop)
    (hevD : Feasible cost GoodD)
    (hevJ : Feasible cost (JointGood GoodV GoodD)) :
    Price cost GoodD hevD ≤ Price cost (JointGood GoodV GoodD) hevJ := by
  apply price_minimal cost GoodD hevD
  rcases price_affordable cost (JointGood GoodV GoodD) hevJ with
    ⟨a, hcost, hgood⟩
  exact ⟨a, hcost, hgood.2⟩

/-- Universal lower bound: joint future price is at least the larger marginal price. -/
theorem max_component_price_le_joint_price
    (cost : A → Nat) (GoodV GoodD : A → Prop)
    (hevV : Feasible cost GoodV)
    (hevD : Feasible cost GoodD)
    (hevJ : Feasible cost (JointGood GoodV GoodD)) :
    max (Price cost GoodV hevV) (Price cost GoodD hevD) ≤
      Price cost (JointGood GoodV GoodD) hevJ := by
  exact max_le
    (viability_price_le_joint_price cost GoodV GoodD hevV hevJ)
    (destruction_price_le_joint_price cost GoodV GoodD hevD hevJ)

end AbstractPrice

/-! # Exact factorization under product-separable interventions -/

section ProductFactorization

variable {AV : Type u₁} {AD : Type u₂}

/-- Additive cost for independent viability and destruction coordinates. -/
def ProductCost (costV : AV → Nat) (costD : AD → Nat) : AV × AD → Nat :=
  fun a => costV a.1 + costD a.2

/-- Product-separable success: each coordinate satisfies only its own component. -/
def ProductGood (GoodV : AV → Prop) (GoodD : AD → Prop) : AV × AD → Prop :=
  fun a => GoodV a.1 ∧ GoodD a.2

/-- Separate feasibility implies feasibility of the product repair. -/
theorem product_feasible
    (costV : AV → Nat) (costD : AD → Nat)
    (GoodV : AV → Prop) (GoodD : AD → Prop)
    (hevV : Feasible costV GoodV)
    (hevD : Feasible costD GoodD) :
    Feasible (ProductCost costV costD) (ProductGood GoodV GoodD) := by
  rcases hevV with ⟨BV, v, hcv, hgv⟩
  rcases hevD with ⟨BD, d, hcd, hgd⟩
  refine ⟨BV + BD, (v, d), ?_, ?_⟩
  · exact Nat.add_le_add hcv hcd
  · exact ⟨hgv, hgd⟩

/-- Exact price factorization theorem.
If interventions genuinely factor as independent coordinates, their costs add, and success is
coordinatewise, then and only then at this structural level the joint minimum equals the sum
of the two marginal minima. -/
theorem product_price_factorizes
    (costV : AV → Nat) (costD : AD → Nat)
    (GoodV : AV → Prop) (GoodD : AD → Prop)
    (hevV : Feasible costV GoodV)
    (hevD : Feasible costD GoodD) :
    Price (ProductCost costV costD) (ProductGood GoodV GoodD)
        (product_feasible costV costD GoodV GoodD hevV hevD) =
      Price costV GoodV hevV + Price costD GoodD hevD := by
  apply Nat.le_antisymm
  · apply price_minimal
    rcases exists_price_attainer costV GoodV hevV with ⟨v, hcv, hgv⟩
    rcases exists_price_attainer costD GoodD hevD with ⟨d, hcd, hgd⟩
    refine ⟨(v, d), ?_, ?_⟩
    · simp [ProductCost, hcv, hcd]
    · exact ⟨hgv, hgd⟩
  · rcases price_affordable
      (ProductCost costV costD) (ProductGood GoodV GoodD)
      (product_feasible costV costD GoodV GoodD hevV hevD) with
      ⟨a, hcost, hgood⟩
    have hvmin : Price costV GoodV hevV ≤ costV a.1 := by
      apply price_minimal costV GoodV hevV
      exact ⟨a.1, le_rfl, hgood.1⟩
    have hdmin : Price costD GoodD hevD ≤ costD a.2 := by
      apply price_minimal costD GoodD hevD
      exact ⟨a.2, le_rfl, hgood.2⟩
    have hsum :
        Price costV GoodV hevV + Price costD GoodD hevD ≤
          costV a.1 + costD a.2 := Nat.add_le_add hvmin hdmin
    exact le_trans hsum hcost

end ProductFactorization

/-! # A single exact family spanning synergy, additivity, and conflict -/

section CouplingWitness

inductive CouplingRepair
  | viabilityOnly
  | destructionOnly
  | joint
  deriving DecidableEq, Repr

open CouplingRepair

/-- Marginal repairs cost K; the only repair satisfying both components costs M. -/
def couplingCost (K M : Nat) : CouplingRepair → Nat
  | viabilityOnly => K
  | destructionOnly => K
  | joint => M

/-- Viability can be repaired either directly or by the joint intervention. -/
def CouplingVGood : CouplingRepair → Prop
  | viabilityOnly => True
  | destructionOnly => False
  | joint => True

/-- Destruction debt can be repaired either directly or by the joint intervention. -/
def CouplingDGood : CouplingRepair → Prop
  | viabilityOnly => False
  | destructionOnly => True
  | joint => True

theorem coupling_v_feasible (K M : Nat) :
    Feasible (couplingCost K M) CouplingVGood := by
  exact ⟨K, viabilityOnly, le_rfl, by simp [CouplingVGood]⟩

theorem coupling_d_feasible (K M : Nat) :
    Feasible (couplingCost K M) CouplingDGood := by
  exact ⟨K, destructionOnly, le_rfl, by simp [CouplingDGood]⟩

theorem coupling_joint_feasible (K M : Nat) :
    Feasible (couplingCost K M) (JointGood CouplingVGood CouplingDGood) := by
  exact ⟨M, joint, le_rfl, by simp [JointGood, CouplingVGood, CouplingDGood]⟩

/-- If the joint repair is no cheaper than a marginal repair, the viability marginal price is K. -/
theorem coupling_v_price_eq
    (K M : Nat) (hKM : K ≤ M) :
    Price (couplingCost K M) CouplingVGood (coupling_v_feasible K M) = K := by
  apply Nat.le_antisymm
  · apply price_minimal
    exact ⟨viabilityOnly, le_rfl, by simp [CouplingVGood]⟩
  · rcases price_affordable
      (couplingCost K M) CouplingVGood (coupling_v_feasible K M) with
      ⟨a, hcost, hgood⟩
    cases a with
    | viabilityOnly => simpa [couplingCost] using hcost
    | destructionOnly => simp [CouplingVGood] at hgood
    | joint =>
        have hMP : M ≤ Price (couplingCost K M) CouplingVGood
            (coupling_v_feasible K M) := by
          simpa [couplingCost] using hcost
        exact le_trans hKM hMP

/-- Symmetric destruction marginal price. -/
theorem coupling_d_price_eq
    (K M : Nat) (hKM : K ≤ M) :
    Price (couplingCost K M) CouplingDGood (coupling_d_feasible K M) = K := by
  apply Nat.le_antisymm
  · apply price_minimal
    exact ⟨destructionOnly, le_rfl, by simp [CouplingDGood]⟩
  · rcases price_affordable
      (couplingCost K M) CouplingDGood (coupling_d_feasible K M) with
      ⟨a, hcost, hgood⟩
    cases a with
    | viabilityOnly => simp [CouplingDGood] at hgood
    | destructionOnly => simpa [couplingCost] using hcost
    | joint =>
        have hMP : M ≤ Price (couplingCost K M) CouplingDGood
            (coupling_d_feasible K M) := by
          simpa [couplingCost] using hcost
        exact le_trans hKM hMP

/-- The joint price is exactly M because only `joint` satisfies both components. -/
theorem coupling_joint_price_eq (K M : Nat) :
    Price (couplingCost K M) (JointGood CouplingVGood CouplingDGood)
      (coupling_joint_feasible K M) = M := by
  apply Nat.le_antisymm
  · apply price_minimal
    exact ⟨joint, le_rfl, by simp [JointGood, CouplingVGood, CouplingDGood]⟩
  · rcases price_affordable
      (couplingCost K M) (JointGood CouplingVGood CouplingDGood)
      (coupling_joint_feasible K M) with ⟨a, hcost, hgood⟩
    have ha : a = joint := by
      cases a <;> simp [JointGood, CouplingVGood, CouplingDGood] at hgood ⊢
    subst a
    simpa [couplingCost] using hcost

/-- Same two marginal prices K, but an arbitrary joint price M ≥ K.
Thus marginal prices do not determine the joint future price. -/
theorem same_marginals_arbitrary_joint
    (K M : Nat) (hKM : K ≤ M) :
    Price (couplingCost K M) CouplingVGood (coupling_v_feasible K M) = K ∧
    Price (couplingCost K M) CouplingDGood (coupling_d_feasible K M) = K ∧
    Price (couplingCost K M) (JointGood CouplingVGood CouplingDGood)
      (coupling_joint_feasible K M) = M := by
  exact ⟨coupling_v_price_eq K M hKM,
    coupling_d_price_eq K M hKM,
    coupling_joint_price_eq K M⟩

/-- Even with both marginal prices fixed at one, the joint price is unbounded. -/
theorem fixed_unit_marginals_unbounded_joint (N : Nat) :
    ∃ M,
      N < M ∧
      Price (couplingCost 1 M) CouplingVGood (coupling_v_feasible 1 M) = 1 ∧
      Price (couplingCost 1 M) CouplingDGood (coupling_d_feasible 1 M) = 1 ∧
      Price (couplingCost 1 M) (JointGood CouplingVGood CouplingDGood)
        (coupling_joint_feasible 1 M) = M := by
  refine ⟨N + 1, by omega, ?_, ?_, ?_⟩
  · exact coupling_v_price_eq 1 (N + 1) (by omega)
  · exact coupling_d_price_eq 1 (N + 1) (by omega)
  · exact coupling_joint_price_eq 1 (N + 1)

/-- Signed departure from naive additive factorization. -/
def SignedInteraction (jointPrice viabilityPrice destructionPrice : Nat) : Int :=
  (jointPrice : Int) - (viabilityPrice : Int) - (destructionPrice : Int)

/-- In the exact coupling family, the interaction term is M - 2K.
Hence the same construction contains synergistic (M<2K), additive (M=2K), and
conflict/coordination-premium (M>2K) regimes. -/
theorem coupling_signed_interaction
    (K M : Nat) (hKM : K ≤ M) :
    SignedInteraction
      (Price (couplingCost K M) (JointGood CouplingVGood CouplingDGood)
        (coupling_joint_feasible K M))
      (Price (couplingCost K M) CouplingVGood (coupling_v_feasible K M))
      (Price (couplingCost K M) CouplingDGood (coupling_d_feasible K M)) =
      (M : Int) - 2 * (K : Int) := by
  rw [coupling_joint_price_eq K M,
      coupling_v_price_eq K M hKM,
      coupling_d_price_eq K M hKM]
  simp [SignedInteraction]
  ring

end CouplingWitness

/-! # Bridge back to robust future price -/

section FuturePriceBridge

variable {State : Type u} {Req : Type v} {Cap : Type w} {Intervention : Type z}

/-- Destruction debt after applying the same intervention to source and destroyed state. -/
def IntervenedDebtAt
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (d : State → State) (x : State)
    (a : Intervention) (h : Nat) : Prop :=
  ∃ c q,
    c ∈ C h ∧ q ∈ Γ h ∧
    Win (apply a x) c q ∧ ¬ Win (apply a (d x)) c q

/-- Source viability component through H. -/
def SourceSafeThrough
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (x : State) (a : Intervention) (H : Nat) : Prop :=
  ∀ h, h ≤ H → ViableAt Win Γ C (apply a x) h

/-- Destruction-debt component through H. -/
def DebtFreeThrough
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (d : State → State) (x : State)
    (a : Intervention) (H : Nat) : Prop :=
  ∀ h, h ≤ H → ¬ IntervenedDebtAt Win Γ C apply d x a h

/-- At one horizon, intervened robust safety is exactly source viability plus absence of
intervened destruction debt. -/
theorem intervenedSafe_iff_source_and_noDebt
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (d : State → State) (x : State)
    (a : Intervention) (h : Nat) :
    IntervenedSafeAt Win Γ C apply d x a h ↔
      ViableAt Win Γ C (apply a x) h ∧
      ¬ IntervenedDebtAt Win Γ C apply d x a h := by
  constructor
  · rintro ⟨hsrc, htgt⟩
    refine ⟨hsrc, ?_⟩
    rintro ⟨c, q, hc, hq, hx, hnot⟩
    exact hnot (htgt c hc q hq)
  · rintro ⟨hsrc, hnodebt⟩
    refine ⟨hsrc, ?_⟩
    intro c hc q hq
    by_contra hnot
    exact hnodebt ⟨c, q, hc, hq, hsrc c hc q hq, hnot⟩

/-- Through a horizon, robust future safety is an exact intersection of two intervention
properties: keeping the source viable and keeping destruction debt absent. -/
theorem safeThrough_iff_sourceSafe_and_debtFree
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (d : State → State) (x : State)
    (a : Intervention) (H : Nat) :
    SafeThrough Win Γ C apply d x a H ↔
      SourceSafeThrough Win Γ C apply x a H ∧
      DebtFreeThrough Win Γ C apply d x a H := by
  constructor
  · intro hs
    constructor
    · intro h hh
      exact (hs h hh).1
    · intro h hh
      exact (intervenedSafe_iff_source_and_noDebt
        Win Γ C apply d x a h).mp (hs h hh) |>.2
  · rintro ⟨hsrc, hdebt⟩
    intro h hh
    apply (intervenedSafe_iff_source_and_noDebt Win Γ C apply d x a h).mpr
    exact ⟨hsrc h hh, hdebt h hh⟩

/-- The actual robust FuturePrice dominates both causal component prices.
This is the direct bridge from the abstract intersection geometry back to the certified
future-price model. -/
theorem max_causal_component_price_le_futurePrice
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    (H : Nat)
    (hevS : Feasible cost (fun a => SourceSafeThrough Win Γ C apply x a H))
    (hevD : Feasible cost (fun a => DebtFreeThrough Win Γ C apply d x a H))
    (hevR : FeasibleThrough Win Γ C apply cost d x H) :
    max
      (Price cost (fun a => SourceSafeThrough Win Γ C apply x a H) hevS)
      (Price cost (fun a => DebtFreeThrough Win Γ C apply d x a H) hevD) ≤
    FuturePrice Win Γ C apply cost d x H hevR := by
  rcases futurePrice_affordable Win Γ C apply cost d x H hevR with
    ⟨a, hcost, hsafe⟩
  have hsplit := (safeThrough_iff_sourceSafe_and_debtFree
    Win Γ C apply d x a H).mp hsafe
  have hS :
      Price cost (fun a => SourceSafeThrough Win Γ C apply x a H) hevS ≤
        FuturePrice Win Γ C apply cost d x H hevR := by
    apply price_minimal
    exact ⟨a, hcost, hsplit.1⟩
  have hD :
      Price cost (fun a => DebtFreeThrough Win Γ C apply d x a H) hevD ≤
        FuturePrice Win Γ C apply cost d x H hevR := by
    apply price_minimal
    exact ⟨a, hcost, hsplit.2⟩
  exact max_le hS hD

/-- Consolidated causal-price statement: robust repair is an intersection optimization;
component prices are universal lower bounds; exact additivity requires product-separable
intervention geometry and does not hold from the two-clock decomposition alone. -/
theorem causal_price_factorization_boundary_v1
    (Win : State → Cap → Req → Prop)
    (Γ : Nat → Set Req) (C : Nat → Set Cap)
    (apply : Intervention → State → State)
    (cost : Intervention → Nat)
    (d : State → State) (x : State)
    (H : Nat)
    (hevS : Feasible cost (fun a => SourceSafeThrough Win Γ C apply x a H))
    (hevD : Feasible cost (fun a => DebtFreeThrough Win Γ C apply d x a H))
    (hevR : FeasibleThrough Win Γ C apply cost d x H) :
    (∀ a,
      SafeThrough Win Γ C apply d x a H ↔
        SourceSafeThrough Win Γ C apply x a H ∧
        DebtFreeThrough Win Γ C apply d x a H) ∧
    max
      (Price cost (fun a => SourceSafeThrough Win Γ C apply x a H) hevS)
      (Price cost (fun a => DebtFreeThrough Win Γ C apply d x a H) hevD) ≤
      FuturePrice Win Γ C apply cost d x H hevR := by
  constructor
  · intro a
    exact safeThrough_iff_sourceSafe_and_debtFree Win Γ C apply d x a H
  · exact max_causal_component_price_le_futurePrice
      Win Γ C apply cost d x H hevS hevD hevR

end FuturePriceBridge

end InsacermoCausalPriceFactorization
