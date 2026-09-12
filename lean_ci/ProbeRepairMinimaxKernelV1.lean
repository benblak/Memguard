import Mathlib
import ProbeRepairRealizationKernelV1

namespace InsacermoProbeRepairMinimax

/-!
INSACERMO Probe–Repair Minimax Kernel V1.

No new INSACERMO law is introduced here.  This file derives a sequential property of the
existing CONTRACT -> ACTIONABILITY -> PLANNER architecture.

Part I gives a concrete hidden-vector realization.  A world with k remaining stages is a Boolean
vector `Fin k -> Bool`.  At a nonterminal stage only the head bit is observable.  A repair is safe
exactly when it matches that head bit.  After the matched repair, the head is discarded and the
set of possible tails is again the full `(k-1)`-stage world space.

Part II studies the exact role-level sufficient state induced by those belief sets.  Unlike the
previous quotient kernel, redundant probes ARE allowed after information is already available.
Thus alternation is not hard-coded as the only executable trace.  Instead we prove:

* every safe winning trace from k unresolved stages has length at least 2k;
* the canonical (PROBE,REPAIR)^k trace has length exactly 2k and wins;
* every optimal trace is exactly that canonical role trace;
* therefore every optimal trace has exactly 2k-1 role changes for k>0.

This is the formal minimax/optimal-policy version of the probe-repair alternation result.
-/

open Set

/-! ## I. Concrete hidden-vector realization -/

abbrev Hidden (k : Nat) := Fin k → Bool

def head {k : Nat} (w : Hidden (k + 1)) : Bool := w 0

def tail {k : Nat} (w : Hidden (k + 1)) : Hidden k := fun i => w i.succ

def prepend {k : Nat} (b : Bool) (t : Hidden k) : Hidden (k + 1) :=
  Fin.cases b t

@[simp] theorem head_prepend {k : Nat} (b : Bool) (t : Hidden k) :
    head (prepend b t) = b := by
  rfl

@[simp] theorem tail_prepend {k : Nat} (b : Bool) (t : Hidden k) :
    tail (prepend b t) = t := by
  funext i
  rfl

def unresolvedBelief (k : Nat) : Set (Hidden k) := Set.univ

def posteriorBelief (k : Nat) (b : Bool) : Set (Hidden (k + 1)) :=
  {w | head w = b}

def CommonSafeRepair {k : Nat} (F : Set (Hidden (k + 1))) : Prop :=
  ∃ r : Bool, ∀ w, w ∈ F → head w = r

/-- A genuinely unresolved nonterminal stage has no common safe repair. -/
theorem unresolved_no_common_repair (k : Nat) :
    ¬ CommonSafeRepair (unresolvedBelief (k + 1)) := by
  intro h
  rcases h with ⟨r, hr⟩
  let z : Hidden k := fun _ => false
  have h0 : head (prepend false z) = r := hr (prepend false z) (by simp [unresolvedBelief])
  have h1 : head (prepend true z) = r := hr (prepend true z) (by simp [unresolvedBelief])
  simp at h0 h1
  cases r <;> simp_all

/-- Once the probe reports b, b itself is a common safe repair. -/
theorem posterior_has_common_repair (k : Nat) (b : Bool) :
    CommonSafeRepair (posteriorBelief k b) := by
  refine ⟨b, ?_⟩
  intro w hw
  exact hw

/-- The repair enabled by the posterior is unique. -/
theorem posterior_unique_repair (k : Nat) (b r : Bool)
    (h : ∀ w, w ∈ posteriorBelief k b → head w = r) : r = b := by
  let z : Hidden k := fun _ => false
  have hz : head (prepend b z) = r := h (prepend b z) (by simp [posteriorBelief])
  simpa using hz.symm

def afterRepairBelief (k : Nat) (b : Bool) : Set (Hidden k) :=
  tail '' posteriorBelief k b

/-- Critical recursive closure: after the matched repair, every future tail is again possible. -/
theorem after_repair_is_fresh_unresolved (k : Nat) (b : Bool) :
    afterRepairBelief k b = unresolvedBelief k := by
  ext t
  constructor
  · intro _
    simp [unresolvedBelief]
  · intro _
    refine ⟨prepend b t, ?_, ?_⟩
    · simp [posteriorBelief]
    · simp [tail_prepend]

/-- One concrete semantic stage: obstruction -> probe posterior -> unique safe repair -> fresh tail. -/
theorem hidden_stage_closure (k : Nat) :
    (¬ CommonSafeRepair (unresolvedBelief (k + 1))) ∧
    (∀ b : Bool, CommonSafeRepair (posteriorBelief k b)) ∧
    (∀ b : Bool, afterRepairBelief k b = unresolvedBelief k) := by
  exact ⟨unresolved_no_common_repair k,
    posterior_has_common_repair k,
    after_repair_is_fresh_unresolved k⟩

/-! ## II. Optimal planner on the exact two-phase sufficient state -/

inductive Role
  | probe
  | repair
  deriving DecidableEq, Repr

open Role

structure PlannerState where
  remaining : Nat
  informed : Bool
  deriving DecidableEq, Repr

/-- Role dynamics justified by the concrete belief semantics above.  Redundant probes are legal. -/
def step : PlannerState → Role → Option PlannerState
  | ⟨0, _⟩, _ => none
  | ⟨n + 1, _⟩, probe => some ⟨n + 1, true⟩
  | ⟨n + 1, false⟩, repair => none
  | ⟨n + 1, true⟩, repair => some ⟨n, false⟩

def run : PlannerState → List Role → Option PlannerState
  | s, [] => some s
  | s, a :: xs =>
      match step s a with
      | none => none
      | some s' => run s' xs

def initial (k : Nat) : PlannerState := ⟨k, false⟩
def goal : PlannerState := ⟨0, false⟩

/-- Remaining unavoidable unit-cost work. -/
def need : PlannerState → Nat
  | ⟨0, _⟩ => 0
  | ⟨n + 1, false⟩ => 2 * (n + 1)
  | ⟨n + 1, true⟩ => 2 * n + 1

/-- Every legal one-step transition can reduce `need` by at most one. -/
theorem need_le_succ_need_of_step {s s' : PlannerState} {a : Role}
    (h : step s a = some s') : need s ≤ need s' + 1 := by
  rcases s with ⟨n, info⟩
  cases n with
  | zero =>
      simp [step] at h
  | succ n =>
      cases info with
      | false =>
          cases a with
          | probe =>
              simp [step] at h
              subst s'
              simp [need]
              omega
          | repair =>
              simp [step] at h
      | true =>
          cases a with
          | probe =>
              simp [step] at h
              subst s'
              simp [need]
          | repair =>
              simp [step] at h
              subst s'
              cases n <;> simp [need] <;> omega

/-- Any trace reaching the contract goal must pay at least the current potential. -/
theorem need_le_length_of_winning_trace {s : PlannerState} {xs : List Role}
    (h : run s xs = some goal) : need s ≤ xs.length := by
  induction xs generalizing s with
  | nil =>
      simp [run] at h
      subst s
      simp [need, goal]
  | cons a xs ih =>
      cases hs : step s a with
      | none =>
          simp [run, hs] at h
      | some s' =>
          have hrest : run s' xs = some goal := by
            simpa [run, hs] using h
          have hstep := need_le_succ_need_of_step hs
          have htail := ih hrest
          simp
          omega

@[simp] theorem need_initial (k : Nat) : need (initial k) = 2 * k := by
  cases k <;> rfl

def canonical : Nat → List Role
  | 0 => []
  | k + 1 => probe :: repair :: canonical k

/-- Canonical execution closes all stages. -/
theorem canonical_wins (k : Nat) : run (initial k) (canonical k) = some goal := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change run (initial k) (canonical k) = some goal
      exact ih

@[simp] theorem canonical_length (k : Nat) : (canonical k).length = 2 * k := by
  induction k with
  | zero => simp [canonical]
  | succ k ih =>
      simp [canonical, ih]
      omega

/-- Minimax lower bound: every safe winning trace has cost at least 2k. -/
theorem winning_length_lower_bound (k : Nat) (xs : List Role)
    (h : run (initial k) xs = some goal) : 2 * k ≤ xs.length := by
  have hp := need_le_length_of_winning_trace h
  simpa using hp

def OptimalCost (k c : Nat) : Prop :=
  (∃ xs : List Role, run (initial k) xs = some goal ∧ xs.length = c) ∧
  (∀ xs : List Role, run (initial k) xs = some goal → c ≤ xs.length)

/-- Main minimax value theorem: V_k = 2k. -/
theorem optimal_cost_eq_two_mul (k : Nat) : OptimalCost k (2 * k) := by
  constructor
  · exact ⟨canonical k, canonical_wins k, canonical_length k⟩
  · intro xs h
    exact winning_length_lower_bound k xs h

/-- Every optimal role trace is exactly (PROBE,REPAIR)^k. -/
theorem optimal_trace_eq_canonical (k : Nat) (xs : List Role)
    (hwin : run (initial k) xs = some goal)
    (hlen : xs.length = 2 * k) : xs = canonical k := by
  induction k generalizing xs with
  | zero =>
      cases xs with
      | nil => rfl
      | cons a ys =>
          simp at hlen
  | succ k ih =>
      cases xs with
      | nil =>
          simp at hlen
      | cons a ys =>
          cases a with
          | repair =>
              simp [run, initial, step] at hwin
          | probe =>
              cases ys with
              | nil =>
                  simp at hlen
                  omega
              | cons b zs =>
                  have hlen' : zs.length + 2 = 2 * (k + 1) := by
                    simpa using hlen
                  cases b with
                  | probe =>
                      have hzwin : run ⟨k + 1, true⟩ zs = some goal := by
                        simpa [run, initial, step] using hwin
                      have hlow := need_le_length_of_winning_trace hzwin
                      have hneed : need ⟨k + 1, true⟩ = 2 * k + 1 := by
                        rfl
                      have hlenz : zs.length = 2 * k := by
                        omega
                      rw [hneed] at hlow
                      omega
                  | repair =>
                      have hzwin : run (initial k) zs = some goal := by
                        simpa [run, initial, step] using hwin
                      have hlenz : zs.length = 2 * k := by
                        omega
                      have hz : zs = canonical k := ih zs hzwin hlenz
                      simp [canonical, hz]

/-- Count adjacent changes of role. -/
def roleChanges : List Role → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: xs => (if a = b then 0 else 1) + roleChanges (b :: xs)

/-- Prefixing REPAIR to a nonempty canonical trace creates exactly one new role change. -/
theorem role_changes_repair_cons_canonical (k : Nat) :
    roleChanges (repair :: canonical k) =
      if k = 0 then 0 else 1 + roleChanges (canonical k) := by
  cases k with
  | zero => simp [canonical, roleChanges]
  | succ k => simp [canonical, roleChanges]

/-- Canonical optimal traces change role at every boundary. -/
theorem role_changes_canonical (k : Nat) :
    roleChanges (canonical k) = if k = 0 then 0 else 2 * k - 1 := by
  induction k with
  | zero => simp [canonical, roleChanges]
  | succ k ih =>
      rw [show canonical (k + 1) = probe :: repair :: canonical k by rfl]
      simp only [roleChanges]
      simp [role_changes_repair_cons_canonical, ih]
      by_cases hk : k = 0
      · subst k
        simp
      · simp [hk]
        omega

/-- Interaction-depth theorem for optimal policies: A_k = 2k-1 when k>0. -/
theorem optimal_trace_role_changes (k : Nat) (xs : List Role)
    (hk : 0 < k)
    (hwin : run (initial k) xs = some goal)
    (hlen : xs.length = 2 * k) :
    roleChanges xs = 2 * k - 1 := by
  rw [optimal_trace_eq_canonical k xs hwin hlen, role_changes_canonical]
  simp [Nat.ne_of_gt hk]

/-- Unbounded interaction depth across the concrete hidden-vector family. -/
theorem unbounded_optimal_interaction_depth (K : Nat) :
    ∃ k : Nat, 0 < k ∧
      ∃ xs : List Role,
        run (initial k) xs = some goal ∧
        xs.length = 2 * k ∧
        K < roleChanges xs := by
  let k := K + 1
  refine ⟨k, by dsimp [k]; omega, canonical k, canonical_wins k, canonical_length k, ?_⟩
  have hc : roleChanges (canonical k) = 2 * k - 1 :=
    optimal_trace_role_changes k (canonical k) (by dsimp [k]; omega)
      (canonical_wins k) (canonical_length k)
  rw [hc]
  dsimp [k]
  omega

/-- Consolidated theorem: the semantic gadget recurs on hidden tails, while its induced optimal
planner has value 2k. -/
theorem hidden_vector_probe_repair_minimax (k : Nat) :
    (∀ n : Nat,
      (¬ CommonSafeRepair (unresolvedBelief (n + 1))) ∧
      (∀ b : Bool, CommonSafeRepair (posteriorBelief n b)) ∧
      (∀ b : Bool, afterRepairBelief n b = unresolvedBelief n)) ∧
    OptimalCost k (2 * k) := by
  constructor
  · intro n
    exact hidden_stage_closure n
  · exact optimal_cost_eq_two_mul k

end InsacermoProbeRepairMinimax
