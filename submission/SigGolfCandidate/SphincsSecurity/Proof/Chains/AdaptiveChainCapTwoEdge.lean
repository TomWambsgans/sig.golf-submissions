import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainTwoEdge
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapObservation
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local instance] Classical.propDecidable

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)

include hcharge hreal

theorem realRun_cap_twoEdge_eq :
    Pr[fun result => TwoEdge result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] =
        Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF (State × (Option Result × (Fin (n + 2) → State → Option State))) =>
    Pr[fun result => TwoEdge result.2.2 result.1 | law])
    (realRun_cap_erased_observed auxiliary computation cost budget hcharge hreal)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h

theorem realRun_twoEdge_le_cap_cost (hsmall : budget < Fintype.card State) :
    Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
            (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal) := by
  rw [← realRun_cap_twoEdge_eq auxiliary computation cost budget hcharge hreal]
  have h := realRun_twoEdge_le auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
    budget (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget)
  rw [idealRun_cap_count_expectation auxiliary computation cost budget hcharge hreal hsmall] at h
  exact h

omit hcharge hreal in
def TwoEdgeEvent : {depth : Nat} → (Fin depth → State → Option State) → State → Prop
  | 0, _, _ => False
  | 1, _, _ => False
  | _ + 2, observed, endpoint => TwoEdge observed endpoint

omit hcharge hreal in
theorem realRun_twoEdgeEvent_le_cap_cost {depth : Nat} (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec depth State) Result)
    (cost : Result → Nat) (budget : Nat)
    (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
      result.2 ≤ cost result.1)
    (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
    (hsmall : budget < Fintype.card State) :
    Pr[fun result => TwoEdgeEvent result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
            (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal) := by
  cases depth with
  | zero => simp only [TwoEdgeEvent, probEvent_eq_tsum_ite, if_false, tsum_zero]; exact bot_le
  | succ depth =>
      cases depth with
      | zero => simp only [TwoEdgeEvent, probEvent_eq_tsum_ite, if_false, tsum_zero]; exact bot_le
      | succ depth => exact realRun_twoEdge_le_cap_cost auxiliary computation cost budget hcharge hreal hsmall

omit hcharge hreal in
theorem counted_twoEdge_budget_le_cap
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (budget : Nat) :
    Pr[fun result => TwoEdge result.2.2 result.1 ∧ result.2.1.2 ≤ budget |
      realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none)] ≤
    Pr[fun result => TwoEdge result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
        (fun _ _ => none)] := by
  let observed : Fin (n + 2) → State → Option State := fun _ _ => none
  let p : Option (State × ((Result × Nat) × (Fin (n + 2) → State → Option State))) → Prop :=
    fun opt => ∃ result, opt = some result ∧ TwoEdge result.2.2 result.1
  have hlaw := realRun_cap_finish_counted auxiliary computation observed budget
  have hprob := congrArg (fun law : PMF (Option (State × ((Result × Nat) × (Fin (n + 2) → State → Option State)))) =>
    Pr[p | law]) hlaw
  simp only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] at hprob
  calc
    _ = Pr[fun result => p ((QueryCap.finish budget result.2.1).map
        (fun finished => (result.1, finished, result.2.2))) |
        realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) observed] := by
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
      apply tsum_congr
      intro result
      by_cases hb : result.2.1.2 ≤ budget
      · simp [p, QueryCap.finish, hb, observed]
      · simp [p, QueryCap.finish, hb]
    _ = Pr[fun result => p (result.2.1.map
        (fun finished => (result.1, finished, result.2.2))) |
        realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) observed] := hprob.symm
    _ ≤ _ := by
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hp : p (result.2.1.map (fun finished => (result.1, finished, result.2.2)))
      · have htwo : TwoEdge result.2.2 result.1 := by
          dsimp [p] at hp
          obtain ⟨witness, hw, htwo⟩ := hp
          cases hopt : result.2.1 with
          | none =>
              simp [hopt] at hw
          | some pair =>
              simp [hopt] at hw
              cases hw
              exact htwo
        simp [hp, htwo, observed]
      · simp [hp]

omit hcharge hreal in
theorem counted_twoEdge_budget_le_cap_counted_cost
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (budget : Nat) :
    Pr[fun result => TwoEdge result.2.2 result.1 ∧ result.2.1.2 ≤ budget |
      realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary
            (fun endpoint => QueryCap.counted IsPrefixQuery
              (QueryCap.run IsPrefixQuery (computation endpoint) budget))
            (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  exact (counted_twoEdge_budget_le_cap auxiliary computation budget).trans
    (realRun_twoEdge_le auxiliary
      (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) budget
      (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget))

omit hcharge hreal in
theorem realRun_twoEdge_cost_budget_le_counted
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (cost : Result → Nat) (budget : Nat)
    (hchargeRun : ∀ result ∈
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none)).support, result.2.1.2 ≤ cost result.2.1.1) :
    Pr[fun result => TwoEdge result.2.2 result.1 ∧ cost result.2.1 ≤ budget |
      realRun auxiliary computation (fun _ _ => none)] ≤
    Pr[fun result => TwoEdge result.2.2 result.1 ∧ result.2.1.2 ≤ budget |
      realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none)] := by
  rw [← realRun_counted_forget auxiliary computation (fun _ _ => none)]
  simp only [← PMF.monad_map_eq_map]
  rw [probEvent_map]
  simp only [Function.comp_def, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (realRun auxiliary
      (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
      (fun _ _ => none)).support
  · by_cases hevent : TwoEdge result.2.2 result.1 ∧ cost result.2.1.1 ≤ budget
    · have hcount : result.2.1.2 ≤ budget := (hchargeRun result hr).trans hevent.2
      simp [hevent, hcount]
    · simp [hevent]
  · have hz : (realRun auxiliary
      (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
      (fun _ _ => none)) result = 0 := not_not.mp hr
    simp [hz]

omit hcharge hreal in
theorem realRun_twoEdge_cost_budget_le_cap_counted_cost
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (cost : Result → Nat) (budget : Nat)
    (hchargeRun : ∀ result ∈
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none)).support, result.2.1.2 ≤ cost result.2.1.1) :
    Pr[fun result => TwoEdge result.2.2 result.1 ∧ cost result.2.1 ≤ budget |
      realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary
            (fun endpoint => QueryCap.counted IsPrefixQuery
              (QueryCap.run IsPrefixQuery (computation endpoint) budget))
            (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  exact (realRun_twoEdge_cost_budget_le_counted auxiliary computation cost budget hchargeRun).trans
    (counted_twoEdge_budget_le_cap_counted_cost auxiliary computation budget)

omit hcharge hreal in
theorem idealRun_capped_count_le_budget
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (budget : Nat) (result : State × ((Option (Result × Nat) × Nat) ×
      (Fin (n + 2) → State → Option State)))
    (hr : result ∈ (idealRun auxiliary
      (fun endpoint => QueryCap.counted IsPrefixQuery
        (QueryCap.run IsPrefixQuery (computation endpoint) budget))
      (fun _ _ => none)).support) :
    result.2.1.2 ≤ budget := by
  rw [idealRun, PMF.mem_support_bind_iff] at hr
  obtain ⟨endpoint, _, hr⟩ := hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨output, houtput, rfl⟩ := hr
  exact lazyRun_counted_budget_le (auxiliary endpoint)
    (QueryCap.run IsPrefixQuery (computation endpoint) budget)
    (fun _ _ => none) budget
    (QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget)
    output houtput

omit hcharge hreal in
theorem idealRun_capped_count_expectation_le_budget
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (budget : Nat) :
    (∑' result, idealRun auxiliary
      (fun endpoint => QueryCap.counted IsPrefixQuery
        (QueryCap.run IsPrefixQuery (computation endpoint) budget))
      (fun _ _ => none) result * (result.2.1.2 : ENNReal)) ≤ budget := by
  let law := idealRun auxiliary
    (fun endpoint => QueryCap.counted IsPrefixQuery
      (QueryCap.run IsPrefixQuery (computation endpoint) budget))
    (fun _ _ => none)
  change (∑' result, law result * (result.2.1.2 : ENNReal)) ≤ budget
  calc
    _ ≤ ∑' result, law result * (budget : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ law.support
      · exact mul_le_mul' le_rfl (by exact_mod_cast idealRun_capped_count_le_budget auxiliary computation budget result hr)
      · have hz : law result = 0 := not_not.mp hr
        simp [hz]
    _ = budget := expectation_const law _

omit hcharge hreal in
theorem realRun_twoEdge_cost_budget_le_linear
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (cost : Result → Nat) (budget : Nat)
    (hchargeRun : ∀ result ∈
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none)).support, result.2.1.2 ≤ cost result.2.1.1) :
    Pr[fun result => TwoEdge result.2.2 result.1 ∧ cost result.2.1 ≤ budget |
      realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) * budget := by
  exact (realRun_twoEdge_cost_budget_le_cap_counted_cost
    auxiliary computation cost budget hchargeRun).trans
    (mul_le_mul' le_rfl (idealRun_capped_count_expectation_le_budget auxiliary computation budget))

omit hcharge hreal in
theorem realRun_counted_charge
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (cost : Result → Nat)
    (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
      result.2 ≤ cost result.1)
    (result : State × ((Result × Nat) × (Fin n → State → Option State)))
    (hr : result ∈ (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
      (fun _ _ => none)).support) :
    result.2.1.2 ≤ cost result.2.1.1 := by
  rw [realRun, PMF.mem_support_bind_iff] at hr
  obtain ⟨pair, _, hr⟩ := hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨output, houtput, rfl⟩ := hr
  have hfixed : output.1 ∈ (simulateQ (fixedImpl (auxiliary pair.2) pair.1)
      (QueryCap.counted IsPrefixQuery (computation pair.2))).support := by
    rw [← observedRun_forget (auxiliary pair.2) pair.1
      (QueryCap.counted IsPrefixQuery (computation pair.2)) (fun _ _ => none)]
    exact (PMF.mem_support_map_iff Prod.fst _ _).mpr ⟨output, houtput, rfl⟩
  exact hcharge pair.2 output.1 (QueryCap.simulate_mem_support _ _ output.1 hfixed)

omit hcharge hreal in
theorem realRun_twoEdge_cost_budget_le_linear_of_charge
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (cost : Result → Nat) (budget : Nat)
    (hcharge : ∀ endpoint result,
      result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
        result.2 ≤ cost result.1) :
    Pr[fun result => TwoEdge result.2.2 result.1 ∧ cost result.2.1 ≤ budget |
      realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) * budget := by
  exact realRun_twoEdge_cost_budget_le_linear auxiliary computation cost budget
    (fun result hr => realRun_counted_charge auxiliary computation cost hcharge result hr)

end SphincsSecurity.Concrete.PartialChainEndpoint

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.counted_twoEdge_budget_le_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.counted_twoEdge_budget_le_cap

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.counted_twoEdge_budget_le_cap_counted_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.counted_twoEdge_budget_le_cap_counted_cost

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdge_cost_budget_le_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdge_cost_budget_le_counted

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdge_cost_budget_le_cap_counted_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdge_cost_budget_le_cap_counted_cost

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_capped_count_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_capped_count_le_budget

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_capped_count_expectation_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_capped_count_expectation_le_budget

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdge_cost_budget_le_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdge_cost_budget_le_linear

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_counted_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_counted_charge

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdge_cost_budget_le_linear_of_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdge_cost_budget_le_linear_of_charge

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem realRun_contact_cost_budget_le_linear
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (cost : Result → Nat) (budget : Nat)
    (hchargeRun : ∀ result ∈
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none)).support, result.2.1.2 ≤ cost result.2.1.1) :
    Pr[fun result => Contact result.2.2 result.1 ∧ cost result.2.1 ≤ budget |
      realRun auxiliary computation (fun _ _ => none)] ≤
      (2 / Fintype.card State) * (budget : ENNReal) := by
  apply (realRun_observed_cost_budget_le_cap auxiliary computation
    (fun trace endpoint => Contact trace endpoint) cost budget hchargeRun).trans
  have h := realRun_contact_le auxiliary
    (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
  exact h.trans (mul_le_mul' le_rfl
    (idealRun_capped_count_expectation_le_budget auxiliary computation budget))

end SphincsSecurity.Concrete.PartialChainEndpoint

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_contact_cost_budget_le_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_contact_cost_budget_le_linear

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem realRun_contact_cost_budget_le_capped_expectation
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (cost : Result → Nat) (budget : Nat)
    (hchargeRun : ∀ result ∈
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none)).support, result.2.1.2 ≤ cost result.2.1.1) :
    Pr[fun result => Contact result.2.2 result.1 ∧ cost result.2.1 ≤ budget |
      realRun auxiliary computation (fun _ _ => none)] ≤
      (2 / Fintype.card State) *
        ∑' result, idealRun auxiliary
          (fun endpoint => QueryCap.counted IsPrefixQuery
            (QueryCap.run IsPrefixQuery (computation endpoint) budget))
          (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  apply (realRun_observed_cost_budget_le_cap auxiliary computation
    (fun trace endpoint => Contact trace endpoint) cost budget hchargeRun).trans
  exact realRun_contact_le auxiliary
    (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)

end SphincsSecurity.Concrete.PartialChainEndpoint
/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_contact_cost_budget_le_capped_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_contact_cost_budget_le_capped_expectation
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {Result : Type}

theorem realRun_twoEdgeEvent_cost_budget_le_linear_of_charge {depth : Nat}
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec depth State) Result)
    (cost : Result → Nat) (budget : Nat)
    (hcharge : ∀ endpoint result,
      result ∈ support (QueryCap.counted IsPrefixQuery
        (computation endpoint)) →
      result.2 ≤ cost result.1) :
    Pr[fun result => TwoEdgeEvent result.2.2 result.1 ∧
      cost result.2.1 ≤ budget |
      realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) +
        4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) /
        Fintype.card State) * budget := by
  cases depth with
  | zero =>
      simp only [TwoEdgeEvent, false_and, probEvent_eq_tsum_ite, if_false, tsum_zero]
      exact bot_le
  | succ depth =>
      cases depth with
      | zero =>
          simp only [TwoEdgeEvent, false_and, probEvent_eq_tsum_ite, if_false, tsum_zero]
          exact bot_le
      | succ depth =>
          exact realRun_twoEdge_cost_budget_le_linear_of_charge
            auxiliary computation cost budget hcharge

end SphincsSecurity.Concrete.PartialChainEndpoint

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdgeEvent_cost_budget_le_linear_of_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdgeEvent_cost_budget_le_linear_of_charge
