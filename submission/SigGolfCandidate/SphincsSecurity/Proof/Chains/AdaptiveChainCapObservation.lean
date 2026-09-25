import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapContact
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

private theorem pmf_bind_eq_on_support {First Second : Type} (prior : PMF First) (first second : First → PMF Second)
    (h : ∀ input ∈ prior.support, first input = second input) : prior.bind first = prior.bind second := by
  apply PMF.ext
  intro result
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro input
  by_cases hi : input ∈ prior.support
  · rw [h input hi]
  · have hz : prior input = 0 := not_not.mp hi
    simp only [hz, zero_mul]

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result Next : Type}

omit [Fintype State] [Nonempty State] in
theorem observedRun_map (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (f : Result → Next)
    (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (f <$> computation) observed =
      (observedRun auxiliary tables computation observed).map (fun result => (f result.1, result.2)) := by
  simp only [observedRun, simulateQ_map, StateT.run_map, PMF.monad_map_eq_map]

omit [Fintype State] [Nonempty State] in
theorem observedRun_cap_eq_counted (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ (fixedImpl auxiliary tables) (QueryCap.counted IsPrefixQuery computation)).support,
      result.2 ≤ budget) :
    observedRun auxiliary tables (QueryCap.run IsPrefixQuery computation budget) observed =
      (observedRun auxiliary tables (QueryCap.counted IsPrefixQuery computation) observed).map
        (fun result => (some (result.1.1, budget - result.1.2), result.2)) := by
  induction computation using OracleComp.inductionOn generalizing observed budget with
  | pure value =>
      simp only [QueryCap.run_pure, QueryCap.counted_pure, observedRun_pure, PMF.map, PMF.pure_bind, Function.comp_def, Nat.sub_zero]
  | query_bind input next ih =>
      rw [QueryCap.run_query_bind, QueryCap.counted_query_bind]
      simp only [bind_pure_comp, observedRun_query_bind, observedRun_map]
      cases input with
      | inl input =>
          simp only [IsPrefixQuery, if_false, observedRun_query_bind, observedImpl, StateT.run_mk,
            PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def, Nat.zero_add]
          apply pmf_bind_eq_on_support
          intro answer hanswer
          apply ih answer observed budget
          intro tail htail
          have h := QueryCap.counted_next_bound IsPrefixQuery (fixedImpl auxiliary tables) (.inl input) next budget hbound answer hanswer tail htail
          simpa only [IsPrefixQuery, if_false, Nat.zero_add] using h
      | inr query =>
          simp only [IsPrefixQuery, if_true]
          have hnext := fun tail htail => QueryCap.counted_next_bound IsPrefixQuery (fixedImpl auxiliary tables)
            (.inr query) next budget hbound (tables query.1 query.2) (by simp [fixedImpl]) tail htail
          cases budget with
          | zero =>
              obtain ⟨tail, htail⟩ := (simulateQ (fixedImpl auxiliary tables)
                (QueryCap.counted IsPrefixQuery (next (tables query.1 query.2)))).support_nonempty
              have h := hnext tail htail
              simp only [IsPrefixQuery, if_true] at h
              omega
          | succ budget =>
              simp only [observedRun_query_bind, observedImpl, StateT.run_mk, PMF.pure_bind,
                PMF.map_comp, Function.comp_def, Nat.add_comm 1, Nat.add_sub_add_right]
              apply ih (tables query.1 query.2) (record observed query (tables query.1 query.2)) budget
              intro tail htail
              have h := hnext tail htail
              simp only [IsPrefixQuery, if_true] at h
              omega

theorem realRun_map (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (f : State → Result → Next)
    (observed : Fin n → State → Option State) :
    realRun auxiliary (fun endpoint => f endpoint <$> computation endpoint) observed =
      (realRun auxiliary computation observed).map (fun result => (result.1, f result.1 result.2.1, result.2.2)) := by
  simp only [realRun, observedRun_map, PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem realRun_counted_forget (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) observed).map
      (fun result => (result.1, result.2.1.1, result.2.2)) = realRun auxiliary computation observed := by
  simpa only [QueryCap.counted_forget] using
    (realRun_map auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ => Prod.fst) observed).symm

variable (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)

include hcharge hreal

theorem realRun_cap_eq_counted_observed :
    realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) =
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).map
        (fun result => (result.1, some (result.2.1.1, budget - result.2.1.2), result.2.2)) := by
  simp only [realRun, completeTables_empty, EndpointPreimageDensity.real, PMF.map_bind, PMF.bind_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  apply congrArg (PMF.uniformOfFintype (Fin n → State → State)).bind
  funext tables
  apply congrArg (PMF.uniformOfFintype State).bind
  funext secret
  rw [observedRun_cap_eq_counted (auxiliary (evaluate tables secret)) tables (computation (evaluate tables secret))
    (fun _ _ => none) budget (fixed_counted_le auxiliary computation cost budget hcharge hreal tables secret), PMF.map_comp]
  simp only [Function.comp_def]

theorem realRun_cap_erased_observed :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
      (fun result => (result.1, Option.map Prod.fst result.2.1, result.2.2)) =
      (realRun auxiliary computation (fun _ _ => none)).map (fun result => (result.1, some result.2.1, result.2.2)) := by
  rw [realRun_cap_eq_counted_observed auxiliary computation cost budget hcharge hreal, PMF.map_comp]
  have h := congrArg (PMF.map (fun result : State × (Result × (Fin n → State → Option State)) =>
    (result.1, some result.2.1, result.2.2))) (realRun_counted_forget auxiliary computation (fun _ _ => none))
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some] using h

theorem realRun_cap_contact_eq :
    Pr[fun result => Contact result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] =
        Pr[fun result => Contact result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF (State × (Option Result × (Fin n → State → Option State))) =>
    Pr[fun result => Contact result.2.2 result.1 | law])
    (realRun_cap_erased_observed auxiliary computation cost budget hcharge hreal)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h

theorem realRun_contact_le_cap_cost (hsmall : budget < Fintype.card State) :
    Pr[fun result => Contact result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (2 / Fintype.card State) * ∑' result,
        idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) result *
          (QueryCap.spent budget result.2.1 : ENNReal) := by
  rw [← realRun_cap_contact_eq auxiliary computation cost budget hcharge hreal]
  exact realRun_cap_contact_le auxiliary computation cost budget hcharge hreal hsmall

end SphincsSecurity.Concrete.PartialChainEndpoint

namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

private theorem finish_succ (budget : Nat) (result : Result × Nat) :
    QueryCap.finish (budget + 1) (result.1, 1 + result.2) =
      QueryCap.finish budget result := by
  simp [QueryCap.finish, Nat.add_comm]

private theorem finish_zero_succ (result : Result × Nat) :
    QueryCap.finish 0 (result.1, 1 + result.2) = none := by
  simp [QueryCap.finish]

omit [Fintype State] [Nonempty State] in
theorem observedRun_cap_finish_counted
    (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (budget : Nat) :
    (fun result => result.1.map (fun finished => (finished, result.2))) <$>
      observedRun auxiliary tables (QueryCap.run IsPrefixQuery computation budget) observed =
    (fun result => (QueryCap.finish budget result.1).map (fun finished => (finished, result.2))) <$>
      observedRun auxiliary tables (QueryCap.counted IsPrefixQuery computation) observed := by
  induction computation using OracleComp.inductionOn generalizing observed budget with
  | pure value =>
      simp only [QueryCap.run_pure, QueryCap.counted_pure, observedRun_pure,
        PMF.monad_map_eq_map, PMF.map, PMF.pure_bind, Function.comp_apply, QueryCap.finish]
      simp
  | query_bind input next ih =>
      rw [QueryCap.run_query_bind, QueryCap.counted_query_bind]
      by_cases hselected : IsPrefixQuery input
      · rw [if_pos hselected]
        cases budget with
        | zero =>
            simp only [observedRun_pure, hselected, if_true, PMF.monad_map_eq_map,
              PMF.map, PMF.pure_bind, Function.comp_apply, Option.map_none]
            have hmap (answer : (auxSpec + PrefixSpec n State).Range input)
                (seen : Fin n → State → Option State) :
                observedRun auxiliary tables
                  (do
                    let result ← QueryCap.counted IsPrefixQuery (next answer)
                    pure (result.1, 1 + result.2)) seen =
                  (observedRun auxiliary tables
                    (QueryCap.counted IsPrefixQuery (next answer)) seen).map
                    (fun result => ((result.1.1, 1 + result.1.2), result.2)) := by
              simpa only [bind_pure_comp] using
                (observedRun_map auxiliary tables
                  (QueryCap.counted IsPrefixQuery (next answer))
                  (fun result => (result.1, 1 + result.2)) seen)
            simp only [observedRun_query_bind, hmap, PMF.bind_bind,
              PMF.bind_map, Function.comp_def, finish_zero_succ,
              Option.map_none, PMF.bind_const]
        | succ budget =>
            simp only [observedRun_query_bind, hselected, if_true,
              PMF.monad_map_eq_map, PMF.map_bind]
            have hmap (answer : (auxSpec + PrefixSpec n State).Range input)
                (seen : Fin n → State → Option State) :
                observedRun auxiliary tables
                  (do
                    let result ← QueryCap.counted IsPrefixQuery (next answer)
                    pure (result.1, 1 + result.2)) seen =
                  (observedRun auxiliary tables
                    (QueryCap.counted IsPrefixQuery (next answer)) seen).map
                    (fun result => ((result.1.1, 1 + result.1.2), result.2)) := by
              simpa only [bind_pure_comp] using
                (observedRun_map auxiliary tables
                  (QueryCap.counted IsPrefixQuery (next answer))
                  (fun result => (result.1, 1 + result.2)) seen)
            simp only [hmap, PMF.map_comp, Function.comp_def, finish_succ]
            exact congrArg ((observedImpl auxiliary tables input).run observed).bind
              (funext fun answer => ih answer.1 answer.2 budget)
      · rw [if_neg hselected]
        simp only [observedRun_query_bind, hselected, if_false, Nat.zero_add,
          Prod.mk.eta, bind_pure, PMF.monad_map_eq_map, PMF.map_bind]
        exact congrArg ((observedImpl auxiliary tables input).run observed).bind
          (funext fun answer => ih answer.1 answer.2 budget)

end SphincsSecurity.Concrete.PartialChainEndpoint

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_cap_finish_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_cap_finish_counted

namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem realRun_cap_finish_counted
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (budget : Nat) :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) observed).map
      (fun result => result.2.1.map (fun finished => (result.1, finished, result.2.2))) =
    (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) observed).map
      (fun result => (QueryCap.finish budget result.2.1).map
        (fun finished => (result.1, finished, result.2.2))) := by
  simp only [realRun, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (EndpointPreimageDensity.real (completeTables observed) evaluate).bind
  funext pair
  have h := congrArg (PMF.map (Option.map (fun r : (Result × Nat) × (Fin n → State → Option State) =>
    (pair.2, r.1, r.2))))
    (observedRun_cap_finish_counted (auxiliary pair.2) pair.1
      (computation pair.2) observed budget)
  simpa only [PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, Option.map_map] using h

end SphincsSecurity.Concrete.PartialChainEndpoint

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_cap_finish_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_cap_finish_counted

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem counted_observed_budget_le_cap
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (event : (Fin n → State → Option State) → State → Prop)
    (budget : Nat) :
    Pr[fun result => event result.2.2 result.1 ∧ result.2.1.2 ≤ budget |
      realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none)] ≤
    Pr[fun result => event result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
        (fun _ _ => none)] := by
  let observed : Fin n → State → Option State := fun _ _ => none
  let p : Option (State × ((Result × Nat) × (Fin n → State → Option State))) → Prop :=
    fun opt => ∃ result, opt = some result ∧ event result.2.2 result.1
  have hlaw := realRun_cap_finish_counted auxiliary computation observed budget
  have hprob := congrArg (fun law : PMF (Option (State × ((Result × Nat) × (Fin n → State → Option State)))) =>
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
      · have he : event result.2.2 result.1 := by
          dsimp [p] at hp
          obtain ⟨witness, hw, he⟩ := hp
          cases hopt : result.2.1 with
          | none => simp [hopt] at hw
          | some pair =>
              simp [hopt] at hw
              cases hw
              exact he
        simp [hp, he, observed]
      · simp [hp]

end SphincsSecurity.Concrete.PartialChainEndpoint

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.counted_observed_budget_le_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.counted_observed_budget_le_cap

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem realRun_observed_cost_budget_le_cap
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (event : (Fin n → State → Option State) → State → Prop)
    (cost : Result → Nat) (budget : Nat)
    (hchargeRun : ∀ result ∈
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none)).support, result.2.1.2 ≤ cost result.2.1.1) :
    Pr[fun result => event result.2.2 result.1 ∧ cost result.2.1 ≤ budget |
      realRun auxiliary computation (fun _ _ => none)] ≤
    Pr[fun result => event result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
        (fun _ _ => none)] := by
  apply le_trans ?_ (counted_observed_budget_le_cap auxiliary computation event budget)
  rw [← realRun_counted_forget auxiliary computation (fun _ _ => none)]
  simp only [← PMF.monad_map_eq_map]
  rw [probEvent_map]
  simp only [Function.comp_def, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (realRun auxiliary
      (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
      (fun _ _ => none)).support
  · by_cases hevent : event result.2.2 result.1 ∧ cost result.2.1.1 ≤ budget
    · have hcount : result.2.1.2 ≤ budget := (hchargeRun result hr).trans hevent.2
      simp [hevent, hcount]
    · simp [hevent]
  · have hz : (realRun auxiliary
      (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
      (fun _ _ => none)) result = 0 := not_not.mp hr
    simp [hz]

end SphincsSecurity.Concrete.PartialChainEndpoint

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_observed_cost_budget_le_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_observed_cost_budget_le_cap

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

omit [Fintype State] [Nonempty State] in
theorem observedRun_cap_finish_counted_selected
    (selected : AuxIndex ⊕ (Fin n × State) → Prop) [DecidablePred selected]
    (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (budget : Nat) :
    (fun result => result.1.map (fun finished => (finished, result.2))) <$>
      observedRun auxiliary tables (QueryCap.run selected computation budget) observed =
    (fun result => (QueryCap.finish budget result.1).map (fun finished => (finished, result.2))) <$>
      observedRun auxiliary tables (QueryCap.counted selected computation) observed := by
  induction computation using OracleComp.inductionOn generalizing observed budget with
  | pure value =>
      simp only [QueryCap.run_pure, QueryCap.counted_pure, observedRun_pure,
        PMF.monad_map_eq_map, PMF.map, PMF.pure_bind, Function.comp_apply, QueryCap.finish]
      simp
  | query_bind input next ih =>
      rw [QueryCap.run_query_bind, QueryCap.counted_query_bind]
      by_cases hselected : selected input
      · rw [if_pos hselected]
        cases budget with
        | zero =>
            simp only [observedRun_pure, hselected, if_true, PMF.monad_map_eq_map,
              PMF.map, PMF.pure_bind, Function.comp_apply, Option.map_none]
            have hmap (answer : (auxSpec + PrefixSpec n State).Range input)
                (seen : Fin n → State → Option State) :
                observedRun auxiliary tables
                  (do
                    let result ← QueryCap.counted selected (next answer)
                    pure (result.1, 1 + result.2)) seen =
                  (observedRun auxiliary tables
                    (QueryCap.counted selected (next answer)) seen).map
                    (fun result => ((result.1.1, 1 + result.1.2), result.2)) := by
              simpa only [bind_pure_comp] using
                (observedRun_map auxiliary tables
                  (QueryCap.counted selected (next answer))
                  (fun result => (result.1, 1 + result.2)) seen)
            simp only [observedRun_query_bind, hmap, PMF.bind_bind,
              PMF.bind_map, Function.comp_def, finish_zero_succ,
              Option.map_none, PMF.bind_const]
        | succ budget =>
            simp only [observedRun_query_bind, hselected, if_true,
              PMF.monad_map_eq_map, PMF.map_bind]
            have hmap (answer : (auxSpec + PrefixSpec n State).Range input)
                (seen : Fin n → State → Option State) :
                observedRun auxiliary tables
                  (do
                    let result ← QueryCap.counted selected (next answer)
                    pure (result.1, 1 + result.2)) seen =
                  (observedRun auxiliary tables
                    (QueryCap.counted selected (next answer)) seen).map
                    (fun result => ((result.1.1, 1 + result.1.2), result.2)) := by
              simpa only [bind_pure_comp] using
                (observedRun_map auxiliary tables
                  (QueryCap.counted selected (next answer))
                  (fun result => (result.1, 1 + result.2)) seen)
            simp only [hmap, PMF.map_comp, Function.comp_def, finish_succ]
            exact congrArg ((observedImpl auxiliary tables input).run observed).bind
              (funext fun answer => ih answer.1 answer.2 budget)
      · rw [if_neg hselected]
        simp only [observedRun_query_bind, hselected, if_false, Nat.zero_add,
          Prod.mk.eta, bind_pure, PMF.monad_map_eq_map, PMF.map_bind]
        exact congrArg ((observedImpl auxiliary tables input).run observed).bind
          (funext fun answer => ih answer.1 answer.2 budget)


theorem realRun_cap_finish_counted_selected
    (selected : AuxIndex ⊕ (Fin n × State) → Prop) [DecidablePred selected]
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (budget : Nat) :
    (realRun auxiliary (fun endpoint => QueryCap.run selected (computation endpoint) budget) observed).map
      (fun result => result.2.1.map (fun finished => (result.1, finished, result.2.2))) =
    (realRun auxiliary (fun endpoint => QueryCap.counted selected (computation endpoint)) observed).map
      (fun result => (QueryCap.finish budget result.2.1).map
        (fun finished => (result.1, finished, result.2.2))) := by
  simp only [realRun, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (EndpointPreimageDensity.real (completeTables observed) evaluate).bind
  funext pair
  have h := congrArg (PMF.map (Option.map (fun r : (Result × Nat) × (Fin n → State → Option State) =>
    (pair.2, r.1, r.2))))
    (observedRun_cap_finish_counted_selected selected (auxiliary pair.2) pair.1
      (computation pair.2) observed budget)
  simpa only [PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, Option.map_map] using h

end SphincsSecurity.Concrete.PartialChainEndpoint

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_cap_finish_counted_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_cap_finish_counted_selected
/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_cap_finish_counted_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_cap_finish_counted_selected

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem counted_observed_budget_le_cap_selected
    (selected : AuxIndex ⊕ (Fin n × State) → Prop) [DecidablePred selected]
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (event : (Fin n → State → Option State) → State → Prop)
    (budget : Nat) :
    Pr[fun result => event result.2.2 result.1 ∧ result.2.1.2 ≤ budget |
      realRun auxiliary (fun endpoint => QueryCap.counted selected (computation endpoint))
        (fun _ _ => none)] ≤
    Pr[fun result => event result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run selected (computation endpoint) budget)
        (fun _ _ => none)] := by
  let observed : Fin n → State → Option State := fun _ _ => none
  let p : Option (State × ((Result × Nat) × (Fin n → State → Option State))) → Prop :=
    fun opt => ∃ result, opt = some result ∧ event result.2.2 result.1
  have hlaw := realRun_cap_finish_counted_selected selected auxiliary computation observed budget
  have hprob := congrArg (fun law : PMF (Option (State × ((Result × Nat) × (Fin n → State → Option State)))) =>
    Pr[p | law]) hlaw
  simp only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] at hprob
  calc
    _ = Pr[fun result => p ((QueryCap.finish budget result.2.1).map
        (fun finished => (result.1, finished, result.2.2))) |
        realRun auxiliary (fun endpoint => QueryCap.counted selected (computation endpoint)) observed] := by
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
      apply tsum_congr
      intro result
      by_cases hb : result.2.1.2 ≤ budget
      · simp [p, QueryCap.finish, hb, observed]
      · simp [p, QueryCap.finish, hb]
    _ = Pr[fun result => p (result.2.1.map
        (fun finished => (result.1, finished, result.2.2))) |
        realRun auxiliary (fun endpoint => QueryCap.run selected (computation endpoint) budget) observed] := hprob.symm
    _ ≤ _ := by
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hp : p (result.2.1.map (fun finished => (result.1, finished, result.2.2)))
      · have he : event result.2.2 result.1 := by
          dsimp [p] at hp
          obtain ⟨witness, hw, he⟩ := hp
          cases hopt : result.2.1 with
          | none => simp [hopt] at hw
          | some pair =>
              simp [hopt] at hw
              cases hw
              exact he
        simp [hp, he, observed]
      · simp [hp]

end SphincsSecurity.Concrete.PartialChainEndpoint

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.counted_observed_budget_le_cap_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.counted_observed_budget_le_cap_selected

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem realRun_counted_forget_selected
    (selected : AuxIndex ⊕ (Fin n × State) → Prop) [DecidablePred selected]
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    (realRun auxiliary (fun endpoint => QueryCap.counted selected (computation endpoint)) observed).map
      (fun result => (result.1, result.2.1.1, result.2.2)) =
    realRun auxiliary computation observed := by
  simpa only [QueryCap.counted_forget] using
    (realRun_map auxiliary (fun endpoint => QueryCap.counted selected (computation endpoint))
      (fun _ => Prod.fst) observed).symm

end SphincsSecurity.Concrete.PartialChainEndpoint

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem realRun_observed_cost_budget_le_cap_selected
    (selected : AuxIndex ⊕ (Fin n × State) → Prop) [DecidablePred selected]
    (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (event : (Fin n → State → Option State) → State → Prop)
    (cost : Result → Nat) (budget : Nat)
    (hchargeRun : ∀ result ∈
      (realRun auxiliary (fun endpoint => QueryCap.counted selected (computation endpoint))
        (fun _ _ => none)).support, result.2.1.2 ≤ cost result.2.1.1) :
    Pr[fun result => event result.2.2 result.1 ∧ cost result.2.1 ≤ budget |
      realRun auxiliary computation (fun _ _ => none)] ≤
    Pr[fun result => event result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run selected (computation endpoint) budget)
        (fun _ _ => none)] := by
  apply le_trans ?_ (counted_observed_budget_le_cap_selected selected auxiliary computation event budget)
  rw [← realRun_counted_forget_selected selected auxiliary computation (fun _ _ => none)]
  simp only [← PMF.monad_map_eq_map]
  rw [probEvent_map]
  simp only [Function.comp_def, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (realRun auxiliary
      (fun endpoint => QueryCap.counted selected (computation endpoint))
      (fun _ _ => none)).support
  · by_cases hevent : event result.2.2 result.1 ∧ cost result.2.1.1 ≤ budget
    · have hcount : result.2.1.2 ≤ budget := (hchargeRun result hr).trans hevent.2
      simp [hevent, hcount]
    · simp [hevent]
  · have hz : (realRun auxiliary
      (fun endpoint => QueryCap.counted selected (computation endpoint))
      (fun _ _ => none)) result = 0 := not_not.mp hr
    simp [hz]

end SphincsSecurity.Concrete.PartialChainEndpoint

/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_observed_cost_budget_le_cap_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_observed_cost_budget_le_cap_selected
/-- info: 'SphincsSecurity.Concrete.PartialChainEndpoint.realRun_counted_forget_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.PartialChainEndpoint.realRun_counted_forget_selected
