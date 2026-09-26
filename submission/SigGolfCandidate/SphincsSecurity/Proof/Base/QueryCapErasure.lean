import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryCapAccounting
namespace SphincsSecurity.QueryCap

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

private theorem map_eq_on_support {Result Output : Type} (law : PMF Result) (first second : Result → Output)
    (h : ∀ result ∈ law.support, first result = second result) : law.map first = law.map second := by
  classical
  apply PMF.ext
  intro output
  rw [PMF.map, PMF.map, PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro result
  simp only [Function.comp_apply]
  by_cases hresult : result ∈ law.support
  · rw [h result hresult]
  · have hzero : law result = 0 := by simpa only [PMF.mem_support_iff, not_not] using hresult
    simp only [hzero, zero_mul]

variable {Index : Type} {spec : OracleSpec Index} {Result : Type}
  (selected : Index → Prop) [DecidablePred selected]

theorem counted_simulate_result_mem (impl : QueryImpl spec PMF) (computation : OracleComp spec Result)
    (result : Result × Nat) (hresult : result ∈ (simulateQ impl (counted selected computation)).support) :
    result.1 ∈ (simulateQ impl computation).support := by
  have hmap : (simulateQ impl (counted selected computation)).map Prod.fst = simulateQ impl computation := by
    rw [← PMF.monad_map_eq_map, ← simulateQ_map, counted_forget]
  rw [← hmap, PMF.mem_support_map_iff]
  exact ⟨result, hresult, rfl⟩

theorem run_eq_some_counted (impl : QueryImpl spec PMF) (computation : OracleComp spec Result) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ impl (counted selected computation)).support, result.2 ≤ budget) :
    simulateQ impl (run selected computation budget) =
      (simulateQ impl (counted selected computation)).map (fun result => some (result.1, budget - result.2)) := by
  rw [run_eq_counted]
  apply map_eq_on_support
  intro result hresult
  exact if_pos (hbound result hresult)

theorem run_erased (impl : QueryImpl spec PMF) (computation : OracleComp spec Result) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ impl (counted selected computation)).support, result.2 ≤ budget) :
    (simulateQ impl (run selected computation budget)).map (Option.map Prod.fst) =
      (simulateQ impl computation).map some := by
  rw [run_eq_some_counted selected impl computation budget hbound, PMF.map_comp]
  change (simulateQ impl (counted selected computation)).map (some ∘ Prod.fst) = _
  rw [← PMF.map_comp]
  apply congrArg (PMF.map some)
  rw [← PMF.monad_map_eq_map, ← simulateQ_map, counted_forget]

theorem run_recover_count (impl : QueryImpl spec PMF) (computation : OracleComp spec Result) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ impl (counted selected computation)).support, result.2 ≤ budget) :
    (simulateQ impl (run selected computation budget)).map (Option.map (fun result => (result.1, budget - result.2))) =
      (simulateQ impl (counted selected computation)).map some := by
  rw [run_eq_some_counted selected impl computation budget hbound, PMF.map_comp]
  apply map_eq_on_support
  intro result hresult
  simp only [Function.comp_apply, Option.map_some]
  congr 2
  exact Nat.sub_sub_self (hbound result hresult)

/-- An event within the query budget has exactly the same probability in the
    stopped and counted executions. The stopped run retains its remaining budget. -/
theorem run_budget_event (impl : QueryImpl spec PMF)
    (computation : OracleComp spec Result) (budget : Nat) (event : Result → Prop) :
    Pr[fun result => ∃ value remaining,
      result = some (value, remaining) ∧ event value |
      simulateQ impl (run selected computation budget)] =
    Pr[fun result => result.2 ≤ budget ∧ event result.1 |
      simulateQ impl (counted selected computation)] := by
  rw [run_eq_counted, ← PMF.monad_map_eq_map, probEvent_map]
  congr 1
  funext result
  by_cases hbudget : result.2 ≤ budget
  · simp [finish, hbudget]
  · simp [finish, hbudget]

/-- Successful capped executions preserve both their result and their final
    state, even when oracle queries change that state. -/
def stoppedStateEvent {State : Type} (event : Result → State → Prop)
    (output : Option (Result × Nat) × State) : Prop :=
  match output.1 with
  | none => False
  | some (value, _) => event value output.2

theorem run_budget_event_state {State : Type} (impl : QueryImpl spec (StateT State PMF))
    (computation : OracleComp spec Result) (budget : Nat) (initial : State)
    (event : Result → State → Prop) :
    Pr[stoppedStateEvent event |
      (simulateQ impl (run selected computation budget)).run initial] =
    Pr[fun output => output.1.2 ≤ budget ∧ event output.1.1 output.2 |
      (simulateQ impl (counted selected computation)).run initial] := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget initial with
  | pure value =>
      simp [run_pure, counted_pure, simulateQ_pure, StateT.run_pure,
        ← PMF.monad_pure_eq_pure, probEvent_pure, stoppedStateEvent]
  | query_bind input next ih =>
      rw [run_query_bind, counted_query_bind]
      by_cases hselected : selected input
      · rw [if_pos hselected]
        cases budget with
        | zero =>
            simp [simulateQ_pure, StateT.run_pure,
              simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
              ← PMF.monad_pure_eq_pure, ← PMF.monad_bind_eq_bind,
              ← PMF.monad_map_eq_map, probEvent_bind_eq_tsum,
              probEvent_pure, stoppedStateEvent, hselected, Function.comp_def]
        | succ budget =>
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
              ← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map,
              ← PMF.monad_pure_eq_pure, probEvent_bind_eq_tsum,
              probEvent_pure, hselected, if_true,
              Nat.succ_eq_add_one]
            apply tsum_congr
            intro middle
            congr 1
            simp only [simulateQ_pure, StateT.run_pure,
              ← PMF.monad_pure_eq_pure, probEvent_pure,
              mul_ite, mul_one, mul_zero]
            rw [← probEvent_eq_tsum_ite]
            simpa only [Nat.add_comm 1, Nat.add_le_add_iff_right] using
              ih middle.1 budget middle.2
      · simp only [if_neg hselected, simulateQ_bind, simulateQ_spec_query,
          StateT.run_bind, ← PMF.monad_bind_eq_bind,
          ← PMF.monad_map_eq_map, ← PMF.monad_pure_eq_pure,
          probEvent_bind_eq_tsum, probEvent_pure,
          hselected, if_false, Nat.zero_add]
        apply tsum_congr
        intro middle
        congr 1
        simp only [simulateQ_pure, StateT.run_pure,
          ← PMF.monad_pure_eq_pure, probEvent_pure,
          mul_ite, mul_one, mul_zero]
        rw [← probEvent_eq_tsum_ite]
        exact ih middle.1 budget middle.2

/-- info: 'SphincsSecurity.QueryCap.run_budget_event_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms run_budget_event_state

/-- info: 'SphincsSecurity.QueryCap.run_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms run_budget_event

end SphincsSecurity.QueryCap
