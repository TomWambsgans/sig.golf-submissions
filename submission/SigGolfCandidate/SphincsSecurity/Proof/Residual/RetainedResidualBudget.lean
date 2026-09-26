import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualSuccessTransfer
import SigGolfCandidate.SphincsSecurity.Proof.Reference.FixedQueryBound
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

theorem fixedHashStep_hashCalls (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : InterleavedResidual.Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) (input : HashInput) (memory : Memory) :
    (fixedHashStep parameter words selections routing actual oracle input memory).2.external.hashCalls = memory.external.hashCalls + 1 := by
  rw [fixedHashStep_external]
  exact ResidualByteFrontend.fixedStep_hashCalls parameter words routing.disclosed routing.known actual oracle input memory.external

theorem applyBoundary_recordSigning_hashCalls (memory : Memory) (message : Message) (record : InterleavedResidual.SigningRecord) :
    ((memory.applyBoundary record.2).recordSigning message record).external.hashCalls = memory.external.hashCalls + record.2.hashCalls := rfl

theorem fixedSourceImpl_query_bound {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result)
    (q : Nat) (hbound : FixedHashQueryBound context.oracle (simulateQ (expandedAdversaryImpl context.key)
      (liftM ((OracleWorld + SigningSpec).query input) >>= next)) q)
    (memory : Memory) (result : Option ((OracleWorld + SigningSpec).Range input) × Memory)
    (hresult : (fixedSourceImpl context input).run.run memory result ≠ 0) :
    ∃ cost ≤ q, result.2.external.hashCalls = memory.external.hashCalls + cost ∧
      ∀ answer, result.1 = some answer →
        FixedHashQueryBound context.oracle (simulateQ (expandedAdversaryImpl context.key) (next answer)) (q - cost) := by
  cases input with
  | inl input =>
      rw [simulateQ_expandedAdversaryImpl_query_bind_inl] at hbound
      simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, fixedByteRun, simulateQ_spec_query] at hresult
      cases input with
      | inl input =>
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, RetainedObservation.bind_nonzero] at hresult
          obtain ⟨value, _, hresult⟩ := hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          refine ⟨0, Nat.zero_le _, (Nat.add_zero _).symm, ?_⟩
          intro answer heq
          cases Option.some.inj heq
          exact (fixedHashQueryBound_query_bind context.oracle (.inl input) _ q hbound value
            (by simp [fixedHashWorld])).2
      | inr input =>
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          have hquery := fixedHashQueryBound_query_bind context.oracle (.inr input) _ q hbound
            (context.oracle input) (by simp [fixedHashWorld])
          refine ⟨1, hquery.1, fixedHashStep_hashCalls _ _ _ _ _ _ _ _, ?_⟩
          intro answer heq
          rcases fixedHashStep_answer context input memory with hstop | hlive
          · rw [hstop] at heq; contradiction
          · rw [hlive] at heq
            cases Option.some.inj heq
            exact hquery.2
  | inr message =>
      rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
      change FixedHashQueryBound context.oracle (sign context.key message >>= _) q at hbound
      rw [← signWithView_fst context.key message, bind_map_left] at hbound
      simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨record, hrecord, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      have h := fixedBoundaryRun_bind_query_bound context.key.parameter context.oracle (signWithView context.key message)
        (fun reply => simulateQ (expandedAdversaryImpl context.key) (next reply.1)) q hbound record hrecord
      refine ⟨record.2.hashCalls, h.1, applyBoundary_recordSigning_hashCalls memory message record, ?_⟩
      intro answer heq
      cases Option.some.inj heq
      exact h.2

theorem fixedSourceRun_hashCalls_le {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (q : Nat)
    (hbound : FixedHashQueryBound context.oracle (simulateQ (expandedAdversaryImpl context.key) computation) q)
    (memory : Memory) (result : Option Result × Memory) (hresult : fixedSourceRun context computation memory result ≠ 0) :
    result.2.external.hashCalls ≤ memory.external.hashCalls + q := by
  induction computation using OracleComp.inductionOn generalizing q memory result with
  | pure value =>
      simp only [fixedSourceRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact Nat.le_add_right _ _
  | query_bind input next ih =>
      rw [fixedSourceRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, middle⟩, hmiddle, hresult⟩ := hresult
      obtain ⟨cost, hcost, hpaid, hnext⟩ := fixedSourceImpl_query_bound context input next q hbound memory (answer, middle) hmiddle
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hpaid.trans_le (Nat.add_le_add_left hcost _)
      | some answer =>
          have h := ih answer (q - cost) (hnext answer rfl) middle result hresult
          rw [hpaid] at h
          omega

theorem observedRun_source_hashCalls_le {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (hinputs : sourceInputs context.key computation ⊆ inputs)
    (q : Nat) (hbound : FixedHashQueryBound context.oracle (simulateQ (expandedAdversaryImpl context.key) computation) q)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) (result : Option Result × State inputs)
    (hresult : observedRun context.environment context.actual context.auxiliary.seed
      (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections) computation) state result ≠ 0) :
    result.2.memory.external.hashCalls ≤ state.memory.external.hashCalls + q := by
  have h := map_nonzero _ forgetState result hresult
  rw [observedRun_source_memory context computation hinputs state hcovered hcompatible] at h
  exact fixedSourceRun_hashCalls_le context computation q hbound state.memory (forgetState result) h

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.WeightedCutoff
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Index : Type} {spec : OracleSpec Index}

noncomputable def run {Result : Type} (charge : spec.Domain → Nat)
    (program : OracleComp spec Result) : Nat → OracleComp spec (Option Result) :=
  OracleComp.construct (fun value _ => pure (some value))
    (fun query _ next budget => if charge query ≤ budget then do
      let answer ← liftM (spec.query query)
      next answer (budget - charge query)
    else pure none) program

@[simp] theorem run_pure {Result : Type} (charge : spec.Domain → Nat) (value : Result) (budget : Nat) :
    run charge (pure value : OracleComp spec Result) budget = pure (some value) := rfl

theorem run_query_bind {Result : Type} (charge : spec.Domain → Nat)
    (query : spec.Domain) (next : spec.Range query → OracleComp spec Result) (budget : Nat) :
    run charge (liftM (spec.query query) >>= next) budget =
      if charge query ≤ budget then do
        let answer ← liftM (spec.query query)
        run charge (next answer) (budget - charge query)
      else pure none := rfl

noncomputable def counted {Result : Type} (charge : spec.Domain → Nat)
    (program : OracleComp spec Result) : OracleComp spec (Result × Nat) :=
  OracleComp.construct (fun value => pure (value, 0))
    (fun query _ next => do
      let answer ← liftM (spec.query query)
      let result ← next answer
      pure (result.1, result.2 + charge query)) program

@[simp] theorem counted_pure {Result : Type} (charge : spec.Domain → Nat) (value : Result) :
    counted charge (pure value : OracleComp spec Result) = pure (value, 0) := rfl

theorem counted_query_bind {Result : Type} (charge : spec.Domain → Nat)
    (query : spec.Domain) (next : spec.Range query → OracleComp spec Result) :
    counted charge (liftM (spec.query query) >>= next) = (do
      let answer ← liftM (spec.query query)
      let result ← counted charge (next answer)
      pure (result.1, result.2 + charge query)) := rfl

private theorem run'_query_bind {State Result : Type}
    (implementation : QueryImpl spec (StateT State ProbComp)) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec Result) (state : State) :
    (simulateQ implementation (liftM (spec.query query) >>= next)).run' state =
      ((implementation query).run state >>= fun result =>
        (simulateQ implementation (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind, map_bind]

/-- Exact total-charge cutoff event for an arbitrary stateful probabilistic oracle. -/
theorem prob_run_eq_counted {State Result : Type}
    (charge : spec.Domain → Nat)
    (implementation : QueryImpl spec (StateT State ProbComp))
    (program : OracleComp spec Result) (state : State) (budget : Nat)
    (event : Result → Prop) :
    Pr[fun value => ∃ x, value = some x ∧ event x |
      (simulateQ implementation (run charge program budget)).run' state] =
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      (simulateQ implementation (counted charge program)).run' state] := by
  induction program using OracleComp.inductionOn generalizing state budget with
  | pure value => simp [probEvent_pure]
  | query_bind query next ih =>
      rw [run_query_bind, counted_query_bind]
      by_cases allowed : charge query ≤ budget
      · rw [if_pos allowed, run'_query_bind, run'_query_bind]
        simp only [probEvent_bind_eq_tsum]
        apply tsum_congr
        intro step
        rw [ih step.1 step.2 (budget - charge query)]
        congr 1
        simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
          Functor.map_map, probEvent_map, Function.comp_def]
        apply probEvent_congr' _ rfl
        intro result _
        have arithmetic : result.1.2 ≤ budget - charge query ↔ result.1.2 + charge query ≤ budget := by omega
        exact and_congr_right fun _ => arithmetic
      · rw [if_neg allowed, run'_query_bind]
        have exceeded (count : Nat) : ¬count + charge query ≤ budget := by omega
        simp [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
          Functor.map_map, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def, exceeded]

/-- Any completed capped execution has spent no more than its initial budget. -/
theorem run_counted_support_le {State Result : Type}
    (charge : spec.Domain → Nat)
    (implementation : QueryImpl spec (StateT State ProbComp))
    (program : OracleComp spec Result) (state : State) (budget : Nat)
    (result : Option Result × Nat)
    (hr : result ∈ support
      ((simulateQ implementation (counted charge (run charge program budget))).run' state)) :
    result.2 ≤ budget := by
  induction program using OracleComp.inductionOn generalizing state budget result with
  | pure value =>
      simp only [run_pure, counted_pure, simulateQ_pure, StateT.run'_eq,
        StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at hr
      cases hr
      simp
  | query_bind query next ih =>
      rw [run_query_bind] at hr
      by_cases allowed : charge query ≤ budget
      · rw [if_pos allowed, counted_query_bind, run'_query_bind] at hr
        rw [mem_support_bind_iff] at hr
        obtain ⟨step, _, htail⟩ := hr
        simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
          Functor.map_map, support_map, Set.mem_image] at htail
        obtain ⟨tail, ht, rfl⟩ := htail
        have ht' : tail.1 ∈ support
            ((simulateQ implementation
              (counted charge (run charge (next step.1) (budget - charge query)))).run' step.2) := by
          rw [StateT.run'_eq, support_map, Set.mem_image]
          exact ⟨tail, ht, rfl⟩
        have bound := ih step.1 step.2 (budget - charge query) tail.1 ht'
        omega
      · rw [if_neg allowed] at hr
        simp only [counted_pure, simulateQ_pure, StateT.run'_eq,
          StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at hr
        cases hr
        simp

end SphincsSecurity.WeightedCutoff

namespace SphincsSecurity.WeightedCutoff

/-- The residual World's observable hash-call costs. -/
def residualCharge (inputs : Finset HashInput) :
    (Concrete.RetainedResidual.World inputs).Domain → Nat
  | .inl (.byte _ (.prepare _)) => 1
  | .inl (.byte _ (.account cost)) => cost
  | _ => 0

theorem residual_run_eq_counted {State Result : Type} (inputs : Finset HashInput)
    (implementation : QueryImpl (Concrete.RetainedResidual.World inputs) (StateT State ProbComp))
    (program : OracleComp (Concrete.RetainedResidual.World inputs) Result)
    (state : State) (budget : Nat) (event : Result → Prop) :
    Pr[fun value => ∃ x, value = some x ∧ event x |
      (simulateQ implementation (run (residualCharge inputs) program budget)).run' state] =
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      (simulateQ implementation (counted (residualCharge inputs) program)).run' state] :=
  prob_run_eq_counted (residualCharge inputs) implementation program state budget event

theorem residual_run_counted_support_le {State Result : Type} (inputs : Finset HashInput)
    (implementation : QueryImpl (Concrete.RetainedResidual.World inputs) (StateT State ProbComp))
    (program : OracleComp (Concrete.RetainedResidual.World inputs) Result)
    (state : State) (budget : Nat) (result : Option Result × Nat)
    (hr : result ∈ support
      ((simulateQ implementation
        (counted (residualCharge inputs) (run (residualCharge inputs) program budget))).run' state)) :
    result.2 ≤ budget :=
  run_counted_support_le (residualCharge inputs) implementation program state budget result hr

end SphincsSecurity.WeightedCutoff

/-- info: 'SphincsSecurity.WeightedCutoff.prob_run_eq_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.prob_run_eq_counted

/-- info: 'SphincsSecurity.WeightedCutoff.run_counted_support_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.run_counted_support_le

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_eq_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_eq_counted

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_counted_support_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_counted_support_le
