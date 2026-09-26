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

theorem fixedSourceImpl_sign_exact_cost {inputs : Finset HashInput}
    (context : Context inputs) (message : Message) (memory : Memory) :
    (fun result : Option (Option Signature) × Memory =>
      (result.1, result.2.external.hashCalls - memory.external.hashCalls)) <$>
      (fixedSourceImpl context (.inr message)).run.run memory =
    (fun result : Option Signature × Nat => (some result.1, result.2)) <$>
      simulateQ (fixedHashWorld context.oracle)
        (countHashQueries (scheme.sign context.key message)) := by
  simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk]
  rw [show scheme.sign context.key message = sign context.key message from rfl,
    ← signWithView_fst context.key message]
  simp only [countHashQueries_map, simulateQ_map, Functor.map_map]
  rw [← fixedBoundaryRun_count context.key.parameter context.oracle (signWithView context.key message)]
  simp only [Functor.map_map, ← evalSPMF_map]
  change 𝒮[_ <$> fixedBoundaryRun context.key.parameter context.oracle
      (signWithView context.key message)] =
    𝒮[_ <$> fixedBoundaryRun context.key.parameter context.oracle
      (signWithView context.key message)]
  congr 1
  apply congrArg (fun f => f <$> fixedBoundaryRun context.key.parameter context.oracle
    (signWithView context.key message))
  funext result
  rcases result with ⟨answer, trace⟩
  rw [applyBoundary_recordSigning_hashCalls memory message (answer, trace)]
  simp


/-- info: 'SphincsSecurity.Concrete.RetainedResidual.fixedSourceImpl_sign_exact_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.fixedSourceImpl_sign_exact_cost

theorem fixedSourceImpl_hash_exact_cost {inputs : Finset HashInput}
    (context : Context inputs) (input : HashInput) (memory : Memory) :
    (fun result : Option HashOutput × Memory =>
      (result.1, result.2.external.hashCalls - memory.external.hashCalls)) <$>
      (fixedSourceImpl context (.inl (.inr input))).run.run memory =
    pure ((fixedHashStep context.key.parameter context.words context.auxiliary.selections
      memory.routing context.actual context.oracle input memory).1, 1) := by
  simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, fixedByteRun,
    simulateQ_spec_query, fixedByteImpl, map_pure]
  rw [fixedHashStep_hashCalls]
  simp


/-- info: 'SphincsSecurity.Concrete.RetainedResidual.fixedSourceImpl_hash_exact_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.fixedSourceImpl_hash_exact_cost

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

private theorem run'_query_bind_spmf {State Result : Type}
    (implementation : QueryImpl spec (StateT State SPMF)) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec Result) (state : State) :
    (simulateQ implementation (liftM (spec.query query) >>= next)).run' state =
      ((implementation query).run state >>= fun result =>
        (simulateQ implementation (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind, map_bind]

/-- Exact weighted cutoff event for a stateful subprobability oracle. -/
theorem prob_run_eq_counted_spmf {State Result : Type}
    (charge : spec.Domain → Nat)
    (implementation : QueryImpl spec (StateT State SPMF))
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
      · rw [if_pos allowed, run'_query_bind_spmf, run'_query_bind_spmf]
        simp only [probEvent_bind_eq_tsum]
        apply tsum_congr
        intro step
        rw [ih step.1 step.2 (budget - charge query)]
        congr 1
        simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
          Functor.map_map, probEvent_map, Function.comp_def]
        congr 1
        funext result
        apply propext
        exact and_congr_right fun _ => by omega
      · rw [if_neg allowed, run'_query_bind_spmf]
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

/-- info: 'SphincsSecurity.WeightedCutoff.prob_run_eq_counted_spmf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.prob_run_eq_counted_spmf

/-- info: 'SphincsSecurity.WeightedCutoff.run_counted_support_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.run_counted_support_le

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_eq_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_eq_counted

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_counted_support_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_counted_support_le

namespace SphincsSecurity.WeightedCutoff

attribute [local instance] Classical.propDecidable

/-- The second half of a residual hash query has zero additional cost. -/
theorem residual_run_execute (inputs : Finset HashInput)
    (routing : Concrete.InterleavedResidual.Routing)
    (action : Concrete.ResidualByteAction.Action inputs) (budget : Nat) :
    run (residualCharge inputs)
      (simulateQ (Concrete.RetainedResidual.embed inputs routing)
        (Concrete.ResidualByteFrontend.execute action)) budget =
    (do
      let answer ← simulateQ (Concrete.RetainedResidual.embed inputs routing)
        (Concrete.ResidualByteFrontend.execute action)
      pure (some answer)) := by
  cases action with
  | known answer => rfl
  | read input =>
      simp only [Concrete.ResidualByteFrontend.execute, simulateQ_spec_query,
        Concrete.RetainedResidual.embed]
      rw [← bind_pure (liftM ((Concrete.RetainedResidual.World inputs).query (.inr (.read input))))]
      rw [run_query_bind]
      simp [residualCharge]
  | probe input test =>
      simp only [Concrete.ResidualByteFrontend.execute, simulateQ_spec_query,
        Concrete.RetainedResidual.embed]
      rw [← bind_pure (liftM ((Concrete.RetainedResidual.World inputs).query (.inr (.probe input test))))]
      rw [run_query_bind]
      simp [residualCharge]

theorem residual_run_stop (inputs : Finset HashInput)
    (routing : Concrete.InterleavedResidual.Routing) (budget : Nat) :
    run (residualCharge inputs)
      (simulateQ (Concrete.RetainedResidual.embed inputs routing)
        (liftM ((Concrete.ResidualByteFrontend.World inputs).query (.inl .stop)))) budget =
      (do
        let answer ← simulateQ (Concrete.RetainedResidual.embed inputs routing)
          (liftM ((Concrete.ResidualByteFrontend.World inputs).query (.inl .stop)))
        pure (some answer)) := by
  simp only [simulateQ_spec_query, Concrete.RetainedResidual.embed]
  rw [← bind_pure (liftM ((Concrete.RetainedResidual.World inputs).query (.inl (.byte routing .stop))))]
  rw [run_query_bind]
  simp [residualCharge]

/-- A byte hash's charged preparation is first; all remaining oracle steps are free. -/
theorem residual_run_hashQuery (inputs : Finset HashInput)
    (routing : Concrete.InterleavedResidual.Routing) (input : inputs) (budget : Nat) :
    run (residualCharge inputs)
      (simulateQ (Concrete.RetainedResidual.embed inputs routing)
        (Concrete.ResidualByteFrontend.hashQuery input)) budget =
    if 1 ≤ budget then
      (do
        let answer ← simulateQ (Concrete.RetainedResidual.embed inputs routing)
          (Concrete.ResidualByteFrontend.hashQuery input)
        pure (some answer))
    else pure none := by
  simp only [Concrete.ResidualByteFrontend.hashQuery, simulateQ_bind, simulateQ_spec_query,
    Concrete.RetainedResidual.embed]
  rw [run_query_bind]
  by_cases allowed : residualCharge inputs (.inl (.byte routing (.prepare input))) ≤ budget
  · have h1 : 1 ≤ budget := by simpa [residualCharge] using allowed
    rw [if_pos allowed, if_pos h1]
    simp only [bind_assoc]
    congr 1
    funext action
    exact residual_run_execute inputs routing action (budget - 1)
  · have h1 : ¬1 ≤ budget := by simpa [residualCharge] using allowed
    rw [if_neg allowed, if_neg h1]

theorem residual_run_checkedPost (inputs : Finset HashInput)
    (routing : Concrete.InterleavedResidual.Routing) (reject : HashOutput → Prop)
    (answer : HashOutput) (budget : Nat) :
    run (residualCharge inputs)
      (if reject answer then
        simulateQ (Concrete.RetainedResidual.embed inputs routing)
          (liftM ((Concrete.ResidualByteFrontend.World inputs).query (.inl .stop)))
       else pure answer) budget =
    (do
      let x ← if reject answer then
        simulateQ (Concrete.RetainedResidual.embed inputs routing)
          (liftM ((Concrete.ResidualByteFrontend.World inputs).query (.inl .stop)))
        else pure answer
      pure (some x)) := by
  split
  · exact residual_run_stop inputs routing budget
  · rfl

theorem residual_run_checkedTail (inputs : Finset HashInput)
    (routing : Concrete.InterleavedResidual.Routing)
    (reject : HashOutput → Prop) (action : Concrete.ResidualByteAction.Action inputs)
    (budget : Nat) :
    run (residualCharge inputs)
      (simulateQ (Concrete.RetainedResidual.embed inputs routing) (do
        let answer ← Concrete.ResidualByteFrontend.execute action
        if reject answer then
          liftM ((Concrete.ResidualByteFrontend.World inputs).query (.inl .stop))
        else pure answer)) budget =
    (do
      let x ← simulateQ (Concrete.RetainedResidual.embed inputs routing) (do
        let answer ← Concrete.ResidualByteFrontend.execute action
        if reject answer then
          liftM ((Concrete.ResidualByteFrontend.World inputs).query (.inl .stop))
        else pure answer)
      pure (some x)) := by
  cases action with
  | known answer =>
      simp only [Concrete.ResidualByteFrontend.execute, pure_bind]
      by_cases h : reject answer
      · simpa only [if_pos h] using residual_run_stop inputs routing budget
      · simp [h]

  | read input =>
      simp only [Concrete.ResidualByteFrontend.execute, simulateQ_bind, simulateQ_spec_query,
        Concrete.RetainedResidual.embed]
      rw [run_query_bind]
      simp only [residualCharge, Nat.zero_le, if_pos, Nat.sub_zero, bind_assoc]
      congr 1
      funext answer
      by_cases h : reject answer
      · simpa only [if_pos h] using residual_run_stop inputs routing budget
      · simp [h]
  | probe input test =>
      simp only [Concrete.ResidualByteFrontend.execute, simulateQ_bind, simulateQ_spec_query,
        Concrete.RetainedResidual.embed]
      rw [run_query_bind]
      simp only [residualCharge, Nat.zero_le, if_pos, Nat.sub_zero, bind_assoc]
      congr 1
      funext answer
      by_cases h : reject answer
      · simpa only [if_pos h] using residual_run_stop inputs routing budget
      · simp [h]


end SphincsSecurity.WeightedCutoff

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_execute

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_stop

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_hashQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_hashQuery

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_checkedPost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_checkedPost

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_checkedTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_checkedTail

namespace SphincsSecurity.WeightedCutoff
attribute [local instance] Classical.propDecidable

theorem residual_run_checkedHashQuery (inputs : Finset HashInput)
    (routing : Concrete.InterleavedResidual.Routing)
    (reject : HashInput → HashOutput → Prop) (input : inputs) (budget : Nat) :
    run (residualCharge inputs)
      (simulateQ (Concrete.RetainedResidual.embed inputs routing)
        (Concrete.ResidualByteFrontend.checkedHashQuery reject input)) budget =
    if 1 ≤ budget then
      (do
        let answer ← simulateQ (Concrete.RetainedResidual.embed inputs routing)
          (Concrete.ResidualByteFrontend.checkedHashQuery reject input)
        pure (some answer))
    else pure none := by
  simp only [Concrete.ResidualByteFrontend.checkedHashQuery, Concrete.ResidualByteFrontend.hashQuery,
    simulateQ_bind, simulateQ_spec_query, Concrete.RetainedResidual.embed]
  simp only [bind_assoc]
  rw [run_query_bind]
  by_cases allowed : residualCharge inputs (.inl (.byte routing (.prepare input))) ≤ budget
  · have h1 : 1 ≤ budget := by simpa [residualCharge] using allowed
    rw [if_pos allowed, if_pos h1]
    congr 1
    funext action
    convert residual_run_checkedTail inputs routing (reject input.val) action (budget - 1) using 1
    all_goals first | rfl | simp only [residualCharge, simulateQ_bind, bind_assoc,
      Concrete.ResidualByteFrontend.World]
    congr 1
  · have h1 : ¬1 ≤ budget := by simpa [residualCharge] using allowed
    rw [if_neg allowed, if_neg h1]

end SphincsSecurity.WeightedCutoff

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_checkedHashQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_checkedHashQuery

namespace SphincsSecurity.WeightedCutoff
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Index : Type} {spec : OracleSpec Index}

theorem run_all_zero {Result : Type} (charge : spec.Domain → Nat)
    (program : OracleComp spec Result) (budget : Nat)
    (hzero : AllQueriesSatisfy program (fun query => charge query = 0)) :
    run charge program budget = (do let value ← program; pure (some value)) := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => simp [run_pure]
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at hzero
      rw [run_query_bind, hzero.1]
      simp only [Nat.zero_le, if_pos, Nat.sub_zero, bind_assoc]
      congr 1
      funext answer
      exact ih answer budget (hzero.2 answer)
end SphincsSecurity.WeightedCutoff

namespace SphincsSecurity.WeightedCutoff
open SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable

theorem all_zero_sequenceFin {SourceIndex : Type} {spec : OracleSpec SourceIndex} {Result : Type} {n : Nat}
    (f : Fin n → OracleComp spec Result) (P : spec.Domain → Prop)
    (hf : ∀ i, AllQueriesSatisfy (f i) P) :
    AllQueriesSatisfy (Concrete.sequenceFin f) P := by
  induction n with
  | zero => exact allQueriesSatisfy_pure _ _
  | succ n ih =>
      rw [Concrete.sequenceFin]
      apply allQueriesSatisfy_bind (hf 0)
      intro head
      apply allQueriesSatisfy_bind (ih (fun i => f i.succ) (fun i => hf i.succ))
      intro tail
      exact allQueriesSatisfy_pure _ _

theorem simulateQ_sequenceFin {SourceIndex : Type} {source : OracleSpec SourceIndex} {TargetIndex : Type}
    {target : OracleSpec TargetIndex} {Result : Type} {n : Nat}
    (impl : QueryImpl source (OracleComp target)) (f : Fin n → OracleComp source Result) :
    simulateQ impl (Concrete.sequenceFin f) =
      Concrete.sequenceFin (fun i => simulateQ impl (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure]
      congr 1
      funext head
      rw [ih]

theorem completeRecord_all_zero (inputs : Finset HashInput)
    (routing : InterleavedResidual.Routing) (record : PublicSigningRecord) :
    AllQueriesSatisfy
      (simulateQ (RetainedResidual.embed inputs routing)
        (ResidualByteFrontend.jointCompleteSigningRecord record))
      (fun query => residualCharge inputs query = 0) := by
  obtain ⟨⟨plan, view⟩, trace⟩ := record
  cases plan with
  | none =>
      cases view <;> simp [ResidualByteFrontend.jointCompleteSigningRecord]
  | some plan =>
      cases view with
      | none => simp [ResidualByteFrontend.jointCompleteSigningRecord]
      | some view =>
          simp only [ResidualByteFrontend.jointCompleteSigningRecord, simulateQ_bind]
          apply allQueriesSatisfy_bind
          · let f : Fin (ftsTrees - 1) → OracleComp (ResidualByteFrontend.World inputs) Digest :=
              fun tree => ResidualByteFrontend.jointDisclosure
                (CanonicalCoordinate.ftsStart view.1 tree (view.2 tree))
            change AllQueriesSatisfy (simulateQ (RetainedResidual.embed inputs routing)
              (Concrete.sequenceFin f)) (fun query => residualCharge inputs query = 0)
            rw [simulateQ_sequenceFin (RetainedResidual.embed inputs routing) f]
            apply all_zero_sequenceFin
            intro tree
            dsimp [f, ResidualByteFrontend.jointDisclosure, RetainedResidual.embed]
            exact (allQueriesSatisfy_query_iff _ _).2 rfl
          · intro secrets
            exact allQueriesSatisfy_pure _ _
end SphincsSecurity.WeightedCutoff

namespace SphincsSecurity.WeightedCutoff
open SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable

theorem residual_run_completeSigningWork (inputs : Finset HashInput)
    (routing : InterleavedResidual.Routing) (work : PublicSigningRecord × Nat) (budget : Nat) :
    run (residualCharge inputs)
      (simulateQ (RetainedResidual.embed inputs routing)
        (ResidualByteFrontend.jointCompleteSigningWork work)) budget =
    if work.2 ≤ budget then
      (do
        let answer ← simulateQ (RetainedResidual.embed inputs routing)
          (ResidualByteFrontend.jointCompleteSigningWork work)
        pure (some answer))
    else pure none := by
  simp only [ResidualByteFrontend.jointCompleteSigningWork, simulateQ_bind, simulateQ_spec_query,
    RetainedResidual.embed]
  rw [run_query_bind]
  by_cases allowed : residualCharge inputs (.inl (.byte routing (.account work.2))) ≤ budget
  · have hcost : work.2 ≤ budget := by simpa [residualCharge] using allowed
    rw [if_pos allowed, if_pos hcost]
    simp only [bind_assoc]
    congr 1
    funext _
    have hzero := completeRecord_all_zero inputs routing work.1
    simpa only [residualCharge] using run_all_zero (residualCharge inputs)
      (simulateQ (RetainedResidual.embed inputs routing)
        (ResidualByteFrontend.jointCompleteSigningRecord work.1)) (budget - work.2) hzero
  · have hcost : ¬work.2 ≤ budget := by simpa [residualCharge] using allowed
    rw [if_neg allowed, if_neg hcost]
end SphincsSecurity.WeightedCutoff

/-- info: 'SphincsSecurity.WeightedCutoff.run_all_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.run_all_zero

/-- info: 'SphincsSecurity.WeightedCutoff.all_zero_sequenceFin' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.all_zero_sequenceFin

/-- info: 'SphincsSecurity.WeightedCutoff.simulateQ_sequenceFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.simulateQ_sequenceFin

/-- info: 'SphincsSecurity.WeightedCutoff.completeRecord_all_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.completeRecord_all_zero

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_completeSigningWork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_completeSigningWork

namespace SphincsSecurity.WeightedCutoff
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Index : Type} {spec : OracleSpec Index}

theorem run_bind_zero_prefix {First Result : Type} (charge : spec.Domain → Nat)
    (first : OracleComp spec First) (next : First → OracleComp spec Result) (budget : Nat)
    (hzero : AllQueriesSatisfy first (fun query => charge query = 0)) :
    run charge (first >>= next) budget =
      (do let answer ← first; run charge (next answer) budget) := by
  induction first using OracleComp.inductionOn generalizing budget with
  | pure value => rfl
  | query_bind query rest ih =>
      rw [allQueriesSatisfy_query_bind_iff] at hzero
      rw [bind_assoc, run_query_bind, hzero.1]
      simp only [Nat.zero_le, if_pos, Nat.sub_zero, bind_assoc]
      congr 1
      funext answer
      exact ih answer budget (hzero.2 answer)
end SphincsSecurity.WeightedCutoff

namespace SphincsSecurity.WeightedCutoff
open SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable

theorem residual_run_completeSigningWork_bind (inputs : Finset HashInput)
    (routing : InterleavedResidual.Routing) (work : PublicSigningRecord × Nat)
    {Result : Type} (next : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) →
      OracleComp (RetainedResidual.World inputs) Result) (budget : Nat) :
    run (residualCharge inputs)
      ((simulateQ (RetainedResidual.embed inputs routing)
        (ResidualByteFrontend.jointCompleteSigningWork work)) >>= next) budget =
    if work.2 ≤ budget then
      (do
        let answer ← simulateQ (RetainedResidual.embed inputs routing)
          (ResidualByteFrontend.jointCompleteSigningWork work)
        run (residualCharge inputs) (next answer) (budget - work.2))
    else pure none := by
  simp only [ResidualByteFrontend.jointCompleteSigningWork, simulateQ_bind, simulateQ_spec_query,
    RetainedResidual.embed, bind_assoc]
  rw [run_query_bind]
  by_cases allowed : residualCharge inputs (.inl (.byte routing (.account work.2))) ≤ budget
  · have hcost : work.2 ≤ budget := by simpa [residualCharge] using allowed
    rw [if_pos allowed, if_pos hcost]
    congr 1
    funext _
    have hzero := completeRecord_all_zero inputs routing work.1
    simpa only [residualCharge] using run_bind_zero_prefix (residualCharge inputs)
      (simulateQ (RetainedResidual.embed inputs routing)
        (ResidualByteFrontend.jointCompleteSigningRecord work.1)) next (budget - work.2) hzero
  · have hcost : ¬work.2 ≤ budget := by simpa [residualCharge] using allowed
    rw [if_neg allowed, if_neg hcost]
end SphincsSecurity.WeightedCutoff

namespace SphincsSecurity.WeightedCutoff
open SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable

theorem residual_execute_all_zero (inputs : Finset HashInput)
    (routing : InterleavedResidual.Routing)
    (action : ResidualByteAction.Action inputs) :
    AllQueriesSatisfy
      (simulateQ (RetainedResidual.embed inputs routing)
        (ResidualByteFrontend.execute action))
      (fun query => residualCharge inputs query = 0) := by
  cases action with
  | known answer => exact allQueriesSatisfy_pure _ _
  | read input =>
      simp only [ResidualByteFrontend.execute, simulateQ_spec_query,
        RetainedResidual.embed, allQueriesSatisfy_query_iff, residualCharge]
  | probe input test =>
      simp only [ResidualByteFrontend.execute, simulateQ_spec_query,
        RetainedResidual.embed, allQueriesSatisfy_query_iff, residualCharge]

theorem residual_checkedPost_all_zero (inputs : Finset HashInput)
    (routing : InterleavedResidual.Routing) (reject : HashOutput → Prop)
    (answer : HashOutput) :
    AllQueriesSatisfy
      (simulateQ (RetainedResidual.embed inputs routing)
        (if reject answer then
          liftM ((ResidualByteFrontend.World inputs).query (.inl .stop))
        else pure answer))
      (fun query => residualCharge inputs query = 0) := by
  by_cases h : reject answer
  · simp only [if_pos h, simulateQ_spec_query, RetainedResidual.embed,
      allQueriesSatisfy_query_iff, residualCharge]
  · simp only [if_neg h, simulateQ_pure, allQueriesSatisfy_pure]

theorem residual_checkedTail_all_zero (inputs : Finset HashInput)
    (routing : InterleavedResidual.Routing) (reject : HashOutput → Prop)
    (action : ResidualByteAction.Action inputs) :
    AllQueriesSatisfy
      (simulateQ (RetainedResidual.embed inputs routing) (do
        let answer ← ResidualByteFrontend.execute action
        if reject answer then liftM ((ResidualByteFrontend.World inputs).query (.inl .stop))
        else pure answer))
      (fun query => residualCharge inputs query = 0) := by
  simp only [simulateQ_bind]
  apply allQueriesSatisfy_bind (residual_execute_all_zero inputs routing action)
  intro answer
  exact residual_checkedPost_all_zero inputs routing reject answer

end SphincsSecurity.WeightedCutoff

namespace SphincsSecurity.WeightedCutoff
open SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable

theorem residual_run_checkedHashQuery_bind (inputs : Finset HashInput)
    (routing : InterleavedResidual.Routing)
    (reject : HashInput → HashOutput → Prop) (input : inputs)
    {Result : Type} (next : HashOutput → OracleComp (RetainedResidual.World inputs) Result)
    (budget : Nat) :
    run (residualCharge inputs)
      ((simulateQ (RetainedResidual.embed inputs routing)
        (ResidualByteFrontend.checkedHashQuery reject input)) >>= next) budget =
    if 1 ≤ budget then
      (do
        let answer ← simulateQ (RetainedResidual.embed inputs routing)
          (ResidualByteFrontend.checkedHashQuery reject input)
        run (residualCharge inputs) (next answer) (budget - 1))
    else pure none := by
  simp only [ResidualByteFrontend.checkedHashQuery, ResidualByteFrontend.hashQuery,
    simulateQ_bind, simulateQ_spec_query, RetainedResidual.embed, bind_assoc]
  rw [run_query_bind]
  by_cases allowed : residualCharge inputs (.inl (.byte routing (.prepare input))) ≤ budget
  · have h1 : 1 ≤ budget := by simpa [residualCharge] using allowed
    rw [if_pos allowed, if_pos h1]
    congr 1
    funext action
    have hzero := residual_checkedTail_all_zero inputs routing (reject input.val) action
    convert run_bind_zero_prefix (residualCharge inputs)
      (simulateQ (RetainedResidual.embed inputs routing) (do
        let answer ← ResidualByteFrontend.execute action
        if reject input.val answer then liftM ((ResidualByteFrontend.World inputs).query (.inl .stop))
        else pure answer)) next (budget - 1) hzero using 1
    all_goals first | rfl | simp only [residualCharge, simulateQ_bind, bind_assoc,
      ResidualByteFrontend.World]
    congr 1
  · have h1 : ¬1 ≤ budget := by simpa [residualCharge] using allowed
    rw [if_neg allowed, if_neg h1]
end SphincsSecurity.WeightedCutoff

/-- info: 'SphincsSecurity.WeightedCutoff.run_bind_zero_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.run_bind_zero_prefix

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_completeSigningWork_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_completeSigningWork_bind

/-- info: 'SphincsSecurity.WeightedCutoff.residual_execute_all_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_execute_all_zero

/-- info: 'SphincsSecurity.WeightedCutoff.residual_checkedPost_all_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_checkedPost_all_zero

/-- info: 'SphincsSecurity.WeightedCutoff.residual_checkedTail_all_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_checkedTail_all_zero

/-- info: 'SphincsSecurity.WeightedCutoff.residual_run_checkedHashQuery_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.residual_run_checkedHashQuery_bind
