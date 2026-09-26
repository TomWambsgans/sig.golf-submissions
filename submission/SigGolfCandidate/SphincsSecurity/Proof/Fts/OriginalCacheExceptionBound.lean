import SigGolfCandidate.SphincsSecurity.Proof.Fts.OriginalMessageAllocation
import SigGolfCandidate.SphincsSecurity.Proof.Reference.ReferencePrimitiveBound
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateCacheExceptionKernels
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryCapErasure
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] scheme certificateCacheExceptionWeight expectedBoundaryMessageCalls
  certificateCacheLengthImpl certificateLengthImpl certificateCacheProposalImpl

noncomputable def originalCacheHistoryWeight (key : SecretKey) (state : CertificateCacheMonitorState) : ENNReal :=
  if state.2.2 then 1 else certificateCacheExceptionWeight key state.1

private theorem probOutput_probCompLift {Result : Type} (computation : ProbComp Result) (result : Result) :
    Pr[= result | (liftM computation : PMF Result)] = Pr[= result | computation] := rfl

noncomputable def romPmfImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) PMF) :=
  fun input => StateT.mk fun cache => (liftM ((romImpl input).run cache) : PMF _)

/-- Lazy-oracle state for a query-level stopped cache-exception monitor. The
    third component is the remaining hash-query budget. -/
abbrev CertificateStoppedCacheState := QueryCache HashSpec × (Bool × Nat)

noncomputable def certificateStoppedRomImpl (key : SecretKey) :
    QueryImpl OracleWorld (StateT CertificateStoppedCacheState PMF) :=
  fun input => StateT.mk fun state =>
    ((romPmfImpl input).run state.1).map fun result =>
      (result.1, (result.2,
        (state.2.1 || decide (CertificateCacheExceptional key state.1) ||
          decide (CertificateCacheExceptional key result.2),
          state.2.2 - if input matches .inr _ then 1 else 0)))

theorem certificateStoppedRomImpl_cache_project (key : SecretKey)
    (input : OracleWorld.Domain) (state : CertificateStoppedCacheState) :
    Prod.map id Prod.fst <$> (certificateStoppedRomImpl key input).run state =
      (romPmfImpl input).run state.1 := by
  change PMF.map _ _ = _
  simp only [certificateStoppedRomImpl, StateT.run_mk, PMF.map_comp]
  have hfun :
      (Prod.map id Prod.fst ∘ fun result : OracleWorld.Range input × QueryCache HashSpec =>
        (result.1, (result.2,
          (state.2.1 || decide (CertificateCacheExceptional key state.1) ||
            decide (CertificateCacheExceptional key result.2),
            state.2.2 - if input matches .inr _ then 1 else 0)))) = id := by
    funext result
    rfl
  rw [hfun, PMF.map_id]

theorem certificateStoppedRomImpl_run_cache_project {Result : Type}
    (key : SecretKey) (computation : OracleComp OracleWorld Result)
    (state : CertificateStoppedCacheState) :
    Prod.map id Prod.fst <$>
      (simulateQ (certificateStoppedRomImpl key) computation).run state =
    (simulateQ romPmfImpl computation).run state.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (certificateStoppedRomImpl_cache_project key) computation state

theorem certificateStoppedRomImpl_hit_step (key : SecretKey)
    (input : OracleWorld.Domain) (state : CertificateStoppedCacheState)
    (result : OracleWorld.Range input × CertificateStoppedCacheState)
    (hr : result ∈ ((certificateStoppedRomImpl key input).run state).support) :
    (state.2.1 = true → result.2.2.1 = true) ∧
      (CertificateCacheExceptional key result.2.1 → result.2.2.1 = true) := by
  simp only [certificateStoppedRomImpl, StateT.run_mk, PMF.mem_support_map_iff] at hr
  obtain ⟨source, _, rfl⟩ := hr
  constructor
  · intro hhit
    simp [hhit]
  · intro hbad
    simp [hbad]

theorem certificateStoppedRomImpl_hit_run {Result : Type} (key : SecretKey)
    (computation : OracleComp OracleWorld Result) :
    ∀ (state : CertificateStoppedCacheState)
      (result : Result × CertificateStoppedCacheState),
      (CertificateCacheExceptional key state.1 → state.2.1 = true) →
      result ∈ ((simulateQ (certificateStoppedRomImpl key) computation).run state).support →
      (state.2.1 = true → result.2.2.1 = true) ∧
        (CertificateCacheExceptional key result.2.1 → result.2.2.1 = true) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro state result hcover hr
      simp only [simulateQ_pure, StateT.run_pure,
        PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      exact ⟨id, hcover⟩
  | query_bind input next ih =>
      intro state result hcover hr
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, htail⟩ := hr
      have hstep := certificateStoppedRomImpl_hit_step key input state middle hmiddle
      have hnext := ih middle.1 middle.2 result hstep.2 htail
      exact ⟨fun hhit => hnext.1 (hstep.1 hhit), hnext.2⟩

/-- A ghost state can be carried through the independent proposal-length
    sample without changing the original length/record distribution. -/
theorem recordLengthBridge_joint_project {Ω Γ : Type} (law : PMF (Ω × Γ))
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (fun output : Nat × (Ω × Γ) => (output.1, output.2.1)) <$>
      recordLengthBridge law accept hpos hle =
    recordLengthBridge (Prod.fst <$> law) accept hpos hle := by
  change PMF.map _ _ = _
  rw [recordLengthBridge, PMF.map_bind, recordLengthBridge,
    PMF.monad_map_eq_map, PMF.bind_map]
  apply PMF.bind_congr
  intro pair _
  simp only [PMF.map_comp]
  rfl

/-- The enriched signing record retains the cache-hit monitor while exposing
    the same signing view, boundary trace, and selected index as the original
    proposal record. -/
noncomputable def enrichedSigningRecord (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState) :
    PMF (ProposalExecutionRecord (.inr message) × CertificateStoppedCacheState) :=
  ((simulateQ (certificateStoppedRomImpl key)
      (boundaryComputation key.parameter (signWithView key message))).run state).bind
    fun result =>
      (liftM (completeSelectedIndex result.1.1.2) : PMF Index).map fun index =>
        (⟨result.1.1.1, result.2.1, result.1.2, result.1.1.2, index⟩, result.2)

theorem enrichedSigningRecord_project (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState) :
    (enrichedSigningRecord key message state).map Prod.fst =
      originalProposalRecord key (.inr message) state.1 := by
  have hsource := certificateStoppedRomImpl_run_cache_project key
    (boundaryComputation key.parameter (signWithView key message)) state
  unfold romPmfImpl at hsource
  rw [simulateQ_liftProbCompImpl_run romImpl] at hsource
  conv_rhs at hsource => rw [simulateQ_boundaryComputation]
  change (Prod.map id Prod.fst <$>
    (simulateQ (certificateStoppedRomImpl key)
      (boundaryComputation key.parameter (signWithView key message))).run state) =
    (liftM (tracedSigningRun (signingBoundaryTrace key.parameter) key message state.1) : PMF _) at hsource
  rw [enrichedSigningRecord, PMF.map_bind]
  simp only [PMF.map_comp]
  rw [originalProposalRecord, completedSigningRecord, PMF.map_bind]
  rw [← hsource]
  rw [PMF.monad_map_eq_map, PMF.bind_map]
  apply PMF.bind_congr
  intro result _
  simp only [PMF.map_comp]
  rfl

/-- A capped signer run retains the complete signing trace as well as the
    monitored cache. A successful result can therefore be made into the same
    proposal record as an uncapped signing run. -/
noncomputable def stoppedTracedSigningRun (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState) :
    PMF (Option (((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × Nat) ×
      CertificateStoppedCacheState) :=
  (simulateQ (certificateStoppedRomImpl key) (QueryCap.run
    (fun input : OracleWorld.Domain => input matches .inr _)
    (boundaryComputation key.parameter (signWithView key message)) state.2.2)).run state

noncomputable def enrichedStoppedSigningRecord (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState) :
    PMF (Option (ProposalExecutionRecord (.inr message) × CertificateStoppedCacheState)) :=
  (stoppedTracedSigningRun key message state).bind fun result =>
    match result.1 with
    | none => PMF.pure none
    | some (output, _) =>
        (liftM (completeSelectedIndex output.1.2) : PMF Index).map fun index =>
          some (⟨output.1.1, result.2.1, output.2, output.1.2, index⟩, result.2)

/-- For a boundary-traced computation, the selected-query counter and the
    trace's hash-call count agree on the same outcome. -/
theorem counted_boundaryComputation_eq_trace {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) :
    QueryCap.counted (fun input : OracleWorld.Domain => input matches .inr _)
      (boundaryComputation parameter computation) =
    (fun result : α × SigningBoundaryTrace => (result, result.2.hashCalls)) <$>
      boundaryComputation parameter computation := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp [boundaryComputation, QueryCap.counted_pure, SigningBoundaryTrace.hashCalls]
  | query_bind input next ih =>
      rw [show boundaryComputation parameter
        (liftM (OracleWorld.query input) >>= next) =
        QueryPause.traced (signingBoundaryTrace parameter)
          (liftM (OracleWorld.query input) >>= next) from rfl]
      rw [QueryPause.traced_query_bind]
      rw [QueryCap.counted_query_bind]
      simp only [QueryCap.counted_map]
      simp_rw [show ∀ answer, QueryPause.traced (signingBoundaryTrace parameter) (next answer) =
        boundaryComputation parameter (next answer) from fun _ => rfl]
      simp_rw [ih]
      simp only [map_bind, Functor.map_map, SigningBoundaryTrace.hashCalls_mul,
        signingBoundaryTrace_hashCalls_eq]
      simp only [bind_pure_comp, Functor.map_map]
      cases input <;> rfl

/-- A capped, stateful signing run has exactly the uncapped probability of
    each successful result whose trace fits the initial query budget. -/
theorem stoppedTracedSigningRun_budget_event (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState)
    (event : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) →
      CertificateStoppedCacheState → Prop) :
    Pr[QueryCap.stoppedStateEvent event | stoppedTracedSigningRun key message state] =
    Pr[fun output => output.1.2.hashCalls ≤ state.2.2 ∧ event output.1 output.2 |
      (simulateQ (certificateStoppedRomImpl key)
        (boundaryComputation key.parameter (signWithView key message))).run state] := by
  rw [stoppedTracedSigningRun, QueryCap.run_budget_event_state]
  rw [counted_boundaryComputation_eq_trace]
  simp only [simulateQ_map, StateT.run_map, probEvent_map, Function.comp_def]

/-- Forget the remaining budget after a stopped signing run. Only successful
    outcomes are compared with uncapped executions; stopped failures may have
    a different final cache. -/
noncomputable def stoppedSigningProjected (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState) :
    PMF (Option (((Option Signature × Option FewTimeView) × SigningBoundaryTrace) ×
      CertificateStoppedCacheState)) :=
  (stoppedTracedSigningRun key message state).map fun result =>
    result.1.map fun out => (out.1, result.2)

theorem stoppedSigningProjected_some (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState)
    (x : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) ×
      CertificateStoppedCacheState) :
    stoppedSigningProjected key message state (some x) =
      if x.1.2.hashCalls ≤ state.2.2 then
        ((simulateQ (certificateStoppedRomImpl key)
          (boundaryComputation key.parameter (signWithView key message))).run state) x
      else 0 := by
  classical
  have h := stoppedTracedSigningRun_budget_event key message state
    (fun output finalState => (output, finalState) = x)
  rw [show Pr[QueryCap.stoppedStateEvent
      (fun output finalState => (output, finalState) = x) |
      stoppedTracedSigningRun key message state] =
      Pr[fun result => result = some x | stoppedSigningProjected key message state] from by
        rw [stoppedSigningProjected, ← PMF.monad_map_eq_map, probEvent_map]
        congr 1
        funext result
        cases hresult : result.1 with
        | none => simp [QueryCap.stoppedStateEvent, hresult]
        | some out =>
            rcases out with ⟨value, remaining⟩
            simp [QueryCap.stoppedStateEvent, hresult]] at h
  rw [probEvent_eq_eq_probOutput] at h
  simp only [probOutput_def] at h
  by_cases hb : x.1.2.hashCalls ≤ state.2.2
  · have hpred : (fun output => output.1.2.hashCalls ≤ state.2.2 ∧
        (output.1, output.2) = x) = (fun output => output = x) := by
      funext output
      apply propext
      constructor
      · exact fun hout => by simpa using hout.2
      · intro hout
        subst output
        exact ⟨hb, rfl⟩
    rw [hpred, probEvent_eq_eq_probOutput] at h
    simpa [hb, probOutput_def] using h
  · have hpred : (fun (output : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) ×
        CertificateStoppedCacheState) => output.1.2.hashCalls ≤ state.2.2 ∧
        (output.1, output.2) = x) = (fun _ => False) := by
      funext output
      apply propext
      constructor
      · intro hout
        have heq : output = x := by simpa using hout.2
        subst output
        exact hb hout.1
      · exact False.elim
    rw [hpred] at h
    simpa [hb, probEvent_eq_tsum_ite] using h

/-- A downstream randomized kernel preserves the successful branch of a
    stopped execution, without comparing its failure-state distribution. -/
private theorem some_kernel_transfer {A B : Type} (p : PMF (Option A)) (q : PMF A)
    (good : A → Prop) [DecidablePred good] (hp : ∀ a, p (some a) = if good a then q a else 0)
    (k : A → PMF B) (event : B → Prop) :
    Pr[fun r : Option B => r.elim False event |
      p.bind (fun r => match r with
        | none => PMF.pure none
        | some a => (k a).map some)] =
    Pr[fun r : Option B => r.elim False event |
      q.bind (fun a => if good a then (k a).map some else PMF.pure none)] := by
  classical
  rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum,
    ← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum]
  rw [tsum_option _ ENNReal.summable]
  have hnone : Pr[fun r : Option B => r.elim False event |
      (PMF.pure none : PMF (Option B))] = 0 := by
    rw [← PMF.monad_pure_eq_pure, probEvent_pure]
    simp
  simp only [probOutput_def, hnone, mul_zero, zero_add]
  apply tsum_congr
  intro a
  simp at *
  rw [hp]
  by_cases ha : good a
  · simp [ha]
  · simp [ha, hnone]

noncomputable def signingRecordKernel (_key : SecretKey) (message : Message)
    (x : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) ×
      CertificateStoppedCacheState) :
    PMF (ProposalExecutionRecord (.inr message) × CertificateStoppedCacheState) :=
  (liftM (completeSelectedIndex x.1.1.2) : PMF Index).map fun index =>
    (⟨x.1.1.1, x.2.1, x.1.2, x.1.1.2, index⟩, x.2)

theorem enrichedStoppedSigningRecord_kernel (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState) :
    enrichedStoppedSigningRecord key message state =
      (stoppedSigningProjected key message state).bind fun result =>
        match result with
        | none => PMF.pure none
        | some x => (signingRecordKernel key message x).map some := by
  rw [stoppedSigningProjected, PMF.bind_map]
  unfold enrichedStoppedSigningRecord signingRecordKernel
  apply PMF.bind_congr
  intro result _
  cases hresult : result.1 with
  | none => simp [hresult]
  | some out =>
      rcases out with ⟨value, remaining⟩
      simp [hresult, PMF.map_comp]
      rfl

/-- The capped signer yields exactly the uncapped successful proposal-record
    events whose actual signing trace fits the budget, including the selected
    index sampled after signing. -/
theorem enrichedStoppedSigningRecord_budget_event (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState)
    (event : (ProposalExecutionRecord (.inr message) × CertificateStoppedCacheState) → Prop) :
    Pr[fun result => result.elim False event |
      enrichedStoppedSigningRecord key message state] =
    Pr[fun result => result.elim False event |
      ((simulateQ (certificateStoppedRomImpl key)
        (boundaryComputation key.parameter (signWithView key message))).run state).bind
        (fun x => if x.1.2.hashCalls ≤ state.2.2 then
          (signingRecordKernel key message x).map some else PMF.pure none)] := by
  rw [enrichedStoppedSigningRecord_kernel]
  convert some_kernel_transfer
    (stoppedSigningProjected key message state)
    ((simulateQ (certificateStoppedRomImpl key)
      (boundaryComputation key.parameter (signWithView key message))).run state)
    (fun x => x.1.2.hashCalls ≤ state.2.2)
    (stoppedSigningProjected_some key message state)
    (signingRecordKernel key message) event using 1
  all_goals
    congr 1
    congr 1
    funext r
    cases r <;> rfl

theorem enrichedSigningRecord_kernel (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState) :
    enrichedSigningRecord key message state =
      ((simulateQ (certificateStoppedRomImpl key)
        (boundaryComputation key.parameter (signWithView key message))).run state).bind
        (signingRecordKernel key message) := by
  rfl

/-- Successful stopped signer records project to the actual proposal record,
    restricted by its own trace cost. -/
theorem enrichedStoppedSigningRecord_original_budget_event (key : SecretKey)
    (message : Message) (state : CertificateStoppedCacheState)
    (event : ProposalExecutionRecord (.inr message) → Prop) :
    Pr[fun result => result.elim False (fun record => event record.1) |
      enrichedStoppedSigningRecord key message state] =
    Pr[fun record => record.trace.hashCalls ≤ state.2.2 ∧ event record |
      originalProposalRecord key (.inr message) state.1] := by
  classical
  have h := enrichedStoppedSigningRecord_budget_event key message state
    (fun record => event record.1)
  rw [← enrichedSigningRecord_project, ← PMF.monad_map_eq_map, probEvent_map,
    enrichedSigningRecord_kernel]
  rw [h]
  rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum,
    ← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro x
  congr 1
  by_cases hb : x.1.2.hashCalls ≤ state.2.2
  · simp only [if_pos hb, ← PMF.monad_map_eq_map, probEvent_map,
      Function.comp_def, Option.elim_some, signingRecordKernel]
    simp [hb]
  · simp only [if_neg hb]
    simp only [← PMF.monad_map_eq_map, probEvent_map, signingRecordKernel,
      Function.comp_def]
    simp [hb, probEvent_eq_tsum_ite]
    intro i hi
    cases i <;> simp at *

/-- The full proposal record and the monitored cache have the same joint law
    on successful within-budget executions. -/
theorem enrichedStoppedSigningRecord_unbounded_budget_event (key : SecretKey)
    (message : Message) (state : CertificateStoppedCacheState)
    (event : (ProposalExecutionRecord (.inr message) × CertificateStoppedCacheState) → Prop) :
    Pr[fun result => result.elim False event |
      enrichedStoppedSigningRecord key message state] =
    Pr[fun record => record.1.trace.hashCalls ≤ state.2.2 ∧ event record |
      enrichedSigningRecord key message state] := by
  classical
  have h := enrichedStoppedSigningRecord_budget_event key message state event
  rw [enrichedSigningRecord_kernel]
  rw [h]
  rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum,
    ← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro x
  congr 1
  by_cases hb : x.1.2.hashCalls ≤ state.2.2
  · simp only [if_pos hb, ← PMF.monad_map_eq_map, probEvent_map,
      Function.comp_def, Option.elim_some, signingRecordKernel]
    simp [hb]
  · simp only [if_neg hb]
    simp only [← PMF.monad_map_eq_map, probEvent_map, signingRecordKernel,
      Function.comp_def]
    simp [hb, probEvent_eq_tsum_ite]
    intro i hi
    cases i <;> simp at *

theorem enrichedStoppedSigningRecord_some (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState)
    (x : ProposalExecutionRecord (.inr message) × CertificateStoppedCacheState) :
    enrichedStoppedSigningRecord key message state (some x) =
      if x.1.trace.hashCalls ≤ state.2.2 then
        enrichedSigningRecord key message state x else 0 := by
  classical
  have h := enrichedStoppedSigningRecord_unbounded_budget_event key message state
    (fun record => record = x)
  have hleft : (fun result : Option (ProposalExecutionRecord (.inr message) ×
      CertificateStoppedCacheState) => result.elim False (fun record => record = x)) =
      (fun result => result = some x) := by
    funext result
    cases result <;> simp
  rw [hleft, probEvent_eq_eq_probOutput] at h
  simp only [probOutput_def] at h
  by_cases hb : x.1.trace.hashCalls ≤ state.2.2
  · have hpred : (fun record => record.1.trace.hashCalls ≤ state.2.2 ∧ record = x) =
        (fun record => record = x) := by
      funext record
      apply propext
      constructor
      · exact And.right
      · intro heq
        subst record
        exact ⟨hb, rfl⟩
    rw [hpred, probEvent_eq_eq_probOutput] at h
    simpa [hb, probOutput_def] using h
  · have hpred : (fun record : ProposalExecutionRecord (.inr message) ×
        CertificateStoppedCacheState => record.1.trace.hashCalls ≤ state.2.2 ∧ record = x) =
        (fun _ => False) := by
      funext record
      apply propext
      constructor
      · intro hr
        rw [hr.2] at hr
        exact hb hr.1
      · exact False.elim
    rw [hpred] at h
    simpa [hb, probEvent_eq_tsum_ite] using h

theorem originalProposalRecord_budget_event (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (spent q : Nat) (event : QueryCache HashSpec → Prop) :
    Pr[fun record => event record.cache ∧ spent + record.trace.hashCalls ≤ q |
      originalProposalRecord key input cache] =
    Pr[fun result => event result.2 ∧ spent + result.1.2 ≤ q |
      (simulateQ romImpl (countHashQueries (expandedAdversaryImpl key input))).run cache] := by
  rw [← boundaryRun_count key.parameter (expandedAdversaryImpl key input) cache, probEvent_map]
  have h := congrArg (fun law : PMF _ => Pr[fun result =>
      event result.2 ∧ spent + result.1.2.hashCalls ≤ q | law])
    (originalProposalRecord_boundary key input cache)
  rw [← PMF.monad_map_eq_map, probEvent_map] at h
  simpa only [Function.comp_def, probEvent_eq_tsum_ite, probOutput_probCompLift] using h

theorem originalProposalRecord_cache_exception_budget_event (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) (q : Nat) :
    Pr[fun record => CertificateCacheExceptional key record.cache ∧ record.trace.hashCalls ≤ q |
      originalProposalRecord key input cache] =
    Pr[fun result => CertificateCacheExceptional key result.2 ∧ result.1.2 ≤ q |
      (simulateQ romImpl (countHashQueries (expandedAdversaryImpl key input))).run cache] := by
  simpa only [Nat.zero_add] using originalProposalRecord_budget_event key input cache 0 q
    (CertificateCacheExceptional key)

theorem originalProposalRecord_budget_stopped_event (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (spent q : Nat) (hspent : spent ≤ q) (event : QueryCache HashSpec → Prop) :
    Pr[fun record => event record.cache ∧ spent + record.trace.hashCalls ≤ q |
      originalProposalRecord key input cache] =
    Pr[QueryCap.stoppedStateEvent (fun _ finalCache => event finalCache) |
      (simulateQ romPmfImpl (QueryCap.run
        (fun query : OracleWorld.Domain => query matches .inr _)
        (expandedAdversaryImpl key input) (q - spent))).run cache] := by
  rw [originalProposalRecord_budget_event]
  have hpred :
      (fun result : (((OracleWorld + SigningSpec).Range input × Nat) × QueryCache HashSpec) =>
        event result.2 ∧ spent + result.1.2 ≤ q) =
      (fun result => result.1.2 ≤ q - spent ∧ event result.2) := by
    funext result
    apply propext
    constructor
    · intro ⟨hevent, hcost⟩
      exact ⟨by omega, hevent⟩
    · intro ⟨hcost, hevent⟩
      exact ⟨hevent, by omega⟩
  rw [hpred]
  have hcap := QueryCap.run_budget_event_state
    (fun query : OracleWorld.Domain => query matches .inr _)
    romPmfImpl (expandedAdversaryImpl key input) (q - spent) cache
    (fun (_ : (OracleWorld + SigningSpec).Range input)
      (finalCache : QueryCache HashSpec) => event finalCache)
  have hcountLaw :
      (simulateQ romPmfImpl (QueryCap.counted
        (fun query : OracleWorld.Domain => query matches .inr _)
        (expandedAdversaryImpl key input))).run cache =
      (liftM ((simulateQ romImpl
        (countHashQueries (expandedAdversaryImpl key input))).run cache) : PMF _) := by
    change (simulateQ (fun query => StateT.mk fun current =>
      (liftM ((romImpl query).run current) : PMF _))
        (QueryCap.counted (fun query : OracleWorld.Domain => query matches .inr _)
          (expandedAdversaryImpl key input))).run cache =
      (liftM ((simulateQ romImpl
        (QueryCap.counted (fun query : OracleWorld.Domain => query matches .inr _)
          (expandedAdversaryImpl key input))).run cache) : PMF _)
    exact simulateQ_liftProbCompImpl_run romImpl _ cache
  calc
    _ = Pr[fun result => result.1.2 ≤ q - spent ∧ event result.2 |
        (liftM ((simulateQ romImpl
          (countHashQueries (expandedAdversaryImpl key input))).run cache) : PMF _)] := by
      simp only [probEvent_eq_tsum_ite, probOutput_probCompLift]
    _ = Pr[fun result => result.1.2 ≤ q - spent ∧ event result.2 |
        (simulateQ romPmfImpl (QueryCap.counted
          (fun query : OracleWorld.Domain => query matches .inr _)
          (expandedAdversaryImpl key input))).run cache] := by rw [hcountLaw]
    _ = _ := hcap.symm

private theorem certificateCountedLengthImpl_event_of_record (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (counter : CertificateCountedState → Prop)
    (weight : ProposalExecutionRecord input → Prop)
    (hadvance : ∀ length record, counter
      (originalProposalAdvance (certificateCountedUpdate key budget required stopAfter)
        input state length record) ↔ weight record) :
    Pr[fun result => counter result.2 |
      (certificateCountedLengthImpl key budget required stopAfter input).run state] =
    Pr[weight | originalProposalRecord key input state.1] := by
  simp only [certificateCountedLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk]
  split
  · rw [← PMF.monad_map_eq_map, probEvent_map]
    simp only [Function.comp_def, hadvance]
    have h := congrArg (fun law : PMF (ProposalExecutionRecord input) => Pr[weight | law])
      (recordLengthBridge_record (originalProposalRecord key input state.1)
        targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le)
    rw [← PMF.monad_map_eq_map, probEvent_map] at h
    exact h
  · rw [← PMF.monad_map_eq_map, probEvent_map]
    simp only [Function.comp_def, hadvance]

theorem certificateCountedLengthImpl_hit_budget_stopped_event (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (q : Nat) (hspent : state.2.2 ≤ q) :
    Pr[fun result => result.2.2.1.2 = true ∧ result.2.2.2 ≤ q |
      (certificateCountedLengthImpl key budget required stopAfter input).run state] =
    Pr[QueryCap.stoppedStateEvent (fun _ finalCache =>
      (state.2.1.2 || decide (CertificateCacheExceptional key state.1) ||
        decide (CertificateCacheExceptional key finalCache)) = true) |
      (simulateQ romPmfImpl (QueryCap.run
        (fun query : OracleWorld.Domain => query matches .inr _)
        (expandedAdversaryImpl key input) (q - state.2.2))).run state.1] := by
  let hit : QueryCache HashSpec → Prop := fun finalCache =>
    (state.2.1.2 || decide (CertificateCacheExceptional key state.1) ||
      decide (CertificateCacheExceptional key finalCache)) = true
  have hstep := certificateCountedLengthImpl_event_of_record key budget required stopAfter input state
    (fun after => after.2.1.2 = true ∧ after.2.2 ≤ q)
    (fun record => hit record.cache ∧ state.2.2 + record.trace.hashCalls ≤ q)
    (by intro length record; rfl)
  exact hstep.trans (originalProposalRecord_budget_stopped_event key input state.1
    state.2.2 q hspent hit)

theorem certificateCountedLengthImpl_hit_budget_le_stopped_monitor (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (q : Nat) (hspent : state.2.2 ≤ q) :
    Pr[fun result => result.2.2.1.2 = true ∧ result.2.2.2 ≤ q |
      (certificateCountedLengthImpl key budget required stopAfter input).run state] ≤
    Pr[QueryCap.stoppedStateEvent (fun _ finalState => finalState.2.1 = true) |
      (simulateQ (certificateStoppedRomImpl key) (QueryCap.run
        (fun query : OracleWorld.Domain => query matches .inr _)
        (expandedAdversaryImpl key input) (q - state.2.2))).run
        (state.1, ((state.2.1.2 || decide (CertificateCacheExceptional key state.1)),
          q - state.2.2))] := by
  let selected : OracleWorld.Domain → Prop :=
    fun query => query matches .inr _
  let computation := QueryCap.run selected (expandedAdversaryImpl key input) (q - state.2.2)
  let initial : CertificateStoppedCacheState :=
    (state.1, (state.2.1.2 || decide (CertificateCacheExceptional key state.1),
      q - state.2.2))
  have hprojection := certificateStoppedRomImpl_run_cache_project key computation initial
  have hprob := congrArg (fun law : PMF _ => Pr[QueryCap.stoppedStateEvent
      (fun _ finalCache =>
        (state.2.1.2 || decide (CertificateCacheExceptional key state.1) ||
          decide (CertificateCacheExceptional key finalCache)) = true) | law]) hprojection
  rw [PMF.monad_map_eq_map] at hprob
  rw [← PMF.monad_map_eq_map, probEvent_map] at hprob
  calc
    _ = Pr[QueryCap.stoppedStateEvent (fun _ finalCache =>
          (state.2.1.2 || decide (CertificateCacheExceptional key state.1) ||
            decide (CertificateCacheExceptional key finalCache)) = true) |
          (simulateQ romPmfImpl computation).run state.1] := by
        simpa only [selected, computation] using
          certificateCountedLengthImpl_hit_budget_stopped_event key budget required
            stopAfter input state q hspent
    _ = Pr[fun result => QueryCap.stoppedStateEvent (fun _ finalCache =>
          (state.2.1.2 || decide (CertificateCacheExceptional key state.1) ||
            decide (CertificateCacheExceptional key finalCache)) = true)
          (result.1, result.2.1) |
          (simulateQ (certificateStoppedRomImpl key) computation).run initial] := hprob.symm
    _ ≤ Pr[QueryCap.stoppedStateEvent (fun _ finalState => finalState.2.1 = true) |
          (simulateQ (certificateStoppedRomImpl key) computation).run initial] := by
        rw [← SPMF.probEvent_liftM, ← SPMF.probEvent_liftM]
        apply probEvent_mono
        intro result hr hhit
        have hcover : CertificateCacheExceptional key initial.1 → initial.2.1 = true := by
          intro hbad
          simp [initial, hbad]
        have hinvariant := certificateStoppedRomImpl_hit_run key computation initial result
          hcover (by simpa only [SPMF.support_eq_support, SPMF.support_liftM] using hr)
        cases hoption : result.1 with
        | none => simp [QueryCap.stoppedStateEvent, hoption] at hhit
        | some outcome =>
            simp only [QueryCap.stoppedStateEvent, hoption] at hhit ⊢
            rcases (Bool.or_eq_true _ _).mp hhit with hbefore | hfinal
            · exact hinvariant.1 (by simpa only [initial] using hbefore)
            · exact hinvariant.2 (of_decide_eq_true hfinal)
    _ = _ := rfl

/-- One adaptive outer-oracle step is controlled by the query-level stopped
    monitor, even when the chosen query depends on the preceding history. -/
theorem certificateCountedLengthImpl_adaptive_hit_budget_le_stopped_monitor
    {History : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (history : PMF (History × CertificateCountedState))
    (input : History → (OracleWorld + SigningSpec).Domain) (q : Nat) :
    Pr[fun after => after.2.1.2 = true ∧ after.2.2 ≤ q |
      history.bind (fun before =>
        Prod.snd <$> (certificateCountedLengthImpl key budget required stopAfter
          (input before.1)).run before.2)] ≤
    ∑' before, Pr[= before | history] *
      if before.2.2.2 ≤ q then
        Pr[QueryCap.stoppedStateEvent (fun _ finalState => finalState.2.1 = true) |
          (simulateQ (certificateStoppedRomImpl key) (QueryCap.run
            (fun query : OracleWorld.Domain => query matches .inr _)
            (expandedAdversaryImpl key (input before.1)) (q - before.2.2.2))).run
            (before.2.1,
              (before.2.2.1.2 || decide (CertificateCacheExceptional key before.2.1),
                q - before.2.2.2))]
      else 0 := by
  rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro before
  apply mul_le_mul' le_rfl
  change Pr[fun after => after.2.1.2 = true ∧ after.2.2 ≤ q |
      PMF.map Prod.snd
        ((certificateCountedLengthImpl key budget required stopAfter
          (input before.1)).run before.2)] ≤ _
  rw [← PMF.monad_map_eq_map, probEvent_map]
  simp only [Function.comp_def]
  by_cases hspent : before.2.2.2 ≤ q
  · simp only [if_pos hspent]
    exact certificateCountedLengthImpl_hit_budget_le_stopped_monitor key budget
      required stopAfter (input before.1) before.2 q hspent
  · simp only [if_neg hspent]
    rw [certificateCountedLengthImpl_event_of_record key budget required stopAfter
      (input before.1) before.2
      (fun after => after.2.1.2 = true ∧ after.2.2 ≤ q)
      (fun record =>
        (before.2.2.1.2 || decide (CertificateCacheExceptional key before.2.1) ||
          decide (CertificateCacheExceptional key record.cache)) = true ∧
        before.2.2.2 + record.trace.hashCalls ≤ q)
      (by intro length record; rfl)]
    have hcost (record : ProposalExecutionRecord (input before.1)) :
        ¬ before.2.2.2 + record.trace.hashCalls ≤ q := by omega
    simp only [probEvent_eq_tsum_ite, hcost, and_false, if_false, tsum_zero]
    exact le_rfl

/-- Key generation leaves no cache-exception event for its own secret key. -/
theorem certificateStoppedKeygen_cache_clean
    (generated : ((PublicKey × SecretKey) × SigningBoundaryTrace) × QueryCache HashSpec)
    (hg : generated ∈ support (boundaryRun 0 scheme.keygen ∅)) :
    ¬ CertificateCacheExceptional generated.1.1.2 generated.2 := by
  have hrun : (generated.1.1, generated.2) ∈
      support ((simulateQ romImpl scheme.keygen).run ∅) := by
    rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
    exact ⟨generated, hg, rfl⟩
  have hfinite := finite_cache_of_mem_support scheme.keygen ∅
    generated.1.1 generated.2 hrun finite_empty
  have hzero := certificateCacheExceptionWeight_initial generated.1.1.2 generated.2
    (keygen_cache_message_none (generated.1.1, generated.2) hrun)
  intro hbad
  have hweight := certificateCacheExceptionWeight_bad generated.1.1.2 generated.2
    hfinite hbad
  rw [hzero] at hweight
  norm_num at hweight

abbrev CertificateKeygenBoundaryResult :=
  ((PublicKey × SecretKey) × SigningBoundaryTrace) × QueryCache HashSpec

/-- The in-budget keygen law retains the exact generated values and cache.
    Over-budget keygen executions are represented by `none`. -/
noncomputable def certificateStoppedKeygenInit (q : Nat) :
    PMF (Option (CertificateKeygenBoundaryResult × CertificateStoppedCacheState)) :=
  ((liftM (boundaryRun 0 scheme.keygen ∅) : PMF CertificateKeygenBoundaryResult)).map
    fun generated =>
      if generated.1.2.hashCalls ≤ q then
        some (generated, (generated.2, (false, q - generated.1.2.hashCalls)))
      else none

theorem certificateStoppedKeygenInit_support (q : Nat)
    (result : Option (CertificateKeygenBoundaryResult × CertificateStoppedCacheState))
    (hr : result ∈ (certificateStoppedKeygenInit q).support) :
    ∀ generated state, result = some (generated, state) →
      generated.1.2.hashCalls ≤ q ∧
      state = (generated.2, (false, q - generated.1.2.hashCalls)) ∧
      ¬ CertificateCacheExceptional generated.1.1.2 generated.2 := by
  rw [certificateStoppedKeygenInit, PMF.mem_support_map_iff] at hr
  obtain ⟨source, hsource, hresult⟩ := hr
  intro generated state heq
  by_cases hcost : source.1.2.hashCalls ≤ q
  · simp only [if_pos hcost] at hresult
    cases hresult
    cases heq
    refine ⟨hcost, rfl, ?_⟩
    apply certificateStoppedKeygen_cache_clean source
    simpa only [probCompLift_support] using hsource
  · simp only [if_neg hcost] at hresult
    cases hresult
    cases heq

theorem certificateStoppedKeygenInit_success_mass (q : Nat) :
    Pr[fun result => result.isSome | certificateStoppedKeygenInit q] =
    Pr[fun generated => generated.1.2.hashCalls ≤ q |
      (liftM (boundaryRun 0 scheme.keygen ∅) : PMF CertificateKeygenBoundaryResult)] := by
  rw [certificateStoppedKeygenInit, ← PMF.monad_map_eq_map, probEvent_map]
  congr 1
  funext generated
  by_cases hcost : generated.1.2.hashCalls ≤ q <;> simp [hcost]

/-- The stopped bridge remains valid after an arbitrary adaptive prefix. An
    already exhausted prefix contributes zero to the within-budget event. -/
theorem certificateCountedLengthImpl_hit_budget_stopped_after_prefix {History : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (history : PMF (History × CertificateCountedState))
    (input : (OracleWorld + SigningSpec).Domain) (q : Nat) :
    Pr[fun result => result.2.2.1.2 = true ∧ result.2.2.2 ≤ q |
      history.bind (fun before =>
        (certificateCountedLengthImpl key budget required stopAfter input).run before.2)] =
    ∑' before, Pr[= before | history] *
      if before.2.2.2 ≤ q then
        Pr[QueryCap.stoppedStateEvent (fun _ finalCache =>
          (before.2.2.1.2 || decide (CertificateCacheExceptional key before.2.1) ||
            decide (CertificateCacheExceptional key finalCache)) = true) |
          (simulateQ romPmfImpl (QueryCap.run
            (fun query : OracleWorld.Domain => query matches .inr _)
            (expandedAdversaryImpl key input) (q - before.2.2.2))).run before.2.1]
      else 0 := by
  rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro before
  congr 1
  by_cases hspent : before.2.2.2 ≤ q
  · simp only [if_pos hspent]
    exact certificateCountedLengthImpl_hit_budget_stopped_event key budget required
      stopAfter input before.2 q hspent
  · simp only [if_neg hspent]
    rw [certificateCountedLengthImpl_event_of_record key budget required stopAfter
      input before.2
      (fun after => after.2.1.2 = true ∧ after.2.2 ≤ q)
      (fun record =>
        (before.2.2.1.2 || decide (CertificateCacheExceptional key before.2.1) ||
          decide (CertificateCacheExceptional key record.cache)) = true ∧
        before.2.2.2 + record.trace.hashCalls ≤ q)
      (by intro length record; rfl)]
    simp only [probEvent_eq_tsum_ite]
    have hcost (record : ProposalExecutionRecord input) :
        ¬ before.2.2.2 + record.trace.hashCalls ≤ q := by omega
    simp only [hcost, and_false, if_false, tsum_zero]

theorem expected_certificateCacheLengthImpl_of_record_function (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState)
    (counter : CertificateCacheMonitorState → ENNReal) (weight : ProposalExecutionRecord input → ENNReal)
    (hadvance : ∀ length record, counter
      (originalProposalAdvance (certificateCacheMonitorUpdate key budget required stopAfter) input state length record) = weight record) :
    (∑' result, Pr[= result | (certificateCacheLengthImpl key budget required stopAfter input).run state] * counter result.2) =
      ∑' record, Pr[= record | originalProposalRecord key input state.1] * weight record := by
  simp only [certificateCacheLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk]
  split
  · rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [hadvance]
    have h := congrArg (fun law : PMF (ProposalExecutionRecord input) =>
      ∑' record, Pr[= record | law] * weight record)
      (recordLengthBridge_record (originalProposalRecord key input state.1)
        targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le)
    rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at h
    exact h
  · rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [hadvance]

theorem certificateCacheLengthImpl_original_cache (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState) :
    (fun result => (result.1, result.2.1)) <$> (certificateCacheLengthImpl key budget required stopAfter input).run state =
      (liftM ((simulateQ romImpl (expandedAdversaryImpl key input)).run state.1) : PMF _) := by
  have h := congrArg (Functor.map (fun result => (result.1, result.2.1)))
    (certificateCacheLengthImpl_project key budget required stopAfter input state)
  simp only [Functor.map_map] at h
  exact h.trans (certificateLengthImpl_original_cache key budget required stopAfter input (certificateCacheMonitorProject state))

theorem certificateCacheLengthImpl_finite (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState)
    (hfinite : Finite state.1) (result : (OracleWorld + SigningSpec).Range input × CertificateCacheMonitorState)
    (hr : result ∈ ((certificateCacheLengthImpl key budget required stopAfter input).run state).support) :
    Finite result.2.1 := by
  have hm := (PMF.mem_support_map_iff (fun result => (result.1, result.2.1)) _ _).mpr ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, certificateCacheLengthImpl_original_cache, probCompLift_support] at hm
  exact finite_cache_of_mem_support (expandedAdversaryImpl key input) state.1 result.1 result.2.1 hm hfinite

theorem expected_originalProposalRecord_cacheWeight (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' record, Pr[= record | originalProposalRecord key input cache] * certificateCacheExceptionWeight key record.cache) ≤
      certificateCacheExceptionWeight key cache +
        expectedBoundaryMessageCalls key.parameter (expandedAdversaryImpl key input) cache * certificateCacheExceptionRate := by
  have h := congrArg (fun law => ∑' result, Pr[= result | law] * certificateCacheExceptionWeight key result.2)
    (originalProposalRecord_boundary key input cache)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at h
  simp only [probOutput_probCompLift] at h
  rw [expectedBoundaryMessageCalls]
  exact h.le.trans (expected_certificateCacheExceptionWeight_boundary key (expandedAdversaryImpl key input) cache hfinite)

theorem expected_originalCacheHistoryWeight_step (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState)
    (hfinite : Finite state.1) :
    (∑' result, Pr[= result | (certificateCacheLengthImpl key budget required stopAfter input).run state] *
      originalCacheHistoryWeight key result.2) ≤ originalCacheHistoryWeight key state +
        expectedBoundaryMessageCalls key.parameter (expandedAdversaryImpl key input) state.1 * certificateCacheExceptionRate := by
  rw [expected_certificateCacheLengthImpl_of_record_function key budget required stopAfter input state
    (originalCacheHistoryWeight key)
    (fun record => if state.2.2 || decide (CertificateCacheExceptional key state.1) ||
      decide (CertificateCacheExceptional key record.cache) then 1 else certificateCacheExceptionWeight key record.cache)
    (fun _ _ => rfl)]
  by_cases hhit : state.2.2 = true
  · simp only [hhit, Bool.true_or, if_true, mul_one, tsum_probOutput_of_liftM_PMF, originalCacheHistoryWeight]
    exact le_self_add
  · by_cases hbad : CertificateCacheExceptional key state.1
    · simp only [hbad, decide_true, Bool.or_true, Bool.true_or, if_true, mul_one, tsum_probOutput_of_liftM_PMF,
        originalCacheHistoryWeight, hhit, Bool.false_eq_true, if_false]
      exact (certificateCacheExceptionWeight_bad key state.1 hfinite hbad).trans le_self_add
    · simp only [hhit, Bool.false_or, hbad, decide_false, originalCacheHistoryWeight]
      apply le_trans _ (expected_originalProposalRecord_cacheWeight key input state.1 hfinite)
      apply ENNReal.tsum_le_tsum
      intro record
      by_cases hr : record ∈ (originalProposalRecord key input state.1).support
      · apply mul_le_mul' le_rfl
        split_ifs with hbadRecord
        · have hb := originalProposalRecord_boundary_support key input state.1 record hr
          have hm : (record.output, record.cache) ∈ support ((simulateQ romImpl (expandedAdversaryImpl key input)).run state.1) := by
            rw [← boundaryRun_forget key.parameter (expandedAdversaryImpl key input) state.1, support_map]
            exact ⟨((record.output, record.trace), record.cache), hb, rfl⟩
          exact certificateCacheExceptionWeight_bad key record.cache
            (finite_cache_of_mem_support (expandedAdversaryImpl key input) state.1 record.output record.cache hm hfinite)
            (of_decide_eq_true hbadRecord)
        · exact le_rfl
      · have hz : originalProposalRecord key input state.1 record = 0 := by
          simpa only [PMF.mem_support_iff, not_not] using hr
        rw [PMF.probOutput_eq_apply, hz, zero_mul, zero_mul]

theorem expected_originalCacheHistoryWeight_run {Result : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : CertificateCacheMonitorState)
    (hfinite : Finite state.1) :
    (∑' result, Pr[= result | (simulateQ (certificateCacheLengthImpl key budget required stopAfter) computation).run state] *
      originalCacheHistoryWeight key result.2) ≤ originalCacheHistoryWeight key state +
        expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) computation) state.1 *
          certificateCacheExceptionRate := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, expectedBoundaryMessageCalls_pure,
        zero_mul, add_zero, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        simulateQ_bind, simulateQ_spec_query, expectedBoundaryMessageCalls_bind]
      have hproject := congrArg (fun law => ∑' result, Pr[= result | law] *
        expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) (next result.1)) result.2)
        (certificateCacheLengthImpl_original_cache key budget required stopAfter input state)
      rw [tsum_probOutput_map_mul] at hproject
      simp only [probOutput_probCompLift] at hproject
      calc
        _ ≤ ∑' result, Pr[= result | (certificateCacheLengthImpl key budget required stopAfter input).run state] *
            (originalCacheHistoryWeight key result.2 +
              expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) (next result.1)) result.2.1 *
                certificateCacheExceptionRate) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ ((certificateCacheLengthImpl key budget required stopAfter input).run state).support
          · exact mul_le_mul' le_rfl (ih result.1 result.2
              (certificateCacheLengthImpl_finite key budget required stopAfter input state hfinite result hr))
          · have hz : (certificateCacheLengthImpl key budget required stopAfter input).run state result = 0 := by
              simpa only [PMF.mem_support_iff, not_not] using hr
            rw [PMF.probOutput_eq_apply, hz, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (certificateCacheLengthImpl key budget required stopAfter input).run state] *
              originalCacheHistoryWeight key result.2) +
            (∑' result, Pr[= result | (certificateCacheLengthImpl key budget required stopAfter input).run state] *
              expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) (next result.1)) result.2.1) *
                certificateCacheExceptionRate := by
          simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]
        _ ≤ (originalCacheHistoryWeight key state +
              expectedBoundaryMessageCalls key.parameter (expandedAdversaryImpl key input) state.1 * certificateCacheExceptionRate) +
            (∑' result, Pr[= result | (certificateCacheLengthImpl key budget required stopAfter input).run state] *
              expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) (next result.1)) result.2.1) *
                certificateCacheExceptionRate :=
          add_le_add (expected_originalCacheHistoryWeight_step key budget required stopAfter input state hfinite) le_rfl
        _ = _ := by rw [hproject]; ring

theorem certificateCacheLength_hit_le_message_cost {Result : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : CertificateCacheMonitorState)
    (hfinite : Finite state.1) :
    Pr[fun result => result.2.2.2 = true |
      (simulateQ (certificateCacheLengthImpl key budget required stopAfter) computation).run state] ≤
      originalCacheHistoryWeight key state +
        expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) computation) state.1 *
          certificateCacheExceptionRate := by
  apply le_trans _ (expected_originalCacheHistoryWeight_run key budget required stopAfter computation state hfinite)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hhit : result.2.2.2 = true
  · simp only [hhit, if_true, originalCacheHistoryWeight, mul_one, le_refl]
  · simp only [hhit]
    exact bot_le

theorem certificateCacheProposal_hit_le_message_cost {Result : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : List Index × CertificateCacheMonitorState)
    (hfinite : Finite state.2.1) :
    Pr[fun result => result.2.2.2.2 = true |
      (simulateQ (certificateCacheProposalImpl key budget required stopAfter) computation).run state] ≤
      originalCacheHistoryWeight key state.2 +
        expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) computation) state.2.1 *
          certificateCacheExceptionRate := by
  have h := certificateCacheLength_hit_le_message_cost key budget required stopAfter computation state.2 hfinite
  rw [← simulateQ_certificateCacheProposalImpl_length key budget required stopAfter computation state, probEvent_map] at h
  exact h

private theorem expected_probCompLift_of_map_eq {Source Result : Type}
    (source : ProbComp Source) (result : ProbComp Result) (project : Source → Result)
    (hproject : project <$> source = result) (cost : Result → ENNReal) :
    (∑' value, Pr[= value | (liftM source : PMF Source)] * cost (project value)) =
      ∑' value, Pr[= value | result] * cost value := by
  rw [← hproject, tsum_probOutput_map_mul]
  simp only [probOutput_probCompLift]

theorem expectedBoundaryMessageCalls_le_hashQueryBound {Result : Type}
    (parameter : PublicParameter) (computation : OracleComp OracleWorld Result)
    (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound computation cache q) :
    expectedBoundaryMessageCalls parameter computation cache ≤ (q : ENNReal) := by
  rw [expectedBoundaryMessageCalls]
  calc
    _ ≤ ∑' result, Pr[= result | boundaryRun parameter computation cache] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support (boundaryRun parameter computation cache)
      · apply mul_le_mul' le_rfl
        exact Nat.cast_le.mpr ((List.length_filterMap_le _ _).trans
          ((hashQueryBound_iff_boundaryRun parameter computation cache q).mp hbound result hr))
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = q := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

/-- A stopped computation has a hard query bound even when its original
    computation does not. -/
theorem hashQueryBound_queryCap_run {Result : Type}
    (computation : OracleComp OracleWorld Result) (cache : QueryCache HashSpec)
    (q : Nat) :
    HashQueryBound (QueryCap.run
      (fun input : OracleWorld.Domain => input matches .inr _) computation q) cache q := by
  intro result hr
  have hsyntax : result ∈ support (countHashQueries (QueryCap.run
      (fun input : OracleWorld.Domain => input matches .inr _) computation q)) :=
    support_simulateQ_run'_subset romImpl _ cache hr
  exact QueryCap.counted_le_of_queryBound
    (fun input : OracleWorld.Domain => input matches .inr _)
    (QueryCap.run (fun input : OracleWorld.Domain => input matches .inr _) computation q) q
    (QueryCap.run_queryBound
      (fun input : OracleWorld.Domain => input matches .inr _) computation q)
    result hsyntax

theorem certificateCacheLength_hit_le_hashQueryBound {Result : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : CertificateCacheMonitorState) (hfinite : Finite state.1)
    (q : Nat)
    (hbound : HashQueryBound
      (simulateQ (expandedAdversaryImpl key) computation) state.1 q) :
    Pr[fun result => result.2.2.2 = true |
      (simulateQ (certificateCacheLengthImpl key budget required stopAfter)
        computation).run state] ≤
      originalCacheHistoryWeight key state +
        (q : ENNReal) * certificateCacheExceptionRate := by
  exact (certificateCacheLength_hit_le_message_cost key budget required stopAfter
    computation state hfinite).trans
    (add_le_add le_rfl (mul_le_mul'
      (expectedBoundaryMessageCalls_le_hashQueryBound key.parameter
        (simulateQ (expandedAdversaryImpl key) computation) state.1 q hbound) le_rfl))

theorem certificateCacheProposal_hit_le_hashQueryBound {Result : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : List Index × CertificateCacheMonitorState)
    (hfinite : Finite state.2.1) (q : Nat)
    (hbound : HashQueryBound
      (simulateQ (expandedAdversaryImpl key) computation) state.2.1 q) :
    Pr[fun result => result.2.2.2.2 = true |
      (simulateQ (certificateCacheProposalImpl key budget required stopAfter)
        computation).run state] ≤
      originalCacheHistoryWeight key state.2 +
        (q : ENNReal) * certificateCacheExceptionRate := by
  have h := certificateCacheLength_hit_le_hashQueryBound key budget required stopAfter
    computation state.2 hfinite q hbound
  rw [← simulateQ_certificateCacheProposalImpl_length key budget required
    stopAfter computation state, probEvent_map] at h
  exact h

theorem certificateContextGame_cache_hit_le_original_message (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    Pr[fun result => result.2.2.2.2.2 = true | certificateContextGame adversary budget required stopAfter stopped] ≤
      originalCertificateMessageCost adversary * certificateCacheExceptionRate := by
  rw [certificateContextGame, probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' generated, Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] *
        (expectedBoundaryMessageCalls generated.1.1.2.parameter
          (simulateQ (expandedAdversaryImpl generated.1.1.2)
            (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)) generated.2 * certificateCacheExceptionRate) := by
      apply ENNReal.tsum_le_tsum
      intro generated
      by_cases hg : generated ∈ (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _).support
      · have hb : generated ∈ support (boundaryRun 0 scheme.keygen ∅) := (probCompLift_support _ ▸ hg)
        have hn : (generated.1.1, generated.2) ∈ support ((simulateQ romImpl scheme.keygen).run ∅) := by
          rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
          exact ⟨generated, hb, rfl⟩
        have hf := finite_cache_of_mem_support scheme.keygen ∅ generated.1.1 generated.2 hn finite_empty
        have hzero : originalCacheHistoryWeight generated.1.1.2
            (generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false) = 0 := by
          rw [originalCacheHistoryWeight, if_neg Bool.false_ne_true]
          exact certificateCacheExceptionWeight_initial generated.1.1.2 generated.2
            (keygen_cache_message_none (generated.1.1, generated.2) hn)
        have h := certificateCacheProposal_hit_le_message_cost generated.1.1.2 budget required
          (stopAfter generated.1.1.2) (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)
          ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false) hf
        rw [hzero, zero_add] at h
        apply mul_le_mul' le_rfl
        simpa only [bind_pure_comp, probEvent_map, Function.comp_def] using h
      · have hz : (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _) generated = 0 := by
          simpa only [PMF.mem_support_iff, not_not] using hg
        rw [PMF.probOutput_eq_apply, hz, zero_mul, zero_mul]
    _ = (∑' generated, Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] *
        expectedBoundaryMessageCalls generated.1.1.2.parameter
          (simulateQ (expandedAdversaryImpl generated.1.1.2)
            (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)) generated.2) * certificateCacheExceptionRate := by
      simp only [← mul_assoc, ENNReal.tsum_mul_right]
    _ = _ := by
      apply congrArg (· * certificateCacheExceptionRate)
      exact expected_probCompLift_of_map_eq (boundaryRun 0 scheme.keygen ∅)
        ((simulateQ romImpl scheme.keygen).run ∅) (fun result => (result.1.1, result.2))
        (boundaryRun_forget 0 scheme.keygen ∅) (fun generated =>
          expectedBoundaryMessageCalls generated.1.2.parameter
            (simulateQ (expandedAdversaryImpl generated.1.2)
              (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1)) generated.2)

theorem certificateContextGame_exception_le_cache_add_prefix (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    Pr[fun result => CertificateGameExceptional result.2 | certificateContextGame adversary budget required stopAfter stopped] ≤
      Pr[fun result => result.2.2.2.2.2 = true | certificateContextGame adversary budget required stopAfter stopped] +
      Pr[fun result => ProposalPrefixExceptional result.2.2.2.2.1.proposals result.2.2.2.2.1.log.length |
        certificateContextGame adversary budget required stopAfter stopped] :=
  probEvent_or_le (certificateContextGame adversary budget required stopAfter stopped) _ _

theorem originalCertificateSource_full_le_original_message_add_prefix (adversary : Adversary) (q : Nat)
    (hbudget : q ≤ 2 ^ 128) (hbound : HasHashQueryBound scheme adversary q) :
    Pr[OriginalFullCertificate | originalCertificateSource adversary] ≤
      ((2 ^ 144 : ENNReal)⁻¹ + certificateCacheExceptionRate) * originalCertificateMessageCost adversary +
      (q : ENNReal) * fullCertificateExcessRate +
      Pr[fun result => ProposalPrefixExceptional result.2.2.2.2.1.proposals result.2.2.2.2.1.log.length |
        certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] := by
  have he := (certificateContextGame_exception_le_cache_add_prefix adversary q Finset.univ (fun _ => proposalPrefixStop) false).trans
    (add_le_add (certificateContextGame_cache_hit_le_original_message adversary q Finset.univ (fun _ => proposalPrefixStop) false) le_rfl)
  apply (originalCertificateSource_full_le_original_message_add_exception adversary q hbudget hbound).trans
  calc
    _ ≤ (2 ^ 144 : ENNReal)⁻¹ * originalCertificateMessageCost adversary + (q : ENNReal) * fullCertificateExcessRate +
        (originalCertificateMessageCost adversary * certificateCacheExceptionRate +
          Pr[fun result => ProposalPrefixExceptional result.2.2.2.2.1.proposals result.2.2.2.2.1.log.length |
            certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false]) := add_le_add le_rfl he
    _ = _ := by ring

theorem original_primitive_add_full_certificate_le_small_budget_add_prefix (dummy : OtsReferenceWords)
    (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q)
    (hsmall : q ≤ budgetSplit) :
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      Pr[OriginalFullCertificate | originalCertificateSource adversary] ≤
      primitiveCoefficient * ((q : ENNReal) / 2 ^ 144) + (q : ENNReal) * fullCertificateExcessRate +
      Pr[fun result => ProposalPrefixExceptional result.2.2.2.2.1.proposals result.2.2.2.2.1.log.length |
        certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] := by
  have hbudget : q ≤ 2 ^ 128 := (hsmall.trans budgetSplit_le).trans (by norm_num)
  have hcard : Fintype.card Digest = 2 ^ 160 := by simp [digestBits]
  have hsmallcard : q < Fintype.card Digest :=
    hsmall.trans_lt (budgetSplit_le.trans_lt (by rw [hcard]; norm_num))
  have hr := primitive_rates_small q hsmall
  have hcoeff : primitiveCoefficient / Fintype.card Digest ≤ primitiveCoefficient / 2 ^ 144 := by
    rw [hcard, primitiveCoefficient_def]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  have ho : (Fintype.card Digest : ENNReal)⁻¹ ≤ primitiveCoefficient / 2 ^ 144 := by
    rw [hcard, primitiveCoefficient_def]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_inv, ENNReal.toReal_div]
  have hp := referenceGraphContextGame_primitive_joint_budget dummy adversary q hbound hsmallcard
    (primitiveCoefficient / 2 ^ 144) (hr.1.trans hcoeff) (hr.2.trans hcoeff) ho
  have hrate : (2 ^ 144 : ENNReal)⁻¹ + certificateCacheExceptionRate ≤ primitiveCoefficient / 2 ^ 144 := by
    apply (add_le_add le_rfl certificateCacheExceptionRate_le).trans
    rw [primitiveCoefficient_def]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]
  have hc := (originalCertificateSource_full_le_original_message_add_prefix adversary q hbudget hbound).trans
    (add_le_add (add_le_add (mul_le_mul' hrate (originalCertificateMessageCost_le_referenceRecorded dummy adversary)) le_rfl) le_rfl)
  calc
    _ ≤ Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
        ((primitiveCoefficient / 2 ^ 144) *
          (∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
            (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.messageCalls : ENNReal)) +
          (q : ENNReal) * fullCertificateExcessRate +
          Pr[fun result => ProposalPrefixExceptional result.2.2.2.2.1.proposals result.2.2.2.2.1.log.length |
            certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false]) := add_le_add le_rfl hc
    _ ≤ _ := by
      rw [← add_assoc, ← add_assoc]
      exact add_le_add (add_le_add (by simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hp) le_rfl) le_rfl

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.expectedBoundaryMessageCalls_le_hashQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expectedBoundaryMessageCalls_le_hashQueryBound

/-- info: 'SphincsSecurity.Concrete.certificateCacheLength_hit_le_hashQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCacheLength_hit_le_hashQueryBound

/-- info: 'SphincsSecurity.Concrete.certificateCacheProposal_hit_le_hashQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCacheProposal_hit_le_hashQueryBound

/-- info: 'SphincsSecurity.Concrete.originalProposalRecord_cache_exception_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.originalProposalRecord_cache_exception_budget_event

/-- info: 'SphincsSecurity.Concrete.originalProposalRecord_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.originalProposalRecord_budget_event

/-- info: 'SphincsSecurity.Concrete.originalProposalRecord_budget_stopped_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.originalProposalRecord_budget_stopped_event

/-- info: 'SphincsSecurity.Concrete.certificateCountedLengthImpl_hit_budget_stopped_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedLengthImpl_hit_budget_stopped_event

/-- info: 'SphincsSecurity.Concrete.certificateCountedLengthImpl_hit_budget_stopped_after_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedLengthImpl_hit_budget_stopped_after_prefix

/-- info: 'SphincsSecurity.Concrete.hashQueryBound_queryCap_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.hashQueryBound_queryCap_run

/-- info: 'SphincsSecurity.Concrete.certificateStoppedRomImpl_cache_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedRomImpl_cache_project

/-- info: 'SphincsSecurity.Concrete.certificateStoppedRomImpl_run_cache_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedRomImpl_run_cache_project

/-- info: 'SphincsSecurity.Concrete.certificateStoppedRomImpl_hit_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedRomImpl_hit_run

/-- info: 'SphincsSecurity.Concrete.certificateCountedLengthImpl_hit_budget_le_stopped_monitor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedLengthImpl_hit_budget_le_stopped_monitor

/-- info: 'SphincsSecurity.Concrete.certificateCountedLengthImpl_adaptive_hit_budget_le_stopped_monitor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedLengthImpl_adaptive_hit_budget_le_stopped_monitor

/-- info: 'SphincsSecurity.Concrete.certificateStoppedKeygen_cache_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedKeygen_cache_clean

/-- info: 'SphincsSecurity.Concrete.certificateStoppedKeygenInit_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedKeygenInit_support

/-- info: 'SphincsSecurity.Concrete.certificateStoppedKeygenInit_success_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedKeygenInit_success_mass

/-- info: 'SphincsSecurity.Concrete.recordLengthBridge_joint_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.recordLengthBridge_joint_project

/-- info: 'SphincsSecurity.Concrete.enrichedSigningRecord_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.enrichedSigningRecord_project

/-- info: 'SphincsSecurity.Concrete.counted_boundaryComputation_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.counted_boundaryComputation_eq_trace

/-- info: 'SphincsSecurity.Concrete.stoppedTracedSigningRun_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.stoppedTracedSigningRun_budget_event

/-- info: 'SphincsSecurity.Concrete.stoppedSigningProjected_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.stoppedSigningProjected_some

/-- info: 'SphincsSecurity.Concrete.enrichedStoppedSigningRecord_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.enrichedStoppedSigningRecord_kernel

/-- info: 'SphincsSecurity.Concrete.enrichedStoppedSigningRecord_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.enrichedStoppedSigningRecord_budget_event

/-- info: 'SphincsSecurity.Concrete.enrichedSigningRecord_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.enrichedSigningRecord_kernel

/-- info: 'SphincsSecurity.Concrete.enrichedStoppedSigningRecord_original_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.enrichedStoppedSigningRecord_original_budget_event

/-- info: 'SphincsSecurity.Concrete.enrichedStoppedSigningRecord_unbounded_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.enrichedStoppedSigningRecord_unbounded_budget_event

/-- info: 'SphincsSecurity.Concrete.enrichedStoppedSigningRecord_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.enrichedStoppedSigningRecord_some
