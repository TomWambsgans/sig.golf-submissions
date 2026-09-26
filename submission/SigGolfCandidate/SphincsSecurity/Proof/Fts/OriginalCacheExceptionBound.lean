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

theorem certificateStoppedRomImpl_remaining_step (key : SecretKey)
    (input : OracleWorld.Domain) (state : CertificateStoppedCacheState)
    (result : OracleWorld.Range input × CertificateStoppedCacheState)
    (hr : result ∈ ((certificateStoppedRomImpl key input).run state).support) :
    result.2.2.2 = state.2.2 - if input matches .inr _ then 1 else 0 := by
  simp only [certificateStoppedRomImpl, StateT.run_mk, PMF.mem_support_map_iff] at hr
  obtain ⟨source, _, rfl⟩ := hr
  cases input <;> rfl

/-- The ghost budget is exact for a full boundary-traced run, even though
    subtraction saturates when a run exceeds the starting budget. -/
theorem certificateStoppedRomImpl_remaining_boundary {α : Type} (key : SecretKey)
    (computation : OracleComp OracleWorld α) :
    ∀ (state : CertificateStoppedCacheState)
      (result : (α × SigningBoundaryTrace) × CertificateStoppedCacheState),
      result ∈ ((simulateQ (certificateStoppedRomImpl key)
        (boundaryComputation key.parameter computation)).run state).support →
      result.2.2.2 = state.2.2 - result.1.2.hashCalls := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro state result hr
      change result ∈ (PMF.pure ((value, 1), state)).support at hr
      simp only [PMF.mem_support_pure_iff] at hr
      subst result
      simp [SigningBoundaryTrace.hashCalls]
  | query_bind input next ih =>
      intro state result hr
      rw [show boundaryComputation key.parameter
        (liftM (OracleWorld.query input) >>= next) =
        QueryPause.traced (signingBoundaryTrace key.parameter)
          (liftM (OracleWorld.query input) >>= next) from rfl] at hr
      rw [QueryPause.traced_query_bind, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, htail⟩ := hr
      change result ∈ ((simulateQ (certificateStoppedRomImpl key)
        ((fun tail => (tail.1, signingBoundaryTrace key.parameter input middle.1 * tail.2)) <$>
          boundaryComputation key.parameter (next middle.1))).run middle.2).support at htail
      rw [simulateQ_map, StateT.run_map] at htail
      rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at htail
      obtain ⟨tail, htail, heq⟩ := htail
      subst result
      have hnext := ih middle.1 middle.2 tail htail
      have hstep := certificateStoppedRomImpl_remaining_step key input state middle hmiddle
      simp only [SigningBoundaryTrace.hashCalls_mul,
        signingBoundaryTrace_hashCalls_eq] at *
      cases input <;> simp at hstep ⊢ <;> omega

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

/-- A joint signing outcome retains the proposal record, sampled synthetic
    length, updated certificate state, and stopped lazy-oracle monitor. -/
abbrev CertificateStoppedSigningJointOutput (message : Message) :=
  ProposalExecutionRecord (.inr message) × Nat × CertificateCountedState × CertificateStoppedCacheState

noncomputable def certificateSigningLengthLaw (key : SecretKey)
    (budget : Nat) (_required : Finset FtsTree) (_stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateCountedState) : PMF Nat :=
  if originalProposalActive key (fun state => state.2.1.1.spent)
      (fun message state => certificateMonitorEnabled key budget message
        (certificateCacheMonitorProject (certificateCountedProject state)))
      (.inr message) state then
    proposalBlockLength targetProposalAcceptance targetProposalAcceptance_ne_zero
      targetProposalAcceptance_lt_one.le
  else PMF.pure 0

noncomputable def certificateStoppedSigningJointKernel (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateCountedState)
    (x : ProposalExecutionRecord (.inr message) × CertificateStoppedCacheState) :
    PMF (CertificateStoppedSigningJointOutput message) :=
  (certificateSigningLengthLaw key budget required stopAfter message state).map fun length =>
    (x.1, length, originalProposalAdvance
      (certificateCountedUpdate key budget required stopAfter)
      (.inr message) state length x.1, x.2)

noncomputable def certificateStoppedSigningJointStep (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) :
    PMF (Option (CertificateStoppedSigningJointOutput message)) :=
  (enrichedStoppedSigningRecord key message ghost).bind fun result =>
    match result with
    | none => PMF.pure none
    | some x => (certificateStoppedSigningJointKernel key budget required stopAfter
        message state x).map some

theorem certificateStoppedSigningJointStep_event (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState)
    (event : CertificateStoppedSigningJointOutput message → Prop) :
    Pr[fun result => result.elim False event |
      certificateStoppedSigningJointStep key budget required stopAfter message state ghost] =
    Pr[fun result => result.elim False event |
      (enrichedSigningRecord key message ghost).bind fun x =>
        if x.1.trace.hashCalls ≤ ghost.2.2 then
          (certificateStoppedSigningJointKernel key budget required stopAfter
            message state x).map some else PMF.pure none] := by
  rw [certificateStoppedSigningJointStep]
  convert some_kernel_transfer
    (enrichedStoppedSigningRecord key message ghost)
    (enrichedSigningRecord key message ghost)
    (fun x => x.1.trace.hashCalls ≤ ghost.2.2)
    (enrichedStoppedSigningRecord_some key message ghost)
    (certificateStoppedSigningJointKernel key budget required stopAfter message state)
    event using 1
  all_goals
    congr 1
    congr 1
    funext r
    cases r <;> rfl

noncomputable def certificateUnboundedSigningJointStep (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) :
    PMF (CertificateStoppedSigningJointOutput message) :=
  (enrichedSigningRecord key message ghost).bind
    (certificateStoppedSigningJointKernel key budget required stopAfter message state)

/-- Dropping the record and ghost state recovers the actual certificate
    length step, provided both runs begin with the same lazy-oracle cache. -/
theorem certificateUnboundedSigningJointStep_project (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) (hcache : ghost.1 = state.1) :
    (certificateUnboundedSigningJointStep key budget required stopAfter message state ghost).map
      (fun output => (output.1.output, output.2.2.1)) =
    ((certificateCountedLengthImpl key budget required stopAfter (.inr message)).run state) := by
  unfold certificateUnboundedSigningJointStep certificateStoppedSigningJointKernel
    certificateSigningLengthLaw certificateCountedLengthImpl originalLengthImpl
    lengthRecordImpl
  rw [PMF.map_bind]
  simp only [PMF.map_comp, StateT.run_mk]
  by_cases ha : originalProposalActive key (fun state => state.2.1.1.spent)
      (fun message state => certificateMonitorEnabled key budget message
        (certificateCacheMonitorProject (certificateCountedProject state)))
      (.inr message) state = true
  · simp only [ha, if_true, recordLengthBridge, PMF.map_bind, PMF.map_comp]
    rw [← hcache, ← enrichedSigningRecord_project]
    rw [PMF.bind_map]
    apply PMF.bind_congr
    intro x _
    rfl
  · simp [ha]
    rw [← hcache, ← enrichedSigningRecord_project]
    simp only [PMF.pure_map]
    rw [PMF.map_comp]
    change (enrichedSigningRecord key message ghost).bind
      (PMF.pure ∘ fun a =>
        (a.1.output, originalProposalAdvance
          (certificateCountedUpdate key budget required stopAfter)
          (.inr message) state 0 a.1)) = _
    rw [PMF.bind_pure_comp]
    rfl

/-- This joint one-step law keeps every field needed for later adaptive
    composition while charging the actual trace's hash calls. -/
theorem certificateStoppedSigningJointStep_unbounded_budget_event (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState)
    (event : CertificateStoppedSigningJointOutput message → Prop) :
    Pr[fun result => result.elim False event |
      certificateStoppedSigningJointStep key budget required stopAfter message state ghost] =
    Pr[fun result => result.1.trace.hashCalls ≤ ghost.2.2 ∧ event result |
      certificateUnboundedSigningJointStep key budget required stopAfter message state ghost] := by
  classical
  rw [certificateStoppedSigningJointStep_event]
  unfold certificateUnboundedSigningJointStep
  rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum,
    ← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro x
  congr 1
  by_cases hb : x.1.trace.hashCalls ≤ ghost.2.2
  · simp only [if_pos hb, ← PMF.monad_map_eq_map, probEvent_map,
      Function.comp_def, Option.elim_some, certificateStoppedSigningJointKernel]
    simp [hb]
  · simp only [if_neg hb]
    simp only [← PMF.monad_map_eq_map, probEvent_map, certificateStoppedSigningJointKernel,
      Function.comp_def]
    simp [hb, probEvent_eq_tsum_ite]
    intro i hi
    cases i <;> simp at *

theorem enrichedSigningRecord_remaining (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState)
    (result : ProposalExecutionRecord (.inr message) × CertificateStoppedCacheState)
    (hr : result ∈ (enrichedSigningRecord key message state).support) :
    result.2.2.2 = state.2.2 - result.1.trace.hashCalls := by
  unfold enrichedSigningRecord at hr
  rw [PMF.mem_support_bind_iff] at hr
  obtain ⟨source, hsource, hindex⟩ := hr
  rw [PMF.mem_support_map_iff] at hindex
  obtain ⟨index, _, heq⟩ := hindex
  subst result
  exact certificateStoppedRomImpl_remaining_boundary key (signWithView key message)
    state source hsource

theorem enrichedSigningRecord_cache (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState)
    (result : ProposalExecutionRecord (.inr message) × CertificateStoppedCacheState)
    (hr : result ∈ (enrichedSigningRecord key message state).support) :
    result.1.cache = result.2.1 := by
  unfold enrichedSigningRecord at hr
  rw [PMF.mem_support_bind_iff] at hr
  obtain ⟨source, _, hindex⟩ := hr
  rw [PMF.mem_support_map_iff] at hindex
  obtain ⟨index, _, heq⟩ := hindex
  subst result
  rfl

/-- Every joint output keeps the original and ghost cache synchronized,
    charges exactly the record's hash calls, and updates remaining budget
    by that same amount. -/
theorem certificateUnboundedSigningJointStep_state_relation (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState)
    (result : CertificateStoppedSigningJointOutput message)
    (hr : result ∈ (certificateUnboundedSigningJointStep key budget required stopAfter
      message state ghost).support) :
    result.2.2.2.1 = result.2.2.1.1 ∧
      result.2.2.2.2.2 = ghost.2.2 - result.1.trace.hashCalls ∧
      result.2.2.1.2.2 = state.2.2 + result.1.trace.hashCalls := by
  unfold certificateUnboundedSigningJointStep at hr
  rw [PMF.mem_support_bind_iff] at hr
  obtain ⟨source, hsource, hkernel⟩ := hr
  unfold certificateStoppedSigningJointKernel at hkernel
  rw [PMF.mem_support_map_iff] at hkernel
  obtain ⟨length, _, heq⟩ := hkernel
  subst result
  have hremain := enrichedSigningRecord_remaining key message ghost source hsource
  have hcache := enrichedSigningRecord_cache key message ghost source hsource
  simp only [originalProposalAdvance, certificateCountedUpdate]
  exact ⟨hcache.symm, hremain, trivial⟩

theorem certificateStoppedSigningJointStep_some (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState)
    (x : CertificateStoppedSigningJointOutput message) :
    certificateStoppedSigningJointStep key budget required stopAfter message state ghost (some x) =
      if x.1.trace.hashCalls ≤ ghost.2.2 then
        certificateUnboundedSigningJointStep key budget required stopAfter message state ghost x
      else 0 := by
  classical
  have h := certificateStoppedSigningJointStep_unbounded_budget_event
    key budget required stopAfter message state ghost (fun result => result = x)
  have hleft : (fun result : Option (CertificateStoppedSigningJointOutput message) =>
      result.elim False (fun output => output = x)) = (fun result => result = some x) := by
    funext result
    cases result <;> simp
  rw [hleft, probEvent_eq_eq_probOutput] at h
  simp only [probOutput_def] at h
  by_cases hb : x.1.trace.hashCalls ≤ ghost.2.2
  · have hpred : (fun result => result.1.trace.hashCalls ≤ ghost.2.2 ∧ result = x) =
        (fun result => result = x) := by
      funext result
      apply propext
      constructor
      · exact And.right
      · intro heq
        subst result
        exact ⟨hb, rfl⟩
    rw [hpred, probEvent_eq_eq_probOutput] at h
    simpa [hb, probOutput_def] using h
  · have hpred : (fun result : CertificateStoppedSigningJointOutput message =>
        result.1.trace.hashCalls ≤ ghost.2.2 ∧ result = x) = (fun _ => False) := by
      funext result
      apply propext
      constructor
      · intro hr
        rw [hr.2] at hr
        exact hb hr.1
      · exact False.elim
    rw [hpred] at h
    simpa [hb, probEvent_eq_tsum_ite] using h

/-- Successful stopped signing steps preserve the cache match and the exact
    relation between the original spent count and the ghost remaining budget. -/
theorem certificateStoppedSigningJointStep_relation (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) (q : Nat)
    (hspent : state.2.2 ≤ q) (hremaining : ghost.2.2 = q - state.2.2)
    (x : CertificateStoppedSigningJointOutput message)
    (hx : some x ∈ (certificateStoppedSigningJointStep key budget required stopAfter
      message state ghost).support) :
    x.2.2.2.1 = x.2.2.1.1 ∧ x.2.2.1.2.2 ≤ q ∧
      x.2.2.2.2.2 = q - x.2.2.1.2.2 := by
  rw [PMF.mem_support_iff, certificateStoppedSigningJointStep_some] at hx
  by_cases hcost : x.1.trace.hashCalls ≤ ghost.2.2
  · simp only [if_pos hcost] at hx
    have hfull : x ∈ (certificateUnboundedSigningJointStep key budget required
        stopAfter message state ghost).support := (PMF.mem_support_iff _ _).2 hx
    obtain ⟨hcache', hremaining', hspent'⟩ :=
      certificateUnboundedSigningJointStep_state_relation key budget required
        stopAfter message state ghost x hfull
    constructor
    · exact hcache'
    constructor
    · omega
    · omega
  · simp [hcost] at hx

abbrev CertificateStoppedWorldJointOutput (world : OracleWorld.Domain) :=
  ProposalExecutionRecord (.inl world) × Nat × CertificateCountedState × CertificateStoppedCacheState

noncomputable def certificateWorldJointOutput (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (world : OracleWorld.Domain) (state : CertificateCountedState)
    (answer : OracleWorld.Range world) (ghost : CertificateStoppedCacheState) :
    CertificateStoppedWorldJointOutput world :=
  let record : ProposalExecutionRecord (.inl world) :=
    ⟨answer, ghost.1, signingBoundaryTrace key.parameter world answer, none, 0⟩
  (record, 0, originalProposalAdvance
    (certificateCountedUpdate key budget required stopAfter) (.inl world) state 0 record, ghost)

noncomputable def certificateUnboundedWorldJointStep (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (world : OracleWorld.Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) :
    PMF (CertificateStoppedWorldJointOutput world) :=
  ((certificateStoppedRomImpl key world).run ghost).map fun result =>
    certificateWorldJointOutput key budget required stopAfter world state result.1 result.2

noncomputable def certificateStoppedWorldJointStep (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (world : OracleWorld.Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) :
    PMF (Option (CertificateStoppedWorldJointOutput world)) :=
  ((simulateQ (certificateStoppedRomImpl key) (QueryCap.run
      (fun query : OracleWorld.Domain => query matches .inr _)
      (liftM (OracleWorld.query world)) ghost.2.2)).run ghost).map fun result =>
    match result.1 with
    | none => none
    | some (answer, _) =>
        some (certificateWorldJointOutput key budget required stopAfter world state answer result.2)


theorem counted_world_query (world : OracleWorld.Domain) :
    QueryCap.counted (fun query : OracleWorld.Domain => query matches .inr _)
      (liftM (OracleWorld.query world)) =
    (fun answer => (answer, if world matches .inr _ then 1 else 0)) <$>
      (liftM (OracleWorld.query world) : OracleComp OracleWorld (OracleWorld.Range world)) := by
  cases world <;> rfl


theorem certificateStoppedWorldJointStep_budget_event (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (world : OracleWorld.Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState)
    (event : CertificateStoppedWorldJointOutput world → Prop) :
    Pr[fun result => result.elim False event |
      certificateStoppedWorldJointStep key budget required stopAfter world state ghost] =
    Pr[fun result => result.1.trace.hashCalls ≤ ghost.2.2 ∧ event result |
      certificateUnboundedWorldJointStep key budget required stopAfter world state ghost] := by
  have h := QueryCap.run_budget_event_state
    (fun query : OracleWorld.Domain => query matches .inr _)
    (certificateStoppedRomImpl key)
    (liftM (OracleWorld.query world) : OracleComp OracleWorld (OracleWorld.Range world))
    ghost.2.2 ghost
    (fun answer finalGhost => event
      (certificateWorldJointOutput key budget required stopAfter world state answer finalGhost))
  rw [certificateStoppedWorldJointStep, ← PMF.monad_map_eq_map, probEvent_map]
  have hevent : ((fun result => result.elim False event) ∘ fun result :
        Option (OracleWorld.Range world × Nat) × CertificateStoppedCacheState =>
          match result.1 with
          | none => none
          | some (answer, _) => some
              (certificateWorldJointOutput key budget required stopAfter world state answer result.2)) =
      QueryCap.stoppedStateEvent (fun answer finalGhost => event
        (certificateWorldJointOutput key budget required stopAfter world state answer finalGhost)) := by
    funext result
    cases hresult : result.1 with
    | none => simp [QueryCap.stoppedStateEvent, hresult]
    | some output =>
        rcases output with ⟨answer, remaining⟩
        simp [QueryCap.stoppedStateEvent, hresult]
  rw [hevent, h]
  rw [counted_world_query, simulateQ_map, StateT.run_map]
  rw [probEvent_map]
  rw [certificateUnboundedWorldJointStep, ← PMF.monad_map_eq_map, probEvent_map]
  rw [simulateQ_spec_query]
  congr 1
  funext result
  cases world <;> simp [certificateWorldJointOutput, signingBoundaryTrace_hashCalls_eq]


theorem certificateUnboundedWorldJointStep_project (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (world : OracleWorld.Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) (hcache : ghost.1 = state.1) :
    (certificateUnboundedWorldJointStep key budget required stopAfter world state ghost).map
      (fun output => (output.1.output, output.2.2.1)) =
    ((certificateCountedLengthImpl key budget required stopAfter (.inl world)).run state) := by
  unfold certificateUnboundedWorldJointStep certificateWorldJointOutput
    certificateCountedLengthImpl originalLengthImpl lengthRecordImpl
  simp only [originalProposalActive, StateT.run_mk, originalProposalRecord,
    PMF.map_comp, Bool.false_eq_true, if_false]
  rw [← hcache]
  change PMF.map _ ((certificateStoppedRomImpl key world).run ghost) =
    PMF.map _ ((romPmfImpl world).run ghost.1)
  rw [← certificateStoppedRomImpl_cache_project key world ghost]
  rw [PMF.monad_map_eq_map, PMF.map_comp]
  congr 1


theorem certificateUnboundedWorldJointStep_state_relation (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (world : OracleWorld.Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState)
    (result : CertificateStoppedWorldJointOutput world)
    (hr : result ∈ (certificateUnboundedWorldJointStep key budget required stopAfter
      world state ghost).support) :
    result.2.2.2.1 = result.2.2.1.1 ∧
      result.2.2.2.2.2 = ghost.2.2 - result.1.trace.hashCalls ∧
      result.2.2.1.2.2 = state.2.2 + result.1.trace.hashCalls := by
  unfold certificateUnboundedWorldJointStep at hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨source, hsource, heq⟩ := hr
  subst result
  have hremain := certificateStoppedRomImpl_remaining_step key world ghost source hsource
  simp only [certificateWorldJointOutput, originalProposalAdvance,
    certificateCountedUpdate, signingBoundaryTrace_hashCalls_eq]
  cases world <;> simpa using hremain


theorem certificateStoppedWorldJointStep_some (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (world : OracleWorld.Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState)
    (x : CertificateStoppedWorldJointOutput world) :
    certificateStoppedWorldJointStep key budget required stopAfter world state ghost (some x) =
      if x.1.trace.hashCalls ≤ ghost.2.2 then
        certificateUnboundedWorldJointStep key budget required stopAfter world state ghost x
      else 0 := by
  classical
  have h := certificateStoppedWorldJointStep_budget_event
    key budget required stopAfter world state ghost (fun result => result = x)
  have hleft : (fun result : Option (CertificateStoppedWorldJointOutput world) =>
      result.elim False (fun output => output = x)) = (fun result => result = some x) := by
    funext result
    cases result <;> simp
  rw [hleft, probEvent_eq_eq_probOutput] at h
  simp only [probOutput_def] at h
  by_cases hb : x.1.trace.hashCalls ≤ ghost.2.2
  · have hpred : (fun result => result.1.trace.hashCalls ≤ ghost.2.2 ∧ result = x) =
        (fun result => result = x) := by
      funext result
      apply propext
      constructor
      · exact And.right
      · intro heq
        subst result
        exact ⟨hb, rfl⟩
    rw [hpred, probEvent_eq_eq_probOutput] at h
    simpa [hb, probOutput_def] using h
  · have hpred : (fun result : CertificateStoppedWorldJointOutput world =>
        result.1.trace.hashCalls ≤ ghost.2.2 ∧ result = x) = (fun _ => False) := by
      funext result
      apply propext
      constructor
      · intro hr
        rw [hr.2] at hr
        exact hb hr.1
      · exact False.elim
    rw [hpred] at h
    simpa [hb, probEvent_eq_tsum_ite] using h

theorem certificateStoppedWorldJointStep_relation (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (world : OracleWorld.Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) (q : Nat)
    (hspent : state.2.2 ≤ q) (hremaining : ghost.2.2 = q - state.2.2)
    (x : CertificateStoppedWorldJointOutput world)
    (hx : some x ∈ (certificateStoppedWorldJointStep key budget required stopAfter
      world state ghost).support) :
    x.2.2.2.1 = x.2.2.1.1 ∧ x.2.2.1.2.2 ≤ q ∧
      x.2.2.2.2.2 = q - x.2.2.1.2.2 := by
  rw [PMF.mem_support_iff, certificateStoppedWorldJointStep_some] at hx
  by_cases hcost : x.1.trace.hashCalls ≤ ghost.2.2
  · simp only [if_pos hcost] at hx
    have hfull : x ∈ (certificateUnboundedWorldJointStep key budget required
        stopAfter world state ghost).support := (PMF.mem_support_iff _ _).2 hx
    obtain ⟨hcache', hremaining', hspent'⟩ :=
      certificateUnboundedWorldJointStep_state_relation key budget required
        stopAfter world state ghost x hfull
    constructor
    · exact hcache'
    constructor
    · omega
    · omega
  · simp [hcost] at hx

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


abbrev CertificateStoppedJointOutput (input : (OracleWorld + SigningSpec).Domain) :=
  ProposalExecutionRecord input × Nat × CertificateCountedState × CertificateStoppedCacheState

noncomputable def certificateUnboundedJointStep (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) : PMF (CertificateStoppedJointOutput input) :=
  match input with
  | .inl world => certificateUnboundedWorldJointStep key budget required stopAfter world state ghost
  | .inr message => certificateUnboundedSigningJointStep key budget required stopAfter message state ghost

noncomputable def certificateStoppedJointStep (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) : PMF (Option (CertificateStoppedJointOutput input)) :=
  match input with
  | .inl world => certificateStoppedWorldJointStep key budget required stopAfter world state ghost
  | .inr message => certificateStoppedSigningJointStep key budget required stopAfter message state ghost

theorem certificateStoppedJointStep_some (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) (x : CertificateStoppedJointOutput input) :
    certificateStoppedJointStep key budget required stopAfter input state ghost (some x) =
      if x.1.trace.hashCalls ≤ ghost.2.2 then
        certificateUnboundedJointStep key budget required stopAfter input state ghost x
      else 0 := by
  cases input with
  | inl world => exact certificateStoppedWorldJointStep_some key budget required stopAfter world state ghost x
  | inr message => exact certificateStoppedSigningJointStep_some key budget required stopAfter message state ghost x

theorem certificateStoppedJointStep_relation (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) (q : Nat)
    (hspent : state.2.2 ≤ q) (hremaining : ghost.2.2 = q - state.2.2)
    (x : CertificateStoppedJointOutput input)
    (hx : some x ∈ (certificateStoppedJointStep key budget required stopAfter
      input state ghost).support) :
    x.2.2.2.1 = x.2.2.1.1 ∧ x.2.2.1.2.2 ≤ q ∧
      x.2.2.2.2.2 = q - x.2.2.1.2.2 := by
  cases input with
  | inl world => exact certificateStoppedWorldJointStep_relation key budget required stopAfter world state ghost q hspent hremaining x hx
  | inr message => exact certificateStoppedSigningJointStep_relation key budget required stopAfter message state ghost q hspent hremaining x hx

theorem certificateUnboundedJointStep_project (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) (hcache : ghost.1 = state.1) :
    (certificateUnboundedJointStep key budget required stopAfter input state ghost).map
      (fun output => (output.1.output, output.2.2.1)) =
    ((certificateCountedLengthImpl key budget required stopAfter input).run state) := by
  cases input with
  | inl world => exact certificateUnboundedWorldJointStep_project key budget required stopAfter world state ghost hcache
  | inr message => exact certificateUnboundedSigningJointStep_project key budget required stopAfter message state ghost hcache


abbrev CertificateJointState := CertificateCountedState × CertificateStoppedCacheState

noncomputable def certificateStoppedOuterRun {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    CertificateJointState → PMF (Option (Result × CertificateJointState)) :=
  OracleComp.construct (fun result state => PMF.pure (some (result, state)))
    (fun input _ next state =>
      (certificateStoppedJointStep key budget required stopAfter input state.1 state.2).bind
        fun output => match output with
        | none => PMF.pure none
        | some x => next x.1.output (x.2.2.1, x.2.2.2)) computation

noncomputable def certificateUnboundedOuterRun {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    CertificateJointState → PMF (Result × CertificateJointState) :=
  OracleComp.construct (fun result state => PMF.pure (result, state))
    (fun input _ next state =>
      (certificateUnboundedJointStep key budget required stopAfter input state.1 state.2).bind
        fun x => next x.1.output (x.2.2.1, x.2.2.2)) computation


theorem certificateStoppedOuterRun_pure {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (result : Result) (state : CertificateJointState) :
    certificateStoppedOuterRun key budget required stopAfter
      (pure result : OracleComp (OracleWorld + SigningSpec) Result) state =
    PMF.pure (some (result, state)) := by rfl

theorem certificateStoppedOuterRun_query_bind {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result)
    (state : CertificateJointState) :
    certificateStoppedOuterRun key budget required stopAfter
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
    (certificateStoppedJointStep key budget required stopAfter input state.1 state.2).bind
      (fun output => match output with
      | none => PMF.pure none
      | some x => certificateStoppedOuterRun key budget required stopAfter
          (next x.1.output) (x.2.2.1, x.2.2.2)) := by rfl

theorem certificateUnboundedOuterRun_pure {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (result : Result) (state : CertificateJointState) :
    certificateUnboundedOuterRun key budget required stopAfter
      (pure result : OracleComp (OracleWorld + SigningSpec) Result) state =
    PMF.pure (result, state) := by rfl

theorem certificateUnboundedOuterRun_query_bind {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result)
    (state : CertificateJointState) :
    certificateUnboundedOuterRun key budget required stopAfter
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
    (certificateUnboundedJointStep key budget required stopAfter input state.1 state.2).bind
      (fun x => certificateUnboundedOuterRun key budget required stopAfter
          (next x.1.output) (x.2.2.1, x.2.2.2)) := by rfl


private theorem option_kernel_transfer {A B : Type} (p : PMF (Option A)) (q : PMF A)
    (good : A → Prop) [DecidablePred good]
    (hp : ∀ a, p (some a) = if good a then q a else 0)
    (k : A → PMF (Option B)) (event : B → Prop) :
    Pr[fun r : Option B => r.elim False event |
      p.bind (fun r => match r with
        | none => PMF.pure none
        | some a => k a)] =
    Pr[fun r : Option B => r.elim False event |
      q.bind (fun a => if good a then k a else PMF.pure none)] := by
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


theorem certificateUnboundedJointStep_spent (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) (x : CertificateStoppedJointOutput input)
    (hx : x ∈ (certificateUnboundedJointStep key budget required stopAfter input state ghost).support) :
    x.2.2.1.2.2 = state.2.2 + x.1.trace.hashCalls := by
  cases input with
  | inl world =>
      exact (certificateUnboundedWorldJointStep_state_relation key budget required stopAfter
        world state ghost x hx).2.2
  | inr message =>
      exact (certificateUnboundedSigningJointStep_state_relation key budget required stopAfter
        message state ghost x hx).2.2

theorem certificateUnboundedOuterRun_spent_mono {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    ∀ (state : CertificateJointState) (output : Result × CertificateJointState),
      output ∈ (certificateUnboundedOuterRun key budget required stopAfter computation state).support →
      state.1.2.2 ≤ output.2.1.2.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro state output houtput
      rw [certificateUnboundedOuterRun_pure, PMF.mem_support_pure_iff] at houtput
      subst output
      exact Nat.le_refl _
  | query_bind input next ih =>
      intro state output houtput
      rw [certificateUnboundedOuterRun_query_bind, PMF.mem_support_bind_iff] at houtput
      obtain ⟨middle, hmiddle, htail⟩ := houtput
      have hstep := certificateUnboundedJointStep_spent key budget required stopAfter
        input state.1 state.2 middle hmiddle
      have hnext := ih middle.1.output (middle.2.2.1, middle.2.2.2) output htail
      change middle.2.2.1.2.2 ≤ output.2.1.2.2 at hnext
      omega


theorem certificateStoppedOuterRun_budget_event {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    ∀ (state : CertificateJointState) (q : Nat),
      state.1.2.2 ≤ q → state.2.2.2 = q - state.1.2.2 →
      ∀ (event : Result × CertificateJointState → Prop),
      Pr[fun result => result.elim False event |
        certificateStoppedOuterRun key budget required stopAfter computation state] =
      Pr[fun result => result.2.1.2.2 ≤ q ∧ event result |
        certificateUnboundedOuterRun key budget required stopAfter computation state] := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro state q hspent hremaining event
      classical
      rw [certificateStoppedOuterRun_pure, certificateUnboundedOuterRun_pure]
      rw [← PMF.monad_pure_eq_pure, probEvent_pure,
        ← PMF.monad_pure_eq_pure, probEvent_pure]
      simp [hspent]
  | query_bind input next ih =>
      intro state q hspent hremaining event
      classical
      rw [certificateStoppedOuterRun_query_bind, certificateUnboundedOuterRun_query_bind]
      have hstep := option_kernel_transfer
        (certificateStoppedJointStep key budget required stopAfter input state.1 state.2)
        (certificateUnboundedJointStep key budget required stopAfter input state.1 state.2)
        (fun x => x.1.trace.hashCalls ≤ state.2.2.2)
        (certificateStoppedJointStep_some key budget required stopAfter input state.1 state.2)
        (fun x => certificateStoppedOuterRun key budget required stopAfter
          (next x.1.output) (x.2.2.1, x.2.2.2)) event
      calc
        _ = Pr[fun r => r.elim False event |
            (certificateUnboundedJointStep key budget required stopAfter input state.1 state.2).bind
              (fun a => if a.1.trace.hashCalls ≤ state.2.2.2 then
                certificateStoppedOuterRun key budget required stopAfter
                  (next a.1.output) (a.2.2.1, a.2.2.2) else PMF.pure none)] := by
              convert hstep using 1
              all_goals
                congr 1
                congr 1
                funext r
                cases r <;> rfl
        _ = _ := by
          rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum,
            ← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum]
          apply tsum_congr
          intro x
          rcases Classical.em ((certificateUnboundedJointStep key budget required stopAfter
            input state.1 state.2) x = 0) with hzero | hzero
          · simp [hzero]
          have hx : x ∈ (certificateUnboundedJointStep key budget required stopAfter
            input state.1 state.2).support := (PMF.mem_support_iff _ _).2 hzero
          by_cases hgood : x.1.trace.hashCalls ≤ state.2.2.2
          · have hstopped : some x ∈ (certificateStoppedJointStep key budget required
                stopAfter input state.1 state.2).support := by
              apply (PMF.mem_support_iff _ _).2
              rw [certificateStoppedJointStep_some, if_pos hgood]
              exact hzero
            have hrel := certificateStoppedJointStep_relation key budget required
              stopAfter input state.1 state.2 q hspent hremaining x hstopped
            have hrec := ih x.1.output (x.2.2.1, x.2.2.2) q hrel.2.1 hrel.2.2 event
            simp only [if_pos hgood]
            rw [hrec]
          · have hspentstep := certificateUnboundedJointStep_spent key budget required
              stopAfter input state.1 state.2 x hx
            have hhigh : q < x.2.2.1.2.2 := by omega
            have hzero_tail : probEvent
                (certificateUnboundedOuterRun key budget required stopAfter
                  (next x.1.output) (x.2.2.1, x.2.2.2))
                (fun result => result.2.1.2.2 ≤ q ∧ event result) = 0 := by
              change probEvent (𝒮[certificateUnboundedOuterRun key budget required
                stopAfter (next x.1.output) (x.2.2.1, x.2.2.2)])
                (fun result => result.2.1.2.2 ≤ q ∧ event result) = 0
              apply probEvent_eq_zero
              intro y hy hcondition
              have hy' : y ∈ (certificateUnboundedOuterRun key budget required stopAfter
                  (next x.1.output) (x.2.2.1, x.2.2.2)).support := by
                apply (PMF.mem_support_iff _ _).2
                have hnz := (mem_support_iff (mx := 𝒮[certificateUnboundedOuterRun key
                  budget required stopAfter (next x.1.output) (x.2.2.1, x.2.2.2)]) y).1 hy
                simpa [probOutput_def] using hnz
              have hmono := certificateUnboundedOuterRun_spent_mono key budget required
                stopAfter (next x.1.output) (x.2.2.1, x.2.2.2) y hy'
              change x.2.2.1.2.2 ≤ y.2.1.2.2 at hmono
              omega
            simp only [if_neg hgood]
            rw [← PMF.monad_pure_eq_pure, probEvent_pure]
            simp [hzero_tail]


theorem certificateUnboundedJointStep_cache (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) (x : CertificateStoppedJointOutput input)
    (hx : x ∈ (certificateUnboundedJointStep key budget required stopAfter input state ghost).support) :
    x.2.2.2.1 = x.2.2.1.1 := by
  cases input with
  | inl world =>
      exact (certificateUnboundedWorldJointStep_state_relation key budget required
        stopAfter world state ghost x hx).1
  | inr message =>
      exact (certificateUnboundedSigningJointStep_state_relation key budget required
        stopAfter message state ghost x hx).1

theorem certificateUnboundedOuterRun_project {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    ∀ (state : CertificateJointState), state.2.1 = state.1.1 →
      (certificateUnboundedOuterRun key budget required stopAfter computation state).map
        (fun result => (result.1, result.2.1)) =
      (simulateQ (certificateCountedLengthImpl key budget required stopAfter) computation).run state.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro state hcache
      rw [certificateUnboundedOuterRun_pure, simulateQ_pure]
      rw [PMF.pure_map]
      rfl
  | query_bind input next ih =>
      intro state hcache
      rw [certificateUnboundedOuterRun_query_bind, PMF.map_bind]
      rw [simulateQ_query_bind, StateT.run_bind]
      have hstep := certificateUnboundedJointStep_project key budget required
        stopAfter input state.1 state.2 hcache
      calc
        _ = (certificateUnboundedJointStep key budget required stopAfter input state.1 state.2).bind
            (fun a => (simulateQ (certificateCountedLengthImpl key budget required stopAfter)
              (next a.1.output)).run a.2.2.1) := by
                apply PMF.bind_congr
                intro a ha
                exact ih a.1.output (a.2.2.1, a.2.2.2)
                  (certificateUnboundedJointStep_cache key budget required
                    stopAfter input state.1 state.2 a ((PMF.mem_support_iff _ _).2 ha))
        _ = ((certificateUnboundedJointStep key budget required stopAfter input state.1 state.2).map
            (fun a => (a.1.output, a.2.2.1))).bind
            (fun a => (simulateQ (certificateCountedLengthImpl key budget required stopAfter)
              (next a.1)).run a.2) := by rw [PMF.bind_map]; rfl
        _ = _ := by rw [hstep]; rfl


theorem certificateStoppedOuterRun_hit_budget_event {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : CertificateJointState) (q : Nat)
    (hcache : state.2.1 = state.1.1) (hspent : state.1.2.2 ≤ q)
    (hremaining : state.2.2.2 = q - state.1.2.2) :
    Pr[fun result => result.2.2.1.2 = true ∧ result.2.2.2 ≤ q |
      (simulateQ (certificateCountedLengthImpl key budget required stopAfter)
        computation).run state.1] =
    Pr[fun result => result.elim False (fun value => value.2.1.2.1.2 = true) |
      certificateStoppedOuterRun key budget required stopAfter computation state] := by
  have hproject := certificateUnboundedOuterRun_project key budget required
    stopAfter computation state hcache
  have hbudget := certificateStoppedOuterRun_budget_event key budget required
    stopAfter computation state q hspent hremaining
    (fun result => result.2.1.2.1.2 = true)
  calc
    _ = Pr[fun result => result.2.1.2.2 ≤ q ∧ result.2.1.2.1.2 = true |
        certificateUnboundedOuterRun key budget required stopAfter computation state] := by
          rw [← hproject, ← PMF.monad_map_eq_map, probEvent_map]
          simp only [Function.comp_def, and_comm]
    _ = _ := hbudget.symm


noncomputable def certificateInitialCountedState
    (generated : CertificateKeygenBoundaryResult) (stopped : Bool) : CertificateCountedState :=
  (generated.2, ((initialCertificateMonitor generated.1.2.hashCalls stopped, false),
    generated.1.2.hashCalls))

theorem certificateStoppedKeygenInit_joint_relation (q : Nat) (stopped : Bool)
    (generated : CertificateKeygenBoundaryResult) (ghost : CertificateStoppedCacheState)
    (hinit : some (generated, ghost) ∈ (certificateStoppedKeygenInit q).support) :
    (certificateInitialCountedState generated stopped).2.2 ≤ q ∧
    ghost.1 = (certificateInitialCountedState generated stopped).1 ∧
    ghost.2.2 = q - (certificateInitialCountedState generated stopped).2.2 ∧
    ghost.2.1 = false ∧
    ¬ CertificateCacheExceptional generated.1.1.2 ghost.1 := by
  have h := certificateStoppedKeygenInit_support q (some (generated, ghost)) hinit
    generated ghost rfl
  rcases h with ⟨hcost, rfl, hclean⟩
  exact ⟨hcost, rfl, rfl, rfl, hclean⟩


open FtsProbeSimulation (messageHashCharge)

noncomputable def stoppedCacheHistoryWeight (key : SecretKey)
    (state : CertificateStoppedCacheState) : ENNReal :=
  if state.2.1 then 1 else certificateCacheExceptionWeight key state.1

theorem expected_stoppedCacheHistoryWeight_step (key : SecretKey)
    (input : OracleWorld.Domain) (state : CertificateStoppedCacheState)
    (hfinite : Finite state.1) :
    (∑' result, Pr[= result | (certificateStoppedRomImpl key input).run state] *
      stoppedCacheHistoryWeight key result.2) ≤
      stoppedCacheHistoryWeight key state +
        hashQueryCharge (fun cache hash => messageHashCharge key.parameter cache hash *
          certificateCacheExceptionRate) state.1 input := by
  simp only [certificateStoppedRomImpl, StateT.run_mk]
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
  by_cases hhit : state.2.1 = true
  · simp only [stoppedCacheHistoryWeight, hhit, Bool.true_or, if_true, mul_one,
      tsum_probOutput_of_liftM_PMF]
    exact le_self_add
  · by_cases hbad : CertificateCacheExceptional key state.1
    · simp only [stoppedCacheHistoryWeight, hhit, Bool.false_or, hbad,
        decide_true, Bool.true_or, if_true, mul_one, tsum_probOutput_of_liftM_PMF]
      exact (certificateCacheExceptionWeight_bad key state.1 hfinite hbad).trans le_self_add
    · simp only [stoppedCacheHistoryWeight, hhit, Bool.false_or, hbad, decide_false]
      have hraw := expected_certificateCacheExceptionWeight_rom key input state.1 hfinite
      have hpoint (x : OracleWorld.Range input × QueryCache HashSpec) :
          Pr[= x | (romPmfImpl input).run state.1] =
            Pr[= x | (romImpl input).run state.1] := rfl
      simp only [Bool.false_eq_true, if_false]
      calc
        _ ≤ ∑' x, Pr[= x | (romPmfImpl input).run state.1] *
            certificateCacheExceptionWeight key x.2 := by
          apply ENNReal.tsum_le_tsum
          intro x
          by_cases hx : x ∈ ((romPmfImpl input).run state.1).support
          · apply mul_le_mul' le_rfl
            by_cases hb : CertificateCacheExceptional key x.2
            · simp only [hb, decide_true, if_true]
              have hsource : x ∈ support ((romImpl input).run state.1) := by
                simpa only [romPmfImpl, StateT.run_mk, probCompLift_support] using hx
              exact certificateCacheExceptionWeight_bad key x.2
                (finite_of_mem_support_romImpl hfinite hsource) hb
            · simp [hb]
          · have hz : (romPmfImpl input).run state.1 x = 0 := by
              simpa only [PMF.mem_support_iff, not_not] using hx
            rw [PMF.probOutput_eq_apply, hz, zero_mul, zero_mul]
        _ = ∑' x, Pr[= x | (romImpl input).run state.1] *
            certificateCacheExceptionWeight key x.2 := by
          apply tsum_congr
          intro x
          rw [hpoint]
        _ ≤ _ := hraw


open FtsProbeSimulation (messageHashCharge)

noncomputable def stoppedSuccessPotential {Result : Type} (key : SecretKey)
    (result : Option (Result × Nat) × CertificateStoppedCacheState) : ENNReal :=
  if result.1.isSome then
    stoppedCacheHistoryWeight key result.2 +
      (result.2.2.2 : ENNReal) * certificateCacheExceptionRate else 0

theorem certificateStoppedRomImpl_finite (key : SecretKey)
    (input : OracleWorld.Domain) (state : CertificateStoppedCacheState)
    (hfinite : Finite state.1)
    (result : OracleWorld.Range input × CertificateStoppedCacheState)
    (hr : result ∈ ((certificateStoppedRomImpl key input).run state).support) :
    Finite result.2.1 := by
  have hm : (result.1, result.2.1) ∈ ((romPmfImpl input).run state.1).support := by
    rw [← certificateStoppedRomImpl_cache_project key input state,
      PMF.monad_map_eq_map, PMF.mem_support_map_iff]
    exact ⟨result, hr, rfl⟩
  have hs : (result.1, result.2.1) ∈ support ((romImpl input).run state.1) := by
    simpa only [romPmfImpl, StateT.run_mk, probCompLift_support] using hm
  exact finite_of_mem_support_romImpl hfinite hs

theorem stoppedWorldRun_potential {Result : Type} (key : SecretKey)
    (computation : OracleComp OracleWorld Result) :
    ∀ (budget : Nat) (state : CertificateStoppedCacheState),
      state.2.2 = budget → Finite state.1 →
      (∑' result, Pr[= result |
        (simulateQ (certificateStoppedRomImpl key)
          (QueryCap.run (fun input : OracleWorld.Domain => input matches .inr _)
            computation budget)).run state] * stoppedSuccessPotential key result) ≤
      stoppedCacheHistoryWeight key state +
        (budget : ENNReal) * certificateCacheExceptionRate := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state hremaining hfinite
      rw [QueryCap.run_pure, simulateQ_pure]
      rw [StateT.run_pure, tsum_probOutput_pure_mul]
      simp only [stoppedSuccessPotential, Option.isSome_some, if_true]
      simp [hremaining]
  | query_bind input next ih =>
      intro budget state hremaining hfinite
      rw [QueryCap.run_query_bind]
      by_cases hselected : (fun input : OracleWorld.Domain => input matches .inr _) input
      · simp only [if_pos hselected]
        cases budget with
        | zero =>
            rw [simulateQ_pure]
            rw [StateT.run_pure, tsum_probOutput_pure_mul]
            simp [stoppedSuccessPotential]
        | succ rem =>
            rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
              tsum_probOutput_bind_mul]
            let law := (certificateStoppedRomImpl key input).run state
            have hcharge : hashQueryCharge
                (fun cache hash => messageHashCharge key.parameter cache hash *
                  certificateCacheExceptionRate) state.1 input ≤
                certificateCacheExceptionRate := by
              cases input with
              | inl world => simp at hselected
              | inr hash =>
                  simp only [hashQueryCharge, Sum.elim_inr]
                  unfold messageHashCharge
                  split <;> simp
            calc
              _ ≤ ∑' x, Pr[= x | law] *
                  (stoppedCacheHistoryWeight key x.2 +
                    (rem : ENNReal) * certificateCacheExceptionRate) := by
                apply ENNReal.tsum_le_tsum
                intro x
                by_cases hx : x ∈ law.support
                · apply mul_le_mul' le_rfl
                  have hrem := certificateStoppedRomImpl_remaining_step key input state x hx
                  have hrem' : x.2.2.2 = rem := by
                    cases input with
                    | inl world => simp at hselected
                    | inr hash => simpa [hremaining] using hrem
                  exact ih x.1 rem x.2 hrem'
                    (certificateStoppedRomImpl_finite key input state hfinite x hx)
                · have hz : law x = 0 := by
                    simpa only [PMF.mem_support_iff, not_not] using hx
                  change Pr[= x | law] * _ ≤ Pr[= x | law] * _
                  rw [PMF.probOutput_eq_apply, hz, zero_mul, zero_mul]
              _ = (∑' x, Pr[= x | law] * stoppedCacheHistoryWeight key x.2) +
                    (rem : ENNReal) * certificateCacheExceptionRate := by
                simp_rw [mul_add, ENNReal.tsum_add]
                rw [ENNReal.tsum_mul_right]
                have htotal : (∑' x, Pr[= x | law]) = 1 := by
                  simp only [PMF.probOutput_eq_apply]
                  exact PMF.tsum_coe law
                rw [htotal, one_mul]
              _ ≤ (stoppedCacheHistoryWeight key state +
                    hashQueryCharge
                      (fun cache hash => messageHashCharge key.parameter cache hash *
                        certificateCacheExceptionRate) state.1 input) +
                    (rem : ENNReal) * certificateCacheExceptionRate := by
                exact add_le_add
                  (expected_stoppedCacheHistoryWeight_step key input state hfinite) le_rfl
              _ ≤ _ := by
                calc
                  _ ≤ (stoppedCacheHistoryWeight key state + certificateCacheExceptionRate) +
                      (rem : ENNReal) * certificateCacheExceptionRate :=
                    add_le_add (add_le_add le_rfl hcharge) le_rfl
                  _ = _ := by
                    push_cast
                    ring
      · simp only [if_neg hselected]
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          tsum_probOutput_bind_mul]
        let law := (certificateStoppedRomImpl key input).run state
        have hcharge : hashQueryCharge
            (fun cache hash => messageHashCharge key.parameter cache hash *
              certificateCacheExceptionRate) state.1 input = 0 := by
          cases input with
          | inl world => rfl
          | inr hash => simp at hselected
        calc
          _ ≤ ∑' x, Pr[= x | law] *
              (stoppedCacheHistoryWeight key x.2 +
                (budget : ENNReal) * certificateCacheExceptionRate) := by
            apply ENNReal.tsum_le_tsum
            intro x
            by_cases hx : x ∈ law.support
            · apply mul_le_mul' le_rfl
              have hrem := certificateStoppedRomImpl_remaining_step key input state x hx
              have hrem' : x.2.2.2 = budget := by
                cases input with
                | inl world => simpa [hremaining] using hrem
                | inr hash => simp at hselected
              exact ih x.1 budget x.2 hrem'
                (certificateStoppedRomImpl_finite key input state hfinite x hx)
            · have hz : law x = 0 := by
                simpa only [PMF.mem_support_iff, not_not] using hx
              change Pr[= x | law] * _ ≤ Pr[= x | law] * _
              rw [PMF.probOutput_eq_apply, hz, zero_mul, zero_mul]
          _ = (∑' x, Pr[= x | law] * stoppedCacheHistoryWeight key x.2) +
                (budget : ENNReal) * certificateCacheExceptionRate := by
            simp_rw [mul_add, ENNReal.tsum_add]
            rw [ENNReal.tsum_mul_right]
            have htotal : (∑' x, Pr[= x | law]) = 1 := by
              simp only [PMF.probOutput_eq_apply]
              exact PMF.tsum_coe law
            rw [htotal, one_mul]
          _ ≤ _ := by
            have hstep := expected_stoppedCacheHistoryWeight_step key input state hfinite
            rw [hcharge, add_zero] at hstep
            exact add_le_add hstep le_rfl

theorem stoppedWorldRun_hit_le_Q {Result : Type} (key : SecretKey)
    (computation : OracleComp OracleWorld Result)
    (budget : Nat) (state : CertificateStoppedCacheState)
    (hremaining : state.2.2 = budget) (hfinite : Finite state.1)
    (hzero : stoppedCacheHistoryWeight key state = 0) :
    Pr[fun result => result.1.isSome ∧ result.2.2.1 = true |
      (simulateQ (certificateStoppedRomImpl key)
        (QueryCap.run (fun input : OracleWorld.Domain => input matches .inr _)
          computation budget)).run state] ≤
      (budget : ENNReal) * certificateCacheExceptionRate := by
  have hpotential := stoppedWorldRun_potential key computation budget state
    hremaining hfinite
  rw [hzero, zero_add] at hpotential
  apply le_trans _ hpotential
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hevent : result.1.isSome ∧ result.2.2.1 = true
  · simp only [hevent, if_true, stoppedSuccessPotential]
    rw [stoppedCacheHistoryWeight, if_pos hevent.2]
    calc
      _ = Pr[= result |
          (simulateQ (certificateStoppedRomImpl key)
            (QueryCap.run (fun input : OracleWorld.Domain => input matches .inr _)
              computation budget)).run state] * 1 := by simp
      _ ≤ _ := mul_le_mul' le_rfl le_self_add
  · simp [hevent]


noncomputable def stoppedGhostPotential (key : SecretKey)
    (state : CertificateStoppedCacheState) : ENNReal :=
  stoppedCacheHistoryWeight key state +
    (state.2.2 : ENNReal) * certificateCacheExceptionRate

noncomputable def optionGhostPotential {A : Type} (key : SecretKey)
    (result : Option (A × CertificateStoppedCacheState)) : ENNReal :=
  result.elim 0 (fun x => stoppedGhostPotential key x.2)

theorem expected_option_kernel_same_ghost {A B C : Type} (key : SecretKey)
    (law : PMF (Option (A × CertificateStoppedCacheState)))
    (kernel : A × CertificateStoppedCacheState → PMF B)
    (out : A × CertificateStoppedCacheState → B → C) :
    (∑' result, Pr[= result |
      law.bind (fun source => match source with
        | none => PMF.pure none
        | some x => (kernel x).map (fun b => some (out x b, x.2)))] *
      optionGhostPotential key result) =
    ∑' source, Pr[= source | law] * optionGhostPotential key source := by
  rw [← PMF.monad_bind_eq_bind, tsum_probOutput_bind_mul]
  apply tsum_congr
  intro source
  congr 1
  cases source with
  | none =>
      rw [← PMF.monad_pure_eq_pure, tsum_probOutput_pure_mul]
      rfl
  | some x =>
      change (∑' z, Pr[= z | (kernel x).map (fun b => some (out x b, x.2))] *
        optionGhostPotential key z) = optionGhostPotential key (some x)
      rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
      simp only [optionGhostPotential, Option.elim_some]
      rw [ENNReal.tsum_mul_right]
      have htotal : (∑' b, Pr[= b | kernel x]) = 1 := by
        simp only [PMF.probOutput_eq_apply]
        exact PMF.tsum_coe (kernel x)
      rw [htotal, one_mul]

theorem stoppedSigningProjected_potential (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState) :
    (∑' result, Pr[= result | stoppedSigningProjected key message state] *
      optionGhostPotential key result) =
    ∑' result, Pr[= result | stoppedTracedSigningRun key message state] *
      stoppedSuccessPotential key result := by
  rw [stoppedSigningProjected, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
  apply tsum_congr
  intro result
  congr 1
  cases result with
  | mk selected ghost => cases selected <;> rfl

theorem enrichedStoppedSigningRecord_potential (key : SecretKey) (message : Message)
    (state : CertificateStoppedCacheState) (hfinite : Finite state.1) :
    (∑' result, Pr[= result | enrichedStoppedSigningRecord key message state] *
      optionGhostPotential key result) ≤ stoppedGhostPotential key state := by
  rw [enrichedStoppedSigningRecord_kernel]
  rw [← PMF.monad_bind_eq_bind, tsum_probOutput_bind_mul]
  calc
    _ = ∑' source, Pr[= source | stoppedSigningProjected key message state] *
        optionGhostPotential key source := by
      apply tsum_congr
      intro source
      congr 1
      cases source with
      | none =>
          rw [← PMF.monad_pure_eq_pure, tsum_probOutput_pure_mul]
          rfl
      | some x =>
          change (∑' result, Pr[= result |
            (signingRecordKernel key message x).map some] *
            optionGhostPotential key result) = optionGhostPotential key (some x)
          rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
          unfold signingRecordKernel
          rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
          simp only [optionGhostPotential, Option.elim_some]
          rw [ENNReal.tsum_mul_right]
          have htotal : (∑' index, Pr[= index |
              (liftM (completeSelectedIndex x.1.1.2) : PMF Index)]) = 1 := by
            simp only [PMF.probOutput_eq_apply]
            exact PMF.tsum_coe _
          rw [htotal, one_mul]
    _ = ∑' result, Pr[= result | stoppedTracedSigningRun key message state] *
        stoppedSuccessPotential key result :=
      stoppedSigningProjected_potential key message state
    _ ≤ _ := stoppedWorldRun_potential key
      (boundaryComputation key.parameter (signWithView key message))
      state.2.2 state rfl hfinite

noncomputable def optionJointPotential {input : (OracleWorld + SigningSpec).Domain}
    (key : SecretKey) (result : Option (CertificateStoppedJointOutput input)) : ENNReal :=
  result.elim 0 (fun x => stoppedGhostPotential key x.2.2.2)

theorem certificateStoppedSigningJointStep_potential (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) (hfinite : Finite ghost.1) :
    (∑' result, Pr[= result |
      certificateStoppedSigningJointStep key budget required stopAfter message state ghost] *
      optionJointPotential key result) ≤ stoppedGhostPotential key ghost := by
  rw [certificateStoppedSigningJointStep]
  rw [← PMF.monad_bind_eq_bind, tsum_probOutput_bind_mul]
  calc
    _ = ∑' source, Pr[= source | enrichedStoppedSigningRecord key message ghost] *
        optionGhostPotential key source := by
      apply tsum_congr
      intro source
      congr 1
      cases source with
      | none =>
          rw [← PMF.monad_pure_eq_pure, tsum_probOutput_pure_mul]
          rfl
      | some x =>
          change (∑' result, Pr[= result |
            (certificateStoppedSigningJointKernel key budget required stopAfter
              message state x).map some] *
            optionJointPotential key result) = optionGhostPotential key (some x)
          rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
          unfold certificateStoppedSigningJointKernel
          rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
          simp only [optionJointPotential, Option.elim_some,
            optionGhostPotential]
          rw [ENNReal.tsum_mul_right]
          have htotal : (∑' length, Pr[= length |
              certificateSigningLengthLaw key budget required stopAfter message state]) = 1 := by
            simp only [PMF.probOutput_eq_apply]
            exact PMF.tsum_coe _
          rw [htotal, one_mul]
    _ ≤ _ := enrichedStoppedSigningRecord_potential key message ghost hfinite

theorem certificateStoppedWorldJointStep_potential (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (world : OracleWorld.Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) (hfinite : Finite ghost.1) :
    (∑' result, Pr[= result |
      certificateStoppedWorldJointStep key budget required stopAfter world state ghost] *
      optionJointPotential key result) ≤ stoppedGhostPotential key ghost := by
  rw [certificateStoppedWorldJointStep,
    ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
  calc
    _ = ∑' result, Pr[= result |
        (simulateQ (certificateStoppedRomImpl key) (QueryCap.run
          (fun query : OracleWorld.Domain => query matches .inr _)
          (liftM (OracleWorld.query world)) ghost.2.2)).run ghost] *
        stoppedSuccessPotential key result := by
      apply tsum_congr
      intro result
      congr 1
      cases result with
      | mk selected finalState =>
          cases selected with
          | none => rfl
          | some answer => rfl
    _ ≤ _ := stoppedWorldRun_potential key (liftM (OracleWorld.query world))
      ghost.2.2 ghost rfl hfinite

theorem certificateStoppedJointStep_potential (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState) (hfinite : Finite ghost.1) :
    (∑' result, Pr[= result |
      certificateStoppedJointStep key budget required stopAfter input state ghost] *
      optionJointPotential key result) ≤ stoppedGhostPotential key ghost := by
  cases input with
  | inl world =>
      exact certificateStoppedWorldJointStep_potential key budget required stopAfter
        world state ghost hfinite
  | inr message =>
      exact certificateStoppedSigningJointStep_potential key budget required stopAfter
        message state ghost hfinite

theorem certificateStoppedJointStep_cache_finite (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState)
    (hcache : ghost.1 = state.1) (hfinite : Finite ghost.1)
    (x : CertificateStoppedJointOutput input)
    (hx : some x ∈ (certificateStoppedJointStep key budget required stopAfter
      input state ghost).support) :
    x.2.2.2.1 = x.2.2.1.1 ∧ Finite x.2.2.2.1 := by
  have hsome := (PMF.mem_support_iff _ _).1 hx
  rw [certificateStoppedJointStep_some] at hsome
  have hcost : x.1.trace.hashCalls ≤ ghost.2.2 := by
    by_contra hn
    simp [hn] at hsome
  simp only [if_pos hcost] at hsome
  have hunbounded : x ∈ (certificateUnboundedJointStep key budget required
      stopAfter input state ghost).support := (PMF.mem_support_iff _ _).2 hsome
  have hsame := certificateUnboundedJointStep_cache key budget required
    stopAfter input state ghost x hunbounded
  have hproject : (x.1.output, x.2.2.1) ∈
      ((certificateCountedLengthImpl key budget required stopAfter input).run state).support := by
    rw [← certificateUnboundedJointStep_project key budget required stopAfter
      input state ghost hcache, PMF.mem_support_map_iff]
    exact ⟨x, hunbounded, rfl⟩
  have hproject' : (x.1.output, certificateCountedProject x.2.2.1) ∈
      ((certificateCacheLengthImpl key budget required stopAfter input).run
        (certificateCountedProject state)).support := by
    rw [← certificateCountedLengthImpl_project key budget required stopAfter
      input state, PMF.monad_map_eq_map, PMF.mem_support_map_iff]
    exact ⟨(x.1.output, x.2.2.1), hproject, rfl⟩
  have hfin := certificateCacheLengthImpl_finite key budget required stopAfter
    input (certificateCountedProject state) (by
      have hf : Finite state.1 := by rw [← hcache]; exact hfinite
      simpa [certificateCountedProject] using hf)
    (x.1.output, certificateCountedProject x.2.2.1) hproject'
  exact ⟨hsame, by simpa [certificateCountedProject, hsame] using hfin⟩

noncomputable def optionOuterPotential {Result : Type} (key : SecretKey)
    (result : Option (Result × CertificateJointState)) : ENNReal :=
  result.elim 0 (fun x => stoppedGhostPotential key x.2.2)

theorem certificateStoppedOuterRun_potential {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    ∀ (state : CertificateJointState),
      state.2.1 = state.1.1 → Finite state.2.1 →
      (∑' result, Pr[= result |
        certificateStoppedOuterRun key budget required stopAfter computation state] *
        optionOuterPotential key result) ≤ stoppedGhostPotential key state.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro state hcache hfinite
      rw [certificateStoppedOuterRun_pure, ← PMF.monad_pure_eq_pure,
        tsum_probOutput_pure_mul]
      rfl
  | query_bind input next ih =>
      intro state hcache hfinite
      rw [certificateStoppedOuterRun_query_bind,
        ← PMF.monad_bind_eq_bind, tsum_probOutput_bind_mul]
      calc
        _ ≤ ∑' middle, Pr[= middle |
            certificateStoppedJointStep key budget required stopAfter
              input state.1 state.2] * optionJointPotential key middle := by
          apply ENNReal.tsum_le_tsum
          intro middle
          by_cases hm : middle ∈ (certificateStoppedJointStep key budget required
              stopAfter input state.1 state.2).support
          · apply mul_le_mul' le_rfl
            cases middle with
            | none =>
                rw [← PMF.monad_pure_eq_pure, tsum_probOutput_pure_mul]
                rfl
            | some x =>
                obtain ⟨hsame, hfin⟩ := certificateStoppedJointStep_cache_finite key
                  budget required stopAfter input state.1 state.2 hcache hfinite x hm
                exact ih x.1.output (x.2.2.1, x.2.2.2) hsame hfin
          · have hz : (certificateStoppedJointStep key budget required stopAfter
                input state.1 state.2) middle = 0 := by
              simpa only [PMF.mem_support_iff, not_not] using hm
            rw [PMF.probOutput_eq_apply, hz, zero_mul, zero_mul]
        _ ≤ _ := certificateStoppedJointStep_potential key budget required
          stopAfter input state.1 state.2 hfinite

theorem certificateStoppedOuterRun_hit_le_budget {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : CertificateJointState) (hcache : state.2.1 = state.1.1)
    (hfinite : Finite state.2.1)
    (hzero : stoppedCacheHistoryWeight key state.2 = 0) :
    Pr[fun result => result.elim False (fun value => value.2.2.2.1 = true) |
      certificateStoppedOuterRun key budget required stopAfter computation state] ≤
      (state.2.2.2 : ENNReal) * certificateCacheExceptionRate := by
  classical
  have hpotential := certificateStoppedOuterRun_potential key budget required
    stopAfter computation state hcache hfinite
  rw [stoppedGhostPotential, hzero, zero_add] at hpotential
  apply le_trans _ hpotential
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hevent : result.elim False (fun value => value.2.2.2.1 = true)
  · cases result with
    | none => simp at hevent
    | some value =>
        simp only [Option.elim_some] at hevent
        simp only [hevent, if_true, optionOuterPotential, Option.elim_some,
          stoppedGhostPotential]
        rw [stoppedCacheHistoryWeight, if_pos hevent]
        calc
          _ = Pr[= some value |
              certificateStoppedOuterRun key budget required stopAfter computation state] * 1 := by simp
          _ ≤ _ := mul_le_mul' le_rfl le_self_add
  · simp [hevent]


theorem enrichedSigningRecord_hit (key : SecretKey) (message : Message)
    (ghost : CertificateStoppedCacheState)
    (hcover : CertificateCacheExceptional key ghost.1 → ghost.2.1 = true)
    (x : ProposalExecutionRecord (.inr message) × CertificateStoppedCacheState)
    (hx : x ∈ (enrichedSigningRecord key message ghost).support) :
    (ghost.2.1 = true → x.2.2.1 = true) ∧
    (CertificateCacheExceptional key x.2.1 → x.2.2.1 = true) := by
  unfold enrichedSigningRecord at hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨source, hsource, hindex⟩ := hx
  rw [PMF.mem_support_map_iff] at hindex
  obtain ⟨index, _, heq⟩ := hindex
  subst x
  exact certificateStoppedRomImpl_hit_run key
    (boundaryComputation key.parameter (signWithView key message)) ghost source hcover hsource

theorem certificateUnboundedSigningJointStep_hit (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (message : Message) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState)
    (hcacheBefore : ghost.1 = state.1)
    (hcount : state.2.1.2 = true → ghost.2.1 = true)
    (hcover : CertificateCacheExceptional key ghost.1 → ghost.2.1 = true)
    (x : CertificateStoppedSigningJointOutput message)
    (hx : x ∈ (certificateUnboundedSigningJointStep key budget required stopAfter
      message state ghost).support) :
    (x.2.2.1.2.1.2 = true → x.2.2.2.2.1 = true) ∧
    (CertificateCacheExceptional key x.2.2.2.1 → x.2.2.2.2.1 = true) := by
  classical
  unfold certificateUnboundedSigningJointStep at hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨source, hsource, hkernel⟩ := hx
  unfold certificateStoppedSigningJointKernel at hkernel
  rw [PMF.mem_support_map_iff] at hkernel
  obtain ⟨length, _, heq⟩ := hkernel
  subst x
  have hhit := enrichedSigningRecord_hit key message ghost hcover source hsource
  have hcache := enrichedSigningRecord_cache key message ghost source hsource
  constructor
  · intro hnew
    simp only [originalProposalAdvance, certificateCountedUpdate,
      certificateCacheMonitorUpdate] at hnew
    change source.2.2.1 = true
    simp only [certificateCountedProject] at hnew
    rcases (Bool.or_eq_true _ _).mp hnew with hfirst | hfinal
    · rcases (Bool.or_eq_true _ _).mp hfirst with hprev | hinitial
      · exact hhit.1 (hcount hprev)
      · exact hhit.1 (hcover (by rw [hcacheBefore]; exact of_decide_eq_true hinitial))
    · exact hhit.2 (by rw [← hcache]; exact of_decide_eq_true hfinal)
  · exact hhit.2

theorem certificateUnboundedWorldJointStep_hit (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (world : OracleWorld.Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState)
    (hcacheBefore : ghost.1 = state.1)
    (hcount : state.2.1.2 = true → ghost.2.1 = true)
    (hcover : CertificateCacheExceptional key ghost.1 → ghost.2.1 = true)
    (x : CertificateStoppedWorldJointOutput world)
    (hx : x ∈ (certificateUnboundedWorldJointStep key budget required stopAfter
      world state ghost).support) :
    (x.2.2.1.2.1.2 = true → x.2.2.2.2.1 = true) ∧
    (CertificateCacheExceptional key x.2.2.2.1 → x.2.2.2.2.1 = true) := by
  classical
  unfold certificateUnboundedWorldJointStep at hx
  rw [PMF.mem_support_map_iff] at hx
  obtain ⟨source, hsource, heq⟩ := hx
  subst x
  have hhit := certificateStoppedRomImpl_hit_step key world ghost source hsource
  constructor
  · intro hnew
    simp only [certificateWorldJointOutput, originalProposalAdvance,
      certificateCountedUpdate, certificateCacheMonitorUpdate] at hnew
    change source.2.2.1 = true
    simp only [certificateCountedProject] at hnew
    rcases (Bool.or_eq_true _ _).mp hnew with hfirst | hfinal
    · rcases (Bool.or_eq_true _ _).mp hfirst with hprev | hinitial
      · exact hhit.1 (hcount hprev)
      · exact hhit.1 (hcover (by rw [hcacheBefore]; exact of_decide_eq_true hinitial))
    · exact hhit.2 (of_decide_eq_true hfinal)
  · exact hhit.2

theorem certificateStoppedJointStep_hit (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState)
    (hcacheBefore : ghost.1 = state.1)
    (hcount : state.2.1.2 = true → ghost.2.1 = true)
    (hcover : CertificateCacheExceptional key ghost.1 → ghost.2.1 = true)
    (x : CertificateStoppedJointOutput input)
    (hx : some x ∈ (certificateStoppedJointStep key budget required stopAfter
      input state ghost).support) :
    (x.2.2.1.2.1.2 = true → x.2.2.2.2.1 = true) ∧
    (CertificateCacheExceptional key x.2.2.2.1 → x.2.2.2.2.1 = true) := by
  have hsome := (PMF.mem_support_iff _ _).1 hx
  rw [certificateStoppedJointStep_some] at hsome
  have hcost : x.1.trace.hashCalls ≤ ghost.2.2 := by
    by_contra hn
    simp [hn] at hsome
  simp only [if_pos hcost] at hsome
  have hunbounded : x ∈ (certificateUnboundedJointStep key budget required
      stopAfter input state ghost).support := (PMF.mem_support_iff _ _).2 hsome
  cases input with
  | inl world =>
      exact certificateUnboundedWorldJointStep_hit key budget required stopAfter
        world state ghost hcacheBefore hcount hcover x hunbounded
  | inr message =>
      exact certificateUnboundedSigningJointStep_hit key budget required stopAfter
        message state ghost hcacheBefore hcount hcover x hunbounded

theorem certificateStoppedJointStep_cache (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (ghost : CertificateStoppedCacheState)
    (x : CertificateStoppedJointOutput input)
    (hx : some x ∈ (certificateStoppedJointStep key budget required stopAfter
      input state ghost).support) :
    x.2.2.2.1 = x.2.2.1.1 := by
  have hsome := (PMF.mem_support_iff _ _).1 hx
  rw [certificateStoppedJointStep_some] at hsome
  have hcost : x.1.trace.hashCalls ≤ ghost.2.2 := by
    by_contra hn
    simp [hn] at hsome
  simp only [if_pos hcost] at hsome
  exact certificateUnboundedJointStep_cache key budget required stopAfter
    input state ghost x ((PMF.mem_support_iff _ _).2 hsome)

theorem certificateStoppedOuterRun_hit_cover {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    ∀ (state : CertificateJointState) (output : Result × CertificateJointState),
      state.2.1 = state.1.1 →
      (state.1.2.1.2 = true → state.2.2.1 = true) →
      (CertificateCacheExceptional key state.2.1 → state.2.2.1 = true) →
      some output ∈ (certificateStoppedOuterRun key budget required stopAfter
        computation state).support →
      (output.2.1.2.1.2 = true → output.2.2.2.1 = true) ∧
      (CertificateCacheExceptional key output.2.2.1 → output.2.2.2.1 = true) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro state output hcache hcount hcover houtput
      rw [certificateStoppedOuterRun_pure, PMF.mem_support_pure_iff] at houtput
      cases houtput
      exact ⟨hcount, hcover⟩
  | query_bind input next ih =>
      intro state output hcache hcount hcover houtput
      rw [certificateStoppedOuterRun_query_bind, PMF.mem_support_bind_iff] at houtput
      obtain ⟨middle, hmiddle, htail⟩ := houtput
      cases middle with
      | none =>
          rw [PMF.mem_support_pure_iff] at htail
          cases htail
      | some x =>
          have hstep := certificateStoppedJointStep_hit key budget required
            stopAfter input state.1 state.2 hcache hcount hcover x hmiddle
          have hcache' := certificateStoppedJointStep_cache key budget required
            stopAfter input state.1 state.2 x hmiddle
          exact ih x.1.output (x.2.2.1, x.2.2.2) output hcache'
            hstep.1 hstep.2 htail

theorem certificateCountedLengthImpl_hit_budget_le_rate {Result : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : CertificateJointState) (q : Nat)
    (hcache : state.2.1 = state.1.1)
    (hspent : state.1.2.2 ≤ q)
    (hremaining : state.2.2.2 = q - state.1.2.2)
    (hcount : state.1.2.1.2 = true → state.2.2.1 = true)
    (hcover : CertificateCacheExceptional key state.2.1 → state.2.2.1 = true)
    (hfinite : Finite state.2.1)
    (hzero : stoppedCacheHistoryWeight key state.2 = 0) :
    Pr[fun result => result.2.2.1.2 = true ∧ result.2.2.2 ≤ q |
      (simulateQ (certificateCountedLengthImpl key budget required stopAfter)
        computation).run state.1] ≤
      (q - state.1.2.2 : ENNReal) * certificateCacheExceptionRate := by
  rw [certificateStoppedOuterRun_hit_budget_event key budget required stopAfter
    computation state q hcache hspent hremaining]
  calc
    _ ≤ Pr[fun result => result.elim False (fun value => value.2.2.2.1 = true) |
        certificateStoppedOuterRun key budget required stopAfter computation state] := by
      rw [← SPMF.probEvent_liftM, ← SPMF.probEvent_liftM]
      apply probEvent_mono
      intro result hr hhit
      cases result with
      | none => simp at hhit
      | some output =>
          have hr' : some output ∈
              (certificateStoppedOuterRun key budget required stopAfter
                computation state).support := by
            simpa only [SPMF.support_eq_support, SPMF.support_liftM] using hr
          exact (certificateStoppedOuterRun_hit_cover key budget required
            stopAfter computation state output hcache hcount hcover hr').1 hhit
    _ ≤ _ := by
      rw [← ENNReal.natCast_sub, ← hremaining]
      exact certificateStoppedOuterRun_hit_le_budget key budget required
        stopAfter computation state hcache hfinite hzero

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

/-- info: 'SphincsSecurity.Concrete.certificateStoppedSigningJointStep_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedSigningJointStep_event

/-- info: 'SphincsSecurity.Concrete.certificateUnboundedSigningJointStep_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateUnboundedSigningJointStep_project

/-- info: 'SphincsSecurity.Concrete.certificateStoppedSigningJointStep_unbounded_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedSigningJointStep_unbounded_budget_event

/-- info: 'SphincsSecurity.Concrete.certificateStoppedRomImpl_remaining_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedRomImpl_remaining_step

/-- info: 'SphincsSecurity.Concrete.certificateStoppedRomImpl_remaining_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedRomImpl_remaining_boundary

/-- info: 'SphincsSecurity.Concrete.enrichedSigningRecord_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.enrichedSigningRecord_remaining

/-- info: 'SphincsSecurity.Concrete.enrichedSigningRecord_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.enrichedSigningRecord_cache

/-- info: 'SphincsSecurity.Concrete.certificateUnboundedSigningJointStep_state_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateUnboundedSigningJointStep_state_relation

/-- info: 'SphincsSecurity.Concrete.certificateStoppedSigningJointStep_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedSigningJointStep_some

/-- info: 'SphincsSecurity.Concrete.certificateStoppedSigningJointStep_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedSigningJointStep_relation

/-- info: 'SphincsSecurity.Concrete.counted_world_query' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.counted_world_query

/-- info: 'SphincsSecurity.Concrete.certificateStoppedWorldJointStep_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedWorldJointStep_budget_event

/-- info: 'SphincsSecurity.Concrete.certificateUnboundedWorldJointStep_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateUnboundedWorldJointStep_project

/-- info: 'SphincsSecurity.Concrete.certificateUnboundedWorldJointStep_state_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateUnboundedWorldJointStep_state_relation

/-- info: 'SphincsSecurity.Concrete.certificateStoppedWorldJointStep_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedWorldJointStep_some

/-- info: 'SphincsSecurity.Concrete.certificateStoppedWorldJointStep_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedWorldJointStep_relation

/-- info: 'SphincsSecurity.Concrete.certificateStoppedOuterRun_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedOuterRun_budget_event

/-- info: 'SphincsSecurity.Concrete.certificateUnboundedOuterRun_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateUnboundedOuterRun_project

/-- info: 'SphincsSecurity.Concrete.certificateStoppedOuterRun_hit_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedOuterRun_hit_budget_event

/-- info: 'SphincsSecurity.Concrete.certificateStoppedKeygenInit_joint_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedKeygenInit_joint_relation

/-- info: 'SphincsSecurity.Concrete.expected_stoppedCacheHistoryWeight_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expected_stoppedCacheHistoryWeight_step

/-- info: 'SphincsSecurity.Concrete.stoppedWorldRun_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.stoppedWorldRun_potential

/-- info: 'SphincsSecurity.Concrete.stoppedWorldRun_hit_le_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.stoppedWorldRun_hit_le_Q

/-- info: 'SphincsSecurity.Concrete.enrichedStoppedSigningRecord_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.enrichedStoppedSigningRecord_potential

/-- info: 'SphincsSecurity.Concrete.certificateStoppedSigningJointStep_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedSigningJointStep_potential

/-- info: 'SphincsSecurity.Concrete.certificateStoppedWorldJointStep_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedWorldJointStep_potential

/-- info: 'SphincsSecurity.Concrete.certificateStoppedJointStep_cache_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedJointStep_cache_finite

/-- info: 'SphincsSecurity.Concrete.certificateStoppedOuterRun_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedOuterRun_potential

/-- info: 'SphincsSecurity.Concrete.certificateStoppedOuterRun_hit_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedOuterRun_hit_le_budget

/-- info: 'SphincsSecurity.Concrete.certificateStoppedJointStep_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedJointStep_hit

/-- info: 'SphincsSecurity.Concrete.certificateStoppedOuterRun_hit_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateStoppedOuterRun_hit_cover

/-- info: 'SphincsSecurity.Concrete.certificateCountedLengthImpl_hit_budget_le_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedLengthImpl_hit_budget_le_rate

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal

theorem certificateCountedLengthImpl_spent_mono {Result : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : CertificateCountedState) (output : Result × CertificateCountedState)
    (houtput : output ∈ ((simulateQ (certificateCountedLengthImpl key budget required stopAfter)
      computation).run state).support) :
    state.2.2 ≤ output.2.2.2 := by
  let ghost : CertificateStoppedCacheState := (state.1, (false, 0))
  have hproject := certificateUnboundedOuterRun_project key budget required stopAfter
    computation (state, ghost) rfl
  rw [← hproject, PMF.mem_support_map_iff] at houtput
  obtain ⟨source, hsource, heq⟩ := houtput
  cases heq
  exact certificateUnboundedOuterRun_spent_mono key budget required stopAfter
    computation (state, ghost) source hsource

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal

noncomputable def keygenCountedLengthGame {Result : Type} (_q budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule)
    (stopped : Bool)
    (rest : CertificateKeygenBoundaryResult →
      OracleComp (OracleWorld + SigningSpec) Result) :
    PMF (Result × CertificateCountedState) :=
  (liftM (boundaryRun 0 scheme.keygen ∅) : PMF CertificateKeygenBoundaryResult).bind
    fun generated =>
      (simulateQ (certificateCountedLengthImpl generated.1.1.2 budget required
        (stopAfter generated.1.1.2)) (rest generated)).run
        (certificateInitialCountedState generated stopped)

theorem keygenCountedLengthGame_hit_budget_le_rate {Result : Type}
    (q budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (rest : CertificateKeygenBoundaryResult →
      OracleComp (OracleWorld + SigningSpec) Result) :
    Pr[fun result => result.2.2.1.2 = true ∧ result.2.2.2 ≤ q |
      keygenCountedLengthGame q budget required stopAfter stopped rest] ≤
      (q : ENNReal) * certificateCacheExceptionRate := by
  unfold keygenCountedLengthGame
  rw [← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' generated,
        Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] *
          ((q - generated.1.2.hashCalls : ENNReal) * certificateCacheExceptionRate) := by
      apply ENNReal.tsum_le_tsum
      intro generated
      by_cases hg : generated ∈
          (liftM (boundaryRun 0 scheme.keygen ∅) : PMF CertificateKeygenBoundaryResult).support
      · apply mul_le_mul' le_rfl
        have hb : generated ∈ support (boundaryRun 0 scheme.keygen ∅) :=
          (probCompLift_support _ ▸ hg)
        have hrun : (generated.1.1, generated.2) ∈
            support ((simulateQ romImpl scheme.keygen).run ∅) := by
          rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
          exact ⟨generated, hb, rfl⟩
        let state := certificateInitialCountedState generated stopped
        let ghost : CertificateStoppedCacheState :=
          (generated.2, (false, q - generated.1.2.hashCalls))
        have hfinite : Finite ghost.1 :=
          finite_cache_of_mem_support scheme.keygen ∅ generated.1.1 generated.2 hrun finite_empty
        have hclean := certificateStoppedKeygen_cache_clean generated hb
        have hzero : stoppedCacheHistoryWeight generated.1.1.2 ghost = 0 := by
          rw [stoppedCacheHistoryWeight]
          simp only [ghost, Bool.false_eq_true, if_false]
          exact certificateCacheExceptionWeight_initial generated.1.1.2 generated.2
            (keygen_cache_message_none (generated.1.1, generated.2) hrun)
        by_cases hspent : generated.1.2.hashCalls ≤ q
        · exact certificateCountedLengthImpl_hit_budget_le_rate
            generated.1.1.2 budget required (stopAfter generated.1.1.2)
            (rest generated) (state, ghost) q rfl hspent rfl
            (by simp [state, certificateInitialCountedState])
            (by intro hbad; exact False.elim (hclean hbad))
            hfinite hzero
        · have hnone : Pr[fun result => result.2.2.1.2 = true ∧ result.2.2.2 ≤ q |
              (simulateQ (certificateCountedLengthImpl generated.1.1.2 budget required
                (stopAfter generated.1.1.2)) (rest generated)).run state] = 0 := by
            rw [← SPMF.probEvent_liftM]
            apply probEvent_eq_zero
            intro result hr hevent
            have hr' : result ∈ ((simulateQ (certificateCountedLengthImpl
                generated.1.1.2 budget required (stopAfter generated.1.1.2))
                (rest generated)).run state).support := by
              simpa only [SPMF.support_eq_support, SPMF.support_liftM] using hr
            have hmono := certificateCountedLengthImpl_spent_mono generated.1.1.2
              budget required (stopAfter generated.1.1.2) (rest generated) state result hr'
            simp only [state, certificateInitialCountedState] at hmono
            omega
          rw [hnone]
          exact zero_le
      · have hz : (liftM (boundaryRun 0 scheme.keygen ∅) : PMF CertificateKeygenBoundaryResult) generated = 0 := by
          simpa only [PMF.mem_support_iff, not_not] using hg
        rw [PMF.probOutput_eq_apply, hz, zero_mul, zero_mul]
    _ ≤ ∑' generated,
        Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] *
          ((q : ENNReal) * certificateCacheExceptionRate) := by
      apply ENNReal.tsum_le_tsum
      intro generated
      apply mul_le_mul' le_rfl
      rw [← ENNReal.natCast_sub]
      exact mul_le_mul' (Nat.cast_le.mpr (Nat.sub_le _ _)) le_rfl
    _ = _ := by
      rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.certificateCountedLengthImpl_spent_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedLengthImpl_spent_mono

/-- info: 'SphincsSecurity.Concrete.keygenCountedLengthGame_hit_budget_le_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.keygenCountedLengthGame_hit_budget_le_rate

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal

theorem certificateCountedContextGame_length (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule)
    (stopped : Bool) :
    (fun result : CertificateCountedContextResult => (result.2.1, result.2.2.2)) <$>
      certificateCountedContextGame adversary budget required stopAfter stopped =
    keygenCountedLengthGame budget budget required stopAfter stopped
      (fun generated => FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1) := by
  simp only [certificateCountedContextGame, keygenCountedLengthGame, map_bind, map_pure]
  apply PMF.bind_congr
  intro generated _
  simp only [bind_pure_comp]
  change Prod.map id Prod.snd <$> _ = _
  unfold certificateCountedProposalImpl certificateCountedLengthImpl
  exact simulateQ_originalProposalImpl_length _ _ _ _ _ _

theorem certificateCountedContextGame_cache_hit_budget_le_rate
    (adversary : Adversary) (q : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    Pr[fun result => result.project.2.2.2.2.2 = true ∧ result.originalCost.2 ≤ q |
      certificateCountedContextGame adversary q required stopAfter stopped] ≤
      (q : ENNReal) * certificateCacheExceptionRate := by
  have h := keygenCountedLengthGame_hit_budget_le_rate q q required stopAfter stopped
    (fun generated => FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)
  rw [← certificateCountedContextGame_length adversary q required stopAfter stopped,
    probEvent_map] at h
  simpa only [CertificateCountedContextResult.project,
    CertificateCountedContextResult.originalCost, certificateCountedProject, Function.comp_def] using h

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.certificateCountedContextGame_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedContextGame_length

/-- info: 'SphincsSecurity.Concrete.certificateCountedContextGame_cache_hit_budget_le_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedContextGame_cache_hit_budget_le_rate

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private theorem stateTpmf_support_subset {I State Result : Type} {spec : OracleSpec I}
    (impl : QueryImpl spec (StateT State PMF))
    (computation : OracleComp spec Result) (state : State) :
    ∀ result ∈ ((simulateQ impl computation).run state).support,
      result.1 ∈ support computation := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result hr
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      simp only [mem_support_pure_iff]
  | query_bind input next ih =>
      intro result hr
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, _, htail⟩ := hr
      rw [mem_support_bind_iff]
      exact ⟨middle.1, by simp only [support_query, Set.mem_univ],
        ih middle.1 middle.2 result htail⟩


theorem counted_game_query_le_cost
    (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary)
    (cache : QueryCache HashSpec)
    (result : ((Bool × SigningBoundaryTrace) × Nat) × QueryCache HashSpec)
    (hr : result ∈ ((simulateQ romPmfImpl (QueryCap.counted CausalFrontierProgram.IsHash
      (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary))).run cache).support) :
    result.1.2 ≤ result.1.1.2.hashCalls := by
  have hsource : result.1 ∈ support (QueryCap.counted CausalFrontierProgram.IsHash
      (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary)) :=
    stateTpmf_support_subset romPmfImpl _ cache result hr
  exact CausalFrontierProgram.game_counted_le parameter external ftsSecret words frontier adversary result.1 hsource

theorem counted_game_run_forget
    (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary)
    (cache : QueryCache HashSpec) :
    (fun output : ((Bool × SigningBoundaryTrace) × Nat) × QueryCache HashSpec =>
      (output.1.1, output.2)) <$>
      ((simulateQ romPmfImpl (QueryCap.counted CausalFrontierProgram.IsHash
        (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary))).run cache) =
      ((simulateQ romPmfImpl (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary)).run cache) := by
  rw [← StateT.run_map, ← simulateQ_map, QueryCap.counted_forget]


/-- The organizer's actual-cost event is preserved by one shared hash-query cap. -/
theorem causal_game_globalCap_budget_event
    (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary)
    (cache : QueryCache HashSpec) (q : Nat)
    (event : (Bool × SigningBoundaryTrace) → QueryCache HashSpec → Prop) :
    Pr[QueryCap.stoppedStateEvent
        (fun output finalCache => output.2.hashCalls ≤ q ∧ event output finalCache) |
      (simulateQ romPmfImpl (QueryCap.run CausalFrontierProgram.IsHash
        (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary) q)).run cache] =
    Pr[fun output => output.1.2.hashCalls ≤ q ∧ event output.1 output.2 |
      (simulateQ romPmfImpl (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary)).run cache] := by
  have hcap := QueryCap.run_budget_event_state CausalFrontierProgram.IsHash romPmfImpl
    (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary) q cache
    (fun output finalCache => output.2.hashCalls ≤ q ∧ event output finalCache)
  rw [hcap]
  have hmap := counted_game_run_forget parameter external ftsSecret words frontier adversary cache
  rw [← hmap, probEvent_map]
  change probEvent (liftM ((simulateQ romPmfImpl (QueryCap.counted CausalFrontierProgram.IsHash
    (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary))).run cache) : SPMF _) _ =
    probEvent (liftM ((simulateQ romPmfImpl (QueryCap.counted CausalFrontierProgram.IsHash
    (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary))).run cache) : SPMF _) _
  apply le_antisymm
  · apply probEvent_mono
    intro output _ h
    exact h.2
  · apply probEvent_mono
    intro output houtput h
    change output ∈ (liftM ((simulateQ romPmfImpl (QueryCap.counted CausalFrontierProgram.IsHash
      (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary))).run cache) : SPMF _).support at houtput
    have hpmf : output ∈ ((simulateQ romPmfImpl (QueryCap.counted CausalFrontierProgram.IsHash
        (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary))).run cache).support := by
      simpa only [SPMF.support_liftM] using houtput
    exact ⟨(counted_game_query_le_cost parameter external ftsSecret words frontier adversary cache output hpmf).trans h.1, h⟩


end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.counted_game_query_le_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.counted_game_query_le_cost

/-- info: 'SphincsSecurity.Concrete.counted_game_run_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.counted_game_run_forget

/-- info: 'SphincsSecurity.Concrete.causal_game_globalCap_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.causal_game_globalCap_budget_event
