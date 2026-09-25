import SigGolfCandidate.SphincsInteractionCutoff
import SigGolfCandidate.SphincsAlignedQuery

/-! Distributional interaction lemmas for the organizer's lazy hash oracle and fresh coins. -/

namespace SigGolfCandidate.SphincsAdaptiveCutoffDistribution
open SigGolf OracleComp OracleSpec
set_option maxRecDepth 16384
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false

theorem support_transfer {α : Type} (program : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (property : α → Prop)
    (hproperty : ∀ hash : Hash, property (evalWithAnswerFn hash program))
    (result : α) (finalCache : QueryCache HashSpec)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ (OracleSpec.randomOracle (spec := HashSpec)) program).run cache)) :
    property result := by
  obtain ⟨hash, _, heval⟩ :=
    (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support program cache result).mpr
      ⟨finalCache, hmem⟩
  rw [← heval]
  exact hproperty hash

theorem record_preserves_charge
    (request : SigningRequest)
    (transcript : Transcript SphincsSubmission.submission.sizes)
    (result : RunResult (Bytes SphincsSubmission.submission.sizes.signature))
    (hbefore : transcript.signingRequests ≤ transcript.hashCalls)
    (hfloor : 1 ≤ result.hashCalls) :
    (transcript.record request.message result).signingRequests ≤
      (transcript.record request.message result).hashCalls := by
  simp only [Transcript.record]
  omega

/-- A lazy-oracle signer result always pays for its first HASH. -/
theorem signingOracle_support_floor
    (secretKey : SecretKey) (request : SigningRequest)
    (cache finalCache : QueryCache HashSpec)
    (result : RunResult (Bytes SphincsSubmission.submission.sizes.signature))
    (hmem : (result, finalCache) ∈ support
      ((simulateQ (OracleSpec.randomOracle (spec := HashSpec))
        (SphincsSubmission.submission.signingOracle secretKey request)).run cache)) :
    1 ≤ result.hashCalls := by
  generalize hprogram : SphincsSubmission.submission.signingOracle secretKey request = program at hmem
  have hpoint : ∀ hash : Hash,
      1 ≤ (evalWithAnswerFn hash program).hashCalls := by
    intro hash
    have hfloor := SphincsSignCallFloor.sign_runWith_one_call hash secretKey
      request.cache request.message
    rw [← hprogram]
    change 1 ≤ (SphincsSubmission.submission.runWith hash .sign
      (secretKey, request.cache, request.message)).hashCalls
    exact hfloor
  exact support_transfer program cache (fun result => 1 ≤ result.hashCalls)
    hpoint result finalCache hmem

theorem world_signingOracle_support_floor
    (secretKey : SecretKey) (request : SigningRequest)
    (cache finalCache : QueryCache HashSpec)
    (result : RunResult (Bytes SphincsSubmission.submission.sizes.signature))
    (hmem : (result, finalCache) ∈ support
      ((simulateQ (unifFwdImpl HashSpec +
        (OracleSpec.randomOracle (spec := HashSpec)))
        (liftM (SphincsSubmission.submission.signingOracle secretKey request) :
          OracleComp World (RunResult (Bytes SphincsSubmission.submission.sizes.signature)))).run
        cache)) :
    1 ≤ result.hashCalls := by
  generalize hprogram : SphincsSubmission.submission.signingOracle secretKey request = program at hmem
  rw [QueryImpl.simulateQ_add_liftM_right] at hmem
  have hpoint : ∀ hash : Hash,
      1 ≤ (evalWithAnswerFn hash program).hashCalls := by
    intro hash
    have hfloor := SphincsSignCallFloor.sign_runWith_one_call hash secretKey
      request.cache request.message
    rw [← hprogram]
    change 1 ≤ (SphincsSubmission.submission.runWith hash .sign
      (secretKey, request.cache, request.message)).hashCalls
    exact hfloor
  exact support_transfer program cache (fun result => 1 ≤ result.hashCalls)
    hpoint result finalCache hmem

theorem fixedHash_signingOracle_support_floor
    (secretKey : SecretKey) (request : SigningRequest) (hash : Hash)
    (result : RunResult (Bytes SphincsSubmission.submission.sizes.signature))
    (hmem : result ∈ support
      (simulateQ (unifFwdAnswerImpl hash)
        (liftM (SphincsSubmission.submission.signingOracle secretKey request) :
          OracleComp World (RunResult (Bytes SphincsSubmission.submission.sizes.signature))))) :
    1 ≤ result.hashCalls := by
  generalize hprogram : SphincsSubmission.submission.signingOracle secretKey request = program at hmem
  simp only [unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_right,
    simulateQ_liftTarget] at hmem
  change result ∈ support (pure (evalWithAnswerFn hash program)) at hmem
  simp only [support_pure, Set.mem_singleton_iff] at hmem
  rw [hmem, ← hprogram]
  exact SphincsSignCallFloor.sign_runWith_one_call hash secretKey
    request.cache request.message

theorem fixedHash_support_transfer {α : Type} (program : OracleComp HashSpec α)
    (hash : Hash) (property : α → Prop)
    (hpoint : property (evalWithAnswerFn hash program))
    (result : α)
    (hmem : result ∈ support
      (simulateQ (unifFwdAnswerImpl hash)
        (liftM program : OracleComp World α))) :
    property result := by
  simp only [unifFwdAnswerImpl,
    QueryImpl.simulateQ_add_liftM_right, simulateQ_liftTarget] at hmem
  change result ∈ support (pure (evalWithAnswerFn hash program)) at hmem
  simp only [support_pure, Set.mem_singleton_iff] at hmem
  exact hmem ▸ hpoint

theorem lazyWorld_support_transfer {α : Type} (program : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (property : α → Prop)
    (hpoint : ∀ hash : Hash, property (evalWithAnswerFn hash program))
    (result : α) (finalCache : QueryCache HashSpec)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ (unifFwdImpl HashSpec +
        (OracleSpec.randomOracle (spec := HashSpec)))
        (liftM program : OracleComp World α)).run cache)) :
    property result := by
  rw [QueryImpl.simulateQ_add_liftM_right] at hmem
  exact support_transfer program cache property hpoint result finalCache hmem

private def fixedHashInterpreter (hash : Hash) :
    QueryImpl World ProbComp := unifFwdAnswerImpl hash

theorem fixedHash_interact_calls_ge
    (adversary : Adversary SphincsSubmission.submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) (hash : Hash)
    (rounds : Nat) (state : adversary.State)
    (transcript : Transcript SphincsSubmission.submission.sizes)
    (result : AttackResult)
    (hmem : result ∈ support
      (simulateQ (fixedHashInterpreter hash)
        (SphincsSubmission.submission.interact adversary secretKey pk
          rounds state transcript))) :
    transcript.hashCalls ≤ result.hashCalls := by
  induction rounds generalizing state transcript result with
  | zero =>
      simp [Submission.interact, fixedHashInterpreter] at hmem
      simp [hmem]
  | succ rounds ih =>
      cases haction : adversary.step state with
      | submit candidate =>
          simp [Submission.interact, fixedHashInterpreter, haction] at hmem
          simp only [unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_right,
            simulateQ_liftTarget, liftM] at hmem
          change result ∈ support
            (pure (evalWithAnswerFn hash
              (SphincsSubmission.submission.checkForgery pk transcript candidate))) at hmem
          simp only [support_pure, Set.mem_singleton_iff] at hmem
          rw [hmem]
          exact SphincsInteractionBudget.checkForgery_calls_ge
            SphincsSubmission.submission pk transcript candidate hash
      | hash input resume =>
          simp [Submission.interact, fixedHashInterpreter, haction] at hmem
          obtain ⟨answer, _, hnext⟩ := hmem
          have hge := ih (resume answer)
            { transcript with hashCalls := transcript.hashCalls + 1 } result hnext
          change transcript.hashCalls + 1 ≤ result.hashCalls at hge
          omega
      | sign request resume =>
          simp [Submission.interact, fixedHashInterpreter, haction] at hmem
          by_cases hlife : transcript.signingRequests < LIFETIME
          · simp only [hlife, ↓reduceIte, Set.mem_iUnion] at hmem
            obtain ⟨signResult, _, hnext⟩ := hmem
            have hge := ih (resume signResult.value)
              (transcript.record request.message signResult) result hnext
            have hbase : transcript.hashCalls ≤
                (transcript.record request.message signResult).hashCalls := by
              simp [Transcript.record]
            omega
          · simp only [hlife, ↓reduceIte, Set.mem_singleton_iff] at hmem
            simp [hmem]
      | sample n resume =>
          simp [Submission.interact, fixedHashInterpreter, haction] at hmem
          obtain ⟨answer, _, hnext⟩ := hmem
          exact ih (resume answer) transcript result hnext
      | step next =>
          simp only [Submission.interact, haction] at hmem
          exact ih next transcript result hmem

theorem fixedHash_budget_zero
    (adversary : Adversary SphincsSubmission.submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) (hash : Hash)
    (rounds : Nat) (state : adversary.State)
    (transcript : Transcript SphincsSubmission.submission.sizes)
    (Q : Nat) (hcut : Q < transcript.hashCalls) :
    Pr[fun result => SphincsInteractionCutoff.BudgetWin result Q |
      simulateQ (fixedHashInterpreter hash)
        (SphincsSubmission.submission.interact adversary secretKey pk
          rounds state transcript)] = 0 := by
  apply probEvent_eq_zero
  intro result hmem
  have hge := fixedHash_interact_calls_ge adversary secretKey pk hash
    rounds state transcript result hmem
  intro hw
  exact Nat.not_le_of_gt (lt_of_lt_of_le hcut hge) hw.2

theorem capped_sink_pure
    (adversary : Adversary SphincsSubmission.submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) (Q rounds : Nat)
    (transcript : Transcript SphincsSubmission.submission.sizes) :
    SphincsSubmission.submission.interact
      (SphincsInteractionCutoff.capped adversary Q) secretKey pk
      rounds none transcript = pure ⟨false, transcript.hashCalls⟩ := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => simpa [Submission.interact, SphincsInteractionCutoff.capped] using ih

theorem fixedHash_budget_event_eq
    (adversary : Adversary SphincsSubmission.submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) (hash : Hash)
    (rounds Q : Nat) (state : adversary.State) (count : Nat)
    (transcript : Transcript SphincsSubmission.submission.sizes)
    (hcount : count = transcript.signingRequests)
    (hcharge : count ≤ transcript.hashCalls)
    (hcap : count ≤ Q) :
    Pr[fun result => SphincsInteractionCutoff.BudgetWin result Q |
      simulateQ (fixedHashInterpreter hash)
        (SphincsSubmission.submission.interact adversary secretKey pk
          rounds state transcript)] =
    Pr[fun result => SphincsInteractionCutoff.BudgetWin result Q |
      simulateQ (fixedHashInterpreter hash)
        (SphincsSubmission.submission.interact
          (SphincsInteractionCutoff.capped adversary Q) secretKey pk
          rounds (some (state, count)) transcript)] := by
  induction rounds generalizing state count transcript with
  | zero => simp [Submission.interact]
  | succ rounds ih =>
      cases haction : adversary.step state with
      | submit candidate => simp [Submission.interact, SphincsInteractionCutoff.capped, haction]
      | hash input resume =>
          simp [Submission.interact, SphincsInteractionCutoff.capped, haction,
            fixedHashInterpreter, unifFwdAnswerImpl]
          exact ih (resume (hash input)) count
            { transcript with hashCalls := transcript.hashCalls + 1 }
            hcount (by change count ≤ transcript.hashCalls + 1; omega) hcap
      | sign request resume =>
          generalize hprogram : SphincsSubmission.submission.signingOracle secretKey request = program
          by_cases hq : count < Q
          · simp [Submission.interact, SphincsInteractionCutoff.capped, haction, hq]
            by_cases hlife : transcript.signingRequests < LIFETIME
            · simp only [hlife, ↓reduceIte]
              apply probEvent_bind_congr
              intro signResult hsupp
              have hpoint : 1 ≤ (evalWithAnswerFn hash program).hashCalls := by
                rw [← hprogram]
                change 1 ≤ (SphincsSubmission.submission.runWith hash .sign
                  (secretKey, request.cache, request.message)).hashCalls
                exact SphincsSignCallFloor.sign_runWith_one_call hash secretKey
                  request.cache request.message
              rw [hprogram] at hsupp
              have hfloor := fixedHash_support_transfer program hash
                (fun result => 1 ≤ result.hashCalls) hpoint signResult hsupp
              have hcount' : count + 1 =
                  (transcript.record request.message signResult).signingRequests := by
                simp only [Transcript.record]
                omega
              have hcharge' : count + 1 ≤
                  (transcript.record request.message signResult).hashCalls := by
                change count + 1 ≤ transcript.hashCalls + signResult.hashCalls
                omega
              simpa only [SphincsInteractionCutoff.capped] using
                ih (resume signResult.value) (count + 1)
                  (transcript.record request.message signResult)
                  hcount' hcharge' (by omega)
            · simp [hlife, SphincsInteractionCutoff.BudgetWin]
          · simp [Submission.interact, SphincsInteractionCutoff.capped, haction, hq]
            have hqeq : count = Q := by omega
            change _ = Pr[fun result => SphincsInteractionCutoff.BudgetWin result Q |
              simulateQ (fixedHashInterpreter hash)
                (SphincsSubmission.submission.interact
                  (SphincsInteractionCutoff.capped adversary Q) secretKey pk
                  rounds none transcript)]
            rw [capped_sink_pure adversary secretKey pk Q rounds transcript]
            simp only [simulateQ_pure]
            have hright : Pr[fun result => SphincsInteractionCutoff.BudgetWin result Q |
                (pure ⟨false, transcript.hashCalls⟩ : ProbComp AttackResult)] = 0 := by
              simp [SphincsInteractionCutoff.BudgetWin]
            rw [hright]
            by_cases hlife : transcript.signingRequests < LIFETIME
            · simp only [hlife, ↓reduceIte]
              apply probEvent_eq_zero
              intro result hmem
              simp only [support_bind, Set.mem_iUnion] at hmem
              obtain ⟨signResult, hsupp, hnext⟩ := hmem
              have hpoint : 1 ≤ (evalWithAnswerFn hash program).hashCalls := by
                rw [← hprogram]
                change 1 ≤ (SphincsSubmission.submission.runWith hash .sign
                  (secretKey, request.cache, request.message)).hashCalls
                exact SphincsSignCallFloor.sign_runWith_one_call hash secretKey
                  request.cache request.message
              rw [hprogram] at hsupp
              have hfloor := fixedHash_support_transfer program hash
                (fun result => 1 ≤ result.hashCalls) hpoint signResult hsupp
              have hge := fixedHash_interact_calls_ge adversary secretKey pk hash
                rounds (resume signResult.value)
                (transcript.record request.message signResult) result hnext
              have hcut : Q <
                  (transcript.record request.message signResult).hashCalls := by
                change Q < transcript.hashCalls + signResult.hashCalls
                omega
              intro hw
              exact Nat.not_le_of_gt (lt_of_lt_of_le hcut hge) hw.2
            · simp [hlife]
      | sample n resume =>
          simp [Submission.interact, SphincsInteractionCutoff.capped, haction]
          apply probEvent_bind_congr'
          intro answer
          simpa only [SphincsInteractionCutoff.capped] using
            ih (resume answer) count transcript hcount hcharge hcap
      | step next =>
          simpa [Submission.interact, SphincsInteractionCutoff.capped, haction] using
            ih next count transcript hcount hcharge hcap

/-- Even with a nonempty lazy hash table and fresh private coins, interaction never
decreases the charged hash-call count. -/
theorem lazy_interact_calls_ge
    (adversary : Adversary SphincsSubmission.submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State)
    (transcript : Transcript SphincsSubmission.submission.sizes)
    (cache finalCache : QueryCache HashSpec) (result : AttackResult)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ (unifFwdImpl HashSpec +
        (OracleSpec.randomOracle (spec := HashSpec)))
        (SphincsSubmission.submission.interact adversary secretKey pk
          rounds state transcript)).run cache)) :
    transcript.hashCalls ≤ result.hashCalls := by
  have hprob : Pr[fun pair => transcript.hashCalls ≤ pair.1.hashCalls |
      (simulateQ (unifFwdImpl HashSpec +
        (OracleSpec.randomOracle (spec := HashSpec)))
        (SphincsSubmission.submission.interact adversary secretKey pk
          rounds state transcript)).run cache] = 1 := by
    apply (probEvent_eq_one_simulateQ_unifFwdImpl_add_randomOracle_run_iff
      (SphincsSubmission.submission.interact adversary secretKey pk
        rounds state transcript) cache
      (fun result => transcript.hashCalls ≤ result.hashCalls)).mpr
    intro hash _
    apply probEvent_eq_one_iff.mpr
    refine ⟨probFailure_eq_zero' (by infer_instance), ?_⟩
    intro outcome hout
    exact fixedHash_interact_calls_ge adversary secretKey pk hash
      rounds state transcript outcome hout
  exact (probEvent_eq_one_iff.mp hprob).2 (result, finalCache) hmem

theorem lazy_budget_event_eq
    (adversary : Adversary SphincsSubmission.submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey)
    (rounds Q : Nat) (state : adversary.State) (count : Nat)
    (transcript : Transcript SphincsSubmission.submission.sizes)
    (cache : QueryCache HashSpec)
    (hcount : count = transcript.signingRequests)
    (hcharge : count ≤ transcript.hashCalls)
    (hcap : count ≤ Q) :
    Pr[fun pair => SphincsInteractionCutoff.BudgetWin pair.1 Q |
      (simulateQ (unifFwdImpl HashSpec +
        (OracleSpec.randomOracle (spec := HashSpec)))
        (SphincsSubmission.submission.interact adversary secretKey pk
          rounds state transcript)).run cache] =
    Pr[fun pair => SphincsInteractionCutoff.BudgetWin pair.1 Q |
      (simulateQ (unifFwdImpl HashSpec +
        (OracleSpec.randomOracle (spec := HashSpec)))
        (SphincsSubmission.submission.interact
          (SphincsInteractionCutoff.capped adversary Q) secretKey pk
          rounds (some (state, count)) transcript)).run cache] := by
  induction rounds generalizing state count transcript cache with
  | zero => simp [Submission.interact]
  | succ rounds ih =>
      cases haction : adversary.step state with
      | submit candidate => simp [Submission.interact, SphincsInteractionCutoff.capped, haction]
      | hash input resume =>
          simp [Submission.interact, SphincsInteractionCutoff.capped, haction]
          apply probEvent_bind_congr'
          intro response
          simpa only [SphincsInteractionCutoff.capped] using
            ih (resume response.1) count
              { transcript with hashCalls := transcript.hashCalls + 1 }
              response.2 hcount
              (by change count ≤ transcript.hashCalls + 1; omega) hcap
      | sign request resume =>
          generalize hprogram : SphincsSubmission.submission.signingOracle secretKey request = program
          by_cases hq : count < Q
          · simp [Submission.interact, SphincsInteractionCutoff.capped, haction, hq]
            by_cases hlife : transcript.signingRequests < LIFETIME
            · simp only [hlife, ↓reduceIte, StateT.run_bind]
              apply probEvent_bind_congr
              intro response hsupp
              have hpoint : ∀ hash' : Hash,
                  1 ≤ (evalWithAnswerFn hash' program).hashCalls := by
                intro hash'
                rw [← hprogram]
                change 1 ≤ (SphincsSubmission.submission.runWith hash' .sign
                  (secretKey, request.cache, request.message)).hashCalls
                exact SphincsSignCallFloor.sign_runWith_one_call hash' secretKey
                  request.cache request.message
              rw [hprogram] at hsupp
              have hfloor := lazyWorld_support_transfer program cache
                (fun result => 1 ≤ result.hashCalls) hpoint
                response.1 response.2 hsupp
              have hcount' : count + 1 =
                  (transcript.record request.message response.1).signingRequests := by
                simp only [Transcript.record]
                omega
              have hcharge' : count + 1 ≤
                  (transcript.record request.message response.1).hashCalls := by
                change count + 1 ≤ transcript.hashCalls + response.1.hashCalls
                omega
              simpa only [SphincsInteractionCutoff.capped] using
                ih (resume response.1.value) (count + 1)
                  (transcript.record request.message response.1) response.2
                  hcount' hcharge' (by omega)
            · simp [hlife]
          · simp [Submission.interact, SphincsInteractionCutoff.capped, haction, hq]
            have hqeq : count = Q := by omega
            change _ = Pr[fun pair => SphincsInteractionCutoff.BudgetWin pair.1 Q |
              (simulateQ (unifFwdImpl HashSpec +
                (OracleSpec.randomOracle (spec := HashSpec)))
                (SphincsSubmission.submission.interact
                  (SphincsInteractionCutoff.capped adversary Q) secretKey pk
                  rounds none transcript)).run cache]
            rw [capped_sink_pure adversary secretKey pk Q rounds transcript]
            simp only [simulateQ_pure, StateT.run_pure]
            have hright : Pr[fun pair => SphincsInteractionCutoff.BudgetWin pair.1 Q |
                (pure (⟨false, transcript.hashCalls⟩, cache) :
                  ProbComp (AttackResult × QueryCache HashSpec))] = 0 := by
              simp [SphincsInteractionCutoff.BudgetWin]
            rw [hright]
            by_cases hlife : transcript.signingRequests < LIFETIME
            · simp only [hlife, ↓reduceIte, StateT.run_bind]
              apply probEvent_eq_zero
              intro outcome hmem
              simp only [support_bind, Set.mem_iUnion] at hmem
              obtain ⟨response, hsupp, hnext⟩ := hmem
              have hpoint : ∀ hash' : Hash,
                  1 ≤ (evalWithAnswerFn hash' program).hashCalls := by
                intro hash'
                rw [← hprogram]
                change 1 ≤ (SphincsSubmission.submission.runWith hash' .sign
                  (secretKey, request.cache, request.message)).hashCalls
                exact SphincsSignCallFloor.sign_runWith_one_call hash' secretKey
                  request.cache request.message
              rw [hprogram] at hsupp
              have hfloor := lazyWorld_support_transfer program cache
                (fun result => 1 ≤ result.hashCalls) hpoint
                response.1 response.2 hsupp
              have hge := lazy_interact_calls_ge adversary secretKey pk
                rounds (resume response.1.value)
                (transcript.record request.message response.1)
                response.2 outcome.2 outcome.1 hnext
              have hcut : Q <
                  (transcript.record request.message response.1).hashCalls := by
                change Q < transcript.hashCalls + response.1.hashCalls
                omega
              intro hw
              exact Nat.not_le_of_gt (lt_of_lt_of_le hcut hge) hw.2
            · simp [hlife, SphincsInteractionCutoff.BudgetWin]
      | sample n resume =>
          simp [Submission.interact, SphincsInteractionCutoff.capped, haction]
          apply probEvent_bind_congr'
          intro response
          simpa only [SphincsInteractionCutoff.capped] using
            ih (resume response.1) count transcript response.2
              hcount hcharge hcap
      | step next =>
          simpa [Submission.interact, SphincsInteractionCutoff.capped, haction] using
            ih next count transcript cache hcount hcharge hcap

end SigGolfCandidate.SphincsAdaptiveCutoffDistribution

/-- info: 'SigGolfCandidate.SphincsAdaptiveCutoffDistribution.support_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAdaptiveCutoffDistribution.support_transfer

/-- info: 'SigGolfCandidate.SphincsAdaptiveCutoffDistribution.signingOracle_support_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAdaptiveCutoffDistribution.signingOracle_support_floor

/-- info: 'SigGolfCandidate.SphincsAdaptiveCutoffDistribution.world_signingOracle_support_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAdaptiveCutoffDistribution.world_signingOracle_support_floor

/-- info: 'SigGolfCandidate.SphincsAdaptiveCutoffDistribution.fixedHash_budget_event_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAdaptiveCutoffDistribution.fixedHash_budget_event_eq

/-- info: 'SigGolfCandidate.SphincsAdaptiveCutoffDistribution.lazy_interact_calls_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAdaptiveCutoffDistribution.lazy_interact_calls_ge

/-- info: 'SigGolfCandidate.SphincsAdaptiveCutoffDistribution.lazy_budget_event_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAdaptiveCutoffDistribution.lazy_budget_event_eq
