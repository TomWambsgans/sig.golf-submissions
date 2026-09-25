import SigGolfCandidate.SphincsSignCallFloor

/-! Charging signer requests in the organizer's adaptive interaction. -/

namespace SigGolfCandidate.SphincsInteractionBudget
open SigGolf OracleComp OracleSpec

theorem checkForgery_calls_ge (submission : Submission)
    (pk : PublicKey) (transcript : Transcript submission.sizes)
    (candidate : Forgery submission.sizes)
    (hash : QueryImpl HashSpec Id) :
    transcript.hashCalls ≤
      (evalWithAnswerFn hash
        (submission.checkForgery pk transcript candidate)).hashCalls := by
  cases candidate with
  | witness message witness =>
      simp [Submission.checkForgery]
  | signature message signature =>
      cases h : (evalWithAnswerFn hash
        (submission.run .expand (message, pk, signature))).value with
      | none => simp [Submission.checkForgery, evalWithAnswerFn_bind, h]
      | some witness =>
          simp [Submission.checkForgery, evalWithAnswerFn_bind, h]
          omega

private def projectedHash (world : QueryImpl World Id) : Hash :=
  fun q => evalWithAnswerFn world
    (liftM (HashSpec.query q) : OracleComp World (BitVec 256))

private theorem eval_lift_hash {α : Type} (world : QueryImpl World Id)
    (program : OracleComp HashSpec α) :
    evalWithAnswerFn world (liftM program : OracleComp World α) =
      evalWithAnswerFn (projectedHash world) program := by
  apply QueryImpl.simulateQ_liftM_eq_of_query
  intro t
  rfl

theorem interact_calls_ge (submission : Submission)
    (adversary : Adversary submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State)
    (transcript : Transcript submission.sizes)
    (world : QueryImpl World Id) :
    transcript.hashCalls ≤
      (evalWithAnswerFn world
        (submission.interact adversary secretKey pk rounds state transcript)).hashCalls := by
  induction rounds generalizing state transcript with
  | zero => simp [Submission.interact]
  | succ rounds ih =>
      cases h : adversary.step state with
      | submit candidate =>
          simp [Submission.interact, h]
          rw [eval_lift_hash]
          exact checkForgery_calls_ge submission pk transcript candidate
            (projectedHash world)
      | hash input resume =>
          simp [Submission.interact, h]
          apply Nat.le_trans (Nat.le_succ _)
          let answer := evalWithAnswerFn world
            (liftM (HashSpec.query input) : OracleComp World (BitVec 256))
          simpa only [answer] using
            (ih (resume answer)
              { transcript with hashCalls := transcript.hashCalls + 1 })
      | sign request resume =>
          simp [Submission.interact, h]
          split_ifs with hlt
          · simp only [evalWithAnswerFn_bind]
            let result := evalWithAnswerFn world
              (liftM (submission.signingOracle secretKey request) :
                OracleComp World (RunResult (Bytes submission.sizes.signature)))
            have hnext := ih (resume result.value)
              (transcript.record request.message result)
            have hrecord : transcript.hashCalls ≤
                (transcript.record request.message result).hashCalls := by
              simp only [Transcript.record]
              omega
            simpa only [result] using hrecord.trans hnext
          · simp
      | sample n resume =>
          simp [Submission.interact, h]
          exact ih _ transcript
      | step next =>
          simp [Submission.interact, h]
          exact ih next transcript

theorem next_sign_exceeds_budget
    (adversary : Adversary SphincsSubmission.submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey)
    (rounds Q : Nat) (state : adversary.State)
    (transcript : Transcript SphincsSubmission.submission.sizes)
    (world : QueryImpl World Id)
    (request : SigningRequest)
    (resume : Option (Bytes SphincsSubmission.submission.sizes.signature) → adversary.State)
    (haction : adversary.step state = .sign request resume)
    (henabled : transcript.signingRequests < LIFETIME)
    (hspent : Q ≤ transcript.hashCalls) :
    Q + 1 ≤
      (evalWithAnswerFn world
        (SphincsSubmission.submission.interact adversary secretKey pk
          (rounds + 1) state transcript)).hashCalls := by
  simp only [Submission.interact, haction, if_pos henabled,
    evalWithAnswerFn_bind]
  let result := evalWithAnswerFn world
    (liftM (SphincsSubmission.submission.signingOracle secretKey request) :
      OracleComp World (RunResult (Bytes SphincsSubmission.submission.sizes.signature)))
  have hone : 1 ≤ result.hashCalls := by
    change 1 ≤ (evalWithAnswerFn world
      (liftM (SphincsSubmission.submission.signingOracle secretKey request) :
        OracleComp World (RunResult (Bytes SphincsSubmission.submission.sizes.signature)))).hashCalls
    rw [eval_lift_hash]
    exact SphincsSignCallFloor.sign_runWith_one_call
      (projectedHash world) secretKey request.cache request.message
  have hnext := interact_calls_ge SphincsSubmission.submission adversary
    secretKey pk rounds (resume result.value)
      (transcript.record request.message result) world
  change Q + 1 ≤
    (evalWithAnswerFn world
      (SphincsSubmission.submission.interact adversary secretKey pk
        rounds (resume result.value)
        (transcript.record request.message result))).hashCalls
  have hrec : Q + 1 ≤ (transcript.record request.message result).hashCalls := by
    simp only [Transcript.record]
    omega
  exact hrec.trans hnext

end SigGolfCandidate.SphincsInteractionBudget

/-- info: 'SigGolfCandidate.SphincsInteractionBudget.checkForgery_calls_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsInteractionBudget.checkForgery_calls_ge

/-- info: 'SigGolfCandidate.SphincsInteractionBudget.interact_calls_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsInteractionBudget.interact_calls_ge

/-- info: 'SigGolfCandidate.SphincsInteractionBudget.next_sign_exceeds_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsInteractionBudget.next_sign_exceeds_budget
