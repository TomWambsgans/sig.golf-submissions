import SigGolfCandidate.SphincsInteractionBudget

/-! A request-count cutoff for the organizer's adaptive attacker. -/

namespace SigGolfCandidate.SphincsInteractionCutoff
open SigGolf OracleComp OracleSpec

def capped (adversary : Adversary SphincsSubmission.submission.sizes)
    (Q : Nat) : Adversary SphincsSubmission.submission.sizes where
  State := Option (adversary.State × Nat)
  initial pk cache := some (adversary.initial pk cache, 0)
  step
    | none => .step none
    | some (state, count) =>
        match adversary.step state with
        | .submit candidate => .submit candidate
        | .hash input resume => .hash input (fun answer => some (resume answer, count))
        | .sign request resume =>
            if count < Q then
              .sign request (fun response => some (resume response, count + 1))
            else .step none
        | .sample n resume => .sample n (fun answer => some (resume answer, count))
        | .step next => .step (some (next, count))

theorem sink_false
    (adversary : Adversary SphincsSubmission.submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey) (Q rounds : Nat)
    (transcript : Transcript SphincsSubmission.submission.sizes)
    (world : QueryImpl World Id) :
    (evalWithAnswerFn world
      (SphincsSubmission.submission.interact (capped adversary Q)
        secretKey pk rounds none transcript)).won = false := by
  induction rounds with
  | zero => simp [Submission.interact]
  | succ rounds ih =>
      simpa [Submission.interact, capped] using ih

def BudgetWin (result : AttackResult) (Q : Nat) : Prop :=
  result.won = true ∧ result.hashCalls ≤ Q

theorem budget_event_eq
    (adversary : Adversary SphincsSubmission.submission.sizes)
    (secretKey : SecretKey) (pk : PublicKey)
    (rounds Q : Nat) (state : adversary.State) (count : Nat)
    (transcript : Transcript SphincsSubmission.submission.sizes)
    (world : QueryImpl World Id)
    (hcount : count = transcript.signingRequests)
    (hcharge : count ≤ transcript.hashCalls)
    (hcap : count ≤ Q) :
    BudgetWin (evalWithAnswerFn world
      (SphincsSubmission.submission.interact adversary secretKey pk
        rounds state transcript)) Q ↔
    BudgetWin (evalWithAnswerFn world
      (SphincsSubmission.submission.interact (capped adversary Q)
        secretKey pk rounds (some (state, count)) transcript)) Q := by
  induction rounds generalizing state count transcript with
  | zero => simp [Submission.interact, BudgetWin]
  | succ rounds ih =>
      cases haction : adversary.step state with
      | submit candidate =>
          simp [Submission.interact, capped, haction]
      | hash input resume =>
          simp [Submission.interact, capped, haction]
          apply ih _ count { transcript with hashCalls := transcript.hashCalls + 1 }
          · exact hcount
          · change count ≤ transcript.hashCalls + 1
            omega
          · exact hcap
      | sign request resume =>
          by_cases hq : count < Q
          · simp [Submission.interact, capped, haction, hq]
            by_cases hlife : transcript.signingRequests < LIFETIME
            · simp [hlife]
              let result := evalWithAnswerFn world
                (liftM (SphincsSubmission.submission.signingOracle secretKey request) :
                  OracleComp World (RunResult (Bytes SphincsSubmission.submission.sizes.signature)))
              apply ih (resume result.value) (count + 1)
                (transcript.record request.message result)
              · simp only [Transcript.record]
                omega
              · have hfloor := SphincsSignCallFloor.record_preserves_request_charge
                  (SphincsInteractionBudget.projectedHash world) secretKey request transcript
                  (by omega)
                -- The fixed World interpreter routes the signer's HASH queries to its projection.
                have hroute : result =
                    SphincsSubmission.submission.runWith
                      (SphincsInteractionBudget.projectedHash world) .sign
                      (secretKey, request.cache, request.message) := by
                  change evalWithAnswerFn world
                    (liftM (SphincsSubmission.submission.signingOracle secretKey request) :
                      OracleComp World (RunResult (Bytes SphincsSubmission.submission.sizes.signature))) = _
                  rw [SphincsInteractionBudget.eval_lift_hash]
                  rfl
                simp only [Transcript.record] at hfloor ⊢
                rw [hroute]
                omega
              · omega
            · simp [hlife, BudgetWin]
          · have hqeq : count = Q := by omega
            simp [Submission.interact, capped, haction, hq]
            have hblocked := sink_false adversary secretKey pk Q rounds transcript world
            by_cases hlife : transcript.signingRequests < LIFETIME
            · have hover := SphincsInteractionBudget.next_sign_exceeds_budget
                adversary secretKey pk rounds Q state transcript world
                  request resume haction hlife (by omega)
              constructor
              · intro hw
                have hreal : Q < (evalWithAnswerFn world
                    (if transcript.signingRequests < LIFETIME then do
                      let result ← liftM
                        (SphincsSubmission.submission.signingOracle secretKey request)
                      SphincsSubmission.submission.interact adversary secretKey pk
                        rounds (resume result.value)
                        (transcript.record request.message result)
                    else pure ⟨false, transcript.hashCalls⟩)).hashCalls := by
                  have hstep : Q + 1 ≤ (evalWithAnswerFn world
                      (if transcript.signingRequests < LIFETIME then do
                        let result ← liftM
                          (SphincsSubmission.submission.signingOracle secretKey request)
                        SphincsSubmission.submission.interact adversary secretKey pk
                          rounds (resume result.value)
                          (transcript.record request.message result)
                      else pure ⟨false, transcript.hashCalls⟩)).hashCalls := by
                    simpa only [Submission.interact, haction] using hover
                  omega
                exact False.elim ((Nat.not_le_of_gt hreal) hw.2)
              · intro hw
                have hfalse : false = true := by
                  exact hblocked.symm.trans hw.1
                exact False.elim (Bool.false_ne_true hfalse)
            · simp [hlife, BudgetWin]
              intro hwon
              exact False.elim (Bool.false_ne_true (hblocked.symm.trans hwon))
      | sample n resume =>
          simp [Submission.interact, capped, haction]
          exact ih _ count transcript hcount hcharge hcap
      | step next =>
          simp [Submission.interact, capped, haction]
          exact ih next count transcript hcount hcharge hcap

end SigGolfCandidate.SphincsInteractionCutoff

/-- info: 'SigGolfCandidate.SphincsInteractionCutoff.sink_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsInteractionCutoff.sink_false

/-- info: 'SigGolfCandidate.SphincsInteractionCutoff.budget_event_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsInteractionCutoff.budget_event_eq
