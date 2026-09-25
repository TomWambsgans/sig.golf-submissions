import SigGolf.Statements

namespace SigGolfCandidate.SphincsAllMessagesBridge
open SigGolf OracleComp
set_option maxRecDepth 4096

private theorem foldlM_allSucceed (hash : Hash)
    (program : Message → OracleComp HashSpec HonestResult)
    (messages : List Message) (initial : HonestSummary) :
    (evalWithAnswerFn hash (messages.foldlM (fun summary message => do
      let result ← program message
      return (⟨summary.allSucceed && result.success,
        fun phase => max (summary.maxCosts phase) (result.costs phase)⟩ : HonestSummary)) initial)).allSucceed =
      (initial.allSucceed &&
        messages.all (fun message =>
          (evalWithAnswerFn hash (program message)).success)) := by
  induction messages generalizing initial with
  | nil => simp
  | cons message messages ih =>
    simp only [List.foldlM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rw [ih]
    simp [Bool.and_assoc]

theorem allMessages_success_iff (submission : Submission)
    (hash : Hash) (secretKey : SecretKey) :
    (evalWithAnswerFn hash (submission.allMessages secretKey)).allSucceed = true ↔
      ∀ message : Message,
        (evalWithAnswerFn hash (submission.honest secretKey message)).success = true := by
  simp only [Submission.allMessages, foldlM_allSucceed]
  simp only [Bool.true_and, List.all_eq_true]
  constructor
  · intro h message
    exact h message (Finset.mem_toList.mpr (Finset.mem_univ message))
  · intro h message _
    exact h message

theorem allMessages_failure_iff (submission : Submission)
    (hash : Hash) (secretKey : SecretKey) :
    (evalWithAnswerFn hash (submission.allMessages secretKey)).allSucceed = false ↔
      ∃ message : Message,
        (evalWithAnswerFn hash (submission.honest secretKey message)).success = false := by
  simpa only [Bool.not_eq_true, not_forall] using
    not_congr (allMessages_success_iff submission hash secretKey)

end SigGolfCandidate.SphincsAllMessagesBridge

/-- info: 'SigGolfCandidate.SphincsAllMessagesBridge.allMessages_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAllMessagesBridge.allMessages_success_iff

/-- info: 'SigGolfCandidate.SphincsAllMessagesBridge.allMessages_failure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAllMessagesBridge.allMessages_failure_iff
