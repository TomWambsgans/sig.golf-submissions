import SigGolfCandidate.SphincsMaskedKeygenPadding
import SigGolfCandidate.SphincsSubmission

namespace SigGolfCandidate.SphincsKeygenCost
open SigGolf OracleComp

set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem runWith_cost (hash : Hash) (secretKey : SecretKey) :
    (SphincsSubmission.submission.runWith hash .keygen secretKey).hashCompressions =
      1007616 := by
  obtain ⟨cache, hrun, _, _⟩ :=
    SphincsMaskedKeygenPadding.keygen_runWith_canonical
      SphincsSubmission.submission hash secretKey rfl
      (SphincsSubmission.admissible.2 .keygen) rfl rfl rfl
  rw [hrun]


theorem honest_cost (hash : Hash) (secretKey : SecretKey)
    (message : Message) :
    (evalWithAnswerFn hash
      (SphincsSubmission.submission.honest secretKey message)).costs .keygen =
      1007616 := by
  obtain ⟨cache, hrun, _, _⟩ :=
    SphincsMaskedKeygenPadding.keygen_runWith_canonical
      SphincsSubmission.submission hash secretKey rfl
      (SphincsSubmission.admissible.2 .keygen) rfl rfl rfl
  unfold Submission.runWith at hrun
  simp [Submission.honest, evalWithAnswerFn_bind, hrun,
    evalWithAnswerFn_pure, recordCost]
  split <;> simp [evalWithAnswerFn_bind, evalWithAnswerFn_pure, recordCost]
  split <;> simp [evalWithAnswerFn_bind, evalWithAnswerFn_pure, recordCost]

/-- info: 'SigGolfCandidate.SphincsKeygenCost.runWith_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runWith_cost

/-- info: 'SigGolfCandidate.SphincsKeygenCost.honest_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_cost

end SigGolfCandidate.SphincsKeygenCost
