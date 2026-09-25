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

theorem runWith_termination (hash : Hash) (secretKey : SecretKey) :
    let result := SphincsSubmission.submission.runWith hash .keygen secretKey
    result.finished = true ∧ result.cycles < CYCLE_LIMIT := by
  obtain ⟨cache, hrun, _, _⟩ :=
    SphincsMaskedKeygenPadding.keygen_runWith_canonical
      SphincsSubmission.submission hash secretKey rfl
      (SphincsSubmission.admissible.2 .keygen) rfl rfl rfl
  rw [hrun]
  change true = true ∧ 92369576 < CYCLE_LIMIT
  constructor
  · rfl
  · decide


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


theorem exponential_cost_le_two :
    ENNReal.ofReal (Real.rpow 2 ((1007616 : ℝ) / (BUDGET_KEYGEN : ℝ))) ≤ 2 := by
  have hreal : Real.rpow 2 ((1007616 : ℝ) / (BUDGET_KEYGEN : ℝ)) ≤ (2 : ℝ) := by
    calc
      _ ≤ Real.rpow 2 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [BUDGET_KEYGEN])
      _ = 2 := by norm_num
  exact (ENNReal.ofReal_le_ofReal hreal).trans (by norm_num)

/-- info: 'SigGolfCandidate.SphincsKeygenCost.runWith_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runWith_cost

/-- info: 'SigGolfCandidate.SphincsKeygenCost.runWith_termination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runWith_termination

/-- info: 'SigGolfCandidate.SphincsKeygenCost.honest_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_cost

/-- info: 'SigGolfCandidate.SphincsKeygenCost.exponential_cost_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exponential_cost_le_two

end SigGolfCandidate.SphincsKeygenCost
