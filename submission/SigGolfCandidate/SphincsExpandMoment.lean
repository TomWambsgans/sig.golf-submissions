import SigGolfCandidate.SphincsKeygenMoment
import SigGolfCandidate.SphincsExpansion

namespace SigGolfCandidate.SphincsExpandMoment
open SigGolf OracleComp OracleSpec OracleComp.EvalDist

set_option maxRecDepth 4096

theorem honest_cost (hash : Hash) (secretKey : SecretKey) (message : Message) :
    (evalWithAnswerFn hash
      (SphincsSubmission.submission.honest secretKey message)).costs .expand = 0 := by
  have zero (pk : PublicKey) (signature : Bytes SphincsSubmission.submission.sizes.signature) :
      (evalWithAnswerFn hash
        (SphincsSubmission.submission.run .expand (message, pk, signature))).hashCompressions = 0 :=
    (Sphincs.Expansion.run_bound hash (message, pk, signature)).2.2.2.2
  simp only [Submission.honest, evalWithAnswerFn_bind]
  split <;> simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  · split <;> simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    · split <;> simp [evalWithAnswerFn_pure, recordCost]
      all_goals exact zero _ _
    · simp [recordCost]
  · simp [recordCost]

theorem support_cost (secretKey : SecretKey) (result : HonestResult)
    (mem : result ∈ support (SphincsSubmission.submission.honestWorkload secretKey)) :
    result.costs .expand = 0 := by
  unfold Submission.honestWorkload at mem
  rw [mem_support_bind_iff] at mem
  obtain ⟨message, _, hresult⟩ := mem
  obtain ⟨hash, heval⟩ := SphincsKeygenMoment.fixed_hash_of_support
    (SphincsSubmission.submission.honest secretKey message) result hresult
  rw [← heval]
  exact honest_cost hash secretKey message

theorem compression_bound (secretKey : SecretKey) :
    OracleComp.EvalDist.expectedValue
      (SphincsSubmission.submission.honestWorkload secretKey)
      (fun result => ENNReal.ofReal (Real.rpow 2
        ((result.costs .expand : ℝ) / (Phase.expand.budget : ℝ)))) ≤ 2 := by
  apply expectedValue_le_of_support
  intro result mem
  rw [support_cost secretKey result mem]
  norm_num

/-- info: 'SigGolfCandidate.SphincsExpandMoment.honest_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_cost
/-- info: 'SigGolfCandidate.SphincsExpandMoment.support_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_cost
/-- info: 'SigGolfCandidate.SphincsExpandMoment.compression_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compression_bound

end SigGolfCandidate.SphincsExpandMoment
