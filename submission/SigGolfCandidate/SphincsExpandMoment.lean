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

theorem runWith_termination (hash : Hash)
    (input : Input SphincsSubmission.submission.sizes .expand) :
    let result := SphincsSubmission.submission.runWith hash .expand input
    result.finished = true ∧ result.cycles < CYCLE_LIMIT := by
  have h := Sphincs.Expansion.run_bound hash input
  dsimp at h ⊢
  refine ⟨h.1, ?_⟩
  rw [h.2.2.1]
  decide

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

/-- The two completed program analyses discharge their universal termination cases. -/
theorem keygen_expand_terminate (hash : Hash) (phase : Phase)
    (hphase : phase = .keygen ∨ phase = .expand)
    (input : Input SphincsSubmission.submission.sizes phase) :
    let result := SphincsSubmission.submission.runWith hash phase input
    result.finished = true ∧ result.cycles < CYCLE_LIMIT := by
  rcases hphase with rfl | rfl
  · exact SphincsKeygenCost.runWith_termination hash input
  · exact runWith_termination hash input

/-- The two completed compression-budget cases can be reused in the final certificate. -/
theorem keygen_expand_compression_bound (secretKey : SecretKey) (phase : Phase)
    (hphase : phase = .keygen ∨ phase = .expand) :
    OracleComp.EvalDist.expectedValue
      (SphincsSubmission.submission.honestWorkload secretKey)
      (fun result => ENNReal.ofReal (Real.rpow 2
        ((result.costs phase : ℝ) / (phase.budget : ℝ)))) ≤ 2 := by
  rcases hphase with rfl | rfl
  · exact SphincsKeygenMoment.compression_bound secretKey
  · exact compression_bound secretKey

/-- Only the signer budget remains once its workload moment is established. -/
theorem compressionBounds_of_sign
    (hsign : ∀ secretKey : SecretKey,
      OracleComp.EvalDist.expectedValue
        (SphincsSubmission.submission.honestWorkload secretKey)
        (fun result => ENNReal.ofReal (Real.rpow 2
          ((result.costs .sign : ℝ) / (Phase.sign.budget : ℝ)))) ≤ 2) :
    SphincsSubmission.submission.CompressionBounds := by
  intro secretKey phase hphase
  cases phase with
  | keygen => exact SphincsKeygenMoment.compression_bound secretKey
  | sign => exact hsign secretKey
  | expand => exact compression_bound secretKey
  | verify => simp [Phase.budgeted] at hphase

/-- Only signer and verifier control remain for universal termination. -/
theorem terminates_of_sign_verify
    (hsign : ∀ hash : Hash,
      ∀ input : Input SphincsSubmission.submission.sizes .sign,
      let result := SphincsSubmission.submission.runWith hash .sign input
      result.finished = true ∧ result.cycles < CYCLE_LIMIT)
    (hverify : ∀ hash : Hash,
      ∀ input : Input SphincsSubmission.submission.sizes .verify,
      let result := SphincsSubmission.submission.runWith hash .verify input
      result.finished = true ∧ result.cycles < CYCLE_LIMIT) :
    SphincsSubmission.submission.Terminates := by
  intro hash phase input
  cases phase with
  | keygen => exact SphincsKeygenCost.runWith_termination hash input
  | sign => exact hsign hash input
  | expand => exact runWith_termination hash input
  | verify => exact hverify hash input

/-- info: 'SigGolfCandidate.SphincsExpandMoment.honest_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_cost
/-- info: 'SigGolfCandidate.SphincsExpandMoment.runWith_termination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runWith_termination
/-- info: 'SigGolfCandidate.SphincsExpandMoment.support_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_cost
/-- info: 'SigGolfCandidate.SphincsExpandMoment.compression_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compression_bound

/-- info: 'SigGolfCandidate.SphincsExpandMoment.keygen_expand_terminate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygen_expand_terminate

/-- info: 'SigGolfCandidate.SphincsExpandMoment.keygen_expand_compression_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygen_expand_compression_bound

/-- info: 'SigGolfCandidate.SphincsExpandMoment.compressionBounds_of_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compressionBounds_of_sign

/-- info: 'SigGolfCandidate.SphincsExpandMoment.terminates_of_sign_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminates_of_sign_verify

end SigGolfCandidate.SphincsExpandMoment
