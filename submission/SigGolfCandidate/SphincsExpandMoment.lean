import SigGolfCandidate.SphincsBeta64Images
import SigGolfCandidate.SphincsExpansion
import VCVio.EvalDist.Expectation

namespace SigGolfCandidate.SphincsExpandMoment
open SigGolf OracleComp OracleSpec OracleComp.EvalDist
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem fixed_hash_of_support {α : Type} (program : OracleComp SigGolf.HashSpec α)
    (value : α) (mem : value ∈ support (withRandomOracle program)) :
    ∃ hash : SigGolf.Hash, evalWithAnswerFn hash program = value := by
  rw [withRandomOracle, StateT.run'_eq] at mem
  obtain ⟨result, hresult, eq⟩ := mem_support_map_peel Prod.fst _ mem
  obtain ⟨hash, _, heval⟩ :=
    (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support program ∅ value).mpr
      ⟨result.2, by simpa only [eq] using hresult⟩
  exact ⟨hash, heval⟩

theorem honest_cost (hash : SigGolf.Hash) (secretKey : SecretKey) (message : Message) :
    (evalWithAnswerFn hash
      (Candidate64.submission.honest secretKey message)).costs .expand = 0 := by
  have zero (pk : PublicKey) (signature : Bytes Candidate64.submission.sizes.signature) :
      (evalWithAnswerFn hash
        (Candidate64.submission.run .expand (message, pk, signature))).hashCompressions = 0 :=
    (SigGolfCandidate.Sphincs.Expansion.run_bound_generic
      Candidate64.submission Candidate64.admissible (by rfl) hash (message, pk, signature)).2.2.2.2
  simp only [Submission.honest, evalWithAnswerFn_bind]
  split <;> simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  · split <;> simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    · split <;> simp [evalWithAnswerFn_pure, recordCost]
      all_goals exact zero _ _
    · simp [recordCost]
  · simp [recordCost]

theorem support_cost (secretKey : SecretKey) (result : HonestResult)
    (mem : result ∈ support (Candidate64.submission.honestWorkload secretKey)) :
    result.costs .expand = 0 := by
  unfold Submission.honestWorkload at mem
  rw [mem_support_bind_iff] at mem
  obtain ⟨message, _, hresult⟩ := mem
  obtain ⟨hash, heval⟩ := fixed_hash_of_support
    (Candidate64.submission.honest secretKey message) result hresult
  rw [← heval]
  exact honest_cost hash secretKey message

theorem compression_bound (secretKey : SecretKey) :
    OracleComp.EvalDist.expectedValue
      (Candidate64.submission.honestWorkload secretKey)
      (fun result => ENNReal.ofReal (Real.rpow 2
        ((result.costs .expand : ℝ) / (Phase.expand.budget : ℝ)))) ≤ 2 := by
  apply expectedValue_le_of_support
  intro result mem
  rw [support_cost secretKey result mem]
  norm_num

theorem runWith_termination (hash : SigGolf.Hash)
    (input : Input Candidate64.submission.sizes .expand) :
    let result := Candidate64.submission.runWith hash .expand input
    result.finished = true ∧ result.cycles < CYCLE_LIMIT := by
  exact SigGolfCandidate.Sphincs.Expansion.expand_terminates_generic
    Candidate64.submission Candidate64.admissible (by rfl) hash input

theorem compressionBounds_of_keygen_sign
    (hkeygen : ∀ secretKey : SecretKey,
      OracleComp.EvalDist.expectedValue
        (Candidate64.submission.honestWorkload secretKey)
        (fun result => ENNReal.ofReal (Real.rpow 2
          ((result.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ)))) ≤ 2)
    (hsign : ∀ secretKey : SecretKey,
      OracleComp.EvalDist.expectedValue
        (Candidate64.submission.honestWorkload secretKey)
        (fun result => ENNReal.ofReal (Real.rpow 2
          ((result.costs .sign : ℝ) / (Phase.sign.budget : ℝ)))) ≤ 2) :
    Candidate64.submission.CompressionBounds := by
  intro secretKey phase hphase
  cases phase with
  | keygen => exact hkeygen secretKey
  | sign => exact hsign secretKey
  | expand => exact compression_bound secretKey
  | verify => simp [Phase.budgeted] at hphase

theorem terminates_of_keygen_sign_verify
    (hkeygen : ∀ hash : SigGolf.Hash,
      ∀ input : Input Candidate64.submission.sizes .keygen,
      let result := Candidate64.submission.runWith hash .keygen input
      result.finished = true ∧ result.cycles < CYCLE_LIMIT)
    (hsign : ∀ hash : SigGolf.Hash,
      ∀ input : Input Candidate64.submission.sizes .sign,
      let result := Candidate64.submission.runWith hash .sign input
      result.finished = true ∧ result.cycles < CYCLE_LIMIT)
    (hverify : ∀ hash : SigGolf.Hash,
      ∀ input : Input Candidate64.submission.sizes .verify,
      let result := Candidate64.submission.runWith hash .verify input
      result.finished = true ∧ result.cycles < CYCLE_LIMIT) :
    Candidate64.submission.Terminates := by
  intro hash phase input
  cases phase with
  | keygen => exact hkeygen hash input
  | sign => exact hsign hash input
  | expand => exact runWith_termination hash input
  | verify => exact hverify hash input

#print axioms runWith_termination
#print axioms compressionBounds_of_keygen_sign
#print axioms terminates_of_keygen_sign_verify

#print axioms compression_bound
end SigGolfCandidate.SphincsExpandMoment
