import SigGolfCandidate.SphincsExpandMoment

namespace SigGolf.Challenge

noncomputable def submission : SigGolf.Submission := Candidate64.submission

theorem signature_bytes : submission.sizes.signature = 11324 := by rfl

theorem witness_bytes : submission.sizes.witness = 11324 := by rfl

theorem layout_offsets : submission.layout =
    { message := 0, secretKey := 0x20, publicKey := 0x40,
      cache := 0x60, signature := 0x20060, witness := 0x22ca0 } := by
  decide

theorem admissible : submission.Admissible := Candidate64.admissible

theorem expand_terminates (hash : SigGolf.Hash)
    (input : SigGolf.Input submission.sizes .expand) :
    let result := submission.runWith hash .expand input
    result.finished = true ∧ result.cycles < SigGolf.CYCLE_LIMIT := by
  exact SigGolfCandidate.SphincsExpandMoment.runWith_termination hash input

theorem expand_compression_bound (secretKey : SigGolf.SecretKey) :
    OracleComp.EvalDist.expectedValue
      (submission.honestWorkload secretKey)
      (fun result => ENNReal.ofReal (Real.rpow 2
        ((result.costs .expand : ℝ) / (SigGolf.Phase.expand.budget : ℝ)))) ≤ 2 := by
  exact SigGolfCandidate.SphincsExpandMoment.compression_bound secretKey

-- The certificate will be added only after all six claims are proved for these images.

end SigGolf.Challenge
