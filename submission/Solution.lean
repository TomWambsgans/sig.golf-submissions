import SigGolfCandidate.SphincsBeta64Images

namespace SigGolf.Challenge

noncomputable def submission : SigGolf.Submission := Candidate64.submission

theorem signature_bytes : submission.sizes.signature = 11324 := by rfl

theorem witness_bytes : submission.sizes.witness = 11324 := by rfl

theorem layout_offsets : submission.layout =
    { message := 0, secretKey := 0x20, publicKey := 0x40,
      cache := 0x60, signature := 0x20060, witness := 0x22ca0 } := by
  decide

theorem admissible : submission.Admissible := Candidate64.admissible

-- The certificate will be added only after all six claims are proved for these images.

end SigGolf.Challenge
