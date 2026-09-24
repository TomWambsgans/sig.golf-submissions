import SigGolfCandidate.SphincsSubmission

namespace SigGolf.Challenge

noncomputable def submission : SigGolf.Submission :=
  SigGolfCandidate.SphincsSubmission.submission

theorem signature_bytes : submission.sizes.signature = 11324 := by
  simpa [submission, SigGolfCandidate.SphincsSubmission.submission,
    SigGolfCandidate.SphincsSubmission.sizes] using
    SigGolfCandidate.SphincsWire.signatureBytes_eq

theorem witness_bytes : submission.sizes.witness = 11324 := by
  simpa [submission, SigGolfCandidate.SphincsSubmission.submission,
    SigGolfCandidate.SphincsSubmission.sizes] using
    SigGolfCandidate.SphincsWire.signatureBytes_eq

theorem layout_offsets : submission.layout =
    { message := 0, secretKey := 0x20, publicKey := 0x40,
      cache := 0x60, signature := 0x20060, witness := 0x22ca0 } := by
  simp [submission, SigGolfCandidate.SphincsSubmission.submission,
    SigGolfCandidate.SphincsSubmission.layout,
    SigGolfCandidate.SphincsSubmission.sizes,
    SigGolf.Riscv.standardLayout, SigGolf.Riscv.witnessBase,
    SigGolf.Riscv.signatureBase,
    SigGolfCandidate.SphincsWire.signatureBytes_eq]

-- The candidate is still being proved. The `certificate` theorem will be
-- added only when it establishes all claims for these exact four images.

end SigGolf.Challenge
