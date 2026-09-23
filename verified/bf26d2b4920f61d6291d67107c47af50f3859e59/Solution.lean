import SigGolfCandidate.Hypertree.Certificate

namespace SigGolf.Challenge

noncomputable def submission : SigGolf.Submission := SigGolfCandidate.Hypertree.submission

theorem signature_bytes : submission.sizes.signature = 113616 := by rfl

theorem witness_bytes : submission.sizes.witness = 113616 := by rfl

theorem certificate : SigGolf.Certificate submission 2870203 :=
  SigGolfCandidate.Hypertree.Candidate.certificate

end SigGolf.Challenge
