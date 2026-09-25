import SigGolfCandidate.SphincsExpansionValue
import SigGolf.Security

namespace SigGolfCandidate.Sphincs.ExpansionSecurityBridge
open SigGolf OracleComp

/-- A compact-signature submission to the actual security game does not issue
    any expansion query: the submitted signature itself is the witness. -/
theorem checkForgery_signature (pk : PublicKey)
    (transcript : Transcript SphincsSubmission.submission.sizes)
    (message : Message)
    (signature : Bytes SphincsSubmission.submission.sizes.signature) :
    SphincsSubmission.submission.checkForgery pk transcript
        (.signature message signature) =
      (do
        let verify ← SphincsSubmission.submission.run .verify
          (message, pk, signature)
        pure ⟨verify.value.isSome && transcript.freshSignature message signature,
          transcript.hashCalls + verify.hashCalls⟩) := by
  simp only [Submission.checkForgery]
  rw [ExpansionValue.run_expand_pure]
  simp only [pure_bind]
  rfl

/-- info: 'SigGolfCandidate.Sphincs.ExpansionSecurityBridge.checkForgery_signature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkForgery_signature

end SigGolfCandidate.Sphincs.ExpansionSecurityBridge
