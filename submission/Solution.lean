import SigGolf
import SigGolfCandidate.Final.Main

/-!
# sig.golf solution (template)

`S = W = 7756`, `C = 18388`. Layout (bytes): message 64, secret key 128, public key 160,
cache 17568, signature 9808, witness 2048.

The certificate is `SigGolfCandidate.Final.certificate_of`, which takes the bundle
`SigGolfCandidate.Final.Pending` of the component statements still being proved (see
`SigGolfCandidate/Final/Pending.lean`). The final step, once those theorems exist, is to replace
`certificate_of_pending` below by

```lean
theorem certificate : SigGolf.Certificate submission 18388 :=
  SigGolfCandidate.Final.certificate_of
    { signRefinement := <SignRefinementStatement proof>
      signTermination := <SignTerminationStatement proof>
      verifyRefinement := <VerifyRefinementStatement proof>
      verifyTermination := <VerifyTerminationStatement proof>
      verifyCycles := <VerifyCyclesStatement proof>
      eventSecurity := <EventSecurityStatement proof> }
```
-/

namespace SigGolf.Challenge

noncomputable def submission : SigGolf.Submission := SigGolfCandidate.submission

theorem signature_bytes : submission.sizes.signature = 7756 := rfl

theorem witness_bytes : submission.sizes.witness = 7756 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 17568, signature := 9808, witness := 2048 } := rfl

/-- The certificate, from the pending component statements. PLACEHOLDER: becomes
`theorem certificate : SigGolf.Certificate submission 18388` once `Pending` is proved. -/
theorem certificate_of_pending (P : SigGolfCandidate.Final.Pending) :
    SigGolf.Certificate submission 18388 :=
  SigGolfCandidate.Final.certificate_of P

end SigGolf.Challenge
