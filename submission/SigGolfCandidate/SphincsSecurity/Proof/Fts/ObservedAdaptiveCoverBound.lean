import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeUniform
import SigGolfCandidate.SphincsSecurity.Proof.Fts.JointProbeMessageAnswers

/-! ## ObservedCoverPattern -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def observedSigningView? (answers : HashInput → Option HashOutput) (root : Digest) (entry : SigningEntry) : Option FewTimeView := do
  let signature ← entry.2
  let answer ← answers (messageDigestPayload root entry.1 signature.randomness)
  pure (hashOutputFewTimeView answer)

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def eligibleSigningView? (answers : HashInput → Option HashOutput) (root : Digest)
    (targetPayload : HashInput) (entry : SigningEntry) : Option FewTimeView := do
  let signature ← entry.2
  if messageDigestPayload root entry.1 signature.randomness = targetPayload then none
  else observedSigningView? answers root entry

noncomputable def eligibleSigningViews (answers : HashInput → Option HashOutput) (root : Digest)
    (targetPayload : HashInput) (log : QueryLog SigningSpec) : Fin log.length → Option FewTimeView :=
  fun slot => eligibleSigningView? answers root targetPayload (log.get slot)

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def fixedSigningViews (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (root : Digest) (log : QueryLog SigningSpec) (input : HashInput) : Fin log.length → Option FewTimeView :=
  eligibleSigningViews (messageAnswers parameter cache) root (payloadOf input) log

def SigningDigestsCached (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (root : Digest) (log : QueryLog SigningSpec) : Prop :=
  ∀ entry ∈ log, ∀ signature, entry.2 = some signature →
    messageAnswers parameter cache (messageDigestPayload root entry.1 signature.randomness) ≠ none

end SphincsSecurity.Concrete
