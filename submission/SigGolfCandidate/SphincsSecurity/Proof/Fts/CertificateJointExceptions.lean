import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateCacheMonitor
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateGame
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateProposalPrefixException
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation)
set_option backward.isDefEq.respectTransparency false

abbrev CertificateCacheGameResult := RetainedRestResult × (List Index × CertificateCacheMonitorState)

def certificateCacheGameProject (result : CertificateCacheGameResult) : CertificateGameResult :=
  (result.1, result.2.1, certificateCacheMonitorProject result.2.2)

noncomputable def certificateCacheGame (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) : PMF CertificateCacheGameResult := do
  let generated ← (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)
  let key := generated.1.1.2
  (simulateQ (certificateCacheProposalImpl key budget required (stopAfter key))
    (retainedGameRestComputation adversary generated.1.1.1)).run
      ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false)

theorem certificateCacheGame_project (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    certificateCacheGameProject <$> certificateCacheGame adversary budget required stopAfter stopped =
      certificateGame adversary budget required stopAfter stopped := by
  rw [certificateCacheGame, map_bind]
  change ((liftM (boundaryRun 0 scheme.keygen ∅) : PMF _) >>= fun generated =>
    Prod.map id (Prod.map id certificateCacheMonitorProject) <$>
      (simulateQ (certificateCacheProposalImpl generated.1.1.2 budget required (stopAfter generated.1.1.2))
        (retainedGameRestComputation adversary generated.1.1.1)).run
        ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false)) = _
  simp_rw [simulateQ_certificateCacheProposalImpl_project]
  rfl

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false

def CertificateGameExceptional (result : CertificateCacheGameResult) : Prop :=
  result.2.2.2.2 = true ∨
    ProposalPrefixExceptional result.2.2.2.1.proposals result.2.2.2.1.log.length

theorem expected_certificateCacheGame_project (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (weight : CertificateGameResult → ENNReal) :
    (∑' result, Pr[= result | certificateCacheGame adversary budget required stopAfter stopped] *
      weight (certificateCacheGameProject result)) =
        ∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * weight result := by
  have h := congrArg (fun law : PMF CertificateGameResult => ∑' result, Pr[= result | law] * weight result)
    (certificateCacheGame_project adversary budget required stopAfter stopped)
  rw [tsum_probOutput_map_mul] at h
  exact h

end SphincsSecurity.Concrete
