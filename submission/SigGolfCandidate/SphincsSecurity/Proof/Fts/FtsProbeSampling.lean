import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeLoop
import SigGolfCandidate.SphincsSecurity.Proof.Reference.SigningTrace
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Secrets
import SigGolfCandidate.SphincsSecurity.Proof.Reference.FixedQueryBound
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FtsProbeProbability
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FtsProbeOrigin
/-!
# Sources of previously cached selected digests

If a selected signer digest was already cached when that signer began, the full adversary trace
locates the earlier interval that first inserted it. Key generation is not a possible source.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem sequenceFin_some {alpha : Type} {count : Nat}
    (values : Fin count → alpha) :
    sequenceFin (m := Option) (fun position => some (values position)) = some values := by
  induction count with
  | zero =>
      rw [sequenceFin]
      congr
      funext position
      exact Fin.elim0 position
  | succ count ih =>
      rw [sequenceFin, ih]
      change some (Fin.cases (values 0) (fun position => values position.succ)) = some values
      rw [Option.some.injEq]
      funext position
      cases position using Fin.cases <;> rfl

end SphincsSecurity.Concrete

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace Concrete.FtsProbeSimulation

attribute [local semireducible] sampleFtsSecrets

abbrev RetainedRestResult := (Forgery × QueryLog SigningSpec) × Bool

noncomputable def retainedGameRestComputation (adversary : Adversary)
    (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) RetainedRestResult := do
  let (forgery, log) ← signingTraceComputation (adversary.main publicKey)
  let verified ← liftOracleWorldLeft
    (scheme.verify publicKey forgery.message forgery.signature)
  pure ((forgery, log), verified)

theorem retainedGameRestComputation_verdict_projection
    (adversary : Adversary) (publicKey : PublicKey) :
    (fun result : RetainedRestResult =>
      decide (SigningTranscript.Valid result.1.2 ∧
        ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2) <$>
        retainedGameRestComputation adversary publicKey =
      tracedGameRestComputation adversary publicKey := by
  simp [retainedGameRestComputation, tracedGameRestComputation]

theorem simulateQ_expanded_retainedGameRestComputation_fixedHashQueryBound
    (oracle : QueryImpl HashSpec Id) (adversary : Adversary) (secretKey : SecretKey) (q : Nat)
    (hbound : FixedHashQueryBound oracle (gameRest scheme adversary
      ⟨secretKey.root, secretKey.parameter⟩ secretKey) q) :
    FixedHashQueryBound oracle (simulateQ (expandedAdversaryImpl secretKey)
      (retainedGameRestComputation adversary
        ⟨secretKey.root, secretKey.parameter⟩)) q := by
  let verdict := fun result : RetainedRestResult =>
        decide (SigningTranscript.Valid result.1.2 ∧
          ¬SigningTranscript.Contains result.1.2 result.1.1) && result.2
  have heq : verdict <$>
        simulateQ (expandedAdversaryImpl secretKey)
          (retainedGameRestComputation adversary
            ⟨secretKey.root, secretKey.parameter⟩) =
      simulateQ (expandedAdversaryImpl secretKey)
        (tracedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩) := by
            rw [← retainedGameRestComputation_verdict_projection]
            simp [verdict]
  have hmap : FixedHashQueryBound oracle (verdict <$>
      simulateQ (expandedAdversaryImpl secretKey)
        (retainedGameRestComputation adversary
          ⟨secretKey.root, secretKey.parameter⟩)) q := by
    rw [heq, simulateQ_expanded_tracedGameRestComputation adversary secretKey]
    exact hbound
  exact (fixedHashQueryBound_map_iff oracle _ verdict q).mp hmap

end Concrete.FtsProbeSimulation

end SphincsSecurity
