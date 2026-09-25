import SigGolfCandidate.SphincsCacheMacFreshness
import SigGolfCandidate.SphincsCacheMacFiniteTrace

/-! Apply the generic finite pre-sampling/trace lemmas to actual tag-15
altered-cache MAC inputs in the seeded SPHINCS construction. -/

namespace SigGolfCandidate.SphincsCacheMacTargetPackage
open OracleComp OracleSpec SphincsSecurity SphincsSecurity.Seeded
open SigGolfCandidate.SphincsCacheSecretDomains
open SigGolfCandidate.SphincsMaskedCacheProgramming
open SigGolfCandidate.SphincsCacheMacFreshness
open SigGolfCandidate.SphincsCacheMacFinitePresampling
open SigGolfCandidate.SphincsCacheMacFiniteTrace
open SigGolfCandidate.SphincsCacheMacFirstHit
open SigGolfCandidate.SphincsCacheMacTraceIndependence

def targets {n : Nat} (material : KeyMaterial) (seed : MasterSeed)
    (candidateBytes : Fin n → HashInput) : Fin n → HashInput :=
  fun i => macInput material.1 seed (candidateBytes i)

theorem targets_injective {n : Nat} (material : KeyMaterial)
    (seed : MasterSeed) (candidateBytes : Fin n → HashInput)
    (hinj : Function.Injective candidateBytes) :
    Function.Injective (targets material seed candidateBytes) :=
  (macInput_injective_ciphertext material.1 seed).comp hinj

theorem targets_fresh {n : Nat} (material : KeyMaterial)
    (seed : MasterSeed) (pads : List (BitVec 32 × HashOutput))
    (canonicalBytes : HashInput) (macAnswer : HashOutput)
    (candidateBytes : Fin n → HashInput)
    (hchanged : ∀ i, candidateBytes i ≠ canonicalBytes) :
    ∀ i, maskedMaterialCache material seed pads canonicalBytes macAnswer
      (targets material seed candidateBytes i) = none := by
  intro i
  exact maskedMaterialCache_altered_fresh seed material pads
    canonicalBytes (candidateBytes i) macAnswer (hchanged i)

theorem presample_altered_targets {α : Type} {n : Nat}
    (material : KeyMaterial) (seed : MasterSeed)
    (pads : List (BitVec 32 × HashOutput))
    (canonicalBytes : HashInput) (macAnswer : HashOutput)
    (candidateBytes : Fin n → HashInput)
    (hinj : Function.Injective candidateBytes)
    (hchanged : ∀ i, candidateBytes i ≠ canonicalBytes)
    (computation : OracleComp OracleWorld α) :
    evalSPMF ((simulateQ romImpl computation).run'
      (maskedMaterialCache material seed pads canonicalBytes macAnswer)) =
    evalSPMF (do
      let outputs ← Concrete.sequenceFin fun _ : Fin n =>
        ($ᵗ HashOutput : ProbComp HashOutput)
      (simulateQ romImpl computation).run'
        (cacheFin (maskedMaterialCache material seed pads canonicalBytes macAnswer)
          (targets material seed candidateBytes) outputs)) :=
  presampleFin computation _ (targets material seed candidateBytes)
    (targets_injective material seed candidateBytes hinj)
    (targets_fresh material seed pads canonicalBytes macAnswer candidateBytes hchanged)

theorem allFailureTrace_altered_targets_congr {α : Type} {n : Nat}
    (material : KeyMaterial) (seed : MasterSeed)
    (pads : List (BitVec 32 × HashOutput))
    (canonicalBytes : HashInput) (macAnswer : HashOutput)
    (candidateBytes : Fin n → HashInput)
    (outputs : Fin n → HashOutput)
    (coins : QueryImpl unifSpec Id)
    (fallback : QueryImpl HashSpec Id)
    (computation : OracleComp (OracleWorld + MacTestSpec) α)
    (hpath : GoodPath
      (coins + completedHash
        (maskedMaterialCache material seed pads canonicalBytes macAnswer) fallback)
      (seedSafe seed) computation) :
    allFailureTrace
        (coins + completedHash
          (maskedMaterialCache material seed pads canonicalBytes macAnswer) fallback)
        computation =
      allFailureTrace
        (coins + completedHash
          (cacheFin (maskedMaterialCache material seed pads canonicalBytes macAnswer)
            (targets material seed candidateBytes) outputs) fallback)
        computation := by
  exact allFailureTrace_presampled_congr seed coins fallback _
    (targets material seed candidateBytes) outputs
    (fun i => macInput_seedHit material.1 seed (candidateBytes i))
    computation hpath

end SigGolfCandidate.SphincsCacheMacTargetPackage

/-- info: 'SigGolfCandidate.SphincsCacheMacTargetPackage.presample_altered_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTargetPackage.presample_altered_targets
