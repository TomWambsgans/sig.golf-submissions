import SigGolfCandidate.SphincsCacheMacTargetPackage
import SigGolfCandidate.SphincsCacheMacFiniteTrace
import Mathlib.Data.List.Dedup

/-! Enumerate the distinct MAC inputs mentioned by an all-failure comparison
trace. This enumeration is chosen before the hidden answers are programmed. -/

namespace SigGolfCandidate.SphincsCacheMacTraceTargets
open SphincsSecurity
open SphincsSecurity.Seeded
open SigGolfCandidate.SphincsCacheSecretDomains
open SigGolfCandidate.SphincsMaskedCacheProgramming
open SigGolfCandidate.SphincsCacheMacFreshness
open SigGolfCandidate.SphincsCacheMacFinitePresampling
open SigGolfCandidate.SphincsCacheMacFiniteTrace
open SigGolfCandidate.SphincsCacheMacFirstHit
open SigGolfCandidate.SphincsCacheMacTraceIndependence

def distinctKeys (attempts : List (HashInput × Digest)) : List HashInput :=
  (attempts.map Prod.fst).dedup

def keys (attempts : List (HashInput × Digest)) :
    Fin (distinctKeys attempts).length → HashInput :=
  (distinctKeys attempts).get

theorem keys_injective (attempts : List (HashInput × Digest)) :
    Function.Injective (keys attempts) := by
  exact (List.nodup_dedup _).injective_get

theorem key_of_attempt (attempts : List (HashInput × Digest))
    (attempt : HashInput × Digest) (hmem : attempt ∈ attempts) :
    ∃ i, keys attempts i = attempt.1 := by
  apply List.mem_iff_get.mp
  exact List.mem_dedup.mpr (List.mem_map.mpr ⟨attempt, hmem, rfl⟩)

theorem each_key_from_attempt (attempts : List (HashInput × Digest))
    (i : Fin (distinctKeys attempts).length) :
    ∃ attempt ∈ attempts, attempt.1 = keys attempts i := by
  have hmem : keys attempts i ∈ distinctKeys attempts := List.get_mem _ i
  obtain ⟨attempt, hmem, heq⟩ :=
    List.mem_map.mp (List.mem_dedup.mp hmem)
  exact ⟨attempt, hmem, heq⟩

theorem keys_are_seed_bearing
    (attempts : List (HashInput × Digest))
    (parameter : PublicParameter) (seed : MasterSeed)
    (hformat : ∀ attempt ∈ attempts,
      ∃ candidateBytes, attempt.1 = macInput parameter seed candidateBytes)
    (i : Fin (distinctKeys attempts).length) :
    SeedHit (keys attempts i) seed := by
  obtain ⟨attempt, hmem, heq⟩ := each_key_from_attempt attempts i
  obtain ⟨candidateBytes, hinput⟩ := hformat attempt hmem
  rw [← heq, hinput]
  exact macInput_seedHit parameter seed candidateBytes

theorem keys_are_fresh
    (attempts : List (HashInput × Digest))
    (material : KeyMaterial) (seed : MasterSeed)
    (pads : List (BitVec 32 × HashOutput))
    (canonicalBytes : HashInput) (macAnswer : HashOutput)
    (hformat : ∀ attempt ∈ attempts,
      ∃ candidateBytes, candidateBytes ≠ canonicalBytes ∧
        attempt.1 = macInput material.1 seed candidateBytes)
    (i : Fin (distinctKeys attempts).length) :
    maskedMaterialCache material seed pads canonicalBytes macAnswer
      (keys attempts i) = none := by
  obtain ⟨attempt, hmem, heq⟩ := each_key_from_attempt attempts i
  obtain ⟨candidateBytes, hchanged, hinput⟩ := hformat attempt hmem
  rw [← heq, hinput]
  exact maskedMaterialCache_altered_fresh seed material pads
    canonicalBytes candidateBytes macAnswer hchanged

theorem presample_trace_keys {α : Type}
    (attempts : List (HashInput × Digest))
    (material : KeyMaterial) (seed : MasterSeed)
    (pads : List (BitVec 32 × HashOutput))
    (canonicalBytes : HashInput) (macAnswer : HashOutput)
    (hformat : ∀ attempt ∈ attempts,
      ∃ candidateBytes, candidateBytes ≠ canonicalBytes ∧
        attempt.1 = macInput material.1 seed candidateBytes)
    (computation : OracleComp OracleWorld α) :
    evalSPMF ((simulateQ romImpl computation).run'
      (maskedMaterialCache material seed pads canonicalBytes macAnswer)) =
    evalSPMF (do
      let outputs ← Concrete.sequenceFin fun _ :
        Fin (distinctKeys attempts).length =>
        ($ᵗ HashOutput : ProbComp HashOutput)
      (simulateQ romImpl computation).run'
        (cacheFin (maskedMaterialCache material seed pads canonicalBytes macAnswer)
          (keys attempts) outputs)) :=
  presampleFin computation _ (keys attempts) (keys_injective attempts)
    (keys_are_fresh attempts material seed pads canonicalBytes macAnswer hformat)

theorem trace_keys_presampling_preserves_plan {α : Type}
    (attempts : List (HashInput × Digest))
    (material : KeyMaterial) (seed : MasterSeed)
    (pads : List (BitVec 32 × HashOutput))
    (canonicalBytes : HashInput) (macAnswer : HashOutput)
    (hformat : ∀ attempt ∈ attempts,
      ∃ candidateBytes, candidateBytes ≠ canonicalBytes ∧
        attempt.1 = macInput material.1 seed candidateBytes)
    (outputs : Fin (distinctKeys attempts).length → HashOutput)
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
            (keys attempts) outputs) fallback)
        computation := by
  apply allFailureTrace_presampled_congr seed coins fallback _
    (keys attempts) outputs _ computation hpath
  intro i
  exact keys_are_seed_bearing attempts material.1 seed
    (fun attempt hmem => by
      obtain ⟨candidateBytes, _, hinput⟩ := hformat attempt hmem
      exact ⟨candidateBytes, hinput⟩) i

end SigGolfCandidate.SphincsCacheMacTraceTargets

/-- info: 'SigGolfCandidate.SphincsCacheMacTraceTargets.each_key_from_attempt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTraceTargets.each_key_from_attempt

/-- info: 'SigGolfCandidate.SphincsCacheMacTraceTargets.presample_trace_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTraceTargets.presample_trace_keys

/-- info: 'SigGolfCandidate.SphincsCacheMacTraceTargets.trace_keys_presampling_preserves_plan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTraceTargets.trace_keys_presampling_preserves_plan
