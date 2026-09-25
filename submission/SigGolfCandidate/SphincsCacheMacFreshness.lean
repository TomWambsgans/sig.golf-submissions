import SigGolfCandidate.SphincsMaskedCacheProgramming
import SigGolfCandidate.SphincsCacheMacAlteredSplit

/-! Every changed authenticated cache prefix addresses a fresh tag-15 RO cell
relative to the canonical seeded key-material/pad/MAC cache. -/

namespace SigGolfCandidate.SphincsCacheMacFreshness
open OracleComp OracleSpec SphincsSecurity SphincsSecurity.Seeded
open SigGolfCandidate.SphincsCacheSecretDomains
open SigGolfCandidate.SphincsMaskedCacheProgramming

theorem materialCache_mac_fresh (seed : MasterSeed) (material : KeyMaterial)
    (candidateBytes : HashInput) :
    materialCache seed material
      (macInput material.1 seed candidateBytes) = none := by
  unfold materialCache programmedCache derivationCache
  rw [cacheTable_apply_of_not_mem]
  · unfold parameterCache
    rw [QueryCache.cacheQuery_of_ne]
    · rfl
    · exact macInput_ne_keygenHashInput _ _ _ _ _ _
  · intro position
    exact macInput_ne_keygenHashInput _ _ _ _ _ _

theorem programPads_preserve_mac (parameter : PublicParameter)
    (seed : MasterSeed) (pads : List (BitVec 32 × HashOutput))
    (base : QueryCache HashSpec) (candidateBytes : HashInput) :
    programPads parameter seed pads base (macInput parameter seed candidateBytes) =
      base (macInput parameter seed candidateBytes) := by
  induction pads generalizing base with
  | nil => rfl
  | cons entry rest ih =>
      unfold programPads
      simp only [List.foldl_cons]
      change programPads parameter seed rest
        (base.cacheQuery (padInput parameter seed entry.1) entry.2)
          (macInput parameter seed candidateBytes) = _
      rw [ih]
      exact QueryCache.cacheQuery_of_ne _ _
        (padInput_ne_macInput parameter parameter seed seed entry.1 candidateBytes).symm

theorem programPads_mac_fresh (seed : MasterSeed)
    (material : KeyMaterial)
    (pads : List (BitVec 32 × HashOutput))
    (candidateBytes : HashInput) :
    programPads material.1 seed pads (materialCache seed material)
      (macInput material.1 seed candidateBytes) = none := by
  rw [programPads_preserve_mac]
  exact materialCache_mac_fresh seed material candidateBytes

theorem maskedMaterialCache_altered_fresh (seed : MasterSeed)
    (material : KeyMaterial)
    (pads : List (BitVec 32 × HashOutput))
    (canonicalBytes candidateBytes : HashInput)
    (macAnswer : HashOutput)
    (hchanged : candidateBytes ≠ canonicalBytes) :
    maskedMaterialCache material seed pads canonicalBytes macAnswer
      (macInput material.1 seed candidateBytes) = none := by
  unfold maskedMaterialCache
  rw [QueryCache.cacheQuery_of_ne]
  · exact programPads_mac_fresh seed material pads candidateBytes
  · exact (macInput_injective_ciphertext material.1 seed).ne hchanged

end SigGolfCandidate.SphincsCacheMacFreshness

/-- info: 'SigGolfCandidate.SphincsCacheMacFreshness.maskedMaterialCache_altered_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacFreshness.maskedMaterialCache_altered_fresh
