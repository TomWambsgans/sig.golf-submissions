import SigGolfCandidate.SphincsCacheSecretDomains
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.GameComparison

/-! Program prospective masked-cache answers on top of the inherited seeded
keygen game, keeping every change inside its existing `SeedHit` region. -/

namespace SigGolfCandidate.SphincsMaskedCacheProgramming
open OracleComp OracleSpec ENNReal SphincsSecurity
open SphincsSecurity.Seeded
open SigGolfCandidate.SphincsCacheSecretDomains

/-- Program a full 256-bit oracle answer whose low 160 bits encrypt one tree
node. The high 96 bits remain free uniform randomness. -/
noncomputable def programmedPadAnswer (node cipher : Digest)
    (high : HighDigest) : HashOutput :=
  outputHalves.symm (cipher ^^^ node, high)

theorem truncate_programmedPadAnswer (node cipher : Digest)
    (high : HighDigest) :
    truncateHash (programmedPadAnswer node cipher high) = cipher ^^^ node := by
  exact truncate_from_halves (cipher ^^^ node) high

def programPads (parameter : PublicParameter) (seed : MasterSeed)
    (entries : List (BitVec 32 × HashOutput)) (base : QueryCache HashSpec) :
    QueryCache HashSpec :=
  entries.foldl (fun cache entry =>
    cache.cacheQuery (padInput parameter seed entry.1) entry.2) base

theorem programPads_agreeOutside (parameter : PublicParameter)
    (seed : MasterSeed) (entries : List (BitVec 32 × HashOutput))
    (base : QueryCache HashSpec)
    (hbase : AgreeOutside (fun input => SeedHit input seed) base ∅) :
    AgreeOutside (fun input => SeedHit input seed)
      (programPads parameter seed entries base) ∅ := by
  induction entries generalizing base with
  | nil => exact hbase
  | cons entry entries ih =>
    unfold programPads
    simp only [List.foldl_cons]
    apply ih
    intro input hnot
    have hne : input ≠ padInput parameter seed entry.1 := by
      intro heq
      exact hnot (heq ▸ padInput_seedHit parameter seed entry.1)
    simpa only [QueryCache.cacheQuery_of_ne _ _ hne] using hbase input hnot

noncomputable def maskedMaterialCache (material : KeyMaterial) (seed : MasterSeed)
    (pads : List (BitVec 32 × HashOutput))
    (ciphertext : HashInput) (macAnswer : HashOutput) : QueryCache HashSpec :=
  (programPads material.1 seed pads (materialCache seed material)).cacheQuery
    (macInput material.1 seed ciphertext) macAnswer

theorem maskedMaterialCache_agreeOutside (material : KeyMaterial)
    (seed : MasterSeed) (pads : List (BitVec 32 × HashOutput))
    (ciphertext : HashInput) (macAnswer : HashOutput) :
    AgreeOutside (fun input => SeedHit input seed)
      (maskedMaterialCache material seed pads ciphertext macAnswer) ∅ := by
  intro input hnot
  have hne : input ≠ macInput material.1 seed ciphertext := by
    intro heq
    exact hnot (heq ▸ macInput_seedHit material.1 seed ciphertext)
  simp only [maskedMaterialCache, QueryCache.cacheQuery_of_ne _ _ hne]
  exact programPads_agreeOutside material.1 seed pads _
    (programmedCache_agreeOutside seed _ _ _ _) input hnot

/-- The existing adaptive theorem applies unchanged to the new tag-14 and
tag-15 entries after the seeded game rearranges material before seed. -/
theorem maskedMaterialCache_adaptive_bound {α : Type}
    (material : KeyMaterial) (pads : List (BitVec 32 × HashOutput))
    (ciphertext : HashInput) (macAnswer : HashOutput)
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : HashQueryBound computation ∅ q) (event : α → Prop) :
    Pr[event | sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl computation).run'
        (maskedMaterialCache material seed pads ciphertext macAnswer)] ≤
    Pr[event | (simulateQ romImpl computation).run' ∅] +
      q / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
  probEvent_random_cache_change_le computation
    (fun seed => maskedMaterialCache material seed pads ciphertext macAnswer) ∅
    (fun seed => maskedMaterialCache_agreeOutside material seed pads ciphertext macAnswer)
    q hbound event

/-- The same contact bound survives the actual seeded proof's `drawKeyMaterial`
sampling order: material, ciphertext and programmed answers may depend on one
another, but none may depend on the master seed. -/
theorem draw_material_masked_adaptive_bound {α : Type}
    (pads : KeyMaterial → List (BitVec 32 × HashOutput))
    (ciphertext : KeyMaterial → HashInput)
    (macAnswer : KeyMaterial → HashOutput)
    (computation : KeyMaterial → OracleComp OracleWorld α)
    (q : Nat)
    (hbound : ∀ material, HashQueryBound (computation material) ∅ q)
    (event : α → Prop) :
    Pr[event | drawKeyMaterial >>= fun material =>
      sampleMasterSeed >>= fun seed =>
        (simulateQ romImpl (computation material)).run'
          (maskedMaterialCache material seed (pads material)
            (ciphertext material) (macAnswer material))] ≤
    Pr[event | drawKeyMaterial >>= fun material =>
      (simulateQ romImpl (computation material)).run' ∅] +
      q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  apply probEvent_bind_congr_le_add
  intro material _
  exact maskedMaterialCache_adaptive_bound material (pads material)
    (ciphertext material) (macAnswer material) (computation material)
    q (hbound material) event

end SigGolfCandidate.SphincsMaskedCacheProgramming

/-- info: 'SigGolfCandidate.SphincsMaskedCacheProgramming.maskedMaterialCache_adaptive_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsMaskedCacheProgramming.maskedMaterialCache_adaptive_bound

/-- info: 'SigGolfCandidate.SphincsMaskedCacheProgramming.draw_material_masked_adaptive_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsMaskedCacheProgramming.draw_material_masked_adaptive_bound
