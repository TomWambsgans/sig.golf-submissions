import SigGolfCandidate.SphincsCacheTreeUniqueness

/-! Abstract meaning of the scratch sign image's public-cache precheck. -/

namespace SigGolfCandidate.SphincsCacheTreeConcrete
open SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCachedSignValue

def parentHash (hash : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (level node : Nat) (left right : Digest) : Digest :=
  truncateHash (hash (tweakableHashInput parameter
    (.node topLayer rootTree level node) (nodePayload left right)))

def Consistent (hash : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (cache : Nat → Nat → Digest) : Prop :=
  ∀ depth, depth < 11 → ∀ node, node < 2 ^ depth →
    cache (11 - depth) node =
      parentHash hash parameter (11 - depth) node
        (cache (11 - (depth + 1)) (2 * node))
        (cache (11 - (depth + 1)) (2 * node + 1))

theorem canonical_consistent (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) :
    Consistent hash secretKey.parameter (canonicalTopCache hash secretKey) := by
  intro depth hd node hn
  have hlevel : 11 - depth = (11 - (depth + 1)) + 1 := by omega
  rw [hlevel]
  simpa only [canonicalTopCache, parentHash] using
    (SphincsSecurity.Completeness.node_succ hash secretKey.parameter
      topLayer rootTree secretKey.seed (11 - (depth + 1)) node)

theorem cache_eq_canonical_of_consistent_root
    (hash : QueryImpl HashSpec Id) (secretKey : Seeded.SecretKey)
    (cache : Nat → Nat → Digest)
    (hconsistent : Consistent hash secretKey.parameter cache)
    (hroot : cache 11 0 = (canonicalTopCache hash secretKey) 11 0)
    (hcollision_free : ∀ depth, depth < 11 → ∀ node, node < 2 ^ depth →
      parentHash hash secretKey.parameter (11 - depth) node
          ((canonicalTopCache hash secretKey) (11 - (depth + 1)) (2 * node))
          ((canonicalTopCache hash secretKey) (11 - (depth + 1)) (2 * node + 1)) =
        parentHash hash secretKey.parameter (11 - depth) node
          (cache (11 - (depth + 1)) (2 * node))
          (cache (11 - (depth + 1)) (2 * node + 1)) →
      (canonicalTopCache hash secretKey) (11 - (depth + 1)) (2 * node) =
        cache (11 - (depth + 1)) (2 * node) ∧
      (canonicalTopCache hash secretKey) (11 - (depth + 1)) (2 * node + 1) =
        cache (11 - (depth + 1)) (2 * node + 1)) :
    ∀ level, level ≤ 11 → ∀ node, node < 2 ^ (11 - level) →
      cache level node = (canonicalTopCache hash secretKey) level node := by
  have result := SphincsCacheTreeUniqueness.nodes_eq_of_consistent_root 11
    (canonicalTopCache hash secretKey) cache
    (fun level node left right =>
      parentHash hash secretKey.parameter level node left right)
    (canonical_consistent hash secretKey) hconsistent hcollision_free hroot.symm
  intro level hl node hn
  exact (result level hl node hn).symm

theorem selected_path_eq_of_nodes_eq
    (hash : QueryImpl HashSpec Id) (secretKey : Seeded.SecretKey)
    (cache : Nat → Nat → Digest) (leaf : LeafIndex)
    (hnodes : ∀ level, level ≤ 11 → ∀ node, node < 2 ^ (11 - level) →
      cache level node = (canonicalTopCache hash secretKey) level node)
    (hsibling : ∀ level : Fin (layerHeight topLayer),
      Nat.xor (leaf.val / 2 ^ level.val) 1 < 2 ^ (11 - level.val)) :
    topPathFromCache cache leaf =
      topPathFromCache (canonicalTopCache hash secretKey) leaf := by
  funext level
  exact hnodes level.val (by simpa [topLayer, layerHeight, maxLayerHeight] using
    (Nat.le_of_lt level.isLt)) _ (hsibling level)

theorem selected_sibling_bound (leaf : LeafIndex)
    (level : Fin (layerHeight topLayer)) :
    Nat.xor (leaf.val / 2 ^ level.val) 1 < 2 ^ (11 - level.val) := by
  have hlevel : level.val < 11 := by
    simpa [topLayer, layerHeight, maxLayerHeight] using level.isLt
  have hleaf : leaf.val < 2 ^ 11 := by
    simpa [maxLayerHeight] using leaf.isLt
  have hpow : 2 ^ level.val * 2 ^ (11 - level.val) = 2 ^ 11 := by
    rw [← pow_add]
    congr 1
    omega
  have hdiv : leaf.val / 2 ^ level.val < 2 ^ (11 - level.val) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).2
    simpa only [Nat.mul_comm, hpow] using hleaf
  have hone : 1 < 2 ^ (11 - level.val) := by
    have hk : 0 < 11 - level.val := by omega
    cases h : 11 - level.val with
    | zero => omega
    | succ k =>
        rw [pow_succ]
        have : 0 < 2 ^ k := by positivity
        omega
  exact Nat.xor_lt_two_pow hdiv hone

theorem selected_path_eq_of_consistent_root
    (hash : QueryImpl HashSpec Id) (secretKey : Seeded.SecretKey)
    (cache : Nat → Nat → Digest)
    (hconsistent : Consistent hash secretKey.parameter cache)
    (hroot : cache 11 0 = (canonicalTopCache hash secretKey) 11 0)
    (hcollision_free : ∀ depth, depth < 11 → ∀ node, node < 2 ^ depth →
      parentHash hash secretKey.parameter (11 - depth) node
          ((canonicalTopCache hash secretKey) (11 - (depth + 1)) (2 * node))
          ((canonicalTopCache hash secretKey) (11 - (depth + 1)) (2 * node + 1)) =
        parentHash hash secretKey.parameter (11 - depth) node
          (cache (11 - (depth + 1)) (2 * node))
          (cache (11 - (depth + 1)) (2 * node + 1)) →
      (canonicalTopCache hash secretKey) (11 - (depth + 1)) (2 * node) =
        cache (11 - (depth + 1)) (2 * node) ∧
      (canonicalTopCache hash secretKey) (11 - (depth + 1)) (2 * node + 1) =
        cache (11 - (depth + 1)) (2 * node + 1))
    (leaf : LeafIndex) :
    topPathFromCache cache leaf =
      topPathFromCache (canonicalTopCache hash secretKey) leaf := by
  apply selected_path_eq_of_nodes_eq hash secretKey cache leaf
  · exact cache_eq_canonical_of_consistent_root hash secretKey cache
      hconsistent hroot hcollision_free
  · exact selected_sibling_bound leaf

end SigGolfCandidate.SphincsCacheTreeConcrete

/-- info: 'SigGolfCandidate.SphincsCacheTreeConcrete.cache_eq_canonical_of_consistent_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheTreeConcrete.cache_eq_canonical_of_consistent_root

/-- info: 'SigGolfCandidate.SphincsCacheTreeConcrete.selected_path_eq_of_nodes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheTreeConcrete.selected_path_eq_of_nodes_eq

/-- info: 'SigGolfCandidate.SphincsCacheTreeConcrete.selected_path_eq_of_consistent_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheTreeConcrete.selected_path_eq_of_consistent_root
