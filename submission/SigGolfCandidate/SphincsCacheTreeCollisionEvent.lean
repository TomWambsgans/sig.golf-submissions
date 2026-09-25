import SigGolfCandidate.SphincsCacheTreeConcrete

namespace SigGolfCandidate.SphincsCacheTreeCollisionEvent
open SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCachedSignValue
open SigGolfCandidate.SphincsCacheTreeConcrete

/-- A changed child pair maps to the same 160-bit parent at a fixed top-tree position. -/
def NodeCollision (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (cache : Nat → Nat → Digest) : Prop :=
  ∃ depth, depth < 11 ∧ ∃ node, node < 2 ^ depth ∧
    let level := 11 - (depth + 1)
    let referencePair :=
      ((canonicalTopCache hash secretKey) level (2 * node),
       (canonicalTopCache hash secretKey) level (2 * node + 1))
    let candidatePair :=
      (cache level (2 * node), cache level (2 * node + 1))
    referencePair ≠ candidatePair ∧
      parentHash hash secretKey.parameter (11 - depth) node
        referencePair.1 referencePair.2 =
      parentHash hash secretKey.parameter (11 - depth) node
        candidatePair.1 candidatePair.2

theorem canonical_or_node_collision
    (hash : QueryImpl HashSpec Id) (secretKey : Seeded.SecretKey)
    (cache : Nat → Nat → Digest)
    (hconsistent : Consistent hash secretKey.parameter cache)
    (hroot : cache 11 0 = (canonicalTopCache hash secretKey) 11 0) :
    (∀ level, level ≤ 11 → ∀ node, node < 2 ^ (11 - level) →
      cache level node = (canonicalTopCache hash secretKey) level node) ∨
      NodeCollision hash secretKey cache := by
  classical
  by_cases hcollision : NodeCollision hash secretKey cache
  · exact Or.inr hcollision
  · apply Or.inl
    apply cache_eq_canonical_of_consistent_root hash secretKey cache hconsistent hroot
    intro depth hd node hn heq
    by_contra hpair
    apply hcollision
    refine ⟨depth, hd, node, hn, ?_⟩
    dsimp only
    exact ⟨by
      intro hp
      exact hpair (Prod.mk.inj hp), heq⟩

end SigGolfCandidate.SphincsCacheTreeCollisionEvent

/-- info: 'SigGolfCandidate.SphincsCacheTreeCollisionEvent.canonical_or_node_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheTreeCollisionEvent.canonical_or_node_collision
