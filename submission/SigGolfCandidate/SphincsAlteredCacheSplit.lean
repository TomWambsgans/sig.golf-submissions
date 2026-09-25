import SigGolfCandidate.SphincsActualCachePathBridge
import SigGolfCandidate.SphincsCommitment

/-!
A deterministic split for the actual signer's public, attacker-modifiable cache.
The RISC-V refinement must establish the two checks passed as premises:
the 16-byte public-key commitment check, and the selected top-path root check.
-/

namespace SigGolfCandidate.SphincsAlteredCacheSplit
open SphincsSecurity OracleComp
open SphincsSecurity.Concrete
open SigGolfCandidate.SphincsActualCachePathBridge
open SigGolfCandidate.SphincsWire

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] honestTopNode topNodeHash

def committedKey (f : QueryImpl HashSpec Id) (key : PublicKey) : BitVec 128 :=
  (f (commitmentInput key)).extractLsb' 0 128

/-- An altered internal key passing the same public commitment either is the honest
key or gives a collision between two distinct tag-13 oracle queries. -/
theorem same_commitment_key_or_collision (f : QueryImpl HashSpec Id)
    (honest altered : PublicKey)
    (accepted : committedKey f altered = committedKey f honest) :
    altered = honest ∨
      (commitmentInput altered ≠ commitmentInput honest ∧
        (f (commitmentInput altered)).extractLsb' 0 128 =
          (f (commitmentInput honest)).extractLsb' 0 128) := by
  by_cases same : altered = honest
  · exact Or.inl same
  · exact Or.inr ⟨fun h => same (commitmentInput_injective h), accepted⟩

/-- The two checks together leave only the canonical top cache path, a
160-bit top-node collision, or a 128-bit public commitment collision. -/
theorem accepted_altered_cache_split (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (seed : MasterSeed) (leaf : LeafIndex)
    (cacheRoot : Digest) (cachePath : Nat → Digest)
    (commitmentAccepted :
      committedKey f ⟨cacheRoot, parameter⟩ =
        committedKey f ⟨honestTopNode f parameter seed 11 0, parameter⟩)
    (pathAccepted :
      evalWithAnswerFn f
        (treeFold parameter topLayer rootTree leaf cachePath 11
          (honestTopNode f parameter seed 0 leaf.val) : OracleComp HashSpec Digest) =
        cacheRoot) :
    (cacheRoot = honestTopNode f parameter seed 11 0 ∧
      ∀ level, level < 11 →
        cachePath level = honestTopPath f parameter seed leaf level) ∨
    (∃ level, level < 11 ∧
      let badInput := topNodeInput parameter leaf level
        (SigGolfCandidate.SphincsCachePathCollision.nodeInput
          (topNodeHash f parameter leaf) (fun l => leaf.val.testBit l)
          (honestTopNode f parameter seed 0 leaf.val) cachePath level)
      let goodInput := topNodeInput parameter leaf level
        (SigGolfCandidate.SphincsCachePathCollision.nodeInput
          (topNodeHash f parameter leaf) (fun l => leaf.val.testBit l)
          (honestTopNode f parameter seed 0 leaf.val)
          (honestTopPath f parameter seed leaf) level)
      badInput ≠ goodInput ∧ truncateHash (f badInput) = truncateHash (f goodInput)) ∨
    (commitmentInput ⟨cacheRoot, parameter⟩ ≠
        commitmentInput ⟨honestTopNode f parameter seed 11 0, parameter⟩ ∧
      (f (commitmentInput ⟨cacheRoot, parameter⟩)).extractLsb' 0 128 =
        (f (commitmentInput ⟨honestTopNode f parameter seed 11 0, parameter⟩)).extractLsb' 0 128) := by
  by_cases rootSame : cacheRoot = honestTopNode f parameter seed 11 0
  ·
    have accepted :
        evalWithAnswerFn f
          (treeFold parameter topLayer rootTree leaf cachePath 11
            (honestTopNode f parameter seed 0 leaf.val) : OracleComp HashSpec Digest) =
          honestTopNode f parameter seed 11 0 := pathAccepted.trans rootSame
    rcases accepted_top_cache_path_query_collision f parameter seed leaf cachePath
      accepted with canonical | nodeCollision
    · exact Or.inl ⟨rootSame, canonical⟩
    · exact Or.inr (Or.inl nodeCollision)
  · have different :
        commitmentInput ⟨cacheRoot, parameter⟩ ≠
          commitmentInput ⟨honestTopNode f parameter seed 11 0, parameter⟩ := by
      intro heq
      exact rootSame (congrArg PublicKey.root (commitmentInput_injective heq))
    exact Or.inr (Or.inr ⟨different, commitmentAccepted⟩)

/-- info: 'SigGolfCandidate.SphincsAlteredCacheSplit.accepted_altered_cache_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted_altered_cache_split

end SigGolfCandidate.SphincsAlteredCacheSplit
