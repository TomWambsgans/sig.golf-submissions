import SigGolfCandidate.SphincsCachePathCollision
import SigGolfCandidate.SphincsSecurity.Completeness.Recovery
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Bytes

/-! The sign image folds the selected top-tree cache path and checks it against
the keygen root. This file isolates the cryptographic consequence of that check.
The image-to-`treeFold` refinement is a separate obligation. -/

namespace SigGolfCandidate.SphincsActualCachePathBridge

open SphincsSecurity OracleComp
open SphincsSecurity.Concrete
open SphincsSecurity.Completeness
open SigGolfCandidate.SphincsCachePathCollision

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def topNodeHash (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (leaf : LeafIndex) (level : Nat) (pair : Digest × Digest) : Digest :=
  truncateHash (f (tweakableHashInput parameter
    (.node topLayer rootTree (level + 1) (leaf.val / 2 ^ (level + 1)))
    (nodePayload pair.1 pair.2)))

def topNodeInput (parameter : PublicParameter) (leaf : LeafIndex)
    (level : Nat) (pair : Digest × Digest) : HashInput :=
  tweakableHashInput parameter
    (.node topLayer rootTree (level + 1) (leaf.val / 2 ^ (level + 1)))
    (nodePayload pair.1 pair.2)

theorem topNodeInput_injective_pair (parameter : PublicParameter)
    (leaf : LeafIndex) (level : Nat) :
    Function.Injective (topNodeInput parameter leaf level) := by
  intro x y heq
  simp only [topNodeInput, tweakableHashInput] at heq
  have hparts := (List.append_inj' heq (by rfl)).2
  have hchildren := SphincsSecurity.nodePayload_injective hparts
  exact Prod.ext hchildren.1 hchildren.2

theorem eval_topTreeFold_eq_pathValue (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (leaf : LeafIndex) (path : Nat → Digest)
    (height : Nat) (value : Digest) :
    evalWithAnswerFn f
      (treeFold parameter topLayer rootTree leaf path height value :
        OracleComp HashSpec Digest) =
      pathValue (topNodeHash f parameter leaf)
        (fun level => leaf.val.testBit level) value path height := by
  induction height with
  | zero => simp [treeFold, pathValue]
  | succ height ih =>
      rw [treeFold, evalWithAnswerFn_bind, ih]
      by_cases hbit : leaf.val.testBit height = true
      · simp [pathValue, topNodeHash, orderedPair, hbit, eval_tweakableHash]
        rw [if_pos hbit]
      · simp [pathValue, topNodeHash, orderedPair, hbit, eval_tweakableHash]
        rw [if_neg hbit]

def honestTopNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (level nodeIdx : Nat) : Digest :=
  node f parameter topLayer rootTree seed level nodeIdx

def honestTopPath (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : LeafIndex) (level : Nat) : Digest :=
  honestTopNode f parameter seed level (Nat.xor (leaf.val / 2 ^ level) 1)

theorem honestTopPath_folds_to_root (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (seed : MasterSeed) (leaf : LeafIndex) :
    evalWithAnswerFn f
      (treeFold parameter topLayer rootTree leaf
        (honestTopPath f parameter seed leaf) 11
        (honestTopNode f parameter seed 0 leaf.val) : OracleComp HashSpec Digest) =
      honestTopNode f parameter seed 11 0 := by
  have h := eval_treeFold_path f parameter topLayer rootTree seed leaf
    (honestTopPath f parameter seed leaf) 11 (by intro level hlevel; rfl)
  have hzero : leaf.val / 2 ^ 11 = 0 :=
    Nat.div_eq_of_lt (by simpa [maxLayerHeight] using leaf.isLt)
  simpa only [honestTopNode, honestTopPath, hzero] using h

/-- If the signer's top-cache root check accepts, its selected path is the
canonical one, or two distinct actual Merkle-node oracle inputs collide after
160-bit truncation. This is a fixed-oracle statement: it does not claim a
probability bound on the collision event. -/
theorem accepted_top_cache_path (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (seed : MasterSeed) (leaf : LeafIndex)
    (cachePath : Nat → Digest)
    (accepted :
      evalWithAnswerFn f
        (treeFold parameter topLayer rootTree leaf cachePath 11
          (honestTopNode f parameter seed 0 leaf.val) : OracleComp HashSpec Digest) =
        honestTopNode f parameter seed 11 0) :
    (∀ level, level < 11 →
      cachePath level = honestTopPath f parameter seed leaf level) ∨
    (∃ level, level < 11 ∧
      nodeInput (topNodeHash f parameter leaf) (fun l => leaf.val.testBit l)
        (honestTopNode f parameter seed 0 leaf.val) cachePath level ≠
      nodeInput (topNodeHash f parameter leaf) (fun l => leaf.val.testBit l)
        (honestTopNode f parameter seed 0 leaf.val)
        (honestTopPath f parameter seed leaf) level ∧
      topNodeHash f parameter leaf level
        (nodeInput (topNodeHash f parameter leaf) (fun l => leaf.val.testBit l)
          (honestTopNode f parameter seed 0 leaf.val) cachePath level) =
      topNodeHash f parameter leaf level
        (nodeInput (topNodeHash f parameter leaf) (fun l => leaf.val.testBit l)
          (honestTopNode f parameter seed 0 leaf.val)
          (honestTopPath f parameter seed leaf) level)) := by
  have hpaths :
      pathValue (topNodeHash f parameter leaf) (fun l => leaf.val.testBit l)
        (honestTopNode f parameter seed 0 leaf.val) cachePath 11 =
      pathValue (topNodeHash f parameter leaf) (fun l => leaf.val.testBit l)
        (honestTopNode f parameter seed 0 leaf.val)
        (honestTopPath f parameter seed leaf) 11 := by
    rw [← eval_topTreeFold_eq_pathValue,
      ← eval_topTreeFold_eq_pathValue, accepted,
      honestTopPath_folds_to_root]
  rcases collision_or_same_siblings
    (topNodeHash f parameter leaf) (fun l => leaf.val.testBit l)
    (honestTopNode f parameter seed 0 leaf.val) cachePath
    (honestTopPath f parameter seed leaf) 11 hpaths with hcollision | hsame
  · exact Or.inr hcollision
  · exact Or.inl hsame

/-- The collision above is between distinct serialized random-oracle inputs,
not merely between distinct abstract child pairs. -/
theorem accepted_top_cache_path_query_collision (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (seed : MasterSeed) (leaf : LeafIndex)
    (cachePath : Nat → Digest)
    (accepted :
      evalWithAnswerFn f
        (treeFold parameter topLayer rootTree leaf cachePath 11
          (honestTopNode f parameter seed 0 leaf.val) : OracleComp HashSpec Digest) =
        honestTopNode f parameter seed 11 0) :
    (∀ level, level < 11 →
      cachePath level = honestTopPath f parameter seed leaf level) ∨
    (∃ level, level < 11 ∧
      let badInput := topNodeInput parameter leaf level
        (nodeInput (topNodeHash f parameter leaf) (fun l => leaf.val.testBit l)
          (honestTopNode f parameter seed 0 leaf.val) cachePath level)
      let goodInput := topNodeInput parameter leaf level
        (nodeInput (topNodeHash f parameter leaf) (fun l => leaf.val.testBit l)
          (honestTopNode f parameter seed 0 leaf.val)
          (honestTopPath f parameter seed leaf) level)
      badInput ≠ goodInput ∧ truncateHash (f badInput) = truncateHash (f goodInput)) := by
  rcases accepted_top_cache_path f parameter seed leaf cachePath accepted with
    hsame | ⟨level, hlt, hne, heq⟩
  · exact Or.inl hsame
  · refine Or.inr ⟨level, hlt, ?_⟩
    dsimp
    constructor
    · intro hequal
      exact hne (topNodeInput_injective_pair parameter leaf level hequal)
    · exact heq

/-- info: 'SigGolfCandidate.SphincsActualCachePathBridge.accepted_top_cache_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms accepted_top_cache_path

/-- info: 'SigGolfCandidate.SphincsActualCachePathBridge.accepted_top_cache_path_query_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms accepted_top_cache_path_query_collision

end SigGolfCandidate.SphincsActualCachePathBridge
