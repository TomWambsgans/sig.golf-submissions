import SigGolfCandidate.SphincsSignNoFinalTree
import SigGolfCandidate.SphincsSecurity.Completeness.Recovery

/-! A canonical public top-tree cache changes how the signer obtains its
authentication path, but not the signature produced at a fixed oracle. -/

namespace SigGolfCandidate.SphincsCachedSignValue

open SphincsSecurity OracleComp
open SphincsSecurity.Concrete
open SphincsSecurity.Seeded

set_option maxHeartbeats 1000000

/-- Abstractly, the canonical cache contains every top-tree node. Its byte
layout is proved separately. -/
def canonicalTopCache (hash : HashInput → HashOutput)
    (secretKey : SecretKey) (level nodeIdx : Nat) : Digest :=
  SphincsSecurity.Completeness.node hash secretKey.parameter topLayer rootTree
    secretKey.seed level nodeIdx

def topPathFromCache (cache : Nat → Nat → Digest) (leaf : LeafIndex) :
    Fin (layerHeight topLayer) → Digest :=
  fun level => cache level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)

theorem topTreeIndex (index : Index) :
    treeIndexAt index topLayer = rootTree := by
  apply Fin.ext
  have hheight : heightAbove topLayer = 0 := by
    simp [heightAbove, topLayer]
  change index.val / 2 ^ (totalHeight - heightAbove topLayer) = 0
  rw [hheight]
  simp only [totalHeight, Nat.sub_zero]
  exact Nat.div_eq_of_lt index.isLt

/-- Sign the top layer using cached sibling nodes instead of recomputing its
authentication path. -/
def signTopWithCache (secretKey : SecretKey) (index : Index)
    (cache : Nat → Nat → Digest) :
    OracleComp HashSpec (Option (LayerSignature topLayer)) := do
  let tree := treeIndexAt index topLayer
  let leaf := leafIndexAt index topLayer
  let message ← Seeded.layerMessage secretKey index topLayer
  let some (counter, values) ←
      (Seeded.otsSign secretKey.parameter topLayer tree leaf secretKey.seed message :
        OracleComp HashSpec _) | return none
  return some ⟨counter, values, topPathFromCache cache leaf⟩

theorem canonicalTopCache_path
    (hash : HashInput → HashOutput) (secretKey : SecretKey) (index : Index) :
    topPathFromCache (canonicalTopCache hash secretKey) (leafIndexAt index topLayer) =
      evalWithAnswerFn hash
        (Seeded.treePath secretKey.parameter topLayer (treeIndexAt index topLayer)
          secretKey.seed (leafIndexAt index topLayer) :
          OracleComp HashSpec (Fin (layerHeight topLayer) → Digest)) := by
  funext level
  simpa only [topPathFromCache, canonicalTopCache, topTreeIndex] using
    (SphincsSecurity.Completeness.eval_treePath hash secretKey.parameter
    topLayer (treeIndexAt index topLayer) secretKey.seed
    (leafIndexAt index topLayer) level).symm

theorem signTopWithCache_value
    (hash : HashInput → HashOutput) (secretKey : SecretKey) (index : Index) :
    evalWithAnswerFn hash
      (signTopWithCache secretKey index (canonicalTopCache hash secretKey)) =
      evalWithAnswerFn hash
        (Seeded.signLayer secretKey index topLayer :
          OracleComp HashSpec (Option (LayerSignature topLayer))) := by
  simp only [signTopWithCache, Seeded.signLayer, evalWithAnswerFn_bind]
  cases hots : evalWithAnswerFn hash
      (Seeded.otsSign secretKey.parameter topLayer
        (treeIndexAt index topLayer) (leafIndexAt index topLayer) secretKey.seed
        (evalWithAnswerFn hash
          (Seeded.layerMessage secretKey index topLayer : OracleComp HashSpec Digest)) :
        OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) with
  | none => simp [evalWithAnswerFn_pure]
  | some result =>
    rcases result with ⟨counter, values⟩
    simp only [evalWithAnswerFn_pure, evalWithAnswerFn_bind]
    rw [canonicalTopCache_path]

/-- The five non-top layers keep the original signer. -/
def signLayersWithCache (secretKey : SecretKey) (index : Index)
    (cache : Nat → Nat → Digest) :
    OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay)) := do
  let some bottom ←
      (Seeded.signLayer secretKey index bottomLayer :
        OracleComp HashSpec (Option (LayerSignature bottomLayer))) | return none
  let some middle4 ←
      (Seeded.signLayer secretKey index middle4Layer :
        OracleComp HashSpec (Option (LayerSignature middle4Layer))) | return none
  let some middle3 ←
      (Seeded.signLayer secretKey index middle3Layer :
        OracleComp HashSpec (Option (LayerSignature middle3Layer))) | return none
  let some middle2 ←
      (Seeded.signLayer secretKey index middle2Layer :
        OracleComp HashSpec (Option (LayerSignature middle2Layer))) | return none
  let some middle ←
      (Seeded.signLayer secretKey index middleLayer :
        OracleComp HashSpec (Option (LayerSignature middleLayer))) | return none
  let some top ← signTopWithCache secretKey index cache | return none
  return some (Fin.cases top (Fin.cases middle
    (Fin.cases middle2 (Fin.cases middle3
      (Fin.cases middle4 (Fin.cases bottom (fun i => Fin.elim0 i)))))))

theorem signLayersWithCache_value
    (hash : HashInput → HashOutput) (secretKey : SecretKey) (index : Index) :
    evalWithAnswerFn hash
      (signLayersWithCache secretKey index (canonicalTopCache hash secretKey)) =
      evalWithAnswerFn hash
        (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
          OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))) := by
  unfold signLayersWithCache Concrete.sequenceLayers
  simp only [evalWithAnswerFn_bind]
  cases hbottom : evalWithAnswerFn hash
      (Seeded.signLayer secretKey index bottomLayer :
        OracleComp HashSpec (Option (LayerSignature bottomLayer))) with
  | none => simp [evalWithAnswerFn_pure]
  | some bottom =>
    simp only [evalWithAnswerFn_bind]
    cases hm4 : evalWithAnswerFn hash
        (Seeded.signLayer secretKey index middle4Layer :
          OracleComp HashSpec (Option (LayerSignature middle4Layer))) with
    | none => simp [evalWithAnswerFn_pure]
    | some middle4 =>
      simp only [evalWithAnswerFn_bind]
      cases hm3 : evalWithAnswerFn hash
          (Seeded.signLayer secretKey index middle3Layer :
            OracleComp HashSpec (Option (LayerSignature middle3Layer))) with
      | none => simp [evalWithAnswerFn_pure]
      | some middle3 =>
        simp only [evalWithAnswerFn_bind]
        cases hm2 : evalWithAnswerFn hash
            (Seeded.signLayer secretKey index middle2Layer :
              OracleComp HashSpec (Option (LayerSignature middle2Layer))) with
        | none => simp [evalWithAnswerFn_pure]
        | some middle2 =>
          simp only [evalWithAnswerFn_bind]
          cases hm : evalWithAnswerFn hash
              (Seeded.signLayer secretKey index middleLayer :
                OracleComp HashSpec (Option (LayerSignature middleLayer))) with
          | none => simp [evalWithAnswerFn_pure]
          | some middle =>
            simp only [evalWithAnswerFn_bind]
            rw [signTopWithCache_value]
            cases htop : evalWithAnswerFn hash
                (Seeded.signLayer secretKey index topLayer :
                  OracleComp HashSpec (Option (LayerSignature topLayer))) with
            | none => simp [evalWithAnswerFn_pure]
            | some top => simp [evalWithAnswerFn_pure]

/-- The compact signer after replacing top-tree path recomputation by the
canonical cache and removing its unused final top-root recomputation. -/
def signWithCache (secretKey : SecretKey) (message : Message)
    (cache : Nat → Nat → Digest) : OracleComp HashSpec (Option Signature) := do
  let some (randomness, index, leaves) ←
      (Seeded.signDigestLoop secretKey message digestAttemptLimit 0 :
        OracleComp HashSpec _) | return none
  let secrets ← sequenceFin fun tree =>
    (deriveKey secretKey.parameter
      (.fts index tree (leaves (ftsIndexOf tree))) secretKey.seed :
      OracleComp HashSpec _)
  let ftsPath ←
    (Seeded.ftsOpen secretKey.parameter index leaves secretKey.seed :
      OracleComp HashSpec _)
  let some layers ←
      signLayersWithCache secretKey index cache | return none
  return some ⟨randomness, secrets, ftsPath, layers⟩

theorem signWithCanonicalCache_value
    (hash : HashInput → HashOutput) (secretKey : SecretKey) (message : Message) :
    evalWithAnswerFn hash
      (Seeded.sign secretKey message : OracleComp HashSpec (Option Signature)) =
      evalWithAnswerFn hash
        (signWithCache secretKey message (canonicalTopCache hash secretKey)) := by
  rw [SphincsSignNoFinalTree.signNoFinalTree_value]
  simp only [SphincsSignNoFinalTree.signNoFinalTree, signWithCache,
    evalWithAnswerFn_bind]
  cases h : evalWithAnswerFn hash
      (Seeded.signDigestLoop secretKey message digestAttemptLimit 0 :
        OracleComp HashSpec _) with
  | none => simp [evalWithAnswerFn_pure]
  | some data =>
    rcases data with ⟨randomness, index, leaves⟩
    simp only [evalWithAnswerFn_bind]
    rw [signLayersWithCache_value]
    cases hlayers : evalWithAnswerFn hash
        (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
          OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))) with
    | none => simp [evalWithAnswerFn_pure]
    | some layers => simp [evalWithAnswerFn_pure]

/-- info: 'SigGolfCandidate.SphincsCachedSignValue.canonicalTopCache_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms canonicalTopCache_path

/-- info: 'SigGolfCandidate.SphincsCachedSignValue.signTopWithCache_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms signTopWithCache_value

/-- info: 'SigGolfCandidate.SphincsCachedSignValue.signLayersWithCache_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms signLayersWithCache_value

/-- info: 'SigGolfCandidate.SphincsCachedSignValue.signWithCanonicalCache_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms signWithCanonicalCache_value

end SigGolfCandidate.SphincsCachedSignValue
