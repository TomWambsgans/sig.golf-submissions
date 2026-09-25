import SigGolfCandidate.SphincsCachedSignValue
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryCap

namespace SigGolfCandidate.CachedSignerTrace

open OracleComp SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCachedSignValue
set_option maxRecDepth 8192
set_option maxHeartbeats 0

noncomputable def runCount {α : Type} (hash : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) : α × Nat :=
  evalWithAnswerFn hash (SphincsSecurity.QueryCap.counted (fun _ => True) computation)

theorem runCount_pure {α : Type} (hash : QueryImpl HashSpec Id) (value : α) :
    runCount hash (pure value) = (value, 0) := rfl

theorem runCount_bind {α β : Type} (hash : QueryImpl HashSpec Id)
    (first : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    runCount hash (first >>= next) =
      let a := runCount hash first
      let b := runCount hash (next a.1)
      (b.1, a.2 + b.2) := by
  simp [runCount, SphincsSecurity.QueryCap.counted_bind, evalWithAnswerFn_bind]

theorem runCount_map {α β : Type} (hash : QueryImpl HashSpec Id)
    (first : OracleComp HashSpec α) (f : α → β) :
    runCount hash (f <$> first) =
      (f (runCount hash first).1, (runCount hash first).2) := by
  simp [runCount, SphincsSecurity.QueryCap.counted_map, evalWithAnswerFn_map]

theorem runCount_value {α : Type} (hash : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) :
    (runCount hash computation).1 = evalWithAnswerFn hash computation := by
  have h := SphincsSecurity.QueryCap.counted_forget (fun _ : HashInput => True) computation
  have he := congrArg (evalWithAnswerFn hash) h
  simpa only [runCount, evalWithAnswerFn_map] using he

theorem runCount_hash (hash : QueryImpl HashSpec Id) (input : HashInput) :
    runCount hash (oracleHash input : OracleComp HashSpec HashOutput) =
      (hash input, 1) := by
  rfl

theorem runCount_tweakableHash (hash : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    (runCount hash (tweakableHash parameter domain payload : OracleComp HashSpec Digest)).2 = 1 := by
  simp [tweakableHash, runCount_map, runCount_hash]

theorem runCount_chainWalk (hash : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat)
    (value : Digest) (hsteps : start + steps ≤ chainLength - 1) :
    (runCount hash
      (chainWalk parameter lay tree leaf chainIdx start steps value :
        OracleComp HashSpec Digest)).2 = steps := by
  induction steps with
  | zero => simp [chainWalk, runCount_pure]
  | succ steps ih =>
    have hstep : start + steps < chainLength - 1 := by omega
    have hprev : start + steps ≤ chainLength - 1 := by omega
    simp only [chainWalk, dif_pos hstep, runCount_bind]
    simp [ih hprev, runCount_tweakableHash]

theorem runCount_deriveKey (hash : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    (runCount hash
      (deriveKey parameter domain seed : OracleComp HashSpec Digest)).2 = 1 := by
  simp [deriveKey, runCount_map, runCount_hash]

theorem runCount_sequenceFin {α : Type} {n : Nat}
    (hash : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec α) :
    (runCount hash (sequenceFin computation)).2 =
      ∑ index : Fin n, (runCount hash (computation index)).2 := by
  induction n with
  | zero => simp [sequenceFin, runCount_pure]
  | succ n ih =>
    simp only [sequenceFin, runCount_bind, runCount_pure, Fin.sum_univ_succ]
    rw [ih]
    rfl

theorem runCount_oneTimePublicKey (hash : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    (runCount hash
      (Seeded.oneTimePublicKey parameter lay tree leaf seed :
        OracleComp HashSpec (ChainIndex → Digest))).2 =
      numChains * chainLength := by
  simp only [Seeded.oneTimePublicKey, runCount_sequenceFin]
  have hterm (chainIdx : ChainIndex) :
      (runCount hash (do
        let secret ← (deriveKey parameter (.ots lay tree leaf chainIdx) seed :
          OracleComp HashSpec Digest)
        (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) secret :
          OracleComp HashSpec Digest))).2 = chainLength := by
    simp only [runCount_bind]
    rw [runCount_deriveKey]
    have hpath := runCount_chainWalk hash parameter lay tree leaf chainIdx 0
      (chainLength - 1) (runCount hash
        (deriveKey parameter (.ots lay tree leaf chainIdx) seed :
          OracleComp HashSpec Digest)).1 (by omega)
    rw [hpath]
    norm_num [chainLength, winternitzBits]
  have hcard : (Finset.univ : Finset ChainIndex).card = numChains := by
    simp [ChainIndex]
  simp_rw [hterm]
  simp [hcard]

def seededTreeNodeCalls (level : Nat) : Nat :=
  (numChains * chainLength + 2) * 2 ^ level - 1

theorem seededTreeNodeCalls_zero :
    seededTreeNodeCalls 0 = numChains * chainLength + 1 := by
  simp [seededTreeNodeCalls]

theorem seededTreeNodeCalls_succ (level : Nat) :
    seededTreeNodeCalls (level + 1) =
      seededTreeNodeCalls level + seededTreeNodeCalls level + 1 := by
  unfold seededTreeNodeCalls
  let x := (numChains * chainLength + 2) * 2 ^ level
  have hp : 0 < x := by dsimp [x]; positivity
  rw [pow_succ, ← mul_assoc]
  change x * 2 - 1 = (x - 1) + (x - 1) + 1
  omega

theorem runCount_treeNode (hash : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (level nodeIdx : Nat) :
    (runCount hash
      (Seeded.treeNode parameter lay tree seed level nodeIdx :
        OracleComp HashSpec Digest)).2 = seededTreeNodeCalls level := by
  induction level generalizing nodeIdx with
  | zero =>
    simp only [Seeded.treeNode, runCount_bind]
    rw [runCount_oneTimePublicKey]
    simp [leafHash, runCount_tweakableHash, seededTreeNodeCalls_zero]
  | succ level ih =>
    simp only [Seeded.treeNode, runCount_bind]
    rw [ih (2 * nodeIdx), ih (2 * nodeIdx + 1)]
    simp [runCount_tweakableHash, seededTreeNodeCalls_succ, Nat.add_assoc]

theorem runCount_treeRoot (hash : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) :
    (runCount hash
      (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest)).2 =
      seededTreeNodeCalls (layerHeight lay) := by
  exact runCount_treeNode hash parameter lay tree seed _ _

def seededTopPathCalls : Nat :=
  ∑ level : Fin (layerHeight topLayer), seededTreeNodeCalls level.val

theorem runCount_topPath (hash : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) :
    (runCount hash
      (Seeded.treePath parameter topLayer tree seed leaf :
        OracleComp HashSpec (Fin (layerHeight topLayer) → Digest))).2 =
      seededTopPathCalls := by
  simp only [Seeded.treePath, runCount_sequenceFin, seededTopPathCalls]
  apply Finset.sum_congr rfl
  intro level _
  exact runCount_treeNode hash parameter topLayer tree seed level.val _

theorem seededTopPathCalls_eq : seededTopPathCalls = 855635 := by
  decide

theorem seededFinalTreeCalls_eq :
    seededTreeNodeCalls (layerHeight topLayer) = 856063 := by
  decide

theorem runCount_topLayer_cost (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (index : Index)
    (cache : Nat → Nat → Digest) :
    (runCount hash
      (Seeded.signLayer secretKey index topLayer :
        OracleComp HashSpec (Option (LayerSignature topLayer)))).2 ≤
      (runCount hash
        (signTopWithCache secretKey index cache)).2 + seededTopPathCalls := by
  simp only [Seeded.signLayer, signTopWithCache, runCount_bind]
  cases hmessage : runCount hash
      (Seeded.layerMessage secretKey index topLayer : OracleComp HashSpec Digest) with
  | mk message messageCost =>
    simp only
    cases hots : runCount hash
        (Seeded.otsSign secretKey.parameter topLayer
          (treeIndexAt index topLayer) (leafIndexAt index topLayer)
          secretKey.seed message : OracleComp HashSpec
            (Option (Counter × (ChainIndex → Digest)))) with
    | mk option otsCost =>
      cases option with
      | none => simp [runCount_pure]
      | some result =>
        rcases result with ⟨counter, values⟩
        simp only [runCount_bind, runCount_pure, runCount_topPath]
        omega

theorem runCount_signLayers_cost (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (index : Index)
    (cache : Nat → Nat → Digest) :
    (runCount hash
      (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
        OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay)))).2 ≤
      (runCount hash
        (signLayersWithCache secretKey index cache)).2 + seededTopPathCalls := by
  simp only [Concrete.sequenceLayers, signLayersWithCache, runCount_bind]
  cases hb : runCount hash
      (Seeded.signLayer secretKey index bottomLayer :
        OracleComp HashSpec (Option (LayerSignature bottomLayer))) with
  | mk ob cb =>
    cases ob with
    | none => simp [runCount_pure]
    | some bottom =>
      simp only [runCount_bind]
      cases hm4 : runCount hash
          (Seeded.signLayer secretKey index middle4Layer :
            OracleComp HashSpec (Option (LayerSignature middle4Layer))) with
      | mk om4 cm4 =>
        cases om4 with
        | none => simp [runCount_pure]
        | some middle4 =>
          simp only [runCount_bind]
          cases hm3 : runCount hash
              (Seeded.signLayer secretKey index middle3Layer :
                OracleComp HashSpec (Option (LayerSignature middle3Layer))) with
          | mk om3 cm3 =>
            cases om3 with
            | none => simp [runCount_pure]
            | some middle3 =>
              simp only [runCount_bind]
              cases hm2 : runCount hash
                  (Seeded.signLayer secretKey index middle2Layer :
                    OracleComp HashSpec (Option (LayerSignature middle2Layer))) with
              | mk om2 cm2 =>
                cases om2 with
                | none => simp [runCount_pure]
                | some middle2 =>
                  simp only [runCount_bind]
                  cases hm : runCount hash
                      (Seeded.signLayer secretKey index middleLayer :
                        OracleComp HashSpec (Option (LayerSignature middleLayer))) with
                  | mk om cm =>
                    cases om with
                    | none => simp [runCount_pure]
                    | some middle =>
                      simp only [runCount_bind]
                      have htop := runCount_topLayer_cost hash secretKey index cache
                      cases hraw : runCount hash
                          (Seeded.signLayer secretKey index topLayer :
                            OracleComp HashSpec (Option (LayerSignature topLayer))) with
                      | mk ot ct =>
                        cases hc : runCount hash (signTopWithCache secretKey index cache) with
                        | mk oc cc =>
                          simp only [hraw, hc] at htop ⊢
                          cases ot <;> cases oc <;>
                            simp [runCount_pure] at htop ⊢ <;> omega


end SigGolfCandidate.CachedSignerTrace
