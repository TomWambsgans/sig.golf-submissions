import SigGolfCandidate.SphincsCostFullFloor
import SigGolfCandidate.SphincsCachedTopOverhead

namespace SigGolfCandidate.SphincsCachedLayersBridge
open OracleComp SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.CachedSignerTrace
open SigGolfCandidate.SphincsCachedSignValue
open SigGolfCandidate.SphincsCostComposition
open SigGolfCandidate.SphincsCostFullFloor

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Seeded.signLayer signTopWithCache

def finishWithTop (topProgram : OracleComp HashSpec (Option (LayerSignature topLayer)))
    (lower : LowerFiveResult) :
    OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay)) := by
  let ((((bottom, m4), m3), m2), m) := lower
  exact bindSome topProgram fun top =>
    pure (some (Fin.cases top (Fin.cases m
      (Fin.cases m2 (Fin.cases m3
        (Fin.cases m4 (Fin.cases bottom (fun i => Fin.elim0 i))))))))

theorem finishLayers_eq (secretKey : Seeded.SecretKey) (index : Index)
    (cache : Nat → Nat → Digest) (lower : LowerFiveResult) :
    finishLayers secretKey index cache lower =
      finishWithTop (signTopWithCache secretKey index cache) lower := by
  rfl

theorem rawLayers_eq (secretKey : Seeded.SecretKey) (index : Index) :
    (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
      OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))) =
    bindSome (lowerFive secretKey index)
      (finishWithTop (Seeded.signLayer secretKey index topLayer)) := by
  simp only [lowerFive, bindSome_appendSome_assoc]
  simp only [Concrete.sequenceLayers, finishWithTop, bindSome]
  apply congrArg (fun (continuation : Option (LayerSignature bottomLayer) →
    OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))) =>
      Seeded.signLayer secretKey index bottomLayer >>= continuation)
  funext bottomOption
  cases bottomOption with
  | none => rfl
  | some bottom =>
      apply congrArg (fun (continuation : Option (LayerSignature middle4Layer) →
        OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))) =>
          Seeded.signLayer secretKey index middle4Layer >>= continuation)
      funext m4Option
      cases m4Option with
      | none => rfl
      | some m4 =>
          apply congrArg (fun (continuation : Option (LayerSignature middle3Layer) →
            OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))) =>
              Seeded.signLayer secretKey index middle3Layer >>= continuation)
          funext m3Option
          cases m3Option with
          | none => rfl
          | some m3 =>
              apply congrArg (fun (continuation : Option (LayerSignature middle2Layer) →
                OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))) =>
                  Seeded.signLayer secretKey index middle2Layer >>= continuation)
              funext m2Option
              cases m2Option with
              | none => rfl
              | some m2 =>
                  apply congrArg (fun (continuation : Option (LayerSignature middleLayer) →
                    OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))) =>
                      Seeded.signLayer secretKey index middleLayer >>= continuation)
                  funext mOption
                  cases mOption with
                  | none => rfl
                  | some m =>
                      apply congrArg (fun (continuation : Option (LayerSignature topLayer) →
                        OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))) =>
                          Seeded.signLayer secretKey index topLayer >>= continuation)
                      funext topOption
                      cases topOption <;> rfl

theorem runCount_finishWithTop (hash : QueryImpl HashSpec Id)
    (topProgram : OracleComp HashSpec (Option (LayerSignature topLayer)))
    (lower : LowerFiveResult) :
    let top := runCount hash topProgram
    let result := runCount hash (finishWithTop topProgram lower)
    result.2 = top.2 ∧ result.1.isSome = top.1.isSome := by
  dsimp only
  unfold finishWithTop
  rw [runCount_bindSome]
  cases h : runCount hash topProgram with
  | mk result cost =>
      cases result <;> simp [h, runCount_pure]

theorem runCount_finishWithTop_relation (hash : QueryImpl HashSpec Id)
    (rawTop cachedTop : OracleComp HashSpec (Option (LayerSignature topLayer)))
    (lower : LowerFiveResult) (extra : Nat)
    (hvalue : (runCount hash rawTop).1.isSome =
      (runCount hash cachedTop).1.isSome)
    (hcost : (runCount hash rawTop).2 =
      (runCount hash cachedTop).2 +
        if (runCount hash cachedTop).1.isSome then extra else 0) :
    let raw := runCount hash (finishWithTop rawTop lower)
    let cached := runCount hash (finishWithTop cachedTop lower)
    raw.2 = cached.2 + if cached.1.isSome then extra else 0 := by
  dsimp only
  have hr := (runCount_finishWithTop hash rawTop lower).1
  have hc := runCount_finishWithTop hash cachedTop lower
  rw [hr, hc.1, hc.2]
  exact hcost

theorem runCount_bindSome_relation {α β : Type} (hash : QueryImpl HashSpec Id)
    (first : OracleComp HashSpec (Option α))
    (raw cached : α → OracleComp HashSpec (Option β)) (extra : Nat)
    (hnext : ∀ a,
      let r := runCount hash (raw a)
      let c := runCount hash (cached a)
      r.2 = c.2 + if c.1.isSome then extra else 0) :
    let r := runCount hash (bindSome first raw)
    let c := runCount hash (bindSome first cached)
    r.2 = c.2 + if c.1.isSome then extra else 0 := by
  dsimp only
  rw [runCount_bindSome, runCount_bindSome]
  cases hf : runCount hash first with
  | mk option firstCost =>
    cases option with
    | none => simp [hf]
    | some a =>
      simp only [hf]
      have h := hnext a
      dsimp only at h
      omega

/-- The only extra work in the raw layer sequence is the top authentication path. -/
theorem runCount_layers_exact (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (index : Index) :
    let cache := canonicalTopCache hash secretKey
    let raw := runCount hash
      (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
        OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay)))
    let cached := runCount hash (signLayersWithCache secretKey index cache)
    raw.1 = cached.1 ∧
      raw.2 = cached.2 + if cached.1.isSome then seededTopPathCalls else 0 := by
  dsimp only
  let cache := canonicalTopCache hash secretKey
  have hvalue :
      (runCount hash
        (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
          OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay)))).1 =
      (runCount hash (signLayersWithCache secretKey index cache)).1 := by
    rw [runCount_value, runCount_value]
    exact (signLayersWithCache_value hash secretKey index).symm
  refine ⟨hvalue, ?_⟩
  rw [rawLayers_eq, signLayersWithCache_eq]
  have hfinish : finishLayers secretKey index cache =
      finishWithTop (signTopWithCache secretKey index cache) := by
    funext lower
    exact finishLayers_eq secretKey index cache lower
  rw [hfinish]
  apply runCount_bindSome_relation
  intro lower
  have htopCost := runCount_topLayer_exact hash secretKey index cache
  have htopValue :
      (runCount hash
        (Seeded.signLayer secretKey index topLayer :
          OracleComp HashSpec (Option (LayerSignature topLayer)))).1 =
      (runCount hash (signTopWithCache secretKey index cache)).1 := by
    rw [runCount_value, runCount_value]
    exact (signTopWithCache_value hash secretKey index).symm
  exact runCount_finishWithTop_relation hash
    (Seeded.signLayer secretKey index topLayer)
    (signTopWithCache secretKey index cache) lower seededTopPathCalls
    (congrArg Option.isSome htopValue) htopCost

end SigGolfCandidate.SphincsCachedLayersBridge

/-- info: 'SigGolfCandidate.SphincsCachedLayersBridge.runCount_layers_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCachedLayersBridge.runCount_layers_exact
