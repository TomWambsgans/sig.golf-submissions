import SigGolfCandidate.SphincsCostComposition

namespace SigGolfCandidate.SphincsCostFullFloor
open OracleComp SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.CachedSignerTrace
open SigGolfCandidate.SphincsCachedSignValue
open SigGolfCandidate.SphincsCostComposition
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Seeded.signLayer signTopWithCache

abbrev LowerFiveResult :=
  (((LayerSignature bottomLayer × LayerSignature middle4Layer) ×
    LayerSignature middle3Layer) × LayerSignature middle2Layer) ×
    LayerSignature middleLayer

def finishLayers (secretKey : Seeded.SecretKey) (index : Index)
    (cache : Nat → Nat → Digest) (lower : LowerFiveResult) :
    OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay)) := by
  let ((((bottom, m4), m3), m2), m) := lower
  exact bindSome (signTopWithCache secretKey index cache) fun top =>
    pure (some (Fin.cases top (Fin.cases m
      (Fin.cases m2 (Fin.cases m3
        (Fin.cases m4 (Fin.cases bottom (fun i => Fin.elim0 i))))))))

theorem signLayersWithCache_eq (secretKey : Seeded.SecretKey)
    (index : Index) (cache : Nat → Nat → Digest) :
    signLayersWithCache secretKey index cache =
      bindSome (lowerFive secretKey index)
        (finishLayers secretKey index cache) := by
  simp only [lowerFive, bindSome_appendSome_assoc]
  simp only [signLayersWithCache, finishLayers, bindSome]
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
                          signTopWithCache secretKey index cache >>= continuation)
                      funext topOption
                      cases topOption <;> rfl

theorem signLayersWithCache_success_floor (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (index : Index)
    (cache : Nat → Nat → Digest)
    (success : (runCount hash (signLayersWithCache secretKey index cache)).1 ≠ none) :
    51391 ≤
      (runCount hash (signLayersWithCache secretKey index cache)).2 := by
  rw [signLayersWithCache_eq] at success ⊢
  rw [runCount_bindSome] at success ⊢
  cases h : runCount hash (lowerFive secretKey index) with
  | mk option cost =>
      cases option with
      | none => simp [h] at success
      | some lower =>
          have prefixFloor : 51391 ≤ cost := by
            have hprefix := lowerFive_success_floor hash secretKey index
              (by simp [h])
            rw [lowerFiveTreePathCalls_eq] at hprefix
            simpa only [h] using hprefix
          simp only [h]
          omega

/-- info: 'SigGolfCandidate.SphincsCostFullFloor.signLayersWithCache_success_floor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signLayersWithCache_success_floor

end SigGolfCandidate.SphincsCostFullFloor
