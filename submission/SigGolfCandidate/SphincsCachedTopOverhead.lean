import SigGolfCandidate.SphincsCachedSignTrace

namespace SigGolfCandidate.CachedSignerTrace
open OracleComp SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCachedSignValue
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- The raw top-layer signer pays for the authentication path exactly when its OTS encoding succeeds. -/
theorem runCount_topLayer_exact (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (index : Index)
    (cache : Nat → Nat → Digest) :
    (runCount hash
      (Seeded.signLayer secretKey index topLayer :
        OracleComp HashSpec (Option (LayerSignature topLayer)))).2 =
      (runCount hash (signTopWithCache secretKey index cache)).2 +
        if (runCount hash (signTopWithCache secretKey index cache)).1.isSome
        then seededTopPathCalls else 0 := by
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
        simp [Nat.add_assoc]

end SigGolfCandidate.CachedSignerTrace

/-- info: 'SigGolfCandidate.CachedSignerTrace.runCount_topLayer_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.CachedSignerTrace.runCount_topLayer_exact
