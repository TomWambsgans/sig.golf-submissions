import SigGolfCandidate.SphincsCachedSignTraceRequests

namespace SigGolfCandidate.CachedSignerTrace
open OracleComp SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCachedSignValue
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- The abstract signer's final top-tree recomputation runs only after all layers succeed. -/
theorem runCount_rawTail_exact (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (state : Option PrefixOutput) :
    (runCount hash (rawTail secretKey state)).2 =
      match state with
      | none => 0
      | some (_, index, _, _) =>
          let layers := runCount hash
            (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
              OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay)))
          layers.2 + if layers.1.isSome
            then seededTreeNodeCalls (layerHeight topLayer) else 0 := by
  cases state with
  | none => simp [rawTail, runCount_pure]
  | some data =>
    rcases data with ⟨randomness, index, secrets, ftsPath⟩
    simp only [rawTail, runCount_bind]
    cases h : runCount hash
        (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
          OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))) with
    | mk layers cost =>
      cases layers with
      | none => simp [runCount_pure]
      | some layers => simp [runCount_map, runCount_treeRoot]

end SigGolfCandidate.CachedSignerTrace

/-- info: 'SigGolfCandidate.CachedSignerTrace.runCount_rawTail_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.CachedSignerTrace.runCount_rawTail_exact

