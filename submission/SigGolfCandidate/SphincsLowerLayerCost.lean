import SigGolfCandidate.SphincsCachedSignTrace

namespace SigGolfCandidate.CachedSignerTrace
open OracleComp SphincsSecurity SphincsSecurity.Concrete
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def seededTreePathCalls (lay : Layer) : Nat :=
  ∑ level : Fin (layerHeight lay), seededTreeNodeCalls level.val

theorem runCount_treePath (hash : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (seed : MasterSeed) (leaf : LeafIndex) :
    (runCount hash
      (Seeded.treePath parameter lay tree seed leaf :
        OracleComp HashSpec (Fin (layerHeight lay) → Digest))).2 =
      seededTreePathCalls lay := by
  simp only [Seeded.treePath, runCount_sequenceFin, seededTreePathCalls]
  apply Finset.sum_congr rfl
  intro level _
  exact runCount_treeNode hash parameter lay tree seed level.val _

def lowerFiveTreePathCalls : Nat :=
  seededTreePathCalls bottomLayer + seededTreePathCalls middle4Layer +
    seededTreePathCalls middle3Layer + seededTreePathCalls middle2Layer +
    seededTreePathCalls middleLayer

theorem lowerFiveTreePathCalls_eq : lowerFiveTreePathCalls = 51391 := by
  decide

theorem lowerFiveTreePathCalls_large :
    1711698 ≤ 47 * lowerFiveTreePathCalls := by
  rw [lowerFiveTreePathCalls_eq]
  decide

/-- info: 'SigGolfCandidate.CachedSignerTrace.runCount_treePath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runCount_treePath

end SigGolfCandidate.CachedSignerTrace
