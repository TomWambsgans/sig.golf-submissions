import SigGolfCandidate.SphincsCachedLayersBridge
import SigGolfCandidate.SphincsCachedTailOverhead

namespace SigGolfCandidate.CachedSignerTrace
open SphincsSecurity SphincsSecurity.Concrete

/-- The five lower paths amortize both omitted raw top-tree computations. -/
theorem layer_ratio_arithmetic {α : Type} (raw cached : Option α × Nat)
    (hvalue : raw.1 = cached.1)
    (hcost : raw.2 = cached.2 +
      if cached.1.isSome then seededTopPathCalls else 0)
    (hfloor : cached.1 ≠ none → 51391 ≤ cached.2) :
    raw.2 + (if raw.1.isSome then seededTreeNodeCalls (layerHeight topLayer) else 0) ≤
      48 * cached.2 := by
  have hextra : seededTopPathCalls +
      seededTreeNodeCalls (layerHeight topLayer) ≤ 47 * 51391 := by
    rw [seededTopPathCalls_eq, seededFinalTreeCalls_eq]
    norm_num
  rcases raw with ⟨rawResult, rawCost⟩
  rcases cached with ⟨cachedResult, cachedCost⟩
  simp only at hvalue hcost hfloor ⊢
  subst rawResult
  cases cachedResult with
  | none => simp at hcost ⊢; omega
  | some value =>
    have hlarge := hfloor (by simp)
    simp at hcost ⊢
    omega

end SigGolfCandidate.CachedSignerTrace

/-- info: 'SigGolfCandidate.CachedSignerTrace.layer_ratio_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.CachedSignerTrace.layer_ratio_arithmetic
