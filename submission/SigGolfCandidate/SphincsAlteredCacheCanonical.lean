import SigGolfCandidate.SphincsCachedSignValue
import SigGolfCandidate.SphincsCachedSignTraceSign
import SigGolfCandidate.SphincsCostFullFloor

namespace SigGolfCandidate.SphincsAlteredCacheCanonical
open OracleComp SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCachedSignValue
open SigGolfCandidate.SphincsCostFullFloor

set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Seeded.layerMessage Seeded.otsSign

/-- Only the selected top authentication path can affect this request's top-layer signature. -/
theorem signTopWithCache_eq_of_selected_path
    (secretKey : Seeded.SecretKey) (index : Index)
    (cache cache' : Nat → Nat → Digest)
    (hpath : topPathFromCache cache (leafIndexAt index topLayer) =
      topPathFromCache cache' (leafIndexAt index topLayer)) :
    signTopWithCache secretKey index cache =
      signTopWithCache secretKey index cache' := by
  simp only [signTopWithCache, bind_assoc]
  apply congrArg (fun continuation =>
    Seeded.layerMessage secretKey index topLayer >>= continuation)
  funext message
  apply congrArg (fun continuation =>
    Seeded.otsSign secretKey.parameter topLayer
      (treeIndexAt index topLayer) (leafIndexAt index topLayer)
      secretKey.seed message >>= continuation)
  funext result
  cases result with
  | none => rfl
  | some value =>
    rcases value with ⟨counter, values⟩
    simp [hpath]

theorem signLayersWithCache_eq_of_selected_path
    (secretKey : Seeded.SecretKey) (index : Index)
    (cache cache' : Nat → Nat → Digest)
    (hpath : topPathFromCache cache (leafIndexAt index topLayer) =
      topPathFromCache cache' (leafIndexAt index topLayer)) :
    signLayersWithCache secretKey index cache =
      signLayersWithCache secretKey index cache' := by
  rw [signLayersWithCache_eq secretKey index cache,
    signLayersWithCache_eq secretKey index cache']
  have htop := signTopWithCache_eq_of_selected_path secretKey index cache cache' hpath
  have hfinish : finishLayers secretKey index cache =
      finishLayers secretKey index cache' := by
    funext lower
    unfold finishLayers
    rw [htop]
  rw [hfinish]

theorem cachedTail_eq_of_selected_path
    (secretKey : Seeded.SecretKey) (cache cache' : Nat → Nat → Digest)
    (randomness : Randomness) (index : Index)
    (secrets : FtsTree → Digest)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (hpath : topPathFromCache cache (leafIndexAt index topLayer) =
      topPathFromCache cache' (leafIndexAt index topLayer)) :
    CachedSignerTrace.cachedTail secretKey cache
      (some (randomness, index, secrets, ftsPath)) =
      CachedSignerTrace.cachedTail secretKey cache'
        (some (randomness, index, secrets, ftsPath)) := by
  simp only [CachedSignerTrace.cachedTail]
  rw [signLayersWithCache_eq_of_selected_path secretKey index cache cache' hpath]

/-- For one signing request, only the path selected by the prefix affects the answer. -/
theorem runCount_signWithCache_eq_of_selected_path
    (hash : QueryImpl HashSpec Id) (secretKey : Seeded.SecretKey)
    (message : Message) (cache cache' : Nat → Nat → Digest)
    (hpath : ∀ (randomness : Randomness) (index : Index)
      (secrets : FtsTree → Digest)
      (ftsPath : FtsTree → Fin ftsTreeHeight → Digest),
      (CachedSignerTrace.runCount hash
        (CachedSignerTrace.signPrefix secretKey message)).1 =
          some (randomness, index, secrets, ftsPath) →
        topPathFromCache cache (leafIndexAt index topLayer) =
          topPathFromCache cache' (leafIndexAt index topLayer)) :
    CachedSignerTrace.runCount hash (signWithCache secretKey message cache) =
      CachedSignerTrace.runCount hash (signWithCache secretKey message cache') := by
  rw [CachedSignerTrace.cachedSign_eq_prefix_tail,
    CachedSignerTrace.cachedSign_eq_prefix_tail]
  simp only [CachedSignerTrace.runCount_bind]
  cases hp : CachedSignerTrace.runCount hash
      (CachedSignerTrace.signPrefix secretKey message) with
  | mk result cost =>
    cases result with
    | none => rfl
    | some data =>
      rcases data with ⟨randomness, index, secrets, ftsPath⟩
      have hselected := hpath randomness index secrets ftsPath (by simp [hp])
      rw [cachedTail_eq_of_selected_path secretKey cache cache'
        randomness index secrets ftsPath hselected]

end SigGolfCandidate.SphincsAlteredCacheCanonical

/-- info: 'SigGolfCandidate.SphincsAlteredCacheCanonical.signTopWithCache_eq_of_selected_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAlteredCacheCanonical.signTopWithCache_eq_of_selected_path

/-- info: 'SigGolfCandidate.SphincsAlteredCacheCanonical.signLayersWithCache_eq_of_selected_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAlteredCacheCanonical.signLayersWithCache_eq_of_selected_path

/-- info: 'SigGolfCandidate.SphincsAlteredCacheCanonical.runCount_signWithCache_eq_of_selected_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAlteredCacheCanonical.runCount_signWithCache_eq_of_selected_path
