import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Cached
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Support

namespace SphincsSecurity.Seeded
open OracleComp OracleSpec Concrete

private def parameterOfSeed (f : QueryImpl HashSpec Id) (seed : MasterSeed) : PublicParameter :=
  evalWithAnswerFn f (deriveKey 0 .parameter seed : OracleComp HashSpec PublicParameter)

theorem topTree_cached_of_keygen_cached (seed : MasterSeed)
    (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (h : CachedRun cache f (keygenFromSeed seed)) :
    CachedRun cache f (treeRoot (parameterOfSeed f seed) topLayer rootTree seed :
      OracleComp HashSpec Digest) := by
  unfold keygenFromSeed at h
  have htail := CachedRun.bind_right h
  exact CachedRun.bind_left htail

theorem topTree_cached_of_keygen_run (seed : MasterSeed)
    (initialCache : QueryCache HashSpec) (keys : PublicKey × SecretKey)
    (finalCache : QueryCache HashSpec)
    (hmem : (keys, finalCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) (keygenFromSeed seed)).run initialCache))
    (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f) :
    CachedRun finalCache f
      (treeRoot keys.1.parameter topLayer rootTree seed : OracleComp HashSpec Digest) := by
  obtain ⟨_, hkeys, hcached⟩ :=
    replay_of_mem_support (keygenFromSeed seed) initialCache keys finalCache hmem f hf
  have hparameter : keys.1.parameter = parameterOfSeed f seed := by
    rw [← hkeys]
    simp only [keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      parameterOfSeed]
    rfl
  rw [hparameter]
  exact topTree_cached_of_keygen_cached seed f finalCache hcached

theorem topTree_cached_for_signing_key (seed : MasterSeed)
    (initialCache : QueryCache HashSpec) (keys : PublicKey × SecretKey)
    (finalCache : QueryCache HashSpec)
    (hmem : (keys, finalCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) (keygenFromSeed seed)).run initialCache))
    (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f) :
    CachedRun finalCache f
      (treeRoot keys.2.parameter topLayer rootTree keys.2.seed : OracleComp HashSpec Digest) := by
  obtain ⟨_, hkeys, hcached⟩ :=
    replay_of_mem_support (keygenFromSeed seed) initialCache keys finalCache hmem f hf
  have hseed : keys.2.seed = seed := by
    rw [← hkeys]
    simp only [keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  have hparameter : keys.2.parameter = parameterOfSeed f seed := by
    rw [← hkeys]
    simp only [keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      parameterOfSeed]
    rfl
  rw [hseed, hparameter]
  exact topTree_cached_of_keygen_cached seed f finalCache hcached

end SphincsSecurity.Seeded

/-- info: 'SphincsSecurity.Seeded.topTree_cached_for_signing_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphincsSecurity.Seeded.topTree_cached_for_signing_key

/-- info: 'SphincsSecurity.Seeded.topTree_cached_of_keygen_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphincsSecurity.Seeded.topTree_cached_of_keygen_run

/-- info: 'SphincsSecurity.Seeded.topTree_cached_of_keygen_cached' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SphincsSecurity.Seeded.topTree_cached_of_keygen_cached
