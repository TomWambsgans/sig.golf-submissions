import SigGolfCandidate.SphincsCacheMacFinitePresampling
import SigGolfCandidate.SphincsCacheMacTraceIndependence

/-! On a path with no attacker-direct secret-seed query, pre-sampling any
finite set of seed-bearing MAC entries leaves the altered-cache all-failure
comparison plan unchanged. -/

namespace SigGolfCandidate.SphincsCacheMacFiniteTrace
open OracleComp OracleSpec SphincsSecurity SphincsSecurity.Seeded
open SigGolfCandidate.SphincsCacheMacFirstHit
open SigGolfCandidate.SphincsCacheMacTraceIndependence

def completedHash (cache : QueryCache HashSpec)
    (fallback : QueryImpl HashSpec Id) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD (fallback input)

theorem finite_cache_outside_seed {n : Nat}
    (seed : MasterSeed) (cache : QueryCache HashSpec)
    (inputs : Fin n → HashInput) (outputs : Fin n → HashOutput)
    (hsecret : ∀ i, SeedHit (inputs i) seed)
    (input : HashInput) (hsafe : ¬SeedHit input seed) :
    cacheFin cache inputs outputs input = cache input := by
  apply cacheFin_apply_of_not_mem
  intro i heq
  exact hsafe (heq ▸ hsecret i)

theorem allFailureTrace_presampled_congr {α : Type} {n : Nat}
    (seed : MasterSeed) (coins : QueryImpl unifSpec Id)
    (fallback : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec)
    (inputs : Fin n → HashInput) (outputs : Fin n → HashOutput)
    (hsecret : ∀ i, SeedHit (inputs i) seed)
    (computation : OracleComp (OracleWorld + MacTestSpec) α)
    (hpath : GoodPath (coins + completedHash cache fallback)
      (seedSafe seed) computation) :
    allFailureTrace (coins + completedHash cache fallback) computation =
      allFailureTrace
        (coins + completedHash (cacheFin cache inputs outputs) fallback)
        computation := by
  apply allFailureTrace_seeded_congr seed coins _ _ _ computation hpath
  intro input hsafe
  simp only [completedHash]
  rw [finite_cache_outside_seed seed cache inputs outputs hsecret input hsafe]

end SigGolfCandidate.SphincsCacheMacFiniteTrace

/-- info: 'SigGolfCandidate.SphincsCacheMacFiniteTrace.allFailureTrace_presampled_congr' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacFiniteTrace.allFailureTrace_presampled_congr
