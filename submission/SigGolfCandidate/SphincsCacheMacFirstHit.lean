import SigGolfCandidate.SphincsCacheBlindMacGuess
import SigGolfCandidate.SphincsSecurity.Statement

/-! A fixed-oracle trace identity for adaptive blind MAC comparisons. Every
ordinary RO query and every MAC comparison uses the same hash function. -/

namespace SigGolfCandidate.SphincsCacheMacFirstHit
open SphincsSecurity OracleComp OracleSpec
open SigGolfCandidate.SphincsCacheBlindMacGuess

abbrev MacTestSpec := (HashInput × Digest) →ₒ Bool

def allFailureTrace {α : Type} (world : QueryImpl OracleWorld Id)
    (computation : OracleComp (OracleWorld + MacTestSpec) α) :
    List (HashInput × Digest) :=
  OracleComp.construct
    (fun _ => [])
    (fun input _ next =>
      match input with
      | .inl input => next (world input)
      | .inr test => test :: next false)
    computation

def firstHit {α : Type} (world : QueryImpl OracleWorld Id)
    (hash : QueryImpl HashSpec Id)
    (computation : OracleComp (OracleWorld + MacTestSpec) α) : Bool :=
  OracleComp.construct
    (fun _ => false)
    (fun input _ next =>
      match input with
      | .inl input => next (world input)
      | .inr test =>
        if truncateHash (hash test.1) = test.2 then true else next false)
    computation

theorem allFailureTrace_query_bind {α : Type}
    (world : QueryImpl OracleWorld Id)
    (input : (OracleWorld + MacTestSpec).Domain)
    (next : (OracleWorld + MacTestSpec).Range input →
      OracleComp (OracleWorld + MacTestSpec) α) :
    allFailureTrace world
      (liftM ((OracleWorld + MacTestSpec).query input) >>= next) =
      match input with
      | .inl input => allFailureTrace world (next (world input))
      | .inr test => test :: allFailureTrace world (next false) := by
  cases input <;> rfl

theorem firstHit_query_bind {α : Type}
    (world : QueryImpl OracleWorld Id) (hash : QueryImpl HashSpec Id)
    (input : (OracleWorld + MacTestSpec).Domain)
    (next : (OracleWorld + MacTestSpec).Range input →
      OracleComp (OracleWorld + MacTestSpec) α) :
    firstHit world hash
      (liftM ((OracleWorld + MacTestSpec).query input) >>= next) =
      match input with
      | .inl input => firstHit world hash (next (world input))
      | .inr test =>
        if truncateHash (hash test.1) = test.2 then true
        else firstHit world hash (next false) := by
  cases input <;> rfl

/-- Until the first successful altered-cache MAC comparison, the real adaptive
interaction follows the same branch as the all-failure trace. The full RO is
shared: direct hash queries may be interleaved arbitrarily, and repeated MAC
tests at one input see the same cached answer. -/
theorem first_hit_iff_all_failure_hit {α : Type}
    (world : QueryImpl OracleWorld Id) (hash : QueryImpl HashSpec Id)
    (computation : OracleComp (OracleWorld + MacTestSpec) α) :
    firstHit world hash computation = true ↔
      Hit (allFailureTrace world computation)
        (fun input => truncateHash (hash input)) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [firstHit, allFailureTrace, Hit]
  | query_bind input next ih =>
    cases input with
    | inl input =>
      simp only [firstHit_query_bind, allFailureTrace_query_bind]
      exact ih (world input)
    | inr test =>
      simp only [firstHit_query_bind, allFailureTrace_query_bind,
        hit_cons]
      by_cases hmatch : truncateHash (hash test.1) = test.2
      · simp [hmatch]
      · simp [hmatch, ih false]

theorem shared_world_hash (coins : QueryImpl unifSpec Id)
    (hash : QueryImpl HashSpec Id) (input : HashInput) :
    (coins + hash) (.inr input) = hash input := rfl

theorem first_hit_shared_ro {α : Type}
    (coins : QueryImpl unifSpec Id) (hash : QueryImpl HashSpec Id)
    (computation : OracleComp (OracleWorld + MacTestSpec) α) :
    firstHit (coins + hash) hash computation = true ↔
      Hit (allFailureTrace (coins + hash) computation)
        (fun input => truncateHash (hash input)) :=
  first_hit_iff_all_failure_hit (coins + hash) hash computation

end SigGolfCandidate.SphincsCacheMacFirstHit

/-- info: 'SigGolfCandidate.SphincsCacheMacFirstHit.first_hit_iff_all_failure_hit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacFirstHit.first_hit_iff_all_failure_hit
