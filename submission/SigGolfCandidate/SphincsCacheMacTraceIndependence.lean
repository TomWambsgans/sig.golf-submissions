import SigGolfCandidate.SphincsCacheMacFirstHit
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.CacheCoupling
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.SeedGuessing

/-! The all-failure MAC plan does not depend on hidden oracle entries unless
the adversary directly queries one. This is a deterministic fixed-world fact;
the adaptive probability of such a direct query is bounded separately. -/

namespace SigGolfCandidate.SphincsCacheMacTraceIndependence
open SphincsSecurity OracleComp OracleSpec
open SigGolfCandidate.SphincsCacheMacFirstHit

def GoodPath {α : Type} (world : QueryImpl OracleWorld Id)
    (allowed : OracleWorld.Domain → Prop)
    (computation : OracleComp (OracleWorld + MacTestSpec) α) : Prop :=
  OracleComp.construct
    (fun _ => True)
    (fun input _ next =>
      match input with
      | .inl input => allowed input ∧ next (world input)
      | .inr _ => next false)
    computation

theorem GoodPath_query_bind {α : Type} (world : QueryImpl OracleWorld Id)
    (allowed : OracleWorld.Domain → Prop)
    (input : (OracleWorld + MacTestSpec).Domain)
    (next : (OracleWorld + MacTestSpec).Range input →
      OracleComp (OracleWorld + MacTestSpec) α) :
    GoodPath world allowed
      (liftM ((OracleWorld + MacTestSpec).query input) >>= next) =
      match input with
      | .inl input => allowed input ∧ GoodPath world allowed (next (world input))
      | .inr _ => GoodPath world allowed (next false) := by
  cases input <;> rfl

/-- The failure-path plan is insensitive to oracle-table changes outside
answers that the adversary may legitimately observe. -/
theorem allFailureTrace_congr {α : Type}
    (left right : QueryImpl OracleWorld Id)
    (allowed : OracleWorld.Domain → Prop)
    (hagrees : ∀ input, allowed input → left input = right input)
    (computation : OracleComp (OracleWorld + MacTestSpec) α)
    (hpath : GoodPath left allowed computation) :
    allFailureTrace left computation = allFailureTrace right computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    cases input with
    | inl input =>
      simp only [GoodPath_query_bind] at hpath
      simp only [allFailureTrace_query_bind]
      rw [← hagrees input hpath.1]
      exact ih (left input) hpath.2
    | inr test =>
      simp only [GoodPath_query_bind] at hpath
      simp only [allFailureTrace_query_bind]
      exact congrArg (List.cons test) (ih false hpath)

def seedSafe (seed : MasterSeed) : OracleWorld.Domain → Prop
  | .inl _ => True
  | .inr input => ¬ SeedHit input seed

theorem seeded_world_agrees (seed : MasterSeed)
    (coins : QueryImpl unifSpec Id)
    (left right : QueryImpl HashSpec Id)
    (hagrees : ∀ input, ¬SeedHit input seed → left input = right input) :
    ∀ input, seedSafe seed input →
      (coins + left) input = (coins + right) input := by
  intro input hsafe
  cases input with
  | inl _ => rfl
  | inr input => exact hagrees input hsafe

theorem allFailureTrace_seeded_congr {α : Type}
    (seed : MasterSeed) (coins : QueryImpl unifSpec Id)
    (left right : QueryImpl HashSpec Id)
    (hagrees : ∀ input, ¬SeedHit input seed → left input = right input)
    (computation : OracleComp (OracleWorld + MacTestSpec) α)
    (hpath : GoodPath (coins + left) (seedSafe seed) computation) :
    allFailureTrace (coins + left) computation =
      allFailureTrace (coins + right) computation :=
  allFailureTrace_congr (coins + left) (coins + right) (seedSafe seed)
    (seeded_world_agrees seed coins left right hagrees) computation hpath

end SigGolfCandidate.SphincsCacheMacTraceIndependence

/-- info: 'SigGolfCandidate.SphincsCacheMacTraceIndependence.allFailureTrace_seeded_congr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTraceIndependence.allFailureTrace_seeded_congr
