import SigGolfCandidate.SphincsSeededNoMacQueries
import SigGolfCandidate.SphincsCacheMacTraceTargets
import SigGolfCandidate.SphincsCacheBlindMacGuess
import SigGolfCandidate.SphincsCacheMacUniformSplit
import SigGolfCandidate.SphincsCacheMacFirstHit
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.StoppedRun
import SigGolfCandidate.SphincsMaskedCacheProgramming
import SigGolfCandidate.SphincsCacheMacFinitePresampling
import SigGolfCandidate.SphincsCacheMacFreshness
import Mathlib.Data.List.OfFn
import VCVio.ProgramLogic.Relational.SimulateQ.Epsilon
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingProbability
import SigGolfCandidate.SphincsSecurity.Proof.Reference.FiniteHashWorld

/- BEGIN SigGolfCandidate.SphincsCacheMacSafeRun -/

/-! Lazy-oracle output does not depend on initial cache entries in a region
that the computation never queries. -/

namespace SigGolfCandidate.SphincsCacheMacSafeRun
open OracleComp OracleComp.DeferredSampling OracleSpec SphincsSecurity

def AgreeOutside (region : HashInput → Prop)
    (left right : QueryCache HashSpec) : Prop :=
  ∀ input, ¬ region input → left input = right input

def AvoidsFrom {α : Type} (region : HashInput → Prop)
    (before : QueryCache HashSpec) (computation : OracleComp HashSpec α) : Prop :=
  ∀ f : QueryImpl HashSpec Id, before.AgreesWithFn f →
    ∀ input, region input → input ∉ queriedInputs f computation

theorem agrees_after_update (region : HashInput → Prop)
    (left right : QueryCache HashSpec)
    (hagrees : AgreeOutside region left right)
    (input : HashInput) (answer : HashOutput) :
    AgreeOutside region (left.cacheQuery input answer)
      (right.cacheQuery input answer) := by
  intro target htarget
  by_cases heq : target = input
  · subst target
    simp [QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ heq,
      QueryCache.cacheQuery_of_ne _ _ heq]
    exact hagrees target htarget

theorem avoids_continuation {α : Type} (region : HashInput → Prop)
    (before after : QueryCache HashSpec)
    (hle : before ≤ after)
    (query : HashInput) (answer : HashOutput)
    (hanswer : after query = some answer)
    (next : HashOutput → OracleComp HashSpec α)
    (hsafe : AvoidsFrom region before
      (liftM (HashSpec.query query) >>= next)) :
    AvoidsFrom region after (next answer) := by
  intro f hf target htarget hmem
  have hfBefore : before.AgreesWithFn f :=
    fun input result hcached => hf (hle hcached)
  have hquery : f query = answer := hf hanswer
  have hwhole := hsafe f hfBefore target htarget
  apply hwhole
  rw [queriedInputs_query_bind, hquery]
  exact List.mem_cons_of_mem _ hmem

theorem safe_run_eq {α : Type} (region : HashInput → Prop)
    (computation : OracleComp HashSpec α)
    (left right : QueryCache HashSpec)
    (hagrees : AgreeOutside region left right)
    (hsafe : AvoidsFrom region left computation) :
    evalSPMF ((simulateQ randomOracle computation).run' left) =
      evalSPMF ((simulateQ randomOracle computation).run' right) := by
  induction computation using OracleComp.inductionOn generalizing left right with
  | pure value => simp
  | query_bind input next ih =>
      have hnot : ¬ region input := by
        intro hregion
        obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) left
        exact hsafe f hf input hregion (by
          rw [queriedInputs_query_bind]
          exact List.mem_cons_self)
      have heq := hagrees input hnot
      cases hcache : left input with
      | some answer =>
          have hright : right input = some answer := heq ▸ hcache
          have hs := avoids_continuation region left left le_rfl input answer
            hcache next hsafe
          simpa [simulateQ_bind, StateT.run'_eq, StateT.run_bind,
            OracleSpec.randomOracle, hcache, hright] using
            ih answer left right hagrees hs
      | none =>
          have hright : right input = none := heq ▸ hcache
          simp only [simulateQ_bind, simulateQ_spec_query,
            StateT.run'_eq, StateT.run_bind,
            OracleSpec.randomOracle,
            QueryImpl.withCaching_run_none uniformSampleImpl hcache,
            QueryImpl.withCaching_run_none uniformSampleImpl hright]
          simp only [map_eq_bind_pure_comp, bind_assoc]
          simp only [Function.comp_def, pure_bind, bind_pure_comp,
            ← StateT.run'_eq]
          apply evalSPMF_bind_congr_left
          intro answer
          have hle : left ≤ left.cacheQuery input answer :=
            QueryCache.le_cacheQuery left hcache
          have hs : AvoidsFrom region (left.cacheQuery input answer)
              (next answer) :=
            avoids_continuation region left (left.cacheQuery input answer)
              hle input answer (QueryCache.cacheQuery_self left input answer)
              next hsafe
          exact ih answer _ _
            (agrees_after_update region left right hagrees input answer) hs

end SigGolfCandidate.SphincsCacheMacSafeRun

/-- info: 'SigGolfCandidate.SphincsCacheMacSafeRun.safe_run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacSafeRun.safe_run_eq
/- END SigGolfCandidate.SphincsCacheMacSafeRun -/

/- BEGIN SigGolfCandidate.SphincsCacheMacPatchRun -/

/-! Joint lazy-RO cache coupling across a protected input region. -/

namespace SigGolfCandidate.SphincsCacheMacPatchRun
open OracleComp OracleComp.DeferredSampling OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacSafeRun

noncomputable def patch (region : HashInput → Prop)
    (table : HashInput → HashOutput) (cache : QueryCache HashSpec) :
    QueryCache HashSpec := by
  classical
  exact fun input => if region input then some (table input) else cache input

theorem patch_of_safe (region : HashInput → Prop)
    (table : HashInput → HashOutput) (cache : QueryCache HashSpec)
    (input : HashInput) (hsafe : ¬region input) :
    patch region table cache input = cache input := by
  simp [patch, hsafe]

theorem patch_cacheQuery_of_safe (region : HashInput → Prop)
    (table : HashInput → HashOutput) (cache : QueryCache HashSpec)
    (input : HashInput) (answer : HashOutput) (hsafe : ¬region input) :
    patch region table (cache.cacheQuery input answer) =
      (patch region table cache).cacheQuery input answer := by
  funext target
  by_cases htarget : region target
  · have hne : target ≠ input := by
      intro heq
      exact hsafe (heq ▸ htarget)
    simp [patch, htarget, QueryCache.cacheQuery_of_ne _ _ hne]
  · by_cases heq : target = input
    · subst target
      simp [patch, hsafe, QueryCache.cacheQuery_self]
    · simp [patch, htarget, QueryCache.cacheQuery_of_ne _ _ heq]

theorem patch_run_eq {α : Type}
    (region : HashInput → Prop) (table : HashInput → HashOutput)
    (computation : OracleComp HashSpec α)
    (cache : QueryCache HashSpec)
    (hsafe : AvoidsFrom region cache computation) :
    evalSPMF ((simulateQ randomOracle computation).run
      (patch region table cache)) =
    evalSPMF ((fun result => (result.1, patch region table result.2)) <$>
      (simulateQ randomOracle computation).run cache) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [simulateQ_pure, patch]
  | query_bind input next ih =>
      have hnot : ¬ region input := by
        intro hregion
        obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) cache
        exact hsafe f hf input hregion (by
          rw [queriedInputs_query_bind]
          exact List.mem_cons_self)
      cases hcache : cache input with
      | some answer =>
          have hs := avoids_continuation region cache cache le_rfl input answer
            hcache next hsafe
          simpa [simulateQ_bind, StateT.run_bind,
            OracleSpec.randomOracle, patch_of_safe, hnot, hcache]
            using ih answer cache hs
      | none =>
          have hpatchednone : patch region table cache input = none := by
            rw [patch_of_safe region table cache input hnot]
            exact hcache
          simp only [simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, OracleSpec.randomOracle,
            QueryImpl.withCaching_run_none uniformSampleImpl hcache,
            QueryImpl.withCaching_run_none uniformSampleImpl hpatchednone]
          simp only [map_eq_bind_pure_comp, bind_assoc]
          simp only [Function.comp_def, pure_bind, bind_pure_comp]
          apply evalSPMF_bind_congr_left
          intro answer
          have hle : cache ≤ cache.cacheQuery input answer :=
            QueryCache.le_cacheQuery cache hcache
          have hs : AvoidsFrom region (cache.cacheQuery input answer)
              (next answer) :=
            avoids_continuation region cache (cache.cacheQuery input answer)
              hle input answer (QueryCache.cacheQuery_self cache input answer)
              next hsafe
          rw [← patch_cacheQuery_of_safe region table cache input answer hnot]
          exact ih answer (cache.cacheQuery input answer) hs

end SigGolfCandidate.SphincsCacheMacPatchRun

/-- info: 'SigGolfCandidate.SphincsCacheMacPatchRun.patch_run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacPatchRun.patch_run_eq
/- END SigGolfCandidate.SphincsCacheMacPatchRun -/



/- BEGIN SigGolfCandidate.SphincsCacheMacGameCoupling -/

/-! The all-failure interaction is executable in the ordinary RO game: it
answers every altered-cache comparison `false` and records the guesses. -/

namespace SigGolfCandidate.SphincsCacheMacGameCoupling
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacFirstHit
open SphincsSecurity.Seeded
open SigGolfCandidate.SphincsCacheMacTraceTargets
open SigGolfCandidate.SphincsMaskedCacheProgramming
open SigGolfCandidate.SphincsCacheSecretDomains

def directSeedHit (seed : MasterSeed) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => SeedHit input seed

theorem romImpl_safe_query_preserves_fresh (seed : MasterSeed)
    (target : HashInput) (htarget : SeedHit target seed)
    (query : OracleWorld.Domain) (hsafe : ¬directSeedHit seed query)
    (cache : QueryCache HashSpec) (hfresh : cache target = none)
    (result : OracleWorld.Range query × QueryCache HashSpec)
    (hresult : result ∈ support ((romImpl query).run cache)) :
    result.2 target = none := by
  cases query with
  | inl input =>
      change result ∈ support ((unifFwdImpl HashSpec input).run cache) at hresult
      have hrun : (unifFwdImpl HashSpec input).run cache =
          (fun sample => (sample, cache)) <$>
            (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) := by
        simpa [simulateQ_query] using
          (unifFwdImpl.simulateQ_run
            (hashSpec := HashSpec)
            (liftM (unifSpec.query input) : ProbComp _) cache)
      rw [hrun, support_map] at hresult
      obtain ⟨sample, _, rfl⟩ := hresult
      exact hfresh
  | inr input =>
      have hne : target ≠ input := by
        intro heq
        exact hsafe (heq ▸ htarget)
      change result ∈ support ((randomOracle input).run cache) at hresult
      cases hcache : cache input with
      | some answer =>
          rw [OracleSpec.randomOracle,
            QueryImpl.withCaching_run_some _ hcache,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact hfresh
      | none =>
          rw [OracleSpec.randomOracle,
            QueryImpl.withCaching_run_none _ hcache,
            support_map] at hresult
          obtain ⟨answer, _, rfl⟩ := hresult
          change (cache.cacheQuery input answer) target = none
          rw [QueryCache.cacheQuery_of_ne _ _ hne]
          exact hfresh

theorem stopBefore_preserves_seed_target_fresh {α : Type}
    (seed : MasterSeed) (target : HashInput)
    [DecidablePred (directSeedHit seed)]
    (htarget : SeedHit target seed)
    (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfresh : cache target = none)
    (result : Option α × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ romImpl (stopBefore (directSeedHit seed) computation)).run cache)) :
    result.2 target = none := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simpa only [stopBefore_pure, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] using hresult ▸ hfresh
  | query_bind query next ih =>
      rw [stopBefore_query_bind] at hresult
      by_cases hbad : directSeedHit seed query
      · simp only [if_pos hbad, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hresult
        subst result
        exact hfresh
      · simp only [if_neg hbad, simulateQ_bind, simulateQ_spec_query,
          StateT.run_bind, mem_support_bind_iff] at hresult
        obtain ⟨middle, hquery, hrest⟩ := hresult
        exact ih middle.1 middle.2
          (romImpl_safe_query_preserves_fresh seed target htarget query hbad
            cache hfresh middle hquery) result hrest

def allFailureProgram {α : Type}
    (computation : OracleComp (OracleWorld + MacTestSpec) α) :
    OracleComp OracleWorld (α × List (HashInput × Digest)) :=
  OracleComp.construct
    (fun value => pure (value, []))
    (fun input _ next =>
      match input with
      | .inl query => do
          let answer ← liftM (OracleWorld.query query)
          next answer
      | .inr test => do
          let (value, attempts) ← next false
          pure (value, test :: attempts))
    computation

/-- The all-failure trace's changed MAC targets are still uncached after every
successful stopped run. The monitor counts only attacker-direct RO queries;
forced-false MAC comparisons perform no tag-15 oracle query. -/
theorem post_failure_trace_targets_fresh {α : Type}
    (seed : MasterSeed) [DecidablePred (directSeedHit seed)]
    (material : KeyMaterial)
    (pads : List (BitVec 32 × HashOutput))
    (canonicalBytes : HashInput) (macAnswer : HashOutput)
    (computation : OracleComp (OracleWorld + MacTestSpec) α)
    (result : Option (α × List (HashInput × Digest)) × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ romImpl
        (stopBefore (directSeedHit seed) (allFailureProgram computation))).run
        (maskedMaterialCache material seed pads canonicalBytes macAnswer)))
    (value : α) (attempts : List (HashInput × Digest))
    (hvalue : result.1 = some (value, attempts))
    (hformat : ∀ attempt ∈ attempts,
      ∃ candidateBytes, candidateBytes ≠ canonicalBytes ∧
        attempt.1 = macInput material.1 seed candidateBytes) :
    ∀ i : Fin (distinctKeys attempts).length,
      result.2 (keys attempts i) = none := by
  intro i
  apply stopBefore_preserves_seed_target_fresh seed (keys attempts i)
    (keys_are_seed_bearing attempts material.1 seed
      (fun attempt hmem => by
        obtain ⟨candidateBytes, _, hinput⟩ := hformat attempt hmem
        exact ⟨candidateBytes, hinput⟩) i)
    (allFailureProgram computation)
    (maskedMaterialCache material seed pads canonicalBytes macAnswer)
    (keys_are_fresh attempts material seed pads canonicalBytes macAnswer hformat i)
    result hresult

theorem allFailureProgram_query_bind {α : Type}
    (input : (OracleWorld + MacTestSpec).Domain)
    (next : (OracleWorld + MacTestSpec).Range input →
      OracleComp (OracleWorld + MacTestSpec) α) :
    allFailureProgram (liftM ((OracleWorld + MacTestSpec).query input) >>= next) =
      (match input with
      | .inl query => do
          let answer ← liftM (OracleWorld.query query)
          allFailureProgram (next answer)
      | .inr test => do
          let (value, attempts) ← allFailureProgram (next false)
          pure (value, test :: attempts)) := by
  cases input <;> rfl

theorem allFailureProgram_trace {α : Type}
    (world : QueryImpl OracleWorld Id)
    (computation : OracleComp (OracleWorld + MacTestSpec) α) :
    (evalWithAnswerFn world (allFailureProgram computation)).2 =
      allFailureTrace world computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl query =>
          simp only [allFailureProgram_query_bind,
            allFailureTrace_query_bind]
          simp only [evalWithAnswerFn_bind, ih]
          have hquery : evalWithAnswerFn world
              (liftM (OracleWorld.query query) : OracleComp OracleWorld _) =
              world query := rfl
          rw [hquery]
      | inr test =>
          simp only [allFailureProgram_query_bind,
            allFailureTrace_query_bind]
          simp [evalWithAnswerFn_bind, ih]

end SigGolfCandidate.SphincsCacheMacGameCoupling

/-- info: 'SigGolfCandidate.SphincsCacheMacGameCoupling.allFailureProgram_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacGameCoupling.allFailureProgram_trace

/-- info: 'SigGolfCandidate.SphincsCacheMacGameCoupling.stopBefore_preserves_seed_target_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacGameCoupling.stopBefore_preserves_seed_target_fresh

/-- info: 'SigGolfCandidate.SphincsCacheMacGameCoupling.post_failure_trace_targets_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacGameCoupling.post_failure_trace_targets_fresh
/- END SigGolfCandidate.SphincsCacheMacGameCoupling -/

/- BEGIN SigGolfCandidate.SphincsCacheMacThreeService -/

/-! A three-service outer interface. Attacker-direct RO queries and canonical
signing requests are separate syntactic queries. The seed-contact monitor runs
at this level, before canonical signing is interpreted into internal hashes. -/

namespace SigGolfCandidate.SphincsCacheMacThreeService
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacFirstHit
open SigGolfCandidate.SphincsCacheMacGameCoupling

abbrev OuterWorld := OracleWorld + SigningSpec
abbrev AttackWorld := OuterWorld + MacTestSpec

def allFailureOuter {α : Type} (computation : OracleComp AttackWorld α) :
    OracleComp OuterWorld (α × List (HashInput × Digest)) :=
  OracleComp.construct
    (fun value => pure (value, []))
    (fun input _ next =>
      match input with
      | .inl ordinary => do
          let answer ← liftM (OuterWorld.query ordinary)
          next answer
      | .inr test => do
          let (value, attempts) ← next false
          pure (value, test :: attempts))
    computation

def attackerDirectSeedHit (seed : MasterSeed) : OuterWorld.Domain → Prop
  | .inl (.inl _) => False
  | .inl (.inr input) => SeedHit input seed
  | .inr _ => False

noncomputable instance (seed : MasterSeed) :
    DecidablePred (attackerDirectSeedHit seed) := Classical.decPred _

noncomputable def stopBeforeDirect {α : Type} (seed : MasterSeed)
    (computation : OracleComp OuterWorld α) :
    OracleComp OuterWorld (Option α) := by
  classical
  exact OracleComp.construct
    (fun value => pure (some value))
    (fun input _ next =>
      if attackerDirectSeedHit seed input then pure none else do
        let answer ← liftM (OuterWorld.query input)
        next answer)
    computation

theorem stopBeforeDirect_signing_query {α : Type}
    (seed : MasterSeed) (message : Message)
    (next : (OuterWorld.Range (.inr message)) → OracleComp OuterWorld α) :
    stopBeforeDirect seed
      (liftM (OuterWorld.query (.inr message)) >>= next) =
      (do
        let answer ← liftM (OuterWorld.query (.inr message))
        stopBeforeDirect seed (next answer)) := by
  classical
  simp [stopBeforeDirect, attackerDirectSeedHit]

theorem stopBeforeDirect_hash_query {α : Type}
    (seed : MasterSeed) (input : HashInput)
    [Decidable (SeedHit input seed)]
    (next : (OuterWorld.Range (.inl (.inr input))) → OracleComp OuterWorld α) :
    stopBeforeDirect seed
      (liftM (OuterWorld.query (.inl (.inr input))) >>= next) =
      (if SeedHit input seed then pure none else do
        let answer ← liftM (OuterWorld.query (.inl (.inr input)))
        stopBeforeDirect seed (next answer)) := by
  classical
  by_cases h : SeedHit input seed <;>
    simp [stopBeforeDirect, attackerDirectSeedHit, h]

theorem stopBeforeDirect_query_bind {α : Type}
    (seed : MasterSeed) (input : OuterWorld.Domain)
    (next : OuterWorld.Range input → OracleComp OuterWorld α) :
    stopBeforeDirect seed (liftM (OuterWorld.query input) >>= next) =
      (if attackerDirectSeedHit seed input then pure none else do
        let answer ← liftM (OuterWorld.query input)
        stopBeforeDirect seed (next answer)) := by
  classical
  by_cases h : attackerDirectSeedHit seed input <;>
    simp [stopBeforeDirect, h]

theorem stopBeforeDirect_preserves_fresh {α : Type}
    (seed : MasterSeed) (target : HashInput)
    (htarget : SeedHit target seed)
    (signImpl : QueryImpl SigningSpec
      (StateT (QueryCache HashSpec) ProbComp))
    (hsign : ∀ message cache,
      cache target = none →
      ∀ result ∈ support ((signImpl message).run cache),
        result.2 target = none)
    (computation : OracleComp OuterWorld α)
    (cache : QueryCache HashSpec) (hfresh : cache target = none)
    (result : Option α × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ (romImpl + signImpl)
        (stopBeforeDirect seed computation)).run cache)) :
    result.2 target = none := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simpa only [stopBeforeDirect, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] using hresult ▸ hfresh
  | query_bind query next ih =>
      rw [stopBeforeDirect_query_bind] at hresult
      by_cases hbad : attackerDirectSeedHit seed query
      · simp only [if_pos hbad, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hresult
        subst result
        exact hfresh
      · simp only [if_neg hbad, simulateQ_bind, simulateQ_spec_query,
          StateT.run_bind, mem_support_bind_iff] at hresult
        obtain ⟨middle, hquery, hrest⟩ := hresult
        have hmiddle : middle.2 target = none := by
          cases query with
          | inl direct =>
              have hsafe : ¬directSeedHit seed direct := by
                cases direct with
                | inl sample => simp [directSeedHit]
                | inr input =>
                    simpa [attackerDirectSeedHit, directSeedHit] using hbad
              exact romImpl_safe_query_preserves_fresh seed target htarget direct
                hsafe cache hfresh middle hquery
          | inr message =>
              exact hsign message cache hfresh middle hquery
        exact ih middle.1 middle.2 hmiddle result hrest

end SigGolfCandidate.SphincsCacheMacThreeService

/-- info: 'SigGolfCandidate.SphincsCacheMacThreeService.stopBeforeDirect_signing_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacThreeService.stopBeforeDirect_signing_query

/-- info: 'SigGolfCandidate.SphincsCacheMacThreeService.stopBeforeDirect_preserves_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacThreeService.stopBeforeDirect_preserves_fresh
/- END SigGolfCandidate.SphincsCacheMacThreeService -/

/- BEGIN SigGolfCandidate.SphincsCacheMacStoppedGeneric -/

/-! Lift a cache-patch commutation across the attacker-direct SeedHit stopper.
The step premise is required only for queries that pass the stopper. -/

namespace SigGolfCandidate.SphincsCacheMacStoppedGeneric
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsCacheMacPatchRun

theorem stopped_patch_run_eq {α : Type}
    (region : HashInput → Prop) (table : HashInput → HashOutput)
    (seed : MasterSeed)
    (impl : QueryImpl OuterWorld
      (StateT (QueryCache HashSpec) ProbComp))
    (hstep : ∀ query before,
      ¬attackerDirectSeedHit seed query →
      evalSPMF ((impl query).run (patch region table before)) =
      evalSPMF ((fun result => (result.1, patch region table result.2)) <$>
        (impl query).run before))
    (computation : OracleComp OuterWorld α)
    (before : QueryCache HashSpec) :
    evalSPMF ((simulateQ impl (stopBeforeDirect seed computation)).run
      (patch region table before)) =
    evalSPMF ((fun result => (result.1, patch region table result.2)) <$>
      (simulateQ impl (stopBeforeDirect seed computation)).run before) := by
  induction computation using OracleComp.inductionOn generalizing before with
  | pure value => simp [stopBeforeDirect, simulateQ_pure]
  | query_bind query next ih =>
      rw [stopBeforeDirect_query_bind]
      by_cases hbad : attackerDirectSeedHit seed query
      · simp [hbad, simulateQ_pure]
      · simp only [if_neg hbad, simulateQ_bind, simulateQ_spec_query,
          StateT.run_bind, map_bind]
        calc
          _ = evalSPMF (do
            let p ← (fun (result : OuterWorld.Range query × QueryCache HashSpec) =>
              (result.1, patch region table result.2)) <$>
                (impl query).run before
            (simulateQ impl (stopBeforeDirect seed (next p.1))).run p.2) := by
              rw [evalSPMF_bind, evalSPMF_bind,
                hstep query before hbad]
          _ = evalSPMF (do
            let a ← (impl query).run before
            (simulateQ impl (stopBeforeDirect seed (next a.1))).run
              (patch region table a.2)) := by
                simp only [bind_map_left]
          _ = _ := by
            apply evalSPMF_bind_congr'
            intro a
            exact ih a.1 a.2

end SigGolfCandidate.SphincsCacheMacStoppedGeneric

/-- info: 'SigGolfCandidate.SphincsCacheMacStoppedGeneric.stopped_patch_run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacStoppedGeneric.stopped_patch_run_eq
/- END SigGolfCandidate.SphincsCacheMacStoppedGeneric -/

/- BEGIN SigGolfCandidate.SphincsCacheMacFiniteDomain -/

/-! Symbolic finite domain of altered fixed-length cache ciphertexts. No table
entries are enumerated or evaluated. -/

namespace SigGolfCandidate.SphincsCacheMacFiniteDomain
open OracleComp OracleComp.DeferredSampling OracleSpec SphincsSecurity
open SphincsSecurity.Seeded
open SigGolfCandidate.SphincsCacheSecretDomains
open SigGolfCandidate.SphincsMaskedCacheProgramming
open SigGolfCandidate.SphincsCacheMacFreshness
open SigGolfCandidate.SphincsCacheMacFinitePresampling
open SigGolfCandidate.SphincsCacheBlindMacGuess

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def authenticatedBytes : Nat := 2 ^ 17 - 20
abbrev Ciphertext := Fin authenticatedBytes → UInt8

abbrev Altered (canonical : Ciphertext) :=
  {ciphertext : Ciphertext // ciphertext ≠ canonical}

noncomputable instance (canonical : Ciphertext) : Fintype (Altered canonical) := by
  classical exact inferInstance

def alteredInput (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext) (candidate : Altered canonical) : HashInput :=
  macInput parameter seed (List.ofFn candidate.1)

theorem alteredInput_injective (parameter : PublicParameter)
    (seed : MasterSeed) (canonical : Ciphertext) :
    Function.Injective (alteredInput parameter seed canonical) := by
  intro left right heq
  apply Subtype.ext
  exact List.ofFn_injective (macInput_injective_ciphertext parameter seed heq)

theorem alteredInput_ne_canonical (parameter : PublicParameter)
    (seed : MasterSeed) (canonical : Ciphertext)
    (candidate : Altered canonical) :
    alteredInput parameter seed canonical candidate ≠
      macInput parameter seed (List.ofFn canonical) := by
  intro heq
  apply candidate.2
  exact List.ofFn_injective (macInput_injective_ciphertext parameter seed heq)

theorem alteredInput_seedHit (parameter : PublicParameter)
    (seed : MasterSeed) (canonical : Ciphertext)
    (candidate : Altered canonical) :
    SeedHit (alteredInput parameter seed canonical candidate) seed :=
  macInput_seedHit parameter seed (List.ofFn candidate.1)

theorem alteredInput_fresh (material : Seeded.KeyMaterial)
    (seed : MasterSeed) (pads : List (BitVec 32 × HashOutput))
    (canonical : Ciphertext) (macAnswer : HashOutput)
    (candidate : Altered canonical) :
    maskedMaterialCache material seed pads (List.ofFn canonical) macAnswer
      (alteredInput material.1 seed canonical candidate) = none := by
  exact maskedMaterialCache_altered_fresh seed material pads
    (List.ofFn canonical) (List.ofFn candidate.1) macAnswer
    (List.ofFn_injective.ne candidate.2)

noncomputable def allAlteredInputs (parameter : PublicParameter)
    (seed : MasterSeed) (canonical : Ciphertext) :
    Fin (Fintype.card (Altered canonical)) → HashInput :=
  fun i => alteredInput parameter seed canonical
    ((Fintype.equivFin (Altered canonical)).symm i)

theorem allAlteredInputs_injective (parameter : PublicParameter)
    (seed : MasterSeed) (canonical : Ciphertext) :
    Function.Injective (allAlteredInputs parameter seed canonical) :=
  (alteredInput_injective parameter seed canonical).comp
    (Fintype.equivFin (Altered canonical)).symm.injective

theorem allAlteredInputs_fresh (material : Seeded.KeyMaterial)
    (seed : MasterSeed) (pads : List (BitVec 32 × HashOutput))
    (canonical : Ciphertext) (macAnswer : HashOutput)
    (i : Fin (Fintype.card (Altered canonical))) :
    maskedMaterialCache material seed pads (List.ofFn canonical) macAnswer
      (allAlteredInputs material.1 seed canonical i) = none :=
  alteredInput_fresh material seed pads canonical macAnswer _

theorem presample_all_altered {α : Type}
    (material : Seeded.KeyMaterial) (seed : MasterSeed)
    (pads : List (BitVec 32 × HashOutput))
    (canonical : Ciphertext) (macAnswer : HashOutput)
    (computation : OracleComp OracleWorld α) :
    evalSPMF ((simulateQ romImpl computation).run'
      (maskedMaterialCache material seed pads (List.ofFn canonical) macAnswer)) =
    evalSPMF (do
      let outputs ← Concrete.sequenceFin fun _ :
        Fin (Fintype.card (Altered canonical)) =>
        ($ᵗ HashOutput : ProbComp HashOutput)
      (simulateQ romImpl computation).run'
        (cacheFin
          (maskedMaterialCache material seed pads (List.ofFn canonical) macAnswer)
          (allAlteredInputs material.1 seed canonical) outputs)) := by
  exact presampleFin computation _
    (allAlteredInputs material.1 seed canonical)
    (allAlteredInputs_injective material.1 seed canonical)
    (allAlteredInputs_fresh material seed pads canonical macAnswer)

theorem uniform_altered_marginal (canonical : Ciphertext)
    (candidate : Altered canonical) (guess : Digest) :
    Pr[fun table : Altered canonical → Digest => table candidate = guess |
      ($ᵗ (Altered canonical → Digest) : ProbComp _)] =
      (Fintype.card Digest : ENNReal)⁻¹ := by
  classical
  have h := OracleComp.evalSPMF_uniformSample_bind_update_map
    (D := Altered canonical) (R := Digest) candidate
    (fun table : Altered canonical → Digest => table candidate)
  have hsimple :
      evalSPMF (do
        let u ← ($ᵗ Digest : ProbComp Digest)
        let g ← ($ᵗ (Altered canonical → Digest) : ProbComp _)
        pure ((Function.update g candidate u) candidate)) =
      evalSPMF ($ᵗ Digest : ProbComp Digest) := by
    simp only [Function.update_self]
    calc
      _ = evalSPMF (($ᵗ Digest : ProbComp Digest) >>= fun u => pure u) := by
        apply evalSPMF_bind_congr_left
        intro u
        simpa only [bind_pure_comp] using
          evalSPMF_bind_const_neverFails
            ($ᵗ (Altered canonical → Digest) : ProbComp _)
            (probFailure_uniformSample (α := Altered canonical → Digest)) (pure u)
      _ = _ := by simp
  have hdist :
      evalSPMF ((fun table : Altered canonical → Digest => table candidate) <$>
        ($ᵗ (Altered canonical → Digest) : ProbComp _)) =
      evalSPMF ($ᵗ Digest : ProbComp Digest) := by
    calc
      _ = evalSPMF (do
          let g ← ($ᵗ (Altered canonical → Digest) : ProbComp _)
          pure (g candidate)) := by simp only [evalSPMF_map, bind_pure_comp]
      _ = _ := h.symm.trans hsimple
  rw [show (fun table : Altered canonical → Digest => table candidate = guess) =
    (fun digest => digest = guess) ∘
      (fun table : Altered canonical → Digest => table candidate) from rfl,
    ← probEvent_map]
  rw [probEvent_eq_eq_probOutput]
  exact (evalSPMF_ext_iff.mp hdist guess).trans
    (probOutput_uniformSample Digest guess)

theorem uniform_altered_marginal_pmf (canonical : Ciphertext)
    (candidate : Altered canonical) (guess : Digest) :
    Pr[fun table : Altered canonical → Digest => table candidate = guess |
      PMF.uniformOfFintype (Altered canonical → Digest)] =
      (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [probEvent_def, evalSPMF_uniformSample,
    SPMF.probEvent_liftM] using
      uniform_altered_marginal canonical candidate guess

theorem ideal_altered_blind_bound {Env : Type}
    (canonical : Ciphertext) (environment : PMF Env)
    (plan : Env → List (Altered canonical × Digest))
    (q : Nat) (hbudget : ∀ env, (plan env).length ≤ q) :
    Pr[fun result => Hit (plan result.1) result.2 |
      (do
        let env ← (liftM environment : SPMF Env)
        let table ← (liftM (PMF.uniformOfFintype (Altered canonical → Digest)) :
          SPMF (Altered canonical → Digest))
        pure (env, table))] ≤
      q * (Fintype.card Digest : ENNReal)⁻¹ := by
  exact adaptive_blind_bound environment
    (PMF.uniformOfFintype (Altered canonical → Digest)) plan
    (fun i guess => (uniform_altered_marginal_pmf canonical i guess).le)
    q hbudget

end SigGolfCandidate.SphincsCacheMacFiniteDomain

/-- info: 'SigGolfCandidate.SphincsCacheMacFiniteDomain.presample_all_altered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacFiniteDomain.presample_all_altered

/-- info: 'SigGolfCandidate.SphincsCacheMacFiniteDomain.uniform_altered_marginal_pmf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacFiniteDomain.uniform_altered_marginal_pmf

/-- info: 'SigGolfCandidate.SphincsCacheMacFiniteDomain.ideal_altered_blind_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacFiniteDomain.ideal_altered_blind_bound
/- END SigGolfCandidate.SphincsCacheMacFiniteDomain -/

/- BEGIN SigGolfCandidate.SphincsCacheMacPrePost -/

/-! A protected RO table can be sampled before or after a computation that
never queries its region. The result retains the final lazy-oracle cache. -/

namespace SigGolfCandidate.SphincsCacheMacPrePost
open OracleComp OracleComp.DeferredSampling OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacSafeRun
open SigGolfCandidate.SphincsCacheMacPatchRun

theorem prepost_table {α Table : Type}
    (region : HashInput → Prop)
    (encode : Table → HashInput → HashOutput)
    (draw : ProbComp Table)
    (computation : OracleComp HashSpec α)
    (cache : QueryCache HashSpec)
    (hsafe : AvoidsFrom region cache computation) :
    evalSPMF (do
      let table ← draw
      let result ← (simulateQ randomOracle computation).run
        (patch region (encode table) cache)
      pure (table, result)) =
    evalSPMF (do
      let result ← (simulateQ randomOracle computation).run cache
      let table ← draw
      pure (table, (result.1, patch region (encode table) result.2))) := by
  calc
    _ = evalSPMF (do
      let table ← draw
      let result ← (simulateQ randomOracle computation).run cache
      pure (table, (result.1, patch region (encode table) result.2))) := by
        apply evalSPMF_bind_congr_left
        intro table
        simpa [Function.comp_def, bind_assoc] using
          evalSPMF_map_eq_of_evalSPMF_eq
            (patch_run_eq region (encode table) computation cache hsafe)
            (fun result => (table, result))
    _ = _ := evalSPMF_bind_comm draw
      ((simulateQ randomOracle computation).run cache)
      (fun table result => pure
        (table, (result.1, patch region (encode table) result.2)))

end SigGolfCandidate.SphincsCacheMacPrePost

/-- info: 'SigGolfCandidate.SphincsCacheMacPrePost.prepost_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacPrePost.prepost_table
/- END SigGolfCandidate.SphincsCacheMacPrePost -/

/- BEGIN SigGolfCandidate.SphincsCacheMacSignerPrePost -/

/-! The actual inherited canonical signer is transparent to the entire
altered-ciphertext cache-MAC region, including its final lazy-RO cache. -/

namespace SigGolfCandidate.SphincsCacheMacSignerPrePost
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacFiniteDomain
open SigGolfCandidate.SphincsCacheMacSafeRun
open SigGolfCandidate.SphincsCacheMacPrePost
open SigGolfCandidate.SphincsSeededNoMacQueries

def alteredRegion (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext) (input : HashInput) : Prop :=
  ∃ candidate : Altered canonical,
    input = alteredInput parameter seed canonical candidate

theorem seeded_sign_avoids_altered_region
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (secretKey : Seeded.SecretKey) (message : Message)
    (before : QueryCache HashSpec) :
    AvoidsFrom (alteredRegion parameter seed canonical) before
      (Seeded.sign secretKey message) := by
  intro f _ input hregion hmem
  obtain ⟨candidate, hinput⟩ := hregion
  subst input
  exact seeded_sign_avoids_mac f secretKey message
    parameter seed (List.ofFn candidate.1) hmem

theorem not_altered_of_not_seedHit
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext) (input : HashInput)
    (hsafe : ¬SeedHit input seed) :
    ¬alteredRegion parameter seed canonical input := by
  rintro ⟨candidate, hinput⟩
  exact hsafe (hinput ▸ alteredInput_seedHit parameter seed canonical candidate)

theorem direct_hash_avoids_altered_region
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext) (input : HashInput)
    (before : QueryCache HashSpec)
    (hsafe : ¬SeedHit input seed) :
    AvoidsFrom (alteredRegion parameter seed canonical) before
      (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) := by
  intro f _ target hregion hmem
  have heq : target = input := by
    change target ∈ input :: [] at hmem
    simpa using hmem
  subst target
  exact not_altered_of_not_seedHit parameter seed canonical input hsafe hregion

theorem direct_hash_prepost {Table : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext) (input : HashInput)
    (before : QueryCache HashSpec)
    (hsafe : ¬SeedHit input seed)
    (draw : ProbComp Table)
    (encode : Table → HashInput → HashOutput) :
    evalSPMF (do
      let table ← draw
      let result ← (simulateQ randomOracle
        (liftM (HashSpec.query input))).run
        (SigGolfCandidate.SphincsCacheMacPatchRun.patch
          (alteredRegion parameter seed canonical) (encode table) before)
      pure (table, result)) =
    evalSPMF (do
      let result ← (simulateQ randomOracle
        (liftM (HashSpec.query input))).run before
      let table ← draw
      pure (table, (result.1,
        SigGolfCandidate.SphincsCacheMacPatchRun.patch
          (alteredRegion parameter seed canonical) (encode table) result.2))) := by
  exact prepost_table (alteredRegion parameter seed canonical) encode draw
    (liftM (HashSpec.query input)) before
    (direct_hash_avoids_altered_region parameter seed canonical input before hsafe)

theorem canonical_signer_prepost {Table : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext) (secretKey : Seeded.SecretKey)
    (message : Message) (before : QueryCache HashSpec)
    (draw : ProbComp Table)
    (encode : Table → HashInput → HashOutput) :
    evalSPMF (do
      let table ← draw
      let result ← (canonicalSigner secretKey message).run
        (SigGolfCandidate.SphincsCacheMacPatchRun.patch
          (alteredRegion parameter seed canonical) (encode table) before)
      pure (table, result)) =
    evalSPMF (do
      let result ← (canonicalSigner secretKey message).run before
      let table ← draw
      pure (table, (result.1,
        SigGolfCandidate.SphincsCacheMacPatchRun.patch
          (alteredRegion parameter seed canonical) (encode table) result.2))) := by
  exact prepost_table (alteredRegion parameter seed canonical) encode draw
    (Seeded.sign secretKey message) before
    (seeded_sign_avoids_altered_region parameter seed canonical
      secretKey message before)

end SigGolfCandidate.SphincsCacheMacSignerPrePost

/-- info: 'SigGolfCandidate.SphincsCacheMacSignerPrePost.canonical_signer_prepost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacSignerPrePost.canonical_signer_prepost

/-- info: 'SigGolfCandidate.SphincsCacheMacSignerPrePost.direct_hash_prepost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacSignerPrePost.direct_hash_prepost
/- END SigGolfCandidate.SphincsCacheMacSignerPrePost -/

/- BEGIN SigGolfCandidate.SphincsCacheMacStoppedActual -/

/-! Instantiate stopped cache-patch coupling for the actual inherited RO and
canonical seeded signer. -/

namespace SigGolfCandidate.SphincsCacheMacStoppedActual
open OracleComp OracleComp.DeferredSampling OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsCacheMacPatchRun
open SigGolfCandidate.SphincsCacheMacSignerPrePost
open SigGolfCandidate.SphincsCacheMacStoppedGeneric
open SigGolfCandidate.SphincsSeededNoMacQueries

theorem actual_safe_step
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : SigGolfCandidate.SphincsCacheMacFiniteDomain.Ciphertext)
    (secretKey : Seeded.SecretKey)
    (table : HashInput → HashOutput)
    (query : OuterWorld.Domain)
    (before : QueryCache HashSpec)
    (hsafe : ¬attackerDirectSeedHit seed query) :
    evalSPMF (((romImpl + canonicalSigner secretKey) query).run
      (patch (alteredRegion parameter seed canonical) table before)) =
    evalSPMF ((fun result => (result.1,
      patch (alteredRegion parameter seed canonical) table result.2)) <$>
      ((romImpl + canonicalSigner secretKey) query).run before) := by
  cases query with
  | inl ordinary =>
      cases ordinary with
      | inl coin =>
          change evalSPMF ((unifFwdImpl HashSpec coin).run
            (patch (alteredRegion parameter seed canonical) table before)) =
            evalSPMF ((fun result => (result.1,
              patch (alteredRegion parameter seed canonical) table result.2)) <$>
              (unifFwdImpl HashSpec coin).run before)
          have hrun (cache : QueryCache HashSpec) :
              (unifFwdImpl HashSpec coin).run cache =
                (fun answer => (answer, cache)) <$>
                  (liftM (unifSpec.query coin) : ProbComp _) := by
            simpa [simulateQ_query, OracleSpec.query] using
              (unifFwdImpl.simulateQ_run
                (hashSpec := HashSpec)
                (liftM (unifSpec.query coin) : ProbComp _) cache)
          rw [hrun, hrun]
          simp [Function.comp_def]
      | inr input =>
          have hseed : ¬SeedHit input seed := by
            simpa [attackerDirectSeedHit] using hsafe
          change evalSPMF ((randomOracle input).run
            (patch (alteredRegion parameter seed canonical) table before)) =
            evalSPMF ((fun result => (result.1,
              patch (alteredRegion parameter seed canonical) table result.2)) <$>
              (randomOracle input).run before)
          simpa [simulateQ_query, OracleSpec.query] using
            (patch_run_eq (alteredRegion parameter seed canonical) table
              (liftM (HashSpec.query input)) before
              (direct_hash_avoids_altered_region parameter seed canonical input before hseed))
  | inr message =>
      change evalSPMF ((canonicalSigner secretKey message).run
        (patch (alteredRegion parameter seed canonical) table before)) =
        evalSPMF ((fun result => (result.1,
          patch (alteredRegion parameter seed canonical) table result.2)) <$>
          (canonicalSigner secretKey message).run before)
      exact patch_run_eq (alteredRegion parameter seed canonical) table
        (Seeded.sign secretKey message) before
        (seeded_sign_avoids_altered_region parameter seed canonical
          secretKey message before)

theorem actual_stopped_patch {α : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : SigGolfCandidate.SphincsCacheMacFiniteDomain.Ciphertext)
    (secretKey : Seeded.SecretKey)
    (table : HashInput → HashOutput)
    (computation : OracleComp OuterWorld α)
    (before : QueryCache HashSpec) :
    evalSPMF ((simulateQ (romImpl + canonicalSigner secretKey)
      (stopBeforeDirect seed computation)).run
      (patch (alteredRegion parameter seed canonical) table before)) =
    evalSPMF ((fun result => (result.1,
      patch (alteredRegion parameter seed canonical) table result.2)) <$>
      (simulateQ (romImpl + canonicalSigner secretKey)
        (stopBeforeDirect seed computation)).run before) := by
  exact stopped_patch_run_eq (alteredRegion parameter seed canonical) table seed
    (romImpl + canonicalSigner secretKey)
    (actual_safe_step parameter seed canonical secretKey table)
    computation before

theorem actual_stopped_prepost {α Table : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : SigGolfCandidate.SphincsCacheMacFiniteDomain.Ciphertext)
    (secretKey : Seeded.SecretKey)
    (draw : ProbComp Table)
    (encode : Table → HashInput → HashOutput)
    (computation : OracleComp OuterWorld α)
    (before : QueryCache HashSpec) :
    evalSPMF (do
      let table ← draw
      let result ← (simulateQ (romImpl + canonicalSigner secretKey)
        (stopBeforeDirect seed computation)).run
        (patch (alteredRegion parameter seed canonical) (encode table) before)
      pure (table, result)) =
    evalSPMF (do
      let result ← (simulateQ (romImpl + canonicalSigner secretKey)
        (stopBeforeDirect seed computation)).run before
      let table ← draw
      pure (table, (result.1,
        patch (alteredRegion parameter seed canonical) (encode table) result.2))) := by
  calc
    _ = evalSPMF (do
      let table ← draw
      let result ← (simulateQ (romImpl + canonicalSigner secretKey)
        (stopBeforeDirect seed computation)).run before
      pure (table, (result.1,
        patch (alteredRegion parameter seed canonical) (encode table) result.2))) := by
          apply evalSPMF_bind_congr_left
          intro table
          simpa [Function.comp_def, bind_assoc] using
            evalSPMF_map_eq_of_evalSPMF_eq
              (actual_stopped_patch parameter seed canonical secretKey
                (encode table) computation before)
              (fun result => (table, result))
    _ = _ := evalSPMF_bind_comm draw
      ((simulateQ (romImpl + canonicalSigner secretKey)
        (stopBeforeDirect seed computation)).run before)
      (fun table result => pure (table,
        (result.1, patch (alteredRegion parameter seed canonical)
          (encode table) result.2)))

end SigGolfCandidate.SphincsCacheMacStoppedActual

/-- info: 'SigGolfCandidate.SphincsCacheMacStoppedActual.actual_stopped_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacStoppedActual.actual_stopped_patch

/-- info: 'SigGolfCandidate.SphincsCacheMacStoppedActual.actual_stopped_prepost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacStoppedActual.actual_stopped_prepost
/- END SigGolfCandidate.SphincsCacheMacStoppedActual -/

/- BEGIN SigGolfCandidate.SphincsCacheMacFlagCoupling -/

/-! The real MAC comparison and its all-failure counterpart share the same
lazy oracle and opaque canonical-signing handler. A first successful MAC check
sets the same sticky flag in both games. -/

namespace SigGolfCandidate.SphincsCacheMacFlagCoupling
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsSeededNoMacQueries
open OracleComp.ProgramLogic.Relational

abbrev FlagState := QueryCache HashSpec × Bool

noncomputable def flaggedImpl (secretKey : Seeded.SecretKey) (real : Bool) :
    QueryImpl AttackWorld (StateT FlagState ProbComp)
  | .inl query => fun (cache, bad) => do
      let (answer, cache') ← ((romImpl + canonicalSigner secretKey) query).run cache
      pure (answer, (cache', bad))
  | .inr test => fun (cache, bad) => do
      let (answer, cache') ← (randomOracle test.1).run cache
      let hit := decide (truncateHash answer = test.2)
      pure ((if real then hit else false), (cache', bad || hit))

theorem flaggedImpl_agree_good (secretKey : Seeded.SecretKey)
    (query : AttackWorld.Domain) (cache : QueryCache HashSpec)
    (answer : AttackWorld.Range query) (after : QueryCache HashSpec) :
    Pr[= (answer, (after, false)) |
      (flaggedImpl secretKey false query).run (cache, false)] =
    Pr[= (answer, (after, false)) |
      (flaggedImpl secretKey true query).run (cache, false)] := by
  classical
  cases query with
  | inl ordinary => rfl
  | inr test =>
      letI : DecidableEq (Bool × FlagState) := Classical.decEq _
      simp only [flaggedImpl, StateT.run, Bool.false_eq_true, ↓reduceIte,
        Bool.false_or]
      simp only [bind_pure_comp]
      rw [probOutput_map_eq_tsum, probOutput_map_eq_tsum]
      congr 1
      funext sample
      by_cases hhit : truncateHash sample.1 = test.2
      · simp [hhit, probOutput_pure]
      · simp [hhit, probOutput_pure]

theorem flaggedImpl_preserves_bad (secretKey : Seeded.SecretKey)
    (real : Bool) (query : AttackWorld.Domain)
    (state : FlagState) (hbad : state.2 = true)
    (result : AttackWorld.Range query × FlagState)
    (hresult : result ∈ support ((flaggedImpl secretKey real query).run state)) :
    result.2.2 = true := by
  rcases state with ⟨cache, bad⟩
  simp only at hbad
  subst bad
  cases query with
  | inl ordinary =>
      simp only [flaggedImpl, StateT.run, bind_pure_comp, support_map] at hresult
      obtain ⟨sample, _, rfl⟩ := hresult
      rfl
  | inr test =>
      simp only [flaggedImpl, StateT.run, Bool.true_or, bind_pure_comp,
        support_map] at hresult
      obtain ⟨sample, _, rfl⟩ := hresult
      rfl

theorem real_bad_eq_failure_bad {α : Type}
    (secretKey : Seeded.SecretKey)
    (computation : OracleComp AttackWorld α)
    (cache : QueryCache HashSpec) :
    Pr[fun z : α × FlagState => z.2.2 = true |
      (simulateQ (flaggedImpl secretKey true) computation).run (cache, false)] =
    Pr[fun z : α × FlagState => z.2.2 = true |
      (simulateQ (flaggedImpl secretKey false) computation).run (cache, false)] := by
  exact (probEvent_output_bad_eq'
    (flaggedImpl secretKey false) (flaggedImpl secretKey true)
    (flaggedImpl_agree_good secretKey)
    (flaggedImpl_preserves_bad secretKey false)
    (flaggedImpl_preserves_bad secretKey true)
    computation cache).symm

end SigGolfCandidate.SphincsCacheMacFlagCoupling

/-- info: 'SigGolfCandidate.SphincsCacheMacFlagCoupling.real_bad_eq_failure_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacFlagCoupling.real_bad_eq_failure_bad
/- END SigGolfCandidate.SphincsCacheMacFlagCoupling -/

/- BEGIN SigGolfCandidate.SphincsCacheMacCompiledGame -/

/-! Inline the canonical seeded signer and each failed cache-MAC comparison
into the ordinary RO language. This exposes one shared lazy oracle, enabling
finite-domain presampling without treating honest signing as attacker-direct
queries. -/

namespace SigGolfCandidate.SphincsCacheMacCompiledGame
open OracleComp OracleSpec SphincsSecurity SphincsSecurity.Seeded
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsCacheMacFlagCoupling
open SigGolfCandidate.SphincsCacheMacFiniteDomain
open SigGolfCandidate.SphincsMaskedCacheProgramming

noncomputable def liftHash {α : Type}
    (computation : OracleComp HashSpec α) : OracleComp OracleWorld α :=
  simulateQ (fun input =>
    (liftM (OracleWorld.query (.inr input)) :
      OracleComp OracleWorld HashOutput)) computation

theorem simulateQ_romImpl_liftHash {α : Type}
    (computation : OracleComp HashSpec α) :
    simulateQ romImpl (liftHash computation) =
      simulateQ randomOracle computation := by
  rw [liftHash, ← QueryImpl.simulateQ_compose]
  congr 1
  funext input
  simp [QueryImpl.apply_compose, romImpl, simulateQ_query,
    OracleSpec.query]

noncomputable def compiledFailureFlag {α : Type}
    (secretKey : Seeded.SecretKey)
    (computation : OracleComp AttackWorld α) :
    OracleComp OracleWorld (α × Bool) :=
  OracleComp.construct
    (fun value => pure (value, false))
    (fun input _ next =>
      match input with
      | .inl (.inl ordinary) => do
          let answer ← liftM (OracleWorld.query ordinary)
          next answer
      | .inl (.inr message) => do
          let answer ← liftHash (Seeded.sign secretKey message)
          next answer
      | .inr test => do
          let answer ← liftM (OracleWorld.query (.inr test.1))
          (fun result =>
            (result.1, result.2 || decide (truncateHash answer = test.2))) <$>
            next false)
    computation

noncomputable def stopBeforeAttack {α : Type} (seed : MasterSeed)
    (computation : OracleComp AttackWorld α) :
    OracleComp AttackWorld (Option α) := by
  classical
  exact OracleComp.construct
    (fun value => pure (some value))
    (fun input _ next =>
      match input with
      | .inl ordinary =>
          if attackerDirectSeedHit seed ordinary then pure none else do
            let answer ← liftM (AttackWorld.query (.inl ordinary))
            next answer
      | .inr test => do
          let answer ← liftM (AttackWorld.query (.inr test))
          next answer)
    computation

theorem stopBeforeAttack_query_bind {α : Type}
    (seed : MasterSeed) (input : AttackWorld.Domain)
    (next : AttackWorld.Range input → OracleComp AttackWorld α) :
    stopBeforeAttack seed (liftM (AttackWorld.query input) >>= next) =
      (match input with
      | .inl ordinary =>
          if attackerDirectSeedHit seed ordinary then pure none else do
            let answer ← liftM (AttackWorld.query (.inl ordinary))
            stopBeforeAttack seed (next answer)
      | .inr test => do
          let answer ← liftM (AttackWorld.query (.inr test))
          stopBeforeAttack seed (next answer)) := by
  cases input <;> rfl

theorem compiled_presample_all_altered {α : Type}
    (material : Seeded.KeyMaterial) (seed : MasterSeed)
    (pads : List (BitVec 32 × HashOutput))
    (canonical : Ciphertext) (macAnswer : HashOutput)
    (secretKey : Seeded.SecretKey)
    (computation : OracleComp AttackWorld α) :
    evalSPMF ((simulateQ romImpl
      (compiledFailureFlag secretKey computation)).run'
        (maskedMaterialCache material seed pads (List.ofFn canonical) macAnswer)) =
    evalSPMF (do
      let outputs ← Concrete.sequenceFin fun _ :
        Fin (Fintype.card (Altered canonical)) =>
        ($ᵗ HashOutput : ProbComp HashOutput)
      (simulateQ romImpl
        (compiledFailureFlag secretKey computation)).run'
          (cacheFin
            (maskedMaterialCache material seed pads (List.ofFn canonical) macAnswer)
            (allAlteredInputs material.1 seed canonical) outputs)) := by
  exact presample_all_altered material seed pads canonical macAnswer
    (compiledFailureFlag secretKey computation)

theorem flagged_failure_eq_compiled {α : Type}
    (secretKey : Seeded.SecretKey)
    (computation : OracleComp AttackWorld α)
    (cache : QueryCache HashSpec) (initialBad : Bool) :
    evalSPMF ((simulateQ (flaggedImpl secretKey false) computation).run
      (cache, initialBad)) =
    evalSPMF ((fun result =>
      (result.1.1, (result.2, initialBad || result.1.2))) <$>
      (simulateQ romImpl (compiledFailureFlag secretKey computation)).run cache) := by
  induction computation using OracleComp.inductionOn generalizing cache initialBad with
  | pure value =>
      simp [compiledFailureFlag, simulateQ_pure, flaggedImpl]
  | query_bind input next ih =>
      cases input with
      | inl ordinary =>
          cases ordinary with
          | inl direct =>
              simp only [simulateQ_bind, simulateQ_spec_query,
                StateT.run_bind, flaggedImpl, compiledFailureFlag,
                OracleComp.construct_query_bind]
              simp only [StateT.run, bind_pure_comp, map_bind,
                simulateQ_bind, simulateQ_spec_query]
              simp only [bind_map_left]
              apply evalSPMF_bind_congr'
              intro p
              simpa [compiledFailureFlag, StateT.run,
                map_eq_bind_pure_comp] using
                ih p.1 p.2 initialBad
          | inr message =>
              simp only [simulateQ_bind, simulateQ_spec_query,
                StateT.run_bind, flaggedImpl, compiledFailureFlag,
                OracleComp.construct_query_bind]
              simp only [StateT.run, bind_pure_comp, map_bind,
                simulateQ_bind, simulateQ_spec_query]
              rw [simulateQ_romImpl_liftHash]
              simp only [bind_map_left]
              apply evalSPMF_bind_congr'
              intro p
              simpa [compiledFailureFlag, StateT.run,
                map_eq_bind_pure_comp] using
                ih p.1 p.2 initialBad
      | inr test =>
          simp only [simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, flaggedImpl, compiledFailureFlag,
            OracleComp.construct_query_bind]
          simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_map,
            StateT.run_map, simulateQ_pure, StateT.run_pure]
          simp only [StateT.run, bind_pure_comp, map_bind, bind_map_left]
          apply evalSPMF_bind_congr'
          intro a
          have h := ih false a.2
            (initialBad || decide (truncateHash a.1 = test.2))
          simp only [StateT.run] at h
          rw [h]
          simp only [evalSPMF_map, Functor.map_map]
          congr 1
          funext result
          simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

end SigGolfCandidate.SphincsCacheMacCompiledGame

/-- info: 'SigGolfCandidate.SphincsCacheMacCompiledGame.compiled_presample_all_altered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacCompiledGame.compiled_presample_all_altered

/-- info: 'SigGolfCandidate.SphincsCacheMacCompiledGame.simulateQ_romImpl_liftHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacCompiledGame.simulateQ_romImpl_liftHash

/-- info: 'SigGolfCandidate.SphincsCacheMacCompiledGame.flagged_failure_eq_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacCompiledGame.flagged_failure_eq_compiled
/- END SigGolfCandidate.SphincsCacheMacCompiledGame -/

/- BEGIN SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit -/

/-! First-hit equivalence with signing kept opaque in the outer oracle. -/

namespace SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsCacheMacFirstHit
open SigGolfCandidate.SphincsCacheBlindMacGuess

def outerFailureTrace {α : Type} (world : QueryImpl OuterWorld Id)
    (computation : OracleComp AttackWorld α) :
    List (HashInput × Digest) :=
  OracleComp.construct
    (fun _ => [])
    (fun input _ next =>
      match input with
      | .inl ordinary => next (world ordinary)
      | .inr test => test :: next false)
    computation

def outerFirstHit {α : Type} (world : QueryImpl OuterWorld Id)
    (hash : QueryImpl HashSpec Id)
    (computation : OracleComp AttackWorld α) : Bool :=
  OracleComp.construct
    (fun _ => false)
    (fun input _ next =>
      match input with
      | .inl ordinary => next (world ordinary)
      | .inr test =>
        if truncateHash (hash test.1) = test.2 then true else next false)
    computation

theorem allFailureOuter_query_bind {α : Type}
    (input : AttackWorld.Domain)
    (next : AttackWorld.Range input → OracleComp AttackWorld α) :
    allFailureOuter (liftM (AttackWorld.query input) >>= next) =
      (match input with
      | .inl ordinary => do
          let answer ← liftM (OuterWorld.query ordinary)
          allFailureOuter (next answer)
      | .inr test => do
          let (value, attempts) ← allFailureOuter (next false)
          pure (value, test :: attempts)) := by
  cases input <;> rfl

theorem outerFailureTrace_query_bind {α : Type}
    (world : QueryImpl OuterWorld Id) (input : AttackWorld.Domain)
    (next : AttackWorld.Range input → OracleComp AttackWorld α) :
    outerFailureTrace world (liftM (AttackWorld.query input) >>= next) =
      (match input with
      | .inl ordinary => outerFailureTrace world (next (world ordinary))
      | .inr test => test :: outerFailureTrace world (next false)) := by
  cases input <;> rfl

theorem outer_first_hit_iff_failure_hit {α : Type}
    (world : QueryImpl OuterWorld Id) (hash : QueryImpl HashSpec Id)
    (computation : OracleComp AttackWorld α) :
    outerFirstHit world hash computation = true ↔
      Hit (outerFailureTrace world computation)
        (fun input => truncateHash (hash input)) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [outerFirstHit, outerFailureTrace, Hit]
  | query_bind input next ih =>
      cases input with
      | inl ordinary =>
          simpa [outerFirstHit, outerFailureTrace] using ih (world ordinary)
      | inr test =>
          by_cases hmatch : truncateHash (hash test.1) = test.2
          · simp [outerFirstHit, outerFailureTrace, hmatch, hit_cons]
          · simpa [outerFirstHit, outerFailureTrace, hmatch, hit_cons] using ih false

theorem allFailureOuter_trace {α : Type}
    (world : QueryImpl OuterWorld Id)
    (computation : OracleComp AttackWorld α) :
    (evalWithAnswerFn world (allFailureOuter computation)).2 =
      outerFailureTrace world computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl ordinary =>
          simp only [allFailureOuter_query_bind, outerFailureTrace_query_bind,
            evalWithAnswerFn_bind, ih]
          have hquery : evalWithAnswerFn world
              (liftM (OuterWorld.query ordinary) : OracleComp OuterWorld _) =
              world ordinary := rfl
          rw [hquery]
      | inr test =>
          rw [allFailureOuter_query_bind, outerFailureTrace_query_bind]
          simp [evalWithAnswerFn_bind, ih]

def GoodOuterPath {α : Type} (world : QueryImpl OuterWorld Id)
    (allowed : OuterWorld.Domain → Prop)
    (computation : OracleComp AttackWorld α) : Prop :=
  OracleComp.construct
    (fun _ => True)
    (fun input _ next =>
      match input with
      | .inl ordinary => allowed ordinary ∧ next (world ordinary)
      | .inr _ => next false)
    computation

theorem GoodOuterPath_query_bind {α : Type} (world : QueryImpl OuterWorld Id)
    (allowed : OuterWorld.Domain → Prop)
    (input : AttackWorld.Domain)
    (next : AttackWorld.Range input → OracleComp AttackWorld α) :
    GoodOuterPath world allowed
      (liftM (AttackWorld.query input) >>= next) =
      match input with
      | .inl ordinary => allowed ordinary ∧
          GoodOuterPath world allowed (next (world ordinary))
      | .inr _ => GoodOuterPath world allowed (next false) := by
  cases input <;> rfl

theorem outerFailureTrace_congr {α : Type}
    (left right : QueryImpl OuterWorld Id)
    (allowed : OuterWorld.Domain → Prop)
    (hagrees : ∀ input, allowed input → left input = right input)
    (computation : OracleComp AttackWorld α)
    (hpath : GoodOuterPath left allowed computation) :
    outerFailureTrace left computation =
      outerFailureTrace right computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl ordinary =>
          simp only [GoodOuterPath_query_bind] at hpath
          simp only [outerFailureTrace_query_bind]
          rw [← hagrees ordinary hpath.1]
          exact ih (left ordinary) hpath.2
      | inr test =>
          simp only [GoodOuterPath_query_bind] at hpath
          simp only [outerFailureTrace_query_bind]
          exact congrArg (List.cons test) (ih false hpath)

end SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit

/-- info: 'SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit.outer_first_hit_iff_failure_hit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit.outer_first_hit_iff_failure_hit

/-- info: 'SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit.allFailureOuter_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit.allFailureOuter_trace

/-- info: 'SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit.outerFailureTrace_congr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit.outerFailureTrace_congr
/- END SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit -/

/- BEGIN SigGolfCandidate.SphincsCacheMacFailurePatch -/

/-! The stopped all-failure interaction records altered-MAC tests without
querying their RO inputs, and its entire trace is independent of that region. -/

namespace SigGolfCandidate.SphincsCacheMacFailurePatch
open OracleComp OracleComp.DeferredSampling OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit
open SigGolfCandidate.SphincsCacheMacCompiledGame
open SigGolfCandidate.SphincsCacheMacPatchRun
open SigGolfCandidate.SphincsCacheMacSignerPrePost
open SigGolfCandidate.SphincsCacheMacStoppedActual
open SigGolfCandidate.SphincsSeededNoMacQueries
open SigGolfCandidate.SphincsCacheMacPrePost

theorem stopped_failure_patch {α : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : SigGolfCandidate.SphincsCacheMacFiniteDomain.Ciphertext)
    (secretKey : Seeded.SecretKey)
    (table : HashInput → HashOutput)
    (computation : OracleComp AttackWorld α)
    (before : QueryCache HashSpec) :
    evalSPMF ((simulateQ (romImpl + canonicalSigner secretKey)
      (allFailureOuter (stopBeforeAttack seed computation))).run
      (patch (alteredRegion parameter seed canonical) table before)) =
    evalSPMF ((fun result => (result.1,
      patch (alteredRegion parameter seed canonical) table result.2)) <$>
      (simulateQ (romImpl + canonicalSigner secretKey)
        (allFailureOuter (stopBeforeAttack seed computation))).run before) := by
  induction computation using OracleComp.inductionOn generalizing before with
  | pure value => simp [stopBeforeAttack, allFailureOuter, simulateQ_pure]
  | query_bind input next ih =>
      rw [stopBeforeAttack_query_bind]
      cases input with
      | inl ordinary =>
          by_cases hbad : attackerDirectSeedHit seed ordinary
          · simp [hbad, allFailureOuter, simulateQ_pure]
          · simp only [if_neg hbad, allFailureOuter_query_bind,
              simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
            calc
              _ = evalSPMF (do
                let p ← (fun (result : OuterWorld.Range ordinary × QueryCache HashSpec) => (result.1,
                  patch (alteredRegion parameter seed canonical) table result.2)) <$>
                    ((romImpl + canonicalSigner secretKey) ordinary).run before
                (simulateQ (romImpl + canonicalSigner secretKey)
                  (allFailureOuter (stopBeforeAttack seed (next p.1)))).run p.2) := by
                    rw [evalSPMF_bind, evalSPMF_bind]
                    exact congrArg (fun p : SPMF
                      (OuterWorld.Range ordinary × QueryCache HashSpec) =>
                        p >>= fun x => evalSPMF
                          ((simulateQ (romImpl + canonicalSigner secretKey)
                            (allFailureOuter (stopBeforeAttack seed (next x.1)))).run x.2))
                      (actual_safe_step parameter seed canonical secretKey table
                        ordinary before hbad)
              _ = evalSPMF (do
                let a ← ((romImpl + canonicalSigner secretKey) ordinary).run before
                (simulateQ (romImpl + canonicalSigner secretKey)
                  (allFailureOuter (stopBeforeAttack seed (next a.1)))).run
                    (patch (alteredRegion parameter seed canonical) table a.2)) := by
                      simp only [bind_map_left]
              _ = _ := by
                apply evalSPMF_bind_congr'
                intro a
                exact ih a.1 a.2
      | inr test =>
          simp only [allFailureOuter_query_bind,
            simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
          simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp,
            Functor.map_map]
          simp only [map_pure, bind_pure_comp]
          simpa only [Functor.map_map, Function.comp_def] using
            (evalSPMF_map_eq_of_evalSPMF_eq (ih false before)
              (fun result => ((result.1.1, test :: result.1.2), result.2)))

theorem stopped_failure_prepost {α Table : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : SigGolfCandidate.SphincsCacheMacFiniteDomain.Ciphertext)
    (secretKey : Seeded.SecretKey)
    (draw : ProbComp Table)
    (encode : Table → HashInput → HashOutput)
    (computation : OracleComp AttackWorld α)
    (before : QueryCache HashSpec) :
    evalSPMF (do
      let table ← draw
      let result ← (simulateQ (romImpl + canonicalSigner secretKey)
        (allFailureOuter (stopBeforeAttack seed computation))).run
          (patch (alteredRegion parameter seed canonical) (encode table) before)
      pure (table, result)) =
    evalSPMF (do
      let result ← (simulateQ (romImpl + canonicalSigner secretKey)
        (allFailureOuter (stopBeforeAttack seed computation))).run before
      let table ← draw
      pure (table, (result.1,
        patch (alteredRegion parameter seed canonical) (encode table) result.2))) := by
  calc
    _ = evalSPMF (do
      let table ← draw
      let result ← (simulateQ (romImpl + canonicalSigner secretKey)
        (allFailureOuter (stopBeforeAttack seed computation))).run before
      pure (table, (result.1,
        patch (alteredRegion parameter seed canonical) (encode table) result.2))) := by
          apply evalSPMF_bind_congr_left
          intro table
          simpa [Function.comp_def, bind_assoc] using
            evalSPMF_map_eq_of_evalSPMF_eq
              (stopped_failure_patch parameter seed canonical secretKey
                (encode table) computation before)
              (fun result => (table, result))
    _ = _ := evalSPMF_bind_comm draw
      ((simulateQ (romImpl + canonicalSigner secretKey)
        (allFailureOuter (stopBeforeAttack seed computation))).run before)
      (fun table result => pure (table,
        (result.1, patch (alteredRegion parameter seed canonical)
          (encode table) result.2)))

end SigGolfCandidate.SphincsCacheMacFailurePatch

/-- info: 'SigGolfCandidate.SphincsCacheMacFailurePatch.stopped_failure_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacFailurePatch.stopped_failure_patch

/-- info: 'SigGolfCandidate.SphincsCacheMacFailurePatch.stopped_failure_prepost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacFailurePatch.stopped_failure_prepost
/- END SigGolfCandidate.SphincsCacheMacFailurePatch -/

/- BEGIN SigGolfCandidate.SphincsCacheMacCharge -/

/-! Pathwise accounting for altered-cache MAC tests in the forced-failure
interaction. Each comparison contributes one virtual hash call. -/

namespace SigGolfCandidate.SphincsCacheMacCharge
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit

structure ChargedTrace (α : Type) where
  value : α
  attempts : List (HashInput × Digest)
  ordinaryCalls : Nat
  totalCalls : Nat

def runCharged {α : Type} (world : QueryImpl OuterWorld Id)
    (ordinaryCharge : (input : OuterWorld.Domain) → Nat)
    (computation : OracleComp AttackWorld α) : ChargedTrace α :=
  OracleComp.construct
    (fun value => ⟨value, [], 0, 0⟩)
    (fun input _ next =>
      match input with
      | .inl ordinary =>
          let tail := next (world ordinary)
          ⟨tail.value, tail.attempts,
            ordinaryCharge ordinary + tail.ordinaryCalls,
            ordinaryCharge ordinary + tail.totalCalls⟩
      | .inr test =>
          let tail := next false
          ⟨tail.value, test :: tail.attempts,
            tail.ordinaryCalls, 1 + tail.totalCalls⟩)
    computation

theorem charged_exact {α : Type} (world : QueryImpl OuterWorld Id)
    (ordinaryCharge : (input : OuterWorld.Domain) → Nat)
    (computation : OracleComp AttackWorld α) :
    (runCharged world ordinaryCharge computation).totalCalls =
      (runCharged world ordinaryCharge computation).ordinaryCalls +
        (runCharged world ordinaryCharge computation).attempts.length := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl ordinary =>
          have htail := ih (world ordinary)
          simp only [runCharged] at htail
          simp only [runCharged, OracleComp.construct_query_bind]
          omega
      | inr test =>
          have htail := ih false
          simp only [runCharged] at htail
          simp only [runCharged, OracleComp.construct_query_bind]
          simp only [List.length_cons]
          omega

theorem attempts_le_calls {α : Type} (world : QueryImpl OuterWorld Id)
    (ordinaryCharge : (input : OuterWorld.Domain) → Nat)
    (computation : OracleComp AttackWorld α) :
    (runCharged world ordinaryCharge computation).attempts.length ≤
      (runCharged world ordinaryCharge computation).totalCalls := by
  rw [charged_exact]
  omega

theorem charged_trace_eq_allFailure {α : Type}
    (world : QueryImpl OuterWorld Id)
    (ordinaryCharge : (input : OuterWorld.Domain) → Nat)
    (computation : OracleComp AttackWorld α) :
    (runCharged world ordinaryCharge computation).attempts =
      (evalWithAnswerFn world (allFailureOuter computation)).2 := by
  rw [allFailureOuter_trace]
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl ordinary =>
          have htail := ih (world ordinary)
          simp only [runCharged, OracleComp.construct_query_bind,
            outerFailureTrace_query_bind]
          simpa only [runCharged] using htail
      | inr test =>
          have htail := ih false
          simp only [runCharged, OracleComp.construct_query_bind,
            outerFailureTrace_query_bind]
          simpa only [runCharged] using congrArg (List.cons test) htail

theorem failure_attempts_le_charged_calls {α : Type}
    (world : QueryImpl OuterWorld Id)
    (ordinaryCharge : (input : OuterWorld.Domain) → Nat)
    (computation : OracleComp AttackWorld α) :
    (evalWithAnswerFn world (allFailureOuter computation)).2.length ≤
      (runCharged world ordinaryCharge computation).totalCalls := by
  rw [← charged_trace_eq_allFailure]
  exact attempts_le_calls world ordinaryCharge computation

end SigGolfCandidate.SphincsCacheMacCharge

/-- info: 'SigGolfCandidate.SphincsCacheMacCharge.attempts_le_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacCharge.attempts_le_calls

/-- info: 'SigGolfCandidate.SphincsCacheMacCharge.charged_trace_eq_allFailure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacCharge.charged_trace_eq_allFailure

/-- info: 'SigGolfCandidate.SphincsCacheMacCharge.failure_attempts_le_charged_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacCharge.failure_attempts_le_charged_calls
/- END SigGolfCandidate.SphincsCacheMacCharge -/

/- BEGIN SigGolfCandidate.SphincsCacheMacHashOutputBlind -/

/-! The independent altered-MAC oracle table has 256-bit entries; truncating
each entry to the published 160-bit MAC preserves the exact blind-guess bound. -/

namespace SigGolfCandidate.SphincsCacheMacHashOutputBlind
open OracleComp SphincsSecurity
open SigGolfCandidate.SphincsCacheMacFiniteDomain
open SigGolfCandidate.SphincsCacheBlindMacGuess

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem uniform_altered_hash_marginal (canonical : Ciphertext)
    (candidate : Altered canonical) (guess : Digest) :
    Pr[fun table : Altered canonical → HashOutput =>
      truncateHash (table candidate) = guess |
      ($ᵗ (Altered canonical → HashOutput) : ProbComp _)] =
      (Fintype.card Digest : ENNReal)⁻¹ := by
  have h := OracleComp.evalSPMF_uniformSample_bind_update_map
    (D := Altered canonical) (R := HashOutput) candidate
    (fun table : Altered canonical → HashOutput => table candidate)
  have hsimple :
      evalSPMF (do
        let u ← ($ᵗ HashOutput : ProbComp HashOutput)
        let g ← ($ᵗ (Altered canonical → HashOutput) : ProbComp _)
        pure ((Function.update g candidate u) candidate)) =
      evalSPMF ($ᵗ HashOutput : ProbComp HashOutput) := by
    simp only [Function.update_self]
    calc
      _ = evalSPMF (($ᵗ HashOutput : ProbComp HashOutput) >>= fun u => pure u) := by
        apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
        intro u
        simpa only [bind_pure_comp] using
          OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails
            ($ᵗ (Altered canonical → HashOutput) : ProbComp _)
            (probFailure_uniformSample (α := Altered canonical → HashOutput))
            (pure u)
      _ = _ := by simp
  have hdist :
      evalSPMF ((fun table : Altered canonical → HashOutput => table candidate) <$>
        ($ᵗ (Altered canonical → HashOutput) : ProbComp _)) =
      evalSPMF ($ᵗ HashOutput : ProbComp HashOutput) := by
    calc
      _ = evalSPMF (do
          let g ← ($ᵗ (Altered canonical → HashOutput) : ProbComp _)
          pure (g candidate)) := by simp only [evalSPMF_map, bind_pure_comp]
      _ = _ := h.symm.trans hsimple
  rw [show (fun table : Altered canonical → HashOutput =>
      truncateHash (table candidate) = guess) =
    (fun output : HashOutput => truncateHash output = guess) ∘
      (fun table : Altered canonical → HashOutput => table candidate) from rfl,
    ← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hdist]
  exact probEvent_uniform_truncateHash_eq guess

theorem uniform_altered_hash_marginal_pmf (canonical : Ciphertext)
    (candidate : Altered canonical) (guess : Digest) :
    Pr[fun table : Altered canonical → HashOutput =>
      truncateHash (table candidate) = guess |
      PMF.uniformOfFintype (Altered canonical → HashOutput)] =
      (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [probEvent_def, evalSPMF_uniformSample,
    SPMF.probEvent_liftM] using
      uniform_altered_hash_marginal canonical candidate guess

theorem ideal_hash_table_blind_bound {Env : Type}
    (canonical : Ciphertext) (environment : PMF Env)
    (plan : Env → List (Altered canonical × Digest))
    (q : Nat) (hbudget : ∀ env, (plan env).length ≤ q) :
    Pr[fun result =>
      Hit (plan result.1)
        (fun candidate => truncateHash (result.2 candidate)) |
      (do
        let env ← (liftM environment : SPMF Env)
        let table ← (liftM (PMF.uniformOfFintype
          (Altered canonical → HashOutput)) : SPMF _)
        pure (env, table))] ≤
      q * (Fintype.card Digest : ENNReal)⁻¹ := by
  let targets : PMF (Altered canonical → Digest) :=
    (fun (table : Altered canonical → HashOutput) candidate =>
      truncateHash (table candidate)) <$>
      PMF.uniformOfFintype (Altered canonical → HashOutput)
  have hmarginal : ∀ candidate guess,
      Pr[fun table => table candidate = guess | targets] ≤
        (Fintype.card Digest : ENNReal)⁻¹ := by
    intro candidate guess
    change Pr[fun table => table candidate = guess |
      (fun (raw : Altered canonical → HashOutput) candidate =>
        truncateHash (raw candidate)) <$>
        PMF.uniformOfFintype (Altered canonical → HashOutput)] ≤ _
    rw [probEvent_map]
    exact (uniform_altered_hash_marginal_pmf canonical candidate guess).le
  apply probEvent_bind_le_of_forall_le
  intro env _
  simp only [bind_pure_comp, probEvent_map, Function.comp_def,
    SPMF.probEvent_liftM]
  have hfixed := fixed_plan_bound targets hmarginal (plan env)
  rw [probEvent_map] at hfixed
  exact hfixed.trans (by gcongr; exact_mod_cast hbudget env)

end SigGolfCandidate.SphincsCacheMacHashOutputBlind

/-- info: 'SigGolfCandidate.SphincsCacheMacHashOutputBlind.uniform_altered_hash_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacHashOutputBlind.uniform_altered_hash_marginal

/-- info: 'SigGolfCandidate.SphincsCacheMacHashOutputBlind.ideal_hash_table_blind_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacHashOutputBlind.ideal_hash_table_blind_bound
/- END SigGolfCandidate.SphincsCacheMacHashOutputBlind -/

/- BEGIN SigGolfCandidate.SphincsCacheMacParametricBridge -/

/-! Exact remaining coupling interface for the altered-cache MAC game. The
probabilistic first-hit bound is conditional on a real-to-independent-table
coupling, and on a charge-to-machine-cost refinement. Neither is assumed
silently by the competition security claim. -/

namespace SigGolfCandidate.SphincsCacheMacParametricBridge
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacFlagCoupling
open SigGolfCandidate.SphincsCacheMacCharge
open SigGolfCandidate.SphincsCacheMacFiniteDomain
open SigGolfCandidate.SphincsCacheBlindMacGuess
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsCacheMacHashOutputBlind

abbrev ChargedWithin (α : Type) (q : Nat) :=
  {env : ChargedTrace α //
    env.attempts.length ≤ env.totalCalls ∧ env.totalCalls ≤ q}

def encodePlan (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (plan : List (Altered canonical × Digest)) :
    List (HashInput × Digest) :=
  plan.map (fun attempt =>
    (alteredInput parameter seed canonical attempt.1, attempt.2))

theorem encodePlan_length (parameter : PublicParameter)
    (seed : MasterSeed) (canonical : Ciphertext)
    (plan : List (Altered canonical × Digest)) :
    (encodePlan parameter seed canonical plan).length = plan.length := by
  simp [encodePlan]

theorem hit_encodePlan_iff (parameter : PublicParameter)
    (seed : MasterSeed) (canonical : Ciphertext)
    (plan : List (Altered canonical × Digest))
    (hash : HashInput → HashOutput)
    (table : Altered canonical → Digest)
    (hanswers : ∀ candidate,
      truncateHash (hash (alteredInput parameter seed canonical candidate)) =
        table candidate) :
    Hit (encodePlan parameter seed canonical plan)
      (fun input => truncateHash (hash input)) ↔ Hit plan table := by
  simp only [Hit, encodePlan, List.mem_map]
  constructor
  · rintro ⟨attempt, ⟨original, hmem, rfl⟩, hhit⟩
    exact ⟨original, hmem, by simpa only [hanswers] using hhit⟩
  · rintro ⟨original, hmem, hhit⟩
    exact ⟨(alteredInput parameter seed canonical original.1, original.2),
      ⟨original, hmem, rfl⟩, by simpa only [hanswers] using hhit⟩

theorem first_hit_bound_given_coupling {α : Type}
    (canonical : Ciphertext) (secretKey : Seeded.SecretKey)
    (computation : OracleComp AttackWorld α)
    (cache : QueryCache HashSpec)
    (q : Nat)
    (environment : PMF (ChargedWithin α q))
    (plan : ChargedWithin α q → List (Altered canonical × Digest))
    (hplan : ∀ env, (plan env).length ≤ env.1.attempts.length)
    (hcouple :
      Pr[fun z : α × FlagState => z.2.2 = true |
        (simulateQ (flaggedImpl secretKey false) computation).run
          (cache, false)] =
      Pr[fun result => Hit (plan result.1) result.2 |
        (do
          let env ← (liftM environment : SPMF (ChargedWithin α q))
          let table ← (liftM (PMF.uniformOfFintype
            (Altered canonical → Digest)) : SPMF _)
          pure (env, table))]) :
    Pr[fun z : α × FlagState => z.2.2 = true |
      (simulateQ (flaggedImpl secretKey true) computation).run
        (cache, false)] ≤
      q * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [real_bad_eq_failure_bad secretKey computation cache, hcouple]
  apply ideal_altered_blind_bound canonical environment plan q
  intro env
  exact (hplan env).trans (env.2.1.trans env.2.2)

theorem first_hit_bound_given_hash_table_coupling {α : Type}
    (canonical : Ciphertext) (secretKey : Seeded.SecretKey)
    (computation : OracleComp AttackWorld α)
    (cache : QueryCache HashSpec)
    (q : Nat)
    (environment : PMF (ChargedWithin α q))
    (plan : ChargedWithin α q → List (Altered canonical × Digest))
    (hplan : ∀ env, (plan env).length ≤ env.1.attempts.length)
    (hcouple :
      Pr[fun z : α × FlagState => z.2.2 = true |
        (simulateQ (flaggedImpl secretKey false) computation).run
          (cache, false)] =
      Pr[fun result =>
        Hit (plan result.1)
          (fun candidate => truncateHash (result.2 candidate)) |
        (do
          let env ← (liftM environment : SPMF (ChargedWithin α q))
          let table ← (liftM (PMF.uniformOfFintype
            (Altered canonical → HashOutput)) : SPMF _)
          pure (env, table))]) :
    Pr[fun z : α × FlagState => z.2.2 = true |
      (simulateQ (flaggedImpl secretKey true) computation).run
        (cache, false)] ≤
      q * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [real_bad_eq_failure_bad secretKey computation cache, hcouple]
  apply ideal_hash_table_blind_bound canonical environment plan q
  intro env
  exact (hplan env).trans (env.2.1.trans env.2.2)

end SigGolfCandidate.SphincsCacheMacParametricBridge

/-- info: 'SigGolfCandidate.SphincsCacheMacParametricBridge.first_hit_bound_given_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacParametricBridge.first_hit_bound_given_coupling

/-- info: 'SigGolfCandidate.SphincsCacheMacParametricBridge.hit_encodePlan_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacParametricBridge.hit_encodePlan_iff

/-- info: 'SigGolfCandidate.SphincsCacheMacParametricBridge.first_hit_bound_given_hash_table_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacParametricBridge.first_hit_bound_given_hash_table_coupling
/- END SigGolfCandidate.SphincsCacheMacParametricBridge -/

/- BEGIN SigGolfCandidate.SphincsCacheMacTypedGame -/

/-! Cache-MAC tests are restricted to changed authenticated ciphertexts. The
public canonical ciphertext with a wrong tag is rejected without an oracle
query and is deliberately absent from this oracle interface. -/

namespace SigGolfCandidate.SphincsCacheMacTypedGame
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacFiniteDomain
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit
open SigGolfCandidate.SphincsCacheMacParametricBridge
open SigGolfCandidate.SphincsCacheMacCharge
open SigGolfCandidate.SphincsCacheMacPatchRun
open SigGolfCandidate.SphincsCacheMacSignerPrePost
open SigGolfCandidate.SphincsCacheMacFirstHit
open SigGolfCandidate.SphincsCacheMacHashOutputBlind
open SigGolfCandidate.SphincsCacheBlindMacGuess

abbrev TypedAttackWorld (canonical : Ciphertext) :=
  OuterWorld + ((Altered canonical × Digest) →ₒ Bool)

def encodeTyped {α : Type} (parameter : PublicParameter)
    (seed : MasterSeed) (canonical : Ciphertext)
    (computation : OracleComp (TypedAttackWorld canonical) α) :
    OracleComp AttackWorld α :=
  OracleComp.construct
    pure
    (fun input _ next =>
      match input with
      | .inl ordinary => do
          let answer ← liftM (AttackWorld.query (.inl ordinary))
          next answer
      | .inr test => do
          let answer ← liftM (AttackWorld.query
            (.inr (alteredInput parameter seed canonical test.1, test.2)))
          next answer)
    computation

theorem encodeTyped_query_bind {α : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (input : (TypedAttackWorld canonical).Domain)
    (next : (TypedAttackWorld canonical).Range input →
      OracleComp (TypedAttackWorld canonical) α) :
    encodeTyped parameter seed canonical
      (liftM ((TypedAttackWorld canonical).query input) >>= next) =
    (match input with
    | .inl ordinary => do
        let answer ← liftM (AttackWorld.query (.inl ordinary))
        encodeTyped parameter seed canonical (next answer)
    | .inr test => do
        let answer ← liftM (AttackWorld.query
          (.inr (alteredInput parameter seed canonical test.1, test.2)))
        encodeTyped parameter seed canonical (next answer)) := by
  cases input <;> rfl

def typedFailureTrace {α : Type} {canonical : Ciphertext}
    (world : QueryImpl OuterWorld Id)
    (computation : OracleComp (TypedAttackWorld canonical) α) :
    List (Altered canonical × Digest) :=
  OracleComp.construct
    (fun _ => [])
    (fun input _ next =>
      match input with
      | .inl ordinary => next (world ordinary)
      | .inr test => test :: next false)
    computation

theorem encoded_failure_trace {α : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext) (world : QueryImpl OuterWorld Id)
    (computation : OracleComp (TypedAttackWorld canonical) α) :
    outerFailureTrace world (encodeTyped parameter seed canonical computation) =
      encodePlan parameter seed canonical (typedFailureTrace world computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl ordinary =>
          simpa [encodeTyped, typedFailureTrace, outerFailureTrace,
            encodePlan] using ih (world ordinary)
      | inr test =>
          simpa [encodeTyped, typedFailureTrace, outerFailureTrace,
            encodePlan] using congrArg
              (fun xs => (alteredInput parameter seed canonical test.1, test.2) :: xs)
              (ih false)

theorem patched_altered_test
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext) (table : HashInput → HashOutput)
    (before : QueryCache HashSpec) (candidate : Altered canonical) :
    (randomOracle (alteredInput parameter seed canonical candidate)).run
      (patch (alteredRegion parameter seed canonical) table before) =
    pure (table (alteredInput parameter seed canonical candidate),
      patch (alteredRegion parameter seed canonical) table before) := by
  have hregion : alteredRegion parameter seed canonical
      (alteredInput parameter seed canonical candidate) :=
    ⟨candidate, rfl⟩
  simp [OracleSpec.randomOracle, patch, hregion]

theorem typed_first_hit_iff_failure_hit {α : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext) (world : QueryImpl OuterWorld Id)
    (hash : QueryImpl HashSpec Id)
    (computation : OracleComp (TypedAttackWorld canonical) α) :
    outerFirstHit world hash (encodeTyped parameter seed canonical computation) = true ↔
      Hit (typedFailureTrace world computation)
        (fun candidate => truncateHash
          (hash (alteredInput parameter seed canonical candidate))) := by
  rw [outer_first_hit_iff_failure_hit, encoded_failure_trace]
  exact hit_encodePlan_iff parameter seed canonical
    (typedFailureTrace world computation) hash _ (fun candidate => rfl)

abbrev BudgetedWorld {α : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (ordinaryCharge : (input : OuterWorld.Domain) → Nat)
    (computation : OracleComp (TypedAttackWorld canonical) α)
    (q : Nat) :=
  {world : QueryImpl OuterWorld Id //
    (runCharged world ordinaryCharge
      (encodeTyped parameter seed canonical computation)).totalCalls ≤ q}

theorem typed_attempts_within_budget {α : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (ordinaryCharge : (input : OuterWorld.Domain) → Nat)
    (computation : OracleComp (TypedAttackWorld canonical) α)
    (q : Nat)
    (env : BudgetedWorld parameter seed canonical ordinaryCharge computation q) :
    (typedFailureTrace env.1 computation).length ≤ q := by
  have hlen := encodePlan_length parameter seed canonical
    (typedFailureTrace env.1 computation)
  rw [← hlen, ← encoded_failure_trace,
    ← allFailureOuter_trace]
  exact (failure_attempts_le_charged_calls env.1 ordinaryCharge
    (encodeTyped parameter seed canonical computation)).trans env.2

theorem ideal_typed_first_hit_bound {α : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (ordinaryCharge : (input : OuterWorld.Domain) → Nat)
    (computation : OracleComp (TypedAttackWorld canonical) α)
    (q : Nat)
    (environment : PMF
      (BudgetedWorld parameter seed canonical ordinaryCharge computation q)) :
    Pr[fun result =>
      Hit (typedFailureTrace result.1.1 computation)
        (fun candidate => truncateHash (result.2 candidate)) |
      (do
        let env ← (liftM environment : SPMF _)
        let table ← (liftM (PMF.uniformOfFintype
          (Altered canonical → HashOutput)) : SPMF _)
        pure (env, table))] ≤
      q * (Fintype.card Digest : ENNReal)⁻¹ := by
  exact ideal_hash_table_blind_bound canonical environment
    (fun env => typedFailureTrace env.1 computation) q
    (typed_attempts_within_budget parameter seed canonical ordinaryCharge
      computation q)

end SigGolfCandidate.SphincsCacheMacTypedGame

/-- info: 'SigGolfCandidate.SphincsCacheMacTypedGame.encoded_failure_trace' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTypedGame.encoded_failure_trace

/-- info: 'SigGolfCandidate.SphincsCacheMacTypedGame.patched_altered_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTypedGame.patched_altered_test

/-- info: 'SigGolfCandidate.SphincsCacheMacTypedGame.typed_first_hit_iff_failure_hit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTypedGame.typed_first_hit_iff_failure_hit

/-- info: 'SigGolfCandidate.SphincsCacheMacTypedGame.typed_attempts_within_budget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTypedGame.typed_attempts_within_budget

/-- info: 'SigGolfCandidate.SphincsCacheMacTypedGame.ideal_typed_first_hit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTypedGame.ideal_typed_first_hit_bound
/- END SigGolfCandidate.SphincsCacheMacTypedGame -/

/- BEGIN SigGolfCandidate.SphincsCacheMacEagerGame -/

/-! Sample only the finite hash-query table eagerly. The fixed-hash world
continues to draw uniform coins on demand, and the setup RO cache is retained. -/

namespace SigGolfCandidate.SphincsCacheMacEagerGame
open OracleComp OracleSpec SphincsSecurity
open SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCacheMacFiniteDomain
open SigGolfCandidate.SphincsCacheMacTypedGame
open SigGolfCandidate.SphincsCacheMacCompiledGame
open SigGolfCandidate.SphincsMaskedCacheProgramming

theorem liftHash_eq_liftM {α : Type}
    (computation : OracleComp HashSpec α) :
    liftHash computation =
      (liftM computation : OracleComp OracleWorld α) := by
  rfl

theorem fixed_hash_liftHash {α : Type}
    (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) :
    simulateQ (fixedHashWorld f) (liftHash computation) =
      pure (evalWithAnswerFn f computation) := by
  rw [liftHash_eq_liftM]
  have h := fixedBoundaryRun_forget 0 f
    (liftM computation : OracleComp OracleWorld α)
  rw [fixedBoundaryRun_lift_hash, map_pure, boundaryEval_fst] at h
  exact h.symm

theorem eager_hash_with_cache {α : Type}
    (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    let inputs := hashInputs program
    evalSPMF ((simulateQ romImpl program).run' cache) =
      evalSPMF (do
        let table ← sampleHashTable inputs
        simulateQ (fixedHashWorld
          (finiteHashAnswer cache inputs table)) program) := by
  intro inputs
  exact evalSPMF_romRun_eq_finiteHash program inputs (Finset.Subset.rfl) cache

end SigGolfCandidate.SphincsCacheMacEagerGame

/-- info: 'SigGolfCandidate.SphincsCacheMacEagerGame.eager_hash_with_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacEagerGame.eager_hash_with_cache

/-- info: 'SigGolfCandidate.SphincsCacheMacEagerGame.fixed_hash_liftHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacEagerGame.fixed_hash_liftHash
/- END SigGolfCandidate.SphincsCacheMacEagerGame -/

/- BEGIN SigGolfCandidate.SphincsCacheMacFixedFlagTrace -/

/-! At a fixed hash table the all-failure trace determines the sticky MAC
first-hit flag. Uniform coin queries remain probabilistic and shared. -/

namespace SigGolfCandidate.SphincsCacheMacFixedFlagTrace
open OracleComp OracleSpec SphincsSecurity
open SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCacheMacCompiledGame
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit
open SigGolfCandidate.SphincsCacheMacEagerGame
open SigGolfCandidate.SphincsCacheBlindMacGuess

noncomputable def fixedOuter (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) : QueryImpl OuterWorld ProbComp
  | .inl direct => fixedHashWorld hash direct
  | .inr message => pure (evalWithAnswerFn hash (Seeded.sign secretKey message))

noncomputable def fixedHit (hash : QueryImpl HashSpec Id)
    (attempts : List (HashInput × Digest)) : Bool := by
  classical exact decide (Hit attempts (fun input => truncateHash (hash input)))

theorem fixed_flag_eq_failure_trace {α : Type}
    (hash : QueryImpl HashSpec Id) (secretKey : Seeded.SecretKey)
    (computation : OracleComp AttackWorld α) :
    simulateQ (fixedHashWorld hash)
      (compiledFailureFlag secretKey computation) =
    (fun result => (result.1, fixedHit hash result.2)) <$>
      simulateQ (fixedOuter hash secretKey)
        (allFailureOuter computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp [compiledFailureFlag, allFailureOuter, simulateQ_pure, fixedHit, Hit]
  | query_bind input next ih =>
      cases input with
      | inl ordinary =>
          cases ordinary with
          | inl direct =>
              simp only [compiledFailureFlag, OracleComp.construct_query_bind,
                allFailureOuter_query_bind, simulateQ_bind, simulateQ_spec_query,
                fixedOuter]
              change (fixedHashWorld hash direct >>= fun answer =>
                simulateQ (fixedHashWorld hash)
                  (compiledFailureFlag secretKey (next answer))) = _
              simp only [map_bind]
              apply bind_congr
              intro answer
              exact ih answer
          | inr message =>
              simp only [compiledFailureFlag, OracleComp.construct_query_bind,
                allFailureOuter_query_bind, simulateQ_bind, simulateQ_spec_query,
                fixedOuter]
              rw [fixed_hash_liftHash]
              simp only [pure_bind, map_bind]
              exact ih (evalWithAnswerFn hash (Seeded.sign secretKey message))
      | inr test =>
          simp only [compiledFailureFlag, OracleComp.construct_query_bind,
            allFailureOuter_query_bind, simulateQ_bind, simulateQ_spec_query]
          simp only [fixedHashWorld, pure_bind, simulateQ_map,
            simulateQ_pure, map_pure, Functor.map_map, Function.comp_def]
          change (fun result => (result.1,
            result.2 || decide (truncateHash (hash test.1) = test.2))) <$>
            simulateQ (fixedHashWorld hash)
              (compiledFailureFlag secretKey (next false)) = _
          rw [ih false]
          simp only [fixedHit, Functor.map_map, Function.comp_def]
          simp only [bind_pure_comp, Functor.map_map, Function.comp_def]
          congr 1
          funext result
          by_cases h : truncateHash (hash test.1) = test.2 <;>
            simp [hit_cons, h]

end SigGolfCandidate.SphincsCacheMacFixedFlagTrace

/-- info: 'SigGolfCandidate.SphincsCacheMacFixedFlagTrace.fixed_flag_eq_failure_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacFixedFlagTrace.fixed_flag_eq_failure_trace
/- END SigGolfCandidate.SphincsCacheMacFixedFlagTrace -/

/- BEGIN SigGolfCandidate.SphincsCacheMacEagerFlagBridge -/

/-! The real lazy-RO first-hit output equals a fixed-hash all-failure trace,
averaged over a finite eager hash table and the ordinary coin channel. -/

namespace SigGolfCandidate.SphincsCacheMacEagerFlagBridge
open OracleComp OracleComp.DeferredSampling OracleSpec SphincsSecurity
open SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCacheMacCompiledGame
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsCacheMacFixedFlagTrace
open SigGolfCandidate.SphincsCacheMacEagerGame

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem eager_first_hit_trace {α : Type}
    (secretKey : Seeded.SecretKey)
    (computation : OracleComp AttackWorld α)
    (cache : QueryCache HashSpec) :
    let program := compiledFailureFlag secretKey computation
    let inputs := hashInputs program
    evalSPMF ((simulateQ romImpl program).run' cache) =
      evalSPMF (do
        let table ← sampleHashTable inputs
        let hash := finiteHashAnswer cache inputs table
        (fun (result : α × List (HashInput × Digest)) =>
          (result.1, fixedHit hash result.2)) <$>
          simulateQ (fixedOuter hash secretKey)
            (allFailureOuter computation)) := by
  intro program inputs
  rw [eager_hash_with_cache program cache]
  apply evalSPMF_bind_congr_left
  intro table
  exact congrArg evalSPMF
    (fixed_flag_eq_failure_trace (finiteHashAnswer cache inputs table)
      secretKey computation)

end SigGolfCandidate.SphincsCacheMacEagerFlagBridge

/-- info: 'SigGolfCandidate.SphincsCacheMacEagerFlagBridge.eager_first_hit_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacEagerFlagBridge.eager_first_hit_trace
/- END SigGolfCandidate.SphincsCacheMacEagerFlagBridge -/

/- BEGIN SigGolfCandidate.SphincsCacheMacTypedTrace -/

/-! Preserve typed altered-ciphertext attempts through the all-failure game. -/

namespace SigGolfCandidate.SphincsCacheMacTypedTrace
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsCacheMacThreeServiceFirstHit
open SigGolfCandidate.SphincsCacheMacFiniteDomain
open SigGolfCandidate.SphincsCacheMacTypedGame
open SigGolfCandidate.SphincsCacheMacParametricBridge
open SigGolfCandidate.SphincsCacheMacFixedFlagTrace
open SigGolfCandidate.SphincsCacheMacCompiledGame
open SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCacheBlindMacGuess

def typedFailureProgram {α : Type} {canonical : Ciphertext}
    (computation : OracleComp (TypedAttackWorld canonical) α) :
    OracleComp OuterWorld (α × List (Altered canonical × Digest)) :=
  OracleComp.construct
    (fun value => pure (value, []))
    (fun input _ next =>
      match input with
      | .inl ordinary => do
          let answer ← liftM (OuterWorld.query ordinary)
          next answer
      | .inr test => do
          let (value, attempts) ← next false
          pure (value, test :: attempts))
    computation

theorem typedFailureProgram_query_bind {α : Type} {canonical : Ciphertext}
    (input : (TypedAttackWorld canonical).Domain)
    (next : (TypedAttackWorld canonical).Range input →
      OracleComp (TypedAttackWorld canonical) α) :
    typedFailureProgram (liftM ((TypedAttackWorld canonical).query input) >>= next) =
      (match input with
      | .inl ordinary => do
          let answer ← liftM (OuterWorld.query ordinary)
          typedFailureProgram (next answer)
      | .inr test => do
          let (value, attempts) ← typedFailureProgram (next false)
          pure (value, test :: attempts)) := by
  cases input <;> rfl

theorem allFailure_encodeTyped {α : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (computation : OracleComp (TypedAttackWorld canonical) α) :
    allFailureOuter (encodeTyped parameter seed canonical computation) =
      (fun result => (result.1,
        encodePlan parameter seed canonical result.2)) <$>
      typedFailureProgram computation := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp [allFailureOuter, encodeTyped, typedFailureProgram,
        encodePlan]
  | query_bind input next ih =>
      cases input with
      | inl ordinary =>
          rw [encodeTyped_query_bind, allFailureOuter_query_bind,
            typedFailureProgram_query_bind]
          simp only [map_bind]
          simp only [ih]
      | inr test =>
          rw [encodeTyped_query_bind, allFailureOuter_query_bind,
            typedFailureProgram_query_bind]
          simp only [map_bind]
          rw [ih false]
          simp [encodePlan, Functor.map_map, map_bind]

noncomputable def typedHit (hash : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (attempts : List (Altered canonical × Digest)) : Bool := by
  classical
  exact decide (Hit attempts (fun candidate =>
    truncateHash (hash (alteredInput parameter seed canonical candidate))))

theorem fixed_flag_eq_typed_trace {α : Type}
    (hash : QueryImpl HashSpec Id) (secretKey : Seeded.SecretKey)
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (computation : OracleComp (TypedAttackWorld canonical) α) :
    simulateQ (fixedHashWorld hash)
      (compiledFailureFlag secretKey
        (encodeTyped parameter seed canonical computation)) =
    (fun result => (result.1,
      typedHit hash parameter seed canonical result.2)) <$>
      simulateQ (fixedOuter hash secretKey)
        (typedFailureProgram computation) := by
  classical
  rw [fixed_flag_eq_failure_trace, allFailure_encodeTyped]
  rw [simulateQ_map]
  simp only [Functor.map_map]
  congr 1
  funext result
  congr 1
  simp only [fixedHit, typedHit]
  exact Bool.decide_congr
    (hit_encodePlan_iff parameter seed canonical result.2 hash _
      (fun candidate => rfl))

end SigGolfCandidate.SphincsCacheMacTypedTrace

/-- info: 'SigGolfCandidate.SphincsCacheMacTypedTrace.allFailure_encodeTyped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTypedTrace.allFailure_encodeTyped

/-- info: 'SigGolfCandidate.SphincsCacheMacTypedTrace.fixed_flag_eq_typed_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTypedTrace.fixed_flag_eq_typed_trace
/- END SigGolfCandidate.SphincsCacheMacTypedTrace -/

/- BEGIN SigGolfCandidate.SphincsCacheMacTypedStop -/

/-! Stop attacker-direct secret-key-input contact before it can reveal the
altered-MAC table, while retaining altered-only typed test requests. -/

namespace SigGolfCandidate.SphincsCacheMacTypedStop
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsCacheMacCompiledGame
open SigGolfCandidate.SphincsCacheMacFiniteDomain
open SigGolfCandidate.SphincsCacheMacTypedGame
open SigGolfCandidate.SphincsCacheMacTypedTrace
open SigGolfCandidate.SphincsCacheMacFixedFlagTrace
open SphincsSecurity.Concrete
open OracleComp.DeferredSampling
open SigGolfCandidate.SphincsCacheMacStoppedActual
open SigGolfCandidate.SphincsCacheMacPatchRun
open SigGolfCandidate.SphincsCacheMacSignerPrePost
open SigGolfCandidate.SphincsSeededNoMacQueries

noncomputable def stopBeforeTyped {α : Type} {canonical : Ciphertext}
    (seed : MasterSeed)
    (computation : OracleComp (TypedAttackWorld canonical) α) :
    OracleComp (TypedAttackWorld canonical) (Option α) := by
  classical
  exact OracleComp.construct
    (fun value => pure (some value))
    (fun input _ next =>
      match input with
      | .inl ordinary =>
          if attackerDirectSeedHit seed ordinary then pure none else do
            let answer ← liftM ((TypedAttackWorld canonical).query (.inl ordinary))
            next answer
      | .inr test => do
          let answer ← liftM ((TypedAttackWorld canonical).query (.inr test))
          next answer)
    computation

theorem stopBeforeTyped_query_bind {α : Type} {canonical : Ciphertext}
    (seed : MasterSeed)
    (input : (TypedAttackWorld canonical).Domain)
    (next : (TypedAttackWorld canonical).Range input →
      OracleComp (TypedAttackWorld canonical) α) :
    stopBeforeTyped seed
      (liftM ((TypedAttackWorld canonical).query input) >>= next) =
      (match input with
      | .inl ordinary =>
          if attackerDirectSeedHit seed ordinary then pure none else do
            let answer ← liftM ((TypedAttackWorld canonical).query (.inl ordinary))
            stopBeforeTyped seed (next answer)
      | .inr test => do
          let answer ← liftM ((TypedAttackWorld canonical).query (.inr test))
          stopBeforeTyped seed (next answer)) := by
  cases input <;> rfl

theorem encodeTyped_stopBeforeTyped {α : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (computation : OracleComp (TypedAttackWorld canonical) α) :
    encodeTyped parameter seed canonical (stopBeforeTyped seed computation) =
      stopBeforeAttack seed
        (encodeTyped parameter seed canonical computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl ordinary =>
          rw [stopBeforeTyped_query_bind, encodeTyped_query_bind,
            stopBeforeAttack_query_bind]
          by_cases h : attackerDirectSeedHit seed ordinary
          · simp [h, encodeTyped]
          · simp only [if_neg h, encodeTyped_query_bind, ih]
      | inr test =>
          rw [stopBeforeTyped_query_bind, encodeTyped_query_bind,
            encodeTyped_query_bind,
            stopBeforeAttack_query_bind]
          simp only [encodeTyped_query_bind, ih]

theorem stopped_fixed_flag_eq_typed_trace {α : Type}
    (hash : QueryImpl HashSpec Id) (secretKey : Seeded.SecretKey)
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (computation : OracleComp (TypedAttackWorld canonical) α) :
    simulateQ (fixedHashWorld hash)
      (compiledFailureFlag secretKey
        (stopBeforeAttack seed
          (encodeTyped parameter seed canonical computation))) =
    (fun result => (result.1,
      typedHit hash parameter seed canonical result.2)) <$>
      simulateQ (fixedOuter hash secretKey)
        (typedFailureProgram (stopBeforeTyped seed computation)) := by
  rw [← encodeTyped_stopBeforeTyped]
  exact fixed_flag_eq_typed_trace hash secretKey parameter seed canonical
    (stopBeforeTyped seed computation)

theorem stopped_typed_failure_patch {α : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext) (secretKey : Seeded.SecretKey)
    (table : HashInput → HashOutput)
    (computation : OracleComp (TypedAttackWorld canonical) α)
    (before : QueryCache HashSpec) :
    evalSPMF ((simulateQ (romImpl + canonicalSigner secretKey)
      (typedFailureProgram (stopBeforeTyped seed computation))).run
      (patch (alteredRegion parameter seed canonical) table before)) =
    evalSPMF ((fun result => (result.1,
      patch (alteredRegion parameter seed canonical) table result.2)) <$>
      (simulateQ (romImpl + canonicalSigner secretKey)
        (typedFailureProgram (stopBeforeTyped seed computation))).run before) := by
  induction computation using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp [stopBeforeTyped, typedFailureProgram, simulateQ_pure]
  | query_bind input next ih =>
      rw [stopBeforeTyped_query_bind]
      cases input with
      | inl ordinary =>
          by_cases hbad : attackerDirectSeedHit seed ordinary
          · simp [hbad, typedFailureProgram, simulateQ_pure]
          · simp only [if_neg hbad, typedFailureProgram_query_bind,
              simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
            calc
              _ = evalSPMF (do
                let p ← (fun (result : OuterWorld.Range ordinary × QueryCache HashSpec) => (result.1,
                  patch (alteredRegion parameter seed canonical) table result.2)) <$>
                    ((romImpl + canonicalSigner secretKey) ordinary).run before
                (simulateQ (romImpl + canonicalSigner secretKey)
                  (typedFailureProgram (stopBeforeTyped seed (next p.1)))).run p.2) := by
                    rw [evalSPMF_bind, evalSPMF_bind]
                    exact congrArg (fun p : SPMF
                      (OuterWorld.Range ordinary × QueryCache HashSpec) =>
                        p >>= fun x => evalSPMF
                          ((simulateQ (romImpl + canonicalSigner secretKey)
                            (typedFailureProgram (stopBeforeTyped seed (next x.1)))).run x.2))
                      (actual_safe_step parameter seed canonical secretKey table
                        ordinary before hbad)
              _ = evalSPMF (do
                let a ← ((romImpl + canonicalSigner secretKey) ordinary).run before
                (simulateQ (romImpl + canonicalSigner secretKey)
                  (typedFailureProgram (stopBeforeTyped seed (next a.1)))).run
                    (patch (alteredRegion parameter seed canonical) table a.2)) := by
                      simp only [bind_map_left]
              _ = _ := by
                apply evalSPMF_bind_congr'
                intro a
                exact ih a.1 a.2
      | inr test =>
          simp only [typedFailureProgram_query_bind,
            simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
          simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp,
            Functor.map_map]
          simp only [map_pure, bind_pure_comp]
          simpa only [Functor.map_map, Function.comp_def] using
            (evalSPMF_map_eq_of_evalSPMF_eq (ih false before)
              (fun result => ((result.1.1, test :: result.1.2), result.2)))

theorem stopped_typed_failure_prepost {α Table : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext) (secretKey : Seeded.SecretKey)
    (draw : ProbComp Table)
    (encode : Table → HashInput → HashOutput)
    (computation : OracleComp (TypedAttackWorld canonical) α)
    (before : QueryCache HashSpec) :
    evalSPMF (do
      let table ← draw
      let result ← (simulateQ (romImpl + canonicalSigner secretKey)
        (typedFailureProgram (stopBeforeTyped seed computation))).run
          (patch (alteredRegion parameter seed canonical) (encode table) before)
      pure (table, result)) =
    evalSPMF (do
      let result ← (simulateQ (romImpl + canonicalSigner secretKey)
        (typedFailureProgram (stopBeforeTyped seed computation))).run before
      let table ← draw
      pure (table, (result.1,
        patch (alteredRegion parameter seed canonical) (encode table) result.2))) := by
  calc
    _ = evalSPMF (do
      let table ← draw
      let result ← (simulateQ (romImpl + canonicalSigner secretKey)
        (typedFailureProgram (stopBeforeTyped seed computation))).run before
      pure (table, (result.1,
        patch (alteredRegion parameter seed canonical) (encode table) result.2))) := by
          apply evalSPMF_bind_congr_left
          intro table
          simpa [Function.comp_def, bind_assoc] using
            evalSPMF_map_eq_of_evalSPMF_eq
              (stopped_typed_failure_patch parameter seed canonical secretKey
                (encode table) computation before)
              (fun result => (table, result))
    _ = _ := evalSPMF_bind_comm draw
      ((simulateQ (romImpl + canonicalSigner secretKey)
        (typedFailureProgram (stopBeforeTyped seed computation))).run before)
      (fun table result => pure (table,
        (result.1, patch (alteredRegion parameter seed canonical)
          (encode table) result.2)))

end SigGolfCandidate.SphincsCacheMacTypedStop

/-- info: 'SigGolfCandidate.SphincsCacheMacTypedStop.encodeTyped_stopBeforeTyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTypedStop.encodeTyped_stopBeforeTyped

/-- info: 'SigGolfCandidate.SphincsCacheMacTypedStop.stopped_fixed_flag_eq_typed_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTypedStop.stopped_fixed_flag_eq_typed_trace

/-- info: 'SigGolfCandidate.SphincsCacheMacTypedStop.stopped_typed_failure_prepost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacTypedStop.stopped_typed_failure_prepost
/- END SigGolfCandidate.SphincsCacheMacTypedStop -/

/- BEGIN SigGolfCandidate.SphincsCacheMacInlineOuter -/

/-! Inline opaque canonical-signing requests into the hash/coin world while
retaining the actual lazy random-oracle cache. -/

namespace SigGolfCandidate.SphincsCacheMacInlineOuter
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheMacCompiledGame
open SigGolfCandidate.SphincsCacheMacThreeService
open SigGolfCandidate.SphincsSeededNoMacQueries
open SigGolfCandidate.SphincsCacheMacFixedFlagTrace
open SigGolfCandidate.SphincsCacheMacEagerGame
open SphincsSecurity.Concrete

noncomputable def inlineOuter {α : Type} (secretKey : Seeded.SecretKey)
    (computation : OracleComp OuterWorld α) : OracleComp OracleWorld α :=
  OracleComp.construct
    pure
    (fun input _ next =>
      match input with
      | .inl direct => do
          let answer ← liftM (OracleWorld.query direct)
          next answer
      | .inr message => do
          let answer ← liftHash (Seeded.sign secretKey message)
          next answer)
    computation

theorem inlineOuter_rom_run {α : Type}
    (secretKey : Seeded.SecretKey)
    (computation : OracleComp OuterWorld α)
    (cache : QueryCache HashSpec) :
    evalSPMF ((simulateQ romImpl (inlineOuter secretKey computation)).run cache) =
      evalSPMF ((simulateQ (romImpl + canonicalSigner secretKey) computation).run cache) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp [inlineOuter, simulateQ_pure]
  | query_bind input next ih =>
      cases input with
      | inl direct =>
          simp only [inlineOuter, OracleComp.construct_query_bind,
            simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
          change evalSPMF (do
            let p ← (romImpl direct).run cache
            (simulateQ romImpl (inlineOuter secretKey (next p.1))).run p.2) =
            evalSPMF (do
              let p ← (romImpl direct).run cache
              (simulateQ (romImpl + canonicalSigner secretKey)
                (next p.1)).run p.2)
          apply evalSPMF_bind_congr'
          intro p
          exact ih p.1 p.2

      | inr message =>
          simp only [inlineOuter, OracleComp.construct_query_bind,
            simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
          rw [simulateQ_romImpl_liftHash]
          change evalSPMF (do
            let p ← (canonicalSigner secretKey message).run cache
            (simulateQ romImpl (inlineOuter secretKey (next p.1))).run p.2) =
            evalSPMF (do
              let p ← (canonicalSigner secretKey message).run cache
              (simulateQ (romImpl + canonicalSigner secretKey)
                (next p.1)).run p.2)
          apply evalSPMF_bind_congr'
          intro p
          exact ih p.1 p.2

theorem inlineOuter_rom_run' {α : Type}
    (secretKey : Seeded.SecretKey)
    (computation : OracleComp OuterWorld α)
    (cache : QueryCache HashSpec) :
    evalSPMF ((simulateQ romImpl (inlineOuter secretKey computation)).run' cache) =
      evalSPMF ((simulateQ (romImpl + canonicalSigner secretKey) computation).run' cache) := by
  simpa only [StateT.run'_eq] using
    evalSPMF_map_eq_of_evalSPMF_eq
      (inlineOuter_rom_run secretKey computation cache) Prod.fst

theorem inlineOuter_fixed {α : Type}
    (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey)
    (computation : OracleComp OuterWorld α) :
    simulateQ (fixedHashWorld hash) (inlineOuter secretKey computation) =
      simulateQ (fixedOuter hash secretKey) computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [inlineOuter, simulateQ_pure]
  | query_bind input next ih =>
      cases input with
      | inl direct =>
          simp only [inlineOuter, OracleComp.construct_query_bind,
            simulateQ_bind, simulateQ_spec_query, fixedOuter]
          apply bind_congr
          intro answer
          exact ih answer
      | inr message =>
          simp only [inlineOuter, OracleComp.construct_query_bind,
            simulateQ_bind, simulateQ_spec_query, fixedOuter]
          rw [fixed_hash_liftHash]
          simp only [pure_bind]
          exact ih (evalWithAnswerFn hash (Seeded.sign secretKey message))

end SigGolfCandidate.SphincsCacheMacInlineOuter

/-- info: 'SigGolfCandidate.SphincsCacheMacInlineOuter.inlineOuter_rom_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacInlineOuter.inlineOuter_rom_run

/-- info: 'SigGolfCandidate.SphincsCacheMacInlineOuter.inlineOuter_rom_run'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacInlineOuter.inlineOuter_rom_run'

/-- info: 'SigGolfCandidate.SphincsCacheMacInlineOuter.inlineOuter_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacInlineOuter.inlineOuter_fixed
/- END SigGolfCandidate.SphincsCacheMacInlineOuter -/

/- BEGIN SigGolfCandidate.SphincsCacheMacRealIdeal -/

/-! Join the mixed-channel eager table with the stopped typed trace. -/

namespace SigGolfCandidate.SphincsCacheMacRealIdeal
open OracleComp OracleComp.DeferredSampling OracleSpec SphincsSecurity
open SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCacheMacFiniteDomain
open SigGolfCandidate.SphincsCacheMacCompiledGame
open SigGolfCandidate.SphincsCacheMacTypedGame
open SigGolfCandidate.SphincsCacheMacTypedTrace
open SigGolfCandidate.SphincsCacheMacTypedStop
open SigGolfCandidate.SphincsCacheMacInlineOuter
open SigGolfCandidate.SphincsCacheMacFixedFlagTrace
open SigGolfCandidate.SphincsCacheMacPatchRun
open SigGolfCandidate.SphincsCacheMacSignerPrePost
open SigGolfCandidate.SphincsCacheBlindMacGuess
open SigGolfCandidate.SphincsCacheMacEagerGame
open SigGolfCandidate.SphincsSeededNoMacQueries
open SigGolfCandidate.SphincsMaskedCacheProgramming
open SphincsSecurity.Seeded
open SigGolfCandidate.SphincsCacheMacHashOutputBlind

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem finiteHashAnswer_patched_altered
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (table : HashInput → HashOutput)
    (before : QueryCache HashSpec)
    (inputs : Finset HashInput) (remainder : inputs → HashOutput)
    (candidate : Altered canonical) :
    finiteHashAnswer
      (patch (alteredRegion parameter seed canonical) table before)
      inputs remainder
      (alteredInput parameter seed canonical candidate) =
        table (alteredInput parameter seed canonical candidate) := by
  have hregion : alteredRegion parameter seed canonical
      (alteredInput parameter seed canonical candidate) := ⟨candidate, rfl⟩
  simp [finiteHashAnswer, patch, hregion]

theorem typedHit_congr (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (left right : QueryImpl HashSpec Id)
    (hagrees : ∀ candidate : Altered canonical,
      left (alteredInput parameter seed canonical candidate) =
        right (alteredInput parameter seed canonical candidate))
    (attempts : List (Altered canonical × Digest)) :
    typedHit left parameter seed canonical attempts =
      typedHit right parameter seed canonical attempts := by
  classical
  have hfun : (fun candidate : Altered canonical =>
      truncateHash (left (alteredInput parameter seed canonical candidate))) =
    (fun candidate : Altered canonical =>
      truncateHash (right (alteredInput parameter seed canonical candidate))) := by
    funext candidate
    rw [hagrees candidate]
  simp only [typedHit, hfun]

noncomputable def alteredTableHash (parameter : PublicParameter)
    (seed : MasterSeed) (canonical : Ciphertext)
    (outputs : Altered canonical → HashOutput) :
    HashInput → HashOutput := by
  classical
  exact fun input =>
    if h : alteredRegion parameter seed canonical input then
      outputs (Classical.choose h)
    else 0

theorem alteredTableHash_apply (parameter : PublicParameter)
    (seed : MasterSeed) (canonical : Ciphertext)
    (outputs : Altered canonical → HashOutput)
    (candidate : Altered canonical) :
    alteredTableHash parameter seed canonical outputs
      (alteredInput parameter seed canonical candidate) = outputs candidate := by
  have hregion : alteredRegion parameter seed canonical
      (alteredInput parameter seed canonical candidate) := ⟨candidate, rfl⟩
  have hchoose := Classical.choose_spec hregion
  have heq : Classical.choose hregion = candidate :=
    alteredInput_injective parameter seed canonical hchoose.symm
  simp [alteredTableHash, hregion, heq]

theorem cacheTable_altered_eq_patch (parameter : PublicParameter)
    (seed : MasterSeed) (canonical : Ciphertext)
    (outputs : Altered canonical → HashOutput)
    (before : QueryCache HashSpec) :
    SphincsSecurity.Seeded.cacheTable before
      (alteredInput parameter seed canonical) outputs =
    patch (alteredRegion parameter seed canonical)
      (alteredTableHash parameter seed canonical outputs) before := by
  classical
  funext input
  by_cases hregion : alteredRegion parameter seed canonical input
  · obtain ⟨candidate, htarget⟩ := hregion
    subst input
    rw [SphincsSecurity.Seeded.cacheTable_apply _ _
      (alteredInput_injective parameter seed canonical) outputs candidate]
    have h : alteredRegion parameter seed canonical
        (alteredInput parameter seed canonical candidate) := ⟨candidate, rfl⟩
    simp [patch, h, alteredTableHash_apply]
  · rw [SphincsSecurity.Seeded.cacheTable_apply_of_not_mem]
    · simp [patch, hregion]
    · intro candidate
      exact fun heq => hregion ⟨candidate, heq⟩

theorem presample_altered_patch {α : Type}
    (material : Seeded.KeyMaterial) (seed : MasterSeed)
    (pads : List (BitVec 32 × HashOutput))
    (canonical : Ciphertext) (macAnswer : HashOutput)
    (program : OracleComp OracleWorld α) :
    let before := maskedMaterialCache material seed pads
      (List.ofFn canonical) macAnswer
    evalSPMF ((simulateQ romImpl program).run' before) =
      evalSPMF (do
        let outputs ← ($ᵗ (Altered canonical → HashOutput) : ProbComp _)
        (simulateQ romImpl program).run'
          (patch (alteredRegion material.1 seed canonical)
            (alteredTableHash material.1 seed canonical outputs) before)) := by
  intro before
  rw [presample_all_altered material seed pads canonical macAnswer program]
  rw [evalSPMF_bind,
    SphincsSecurity.Seeded.evalSPMF_sequenceFin_uniform, ← evalSPMF_bind]
  let equiv := SphincsSecurity.Seeded.finTableEquiv
    (Altered canonical) HashOutput
  have huni := evalSPMF_map_bijective_uniform_cross
    (α := Fin (Fintype.card (Altered canonical)) → HashOutput)
    (β := Altered canonical → HashOutput)
    equiv equiv.bijective
  conv_rhs => rw [evalSPMF_bind, ← huni, ← evalSPMF_bind]
  simp only [bind_map_left]
  apply evalSPMF_bind_congr_left
  intro values
  have hcache :
      cacheFin before (allAlteredInputs material.1 seed canonical) values =
        patch (alteredRegion material.1 seed canonical)
          (alteredTableHash material.1 seed canonical (equiv values)) before := by
    rw [← cacheTable_altered_eq_patch]
    change cacheFin before (allAlteredInputs material.1 seed canonical) values =
      cacheFin before (allAlteredInputs material.1 seed canonical)
        (equiv.symm (equiv values))
    rw [Equiv.symm_apply_apply]
  rw [hcache]

theorem stopped_real_eq_typed_hit {α : Type}
    (secretKey : Seeded.SecretKey)
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (computation : OracleComp (TypedAttackWorld canonical) α)
    (table : HashInput → HashOutput)
    (before : QueryCache HashSpec)
    (inputs : Finset HashInput)
    (hattack : hashInputs (compiledFailureFlag secretKey
      (stopBeforeAttack seed
        (encodeTyped parameter seed canonical computation))) ⊆ inputs)
    (hfailure : hashInputs (inlineOuter secretKey
      (typedFailureProgram (stopBeforeTyped seed computation))) ⊆ inputs) :
    let cache := patch (alteredRegion parameter seed canonical) table before
    let attack := compiledFailureFlag secretKey
      (stopBeforeAttack seed (encodeTyped parameter seed canonical computation))
    let failure := typedFailureProgram (stopBeforeTyped seed computation)
    evalSPMF ((simulateQ romImpl attack).run' cache) =
      evalSPMF ((fun result => (result.1,
        typedHit table parameter seed canonical result.2)) <$>
        (simulateQ (romImpl + canonicalSigner secretKey) failure).run' cache) := by
  intro cache attack failure
  let rawFailure := inlineOuter secretKey failure
  rw [evalSPMF_romRun_eq_finiteHash attack inputs hattack cache]
  have hinline := evalSPMF_map_eq_of_evalSPMF_eq
    (inlineOuter_rom_run' secretKey failure cache)
    (fun result => (result.1, typedHit table parameter seed canonical result.2))
  rw [← hinline]
  have heager := evalSPMF_map_eq_of_evalSPMF_eq
    (evalSPMF_romRun_eq_finiteHash rawFailure inputs hfailure cache)
    (fun result => (result.1, typedHit table parameter seed canonical result.2))
  rw [heager]
  simp only [map_bind]
  apply evalSPMF_bind_congr_left
  intro answer
  let hash := finiteHashAnswer cache inputs answer
  have hpatch : ∀ candidate : Altered canonical,
      hash (alteredInput parameter seed canonical candidate) =
        table (alteredInput parameter seed canonical candidate) := by
    intro candidate
    exact finiteHashAnswer_patched_altered parameter seed canonical
      table before inputs answer candidate
  have hhit : ∀ attempts : List (Altered canonical × Digest),
      typedHit hash parameter seed canonical attempts =
        typedHit table parameter seed canonical attempts := by
    intro attempts
    exact typedHit_congr parameter seed canonical hash table hpatch attempts
  rw [stopped_fixed_flag_eq_typed_trace hash secretKey parameter seed
    canonical computation]
  rw [inlineOuter_fixed hash secretKey failure]
  simp only [evalSPMF_map]
  congr 1
  funext result
  exact Prod.ext rfl (hhit result.2)

theorem stopped_typed_failure_prepost_output {α Table : Type}
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext) (secretKey : Seeded.SecretKey)
    (draw : ProbComp Table)
    (encode : Table → HashInput → HashOutput)
    (computation : OracleComp (TypedAttackWorld canonical) α)
    (before : QueryCache HashSpec) :
    let failure := typedFailureProgram (stopBeforeTyped seed computation)
    evalSPMF (do
      let table ← draw
      let result ← (simulateQ (romImpl + canonicalSigner secretKey) failure).run'
        (patch (alteredRegion parameter seed canonical) (encode table) before)
      pure (table, result)) =
    evalSPMF (do
      let result ← (simulateQ (romImpl + canonicalSigner secretKey) failure).run' before
      let table ← draw
      pure (table, result)) := by
  intro failure
  have h := evalSPMF_map_eq_of_evalSPMF_eq
    (stopped_typed_failure_prepost parameter seed canonical secretKey
      draw encode computation before)
    (fun pair => (pair.1, pair.2.1))
  simpa only [StateT.run'_eq, bind_map_left, map_bind,
    Functor.map_map, Function.comp_def, map_pure,
    bind_pure_comp] using h

noncomputable def alteredTableHit (canonical : Ciphertext)
    (outputs : Altered canonical → HashOutput)
    (attempts : List (Altered canonical × Digest)) : Bool := by
  classical
  exact decide (Hit attempts (fun candidate => truncateHash (outputs candidate)))

theorem typedHit_alteredTableHash (parameter : PublicParameter)
    (seed : MasterSeed) (canonical : Ciphertext)
    (outputs : Altered canonical → HashOutput)
    (attempts : List (Altered canonical × Digest)) :
    typedHit (alteredTableHash parameter seed canonical outputs)
      parameter seed canonical attempts =
    alteredTableHit canonical outputs attempts := by
  have hfun : (fun candidate : Altered canonical =>
      truncateHash (alteredTableHash parameter seed canonical outputs
        (alteredInput parameter seed canonical candidate))) =
    (fun candidate => truncateHash (outputs candidate)) := by
      funext candidate
      rw [alteredTableHash_apply]
  simp only [typedHit, alteredTableHit]
  rw [hfun]

theorem stopped_finite_hash_cover {α : Type}
    (secretKey : Seeded.SecretKey)
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonical : Ciphertext)
    (computation : OracleComp (TypedAttackWorld canonical) α) :
    ∃ inputs : Finset HashInput,
      hashInputs (compiledFailureFlag secretKey
        (stopBeforeAttack seed
          (encodeTyped parameter seed canonical computation))) ⊆ inputs ∧
      hashInputs (inlineOuter secretKey
        (typedFailureProgram (stopBeforeTyped seed computation))) ⊆ inputs := by
  let attack := compiledFailureFlag secretKey
    (stopBeforeAttack seed
      (encodeTyped parameter seed canonical computation))
  let failure := inlineOuter secretKey
    (typedFailureProgram (stopBeforeTyped seed computation))
  exact ⟨hashInputs attack ∪ hashInputs failure,
    Finset.subset_union_left, Finset.subset_union_right⟩

theorem real_first_hit_independent {α : Type}
    (secretKey : Seeded.SecretKey)
    (material : Seeded.KeyMaterial) (seed : MasterSeed)
    (pads : List (BitVec 32 × HashOutput))
    (canonical : Ciphertext) (macAnswer : HashOutput)
    (computation : OracleComp (TypedAttackWorld canonical) α)
    (inputs : Finset HashInput)
    (hattack : hashInputs (compiledFailureFlag secretKey
      (stopBeforeAttack seed
        (encodeTyped material.1 seed canonical computation))) ⊆ inputs)
    (hfailure : hashInputs (inlineOuter secretKey
      (typedFailureProgram (stopBeforeTyped seed computation))) ⊆ inputs) :
    let before := maskedMaterialCache material seed pads
      (List.ofFn canonical) macAnswer
    let attack := compiledFailureFlag secretKey
      (stopBeforeAttack seed
        (encodeTyped material.1 seed canonical computation))
    let failure := typedFailureProgram (stopBeforeTyped seed computation)
    evalSPMF ((simulateQ romImpl attack).run' before) =
      evalSPMF (do
        let result ← (simulateQ (romImpl + canonicalSigner secretKey) failure).run' before
        let outputs ← ($ᵗ (Altered canonical → HashOutput) : ProbComp _)
        pure (result.1, alteredTableHit canonical outputs result.2)) := by
  intro before attack failure
  let draw : ProbComp (Altered canonical → HashOutput) := $ᵗ _
  let encode := alteredTableHash material.1 seed canonical
  rw [presample_altered_patch material seed pads canonical macAnswer attack]
  have hstep : ∀ outputs : Altered canonical → HashOutput,
      evalSPMF ((simulateQ romImpl attack).run'
        (patch (alteredRegion material.1 seed canonical) (encode outputs) before)) =
      evalSPMF ((fun result => (result.1,
        typedHit (encode outputs) material.1 seed canonical result.2)) <$>
        (simulateQ (romImpl + canonicalSigner secretKey) failure).run'
          (patch (alteredRegion material.1 seed canonical) (encode outputs) before)) := by
    intro outputs
    exact stopped_real_eq_typed_hit secretKey material.1 seed canonical
      computation (encode outputs) before inputs hattack hfailure
  calc
    _ = evalSPMF (do
      let outputs ← draw
      let result ← (simulateQ (romImpl + canonicalSigner secretKey) failure).run'
        (patch (alteredRegion material.1 seed canonical) (encode outputs) before)
      pure (result.1,
        typedHit (encode outputs) material.1 seed canonical result.2)) := by
          apply evalSPMF_bind_congr_left
          intro outputs
          simpa only [evalSPMF_map, bind_pure_comp] using hstep outputs
    _ = evalSPMF (do
      let result ← (simulateQ (romImpl + canonicalSigner secretKey) failure).run' before
      let outputs ← draw
      pure (result.1,
        typedHit (encode outputs) material.1 seed canonical result.2)) := by
          have hpre := evalSPMF_map_eq_of_evalSPMF_eq
            (stopped_typed_failure_prepost_output material.1 seed canonical
              secretKey draw encode computation before)
            (fun pair => (pair.2.1,
              typedHit (encode pair.1) material.1 seed canonical pair.2.2))
          simpa only [evalSPMF_map, map_bind, map_pure,
            bind_pure_comp, Functor.map_map, Function.comp_def] using hpre
    _ = _ := by
          apply evalSPMF_bind_congr_left
          intro result
          apply evalSPMF_bind_congr_left
          intro outputs
          simp only [encode, typedHit_alteredTableHash]

theorem stopped_trace_blind_bound {Env : Type}
    (canonical : Ciphertext) (environment : ProbComp Env)
    (plan : Env → List (Altered canonical × Digest))
    (q : Nat)
    (hbudget : ∀ env ∈ support environment, (plan env).length ≤ q) :
    Pr[fun result => alteredTableHit canonical result.2 (plan result.1) = true |
      (do
        let env ← environment
        let outputs ← ($ᵗ (Altered canonical → HashOutput) : ProbComp _)
        pure (env, outputs))] ≤
      q * (Fintype.card Digest : ENNReal)⁻¹ := by
  have hevent : (fun result : Env × (Altered canonical → HashOutput) =>
      alteredTableHit canonical result.2 (plan result.1) = true) =
    (fun result => Hit (plan result.1)
      (fun candidate => truncateHash (result.2 candidate))) := by
    funext result
    simp [alteredTableHit]
  rw [hevent]
  apply probEvent_bind_le_of_forall_le
  intro env henv
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  let targets : PMF (Altered canonical → Digest) :=
    (fun (outputs : Altered canonical → HashOutput) candidate =>
      truncateHash (outputs candidate)) <$>
      PMF.uniformOfFintype (Altered canonical → HashOutput)
  have hmarginal : ∀ candidate guess,
      Pr[fun table => table candidate = guess | targets] ≤
        (Fintype.card Digest : ENNReal)⁻¹ := by
    intro candidate guess
    rw [probEvent_map]
    exact (uniform_altered_hash_marginal_pmf canonical candidate guess).le
  have hfixed := fixed_plan_bound targets hmarginal (plan env)
  rw [probEvent_map] at hfixed
  have hq : ((plan env).length : ENNReal) ≤ q := by
    exact_mod_cast hbudget env henv
  have hineq :
      Pr[Hit (plan env) ∘
        (fun outputs : Altered canonical → HashOutput =>
          fun candidate => truncateHash (outputs candidate)) |
        PMF.uniformOfFintype (Altered canonical → HashOutput)] ≤
      q * (Fintype.card Digest : ENNReal)⁻¹ := by
    exact hfixed.trans (by gcongr)
  simpa only [probEvent_def, evalSPMF_uniformSample,
    SPMF.probEvent_liftM, Function.comp_def] using hineq

theorem real_first_hit_le {α : Type}
    (secretKey : Seeded.SecretKey)
    (material : Seeded.KeyMaterial) (seed : MasterSeed)
    (pads : List (BitVec 32 × HashOutput))
    (canonical : Ciphertext) (macAnswer : HashOutput)
    (computation : OracleComp (TypedAttackWorld canonical) α)
    (inputs : Finset HashInput)
    (hattack : hashInputs (compiledFailureFlag secretKey
      (stopBeforeAttack seed
        (encodeTyped material.1 seed canonical computation))) ⊆ inputs)
    (hfailure : hashInputs (inlineOuter secretKey
      (typedFailureProgram (stopBeforeTyped seed computation))) ⊆ inputs)
    (q : Nat)
    (hbudget : ∀ result ∈ support
      ((simulateQ (romImpl + canonicalSigner secretKey)
        (typedFailureProgram (stopBeforeTyped seed computation))).run'
          (maskedMaterialCache material seed pads
            (List.ofFn canonical) macAnswer)),
      result.2.length ≤ q) :
    let before := maskedMaterialCache material seed pads
      (List.ofFn canonical) macAnswer
    let attack := compiledFailureFlag secretKey
      (stopBeforeAttack seed
        (encodeTyped material.1 seed canonical computation))
    Pr[fun result => result.2 = true |
      (simulateQ romImpl attack).run' before] ≤
      q * (Fintype.card Digest : ENNReal)⁻¹ := by
  intro before attack
  let failure := typedFailureProgram (stopBeforeTyped seed computation)
  have hdist := real_first_hit_independent secretKey material seed pads
    canonical macAnswer computation inputs hattack hfailure
  have hbound := stopped_trace_blind_bound canonical
    ((simulateQ (romImpl + canonicalSigner secretKey) failure).run' before)
    (fun result => result.2) q hbudget
  have hright :
      Pr[fun result => result.2 = true |
        (do
          let result ← (simulateQ (romImpl + canonicalSigner secretKey) failure).run' before
          let outputs ← ($ᵗ (Altered canonical → HashOutput) : ProbComp _)
          pure (result.1, alteredTableHit canonical outputs result.2))] ≤
        q * (Fintype.card Digest : ENNReal)⁻¹ := by
    have hcomp :
        (do
          let result ← (simulateQ (romImpl + canonicalSigner secretKey) failure).run' before
          let outputs ← ($ᵗ (Altered canonical → HashOutput) : ProbComp _)
          pure (result.1, alteredTableHit canonical outputs result.2)) =
        (fun pair => (pair.1.1, alteredTableHit canonical pair.2 pair.1.2)) <$>
          (do
            let result ← (simulateQ (romImpl + canonicalSigner secretKey) failure).run' before
            let outputs ← ($ᵗ (Altered canonical → HashOutput) : ProbComp _)
            pure (result, outputs)) := by
      simp only [map_bind, bind_pure_comp, Functor.map_map]
    rw [hcomp, probEvent_map]
    exact hbound
  exact (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans hright

theorem real_first_hit_le_of_attempts {α : Type}
    (secretKey : Seeded.SecretKey)
    (material : Seeded.KeyMaterial) (seed : MasterSeed)
    (pads : List (BitVec 32 × HashOutput))
    (canonical : Ciphertext) (macAnswer : HashOutput)
    (computation : OracleComp (TypedAttackWorld canonical) α)
    (q : Nat)
    (hbudget : ∀ result ∈ support
      ((simulateQ (romImpl + canonicalSigner secretKey)
        (typedFailureProgram (stopBeforeTyped seed computation))).run'
          (maskedMaterialCache material seed pads
            (List.ofFn canonical) macAnswer)),
      result.2.length ≤ q) :
    Pr[fun result => result.2 = true |
      (simulateQ romImpl
        (compiledFailureFlag secretKey
          (stopBeforeAttack seed
            (encodeTyped material.1 seed canonical computation)))).run'
        (maskedMaterialCache material seed pads
          (List.ofFn canonical) macAnswer)] ≤
      q * (Fintype.card Digest : ENNReal)⁻¹ := by
  obtain ⟨inputs, hattack, hfailure⟩ :=
    stopped_finite_hash_cover secretKey material.1 seed canonical computation
  exact real_first_hit_le secretKey material seed pads canonical macAnswer
    computation inputs hattack hfailure q hbudget

end SigGolfCandidate.SphincsCacheMacRealIdeal

/-- info: 'SigGolfCandidate.SphincsCacheMacRealIdeal.finiteHashAnswer_patched_altered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacRealIdeal.finiteHashAnswer_patched_altered

/-- info: 'SigGolfCandidate.SphincsCacheMacRealIdeal.typedHit_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacRealIdeal.typedHit_congr

/-- info: 'SigGolfCandidate.SphincsCacheMacRealIdeal.cacheTable_altered_eq_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacRealIdeal.cacheTable_altered_eq_patch

/-- info: 'SigGolfCandidate.SphincsCacheMacRealIdeal.presample_altered_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacRealIdeal.presample_altered_patch

/-- info: 'SigGolfCandidate.SphincsCacheMacRealIdeal.stopped_real_eq_typed_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacRealIdeal.stopped_real_eq_typed_hit

/-- info: 'SigGolfCandidate.SphincsCacheMacRealIdeal.stopped_typed_failure_prepost_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacRealIdeal.stopped_typed_failure_prepost_output

/-- info: 'SigGolfCandidate.SphincsCacheMacRealIdeal.real_first_hit_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacRealIdeal.real_first_hit_independent

/-- info: 'SigGolfCandidate.SphincsCacheMacRealIdeal.stopped_finite_hash_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacRealIdeal.stopped_finite_hash_cover

/-- info: 'SigGolfCandidate.SphincsCacheMacRealIdeal.real_first_hit_le_of_attempts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacRealIdeal.real_first_hit_le_of_attempts
/- END SigGolfCandidate.SphincsCacheMacRealIdeal -/
