import SigGolf.Security
import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
namespace SigGolfCandidate.SphincsOrganizerFiniteHash

open SigGolf _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false

noncomputable def organizerRom : QueryImpl SigGolf.World
    (StateT (QueryCache SigGolf.HashSpec) ProbComp) :=
  unifFwdImpl SigGolf.HashSpec +
    (randomOracle : QueryImpl SigGolf.HashSpec
      (StateT (QueryCache SigGolf.HashSpec) ProbComp))

noncomputable def fixedOrganizerWorld (hash : SigGolf.Hash) :
    QueryImpl SigGolf.World ProbComp
  | .inl input => liftM (unifSpec.query input)
  | .inr input => pure (hash input)

noncomputable local instance instSampleableFiniteTable
    (inputs : Finset SigGolf.Query) : SampleableType (inputs → BitVec 256) :=
  SampleableType.ofFintype (inputs → BitVec 256)

noncomputable def sampleHashTable (inputs : Finset SigGolf.Query) : ProbComp (inputs → BitVec 256) :=
  $ᵗ (inputs → BitVec 256)

theorem evalSPMF_finiteHashTable_extract {α : Type} (inputs : Finset SigGolf.Query) (input : inputs)
    (next : (inputs → BitVec 256) → BitVec 256 → ProbComp α) :
    𝒮[do let table ← ($ᵗ (inputs → BitVec 256) : ProbComp _); next table (table input)] =
      𝒮[do
        let output ← ($ᵗ BitVec 256 : ProbComp _)
        let table ← ($ᵗ (inputs → BitVec 256) : ProbComp _)
        next (Function.update table input output) output] := by
  classical
  have h := congrArg (fun distribution : SPMF (inputs → BitVec 256) =>
    distribution >>= fun table => 𝒮[next table (table input)])
    (evalSPMF_uniformSample_bind_update (R := BitVec 256) input)
  simpa only [evalSPMF_bind, bind_assoc, evalSPMF_pure, pure_bind, Function.update_self] using h.symm

noncomputable def hashInputs {α : Type} (computation : OracleComp SigGolf.World α) : Finset SigGolf.Query := by
  classical
  induction computation using OracleComp.construct with
  | pure _ => exact ∅
  | query_bind input _ tail =>
      exact (match input with | .inl _ => ∅ | .inr input => {input}) ∪ Finset.univ.biUnion tail

@[simp] theorem hashInputs_pure {α : Type} (value : α) :
    hashInputs (pure value) = ∅ := rfl

theorem hashInputs_query_bind {α : Type} (input : SigGolf.World.Domain)
    (next : SigGolf.World.Range input → OracleComp SigGolf.World α) :
    hashInputs (liftM (SigGolf.World.query input) >>= next) =
      (match input with | .inl _ => ∅ | .inr input => {input}) ∪
        Finset.univ.biUnion (fun output => hashInputs (next output)) := by
  simp only [hashInputs, OracleComp.construct_query_bind]
  cases input <;> rfl

attribute [local irreducible] hashInputs

theorem hashInputs_next_subset {α : Type} (input : SigGolf.World.Domain)
    (next : SigGolf.World.Range input → OracleComp SigGolf.World α) (output : SigGolf.World.Range input) :
    hashInputs (next output) ⊆ hashInputs (liftM (SigGolf.World.query input) >>= next) := by
  intro row hrow
  rw [hashInputs_query_bind, Finset.mem_union]
  exact Or.inr (Finset.mem_biUnion.mpr ⟨output, Finset.mem_univ _, hrow⟩)

theorem mem_hashInputs_hash_bind {α : Type} (input : SigGolf.Query)
    (next : BitVec 256 → OracleComp SigGolf.World α) :
    input ∈ hashInputs (liftM (SigGolf.World.query (.inr input)) >>= next) := by
  rw [hashInputs_query_bind, Finset.mem_union]
  exact Or.inl (Finset.mem_singleton_self _)

noncomputable def finiteHashAnswer (cache : QueryCache SigGolf.HashSpec) (inputs : Finset SigGolf.Query)
    (table : inputs → BitVec 256) : QueryImpl SigGolf.HashSpec Id :=
  fun input => (cache input).getD (if h : input ∈ inputs then table ⟨input, h⟩ else 0)

theorem finiteHashAnswer_some (cache : QueryCache SigGolf.HashSpec) (inputs : Finset SigGolf.Query)
    (table : inputs → BitVec 256) (input : SigGolf.Query) (output : BitVec 256) (h : cache input = some output) :
    finiteHashAnswer cache inputs table input = output := by
  simp only [finiteHashAnswer, h, Option.getD_some]

theorem finiteHashAnswer_none (cache : QueryCache SigGolf.HashSpec) (inputs : Finset SigGolf.Query)
    (table : inputs → BitVec 256) (input : SigGolf.Query) (hin : input ∈ inputs) (h : cache input = none) :
    finiteHashAnswer cache inputs table input = table ⟨input, hin⟩ := by
  simp only [finiteHashAnswer, h, Option.getD_none, dif_pos hin]

theorem finiteHashAnswer_cacheQuery (cache : QueryCache SigGolf.HashSpec) (inputs : Finset SigGolf.Query)
    (table : inputs → BitVec 256) (input : SigGolf.Query) (hin : input ∈ inputs)
    (h : cache input = none) (output : BitVec 256) :
    finiteHashAnswer (cache.cacheQuery input output) inputs table =
      finiteHashAnswer cache inputs (Function.update table ⟨input, hin⟩ output) := by
  classical
  funext row
  by_cases heq : row = input
  · subst row
    simp [finiteHashAnswer, h, hin]
  · by_cases hrow : row ∈ inputs
    · have hne : (⟨row, hrow⟩ : inputs) ≠ ⟨input, hin⟩ := fun hsub => heq (congrArg Subtype.val hsub)
      simp [finiteHashAnswer, QueryCache.cacheQuery, heq, hrow, hne]
    · simp [finiteHashAnswer, QueryCache.cacheQuery, heq, hrow]

theorem romRun_query_bind {α : Type} (input : SigGolf.World.Domain)
    (next : SigGolf.World.Range input → OracleComp SigGolf.World α) (cache : QueryCache SigGolf.HashSpec) :
    (simulateQ organizerRom (liftM (SigGolf.World.query input) >>= next)).run' cache =
      (organizerRom input).run cache >>= fun result => (simulateQ organizerRom (next result.1)).run' result.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

theorem evalSPMF_romRun_eq_finiteHash {α : Type} (computation : OracleComp SigGolf.World α)
    (inputs : Finset SigGolf.Query) (hinputs : hashInputs computation ⊆ inputs) (cache : QueryCache SigGolf.HashSpec) :
    𝒮[(simulateQ organizerRom computation).run' cache] =
      𝒮[do
        let table ← ($ᵗ (inputs → BitVec 256) : ProbComp _)
        simulateQ (fixedOrganizerWorld (finiteHashAnswer cache inputs table)) computation] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      exact (evalSPMF_bind_const_neverFails _ (by simp) (pure value)).symm
  | query_bind input next ih =>
      have hnext : ∀ output, hashInputs (next output) ⊆ inputs :=
        fun output => (hashInputs_next_subset input next output).trans hinputs
      rw [romRun_query_bind]
      cases input with
      | inl sample =>
          change 𝒮[(liftM (unifSpec.query sample) : ProbComp _) >>= fun output =>
            (simulateQ organizerRom (next output)).run' cache] = _
          trans 𝒮[do
            let output ← (liftM (unifSpec.query sample) : ProbComp _)
            let table ← ($ᵗ (inputs → BitVec 256) : ProbComp _)
            simulateQ (fixedOrganizerWorld (finiteHashAnswer cache inputs table)) (next output)]
          · exact evalSPMF_bind_congr_left _ _ _ (fun output => ih output (hnext output) cache)
          · rw [evalSPMF_bind_comm]
            apply evalSPMF_bind_congr_left
            intro table
            simp only [simulateQ_bind, simulateQ_spec_query, fixedOrganizerWorld]
            rfl
      | inr input =>
          have hin : input ∈ inputs := hinputs (mem_hashInputs_hash_bind input next)
          rw [show organizerRom (.inr input) = randomOracle (spec := SigGolf.HashSpec) input from rfl]
          cases hcache : cache input with
          | some output =>
              rw [QueryImpl.withCaching_run_some _ hcache, pure_bind, ih output (hnext output) cache]
              apply evalSPMF_bind_congr_left
              intro table
              simp only [simulateQ_bind, simulateQ_spec_query, fixedOrganizerWorld,
                finiteHashAnswer_some cache inputs table input output hcache, pure_bind]
          | none =>
              rw [QueryImpl.withCaching_run_none _ hcache, map_eq_bind_pure_comp]
              simp only [Function.comp, bind_assoc, pure_bind]
              trans 𝒮[do
                let output ← ($ᵗ BitVec 256 : ProbComp _)
                let table ← ($ᵗ (inputs → BitVec 256) : ProbComp _)
                simulateQ (fixedOrganizerWorld (finiteHashAnswer (cache.cacheQuery input output) inputs table)) (next output)]
              · exact evalSPMF_bind_congr_left _ _ _ (fun output => ih output (hnext output) _)
              · simp_rw [finiteHashAnswer_cacheQuery cache inputs _ input hin hcache]
                rw [← evalSPMF_finiteHashTable_extract inputs (⟨input, hin⟩ : inputs)
                  (fun table output => simulateQ (fixedOrganizerWorld (finiteHashAnswer cache inputs table)) (next output))]
                apply evalSPMF_bind_congr_left
                intro table
                simp only [simulateQ_bind, simulateQ_spec_query, fixedOrganizerWorld,
                  finiteHashAnswer_none cache inputs table input hin hcache, pure_bind]

/-- Keep the public key and cache in the output while analyzing the complete
security interaction. Fresh private `.sample` draws remain probabilistic. -/
def setupAndInteract (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (secretKey : SigGolf.SecretKey) (rounds : Nat) :
    OracleComp SigGolf.World
      (Option (SigGolf.PublicKey × SigGolf.Cache) × SigGolf.AttackResult) := do
  let keygen ← liftM (submission.run .keygen secretKey)
  let some (pk, cache) := keygen.value |
    return (none, ⟨false, keygen.hashCalls⟩)
  let result ← submission.interact adversary secretKey pk rounds
    (adversary.initial pk cache) { hashCalls := keygen.hashCalls }
  return (some (pk, cache), result)

theorem setupAndInteract_finiteLaw
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (secretKey : SigGolf.SecretKey) (rounds : Nat) :
    let program := setupAndInteract submission adversary secretKey rounds
    let inputs := hashInputs program
    𝒮[SigGolf.withRandomness program] =
      𝒮[do
        let table ← sampleHashTable inputs
        simulateQ (fixedOrganizerWorld (finiteHashAnswer ∅ inputs table)) program] := by
  dsimp only
  exact evalSPMF_romRun_eq_finiteHash
    (setupAndInteract submission adversary secretKey rounds)
    (hashInputs (setupAndInteract submission adversary secretKey rounds))
    (Finset.Subset.rfl) ∅

end SigGolfCandidate.SphincsOrganizerFiniteHash

/-- info: 'SigGolfCandidate.SphincsOrganizerFiniteHash.evalSPMF_romRun_eq_finiteHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsOrganizerFiniteHash.evalSPMF_romRun_eq_finiteHash

/-- info: 'SigGolfCandidate.SphincsOrganizerFiniteHash.setupAndInteract_finiteLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsOrganizerFiniteHash.setupAndInteract_finiteLaw
