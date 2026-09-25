import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.TrialSampling
import SigGolfCandidate.SphincsSecurity.Proof.Reference.QueryBound
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.RequestSampling
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.ReferenceSource
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.MemoTable

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

abbrev CostState := QueryCache HashSpec × Nat

noncomputable def costHash : QueryImpl HashSpec (StateT CostState ProbComp) := fun input state => do
  let result ← (randomOracle input).run state.1
  return (result.1, result.2, state.2 + 1)

def queryCost (input : OracleWorld.Domain) : Nat := if input matches .inr _ then 1 else 0

theorem run_costQuery (input : OracleWorld.Domain) (cache : QueryCache HashSpec) (cost : Nat) :
    ((worldHandler costHash) input).run (cache, cost) =
      (fun result => (result.1, result.2, cost + queryCost input)) <$> (romImpl input).run cache := by
  cases input with
  | inl input => rfl
  | inr input =>
      change (do
        let result ← (randomOracle input).run cache
        pure (result.1, result.2, cost + 1)) = _
      rw [bind_pure_comp]
      rfl

theorem run_costWorld {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (cost : Nat) :
    (simulateQ (worldHandler costHash) computation).run (cache, cost) =
      (fun result => (result.1.1, result.2, cost + result.1.2)) <$>
        (simulateQ romImpl (countHashQueries computation)).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache cost with
  | pure value => simp only [simulateQ_pure, countHashQueries_pure, StateT.run_pure, map_pure, Nat.add_zero]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, countHashQueries_query_bind,
        simulateQ_pure, StateT.run_pure, map_bind, run_costQuery, bind_map_left]
      apply bind_congr
      intro result
      rw [ih]
      simp only [map_pure, bind_pure_comp, queryCost, Nat.add_assoc]
      rfl

theorem hashQueryBound_iff_costState {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat) :
    HashQueryBound computation cache q ↔
      ∀ result ∈ support ((simulateQ (worldHandler costHash) computation).run (cache, 0)), result.2.2 ≤ q := by
  rw [hashQueryBound_iff_run, run_costWorld]
  simp only [Nat.zero_add, support_map, Set.forall_mem_image]

end SphincsSecurity.Seeded


open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {State : Type}

attribute [local irreducible] Concrete.treeRoot tableSign

theorem evalSPMF_tableGameAfterParameter_memo (hash : QueryImpl HashSpec (StateT State ProbComp))
    (adversary : Adversary) (parameter : PublicParameter) (outputs : SecretOutputs) (state : State) :
    𝒮[do
      let randomizers ← sampleRandomizerOutputs
      (simulateQ (worldHandler hash) (tableGameAfterParameter (memoAdversary adversary) parameter outputs randomizers)).run state] =
      𝒮[(simulateQ (worldHandler hash) (Concrete.gameAfterSecrets (memoAdversary adversary)
        parameter (tableOts outputs) (tableFts outputs))).run state] := by
  unfold tableGameAfterParameter Concrete.gameAfterSecrets
  simp only [simulateQ_bind, StateT.run_bind]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro result
  change _ = 𝒮[(simulateQ (worldHandler hash) (gameRest Concrete.scheme (memoAdversary adversary)
    ⟨result.1, parameter⟩ (tableKey parameter result.1 outputs))).run result.2]
  have hleft (randomizers) := runSigning_sourceGame randomizers (tableKey parameter result.1 outputs)
    ⟨result.1, parameter⟩ (memoAdversary adversary)
  simp_rw [← hleft]
  rw [← runWorldSigning_sourceGame, simulateQ_runWorldSigning]
  exact evalSPMF_tableRequests hash (tableKey parameter result.1 outputs)
    (sourceGame ⟨result.1, parameter⟩ (memoAdversary adversary))
    (freshRequests_sourceGame_memo _ _) result.2

theorem hashQueryBound_reference_afterSecrets (adversary : Adversary) (parameterOutput : HashOutput)
    (outputs : SecretOutputs) (q : Nat)
    (hbound : ∀ randomizers, HashQueryBound
      (tableGameAfterParameter (memoAdversary adversary) (truncateHash parameterOutput) outputs randomizers) ∅ q) :
    HashQueryBound (Concrete.gameAfterSecrets (memoAdversary adversary)
      (truncateHash parameterOutput) (tableOts outputs) (tableFts outputs)) ∅ q := by
  rw [hashQueryBound_iff_costState]
  intro result hresult
  rw [← mem_support_iff_of_evalSPMF_eq (evalSPMF_tableGameAfterParameter_memo costHash adversary
    (truncateHash parameterOutput) outputs (∅, 0)), mem_support_bind_iff] at hresult
  obtain ⟨randomizers, _, hresult⟩ := hresult
  exact (hashQueryBound_iff_costState _ ∅ q).1 (hbound randomizers) result hresult

theorem referenceBudget_from_table (adversary : Adversary) (q : Nat)
    (hbound : HasTableBudget (memoAdversary adversary) q) :
    HasHashQueryBound Concrete.scheme (memoAdversary adversary) q := by
  rw [hasHashQueryBound_iff, Concrete.gameCore_eq_secrets]
  have htail (parameter : PublicParameter) (ots : OtsSecrets) (fts : FtsSecrets) :
      HashQueryBound (Concrete.gameAfterSecrets (memoAdversary adversary) parameter ots fts) ∅ q := by
    let high : HighSecrets := (fun _ _ _ _ => 0, fun _ _ _ => 0)
    have h := hashQueryBound_reference_afterSecrets adversary (outputHalves.symm (parameter, 0))
      (secretHalves.symm ((ots, fts), high)) q (hbound _ _)
    simpa only [truncate_from_halves, tableOts_from_halves, tableFts_from_halves] using h
  intro result hresult
  simp only [countHashQueries_bind, countHashQueries_lift_prob, simulateQ_bind,
    simulateQ_map, StateT.run'_eq, StateT.run_bind, StateT.run_map,
    romImpl, QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run,
    bind_map_left, map_bind, Nat.zero_add, bind_pure_comp, Functor.map_map,
    support_bind, Set.mem_iUnion, support_map] at hresult
  obtain ⟨parameter, _, ots, _, fts, _, record, hrecord, rfl⟩ := hresult
  apply htail parameter ots fts record.1
  rw [StateT.run'_eq, support_map]
  exact ⟨record, hrecord, rfl⟩

end SphincsSecurity.Seeded
