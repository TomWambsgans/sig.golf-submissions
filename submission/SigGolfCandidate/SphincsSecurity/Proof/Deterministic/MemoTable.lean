import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.TranscriptReduction
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.GameComparison

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

noncomputable def evaluateSource {α : Type} (sign : Message → OracleComp HashSpec (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) : ProbComp α :=
  (simulateQ romImpl (runSigning sign computation)).run' cache

theorem evaluateSource_map {α β : Type} (sign : Message → OracleComp HashSpec (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (f : α → β) :
    evaluateSource sign (f <$> computation) cache = f <$> evaluateSource sign computation cache := by
  simp only [evaluateSource, runSigning, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

theorem evaluateSource_support {α : Type} (sign : Message → OracleComp HashSpec (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    support (evaluateSource sign computation cache) ⊆ support computation := by
  unfold evaluateSource runSigning
  rw [← QueryImpl.simulateQ_compose]
  exact support_simulateQ_run'_subset _ _ _

theorem prob_sourceGame_le_memo (sign : Message → OracleComp HashSpec (Option Signature))
    (publicKey : PublicKey) (adversary : Adversary) (cache : QueryCache HashSpec) :
    Pr[= true | evaluateSource sign (sourceGame publicKey adversary) cache] ≤
      Pr[= true | evaluateSource sign (sourceGame publicKey (memoAdversary adversary)) cache] := by
  unfold evaluateSource
  rw [probOutput_congr rfl (evalSPMF_runSigning_memoize sign (sourceGame publicKey adversary) cache)]
  change Pr[= true | evaluateSource sign (memoize (sourceGame publicKey adversary) ∅) cache] ≤
    Pr[= true | evaluateSource sign (sourceGame publicKey (memoAdversary adversary)) cache]
  rw [← fst_transcriptReduction, ← snd_transcriptReduction, evaluateSource_map, evaluateSource_map]
  simp only [← probEvent_eq_eq_probOutput, probEvent_map]
  apply probEvent_mono
  intro result hresult hwin
  exact transcriptReduction_win publicKey adversary result (evaluateSource_support sign _ cache hresult) hwin

theorem hashQueryBound_sourceGame_memo (sign : Message → OracleComp HashSpec (Option Signature))
    (publicKey : PublicKey) (adversary : Adversary) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (runSigning sign (sourceGame publicKey adversary)) cache q) :
    HashQueryBound (runSigning sign (sourceGame publicKey (memoAdversary adversary))) cache q := by
  have h := hashQueryBound_runSigning_memoize sign (sourceGame publicKey adversary) cache q hbound
  rw [← fst_transcriptReduction, runSigning, simulateQ_map, hashQueryBound_map_iff] at h
  rw [← snd_transcriptReduction, runSigning, simulateQ_map, hashQueryBound_map_iff]
  exact h

end SphincsSecurity.Seeded


open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem hashQueryBound_bind_replace {α β γ : Type} (first : OracleComp OracleWorld α)
    (left : α → OracleComp OracleWorld β) (right : α → OracleComp OracleWorld γ)
    (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (first >>= left) cache q)
    (hnext : ∀ value cache q, HashQueryBound (left value) cache q → HashQueryBound (right value) cache q) :
    HashQueryBound (first >>= right) cache q := by
  rw [hashQueryBound_iff_run]
  intro result hresult
  simp only [countHashQueries_bind, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hresult
  obtain ⟨headResult, hheadResult, tail, htail, rfl⟩ := hresult
  have h := hashQueryBound_bind first left cache q hbound headResult hheadResult
  have ht := hnext headResult.1.1 headResult.2 (q - headResult.1.2) h.2
  rw [hashQueryBound_iff_run] at ht
  have := ht tail htail
  change headResult.1.2 + tail.1.2 ≤ q
  have := h.1
  omega

theorem prob_tableGameAfterParameter_le_memo (adversary : Adversary) (parameter : PublicParameter)
    (outputs : SecretOutputs) (randomizers : RandomizerOutputs) (cache : QueryCache HashSpec) :
    Pr[= true | (simulateQ romImpl (tableGameAfterParameter adversary parameter outputs randomizers)).run' cache] ≤
      Pr[= true | (simulateQ romImpl (tableGameAfterParameter (memoAdversary adversary) parameter outputs randomizers)).run' cache] := by
  unfold tableGameAfterParameter
  rw [run'_lift_hash_bind, run'_lift_hash_bind]
  apply probOutput_bind_mono
  intro result _
  rw [← runSigning_sourceGame, ← runSigning_sourceGame]
  exact prob_sourceGame_le_memo _ _ _ _

theorem tableBudget_memo (adversary : Adversary) (q : Nat) (hbound : HasTableBudget adversary q) :
    HasTableBudget (memoAdversary adversary) q := by
  intro parameter outputs randomizers
  have h := hbound parameter outputs randomizers
  unfold tableGameAfterParameter at h ⊢
  apply hashQueryBound_bind_replace _ _ _ ∅ q h
  intro root cache q hrest
  rw [← runSigning_sourceGame] at hrest ⊢
  exact hashQueryBound_sourceGame_memo _ _ _ cache q hrest

theorem prob_independentTableGame_le_memo (adversary : Adversary) :
    Pr[= true | independentTableGame adversary] ≤ Pr[= true | independentTableGame (memoAdversary adversary)] := by
  unfold independentTableGame
  apply probOutput_bind_mono
  intro material _
  exact prob_tableGameAfterParameter_le_memo _ _ _ _ ∅

end SphincsSecurity.Seeded
