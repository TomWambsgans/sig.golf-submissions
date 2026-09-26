import SigGolfCandidate.SphincsSecurity.Proof.Forced.FtsGuessNearEvent
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec OtsContactTrace ENNReal UniformTableCompletion
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (forcedRun initialState)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval honestNode canonicalGraphLabels

noncomputable def sourceNearWitness (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (before : AdversaryTrace) : Prop :=
  let result := completedReferenceContact key.parameter f (referenceFamilyWords selections dummy)
    (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords selections dummy)) before
  SigningTranscript.Valid before.1.1.2 ∧ ReferenceFtsCoverage.NearGuess (ReferenceVerifierWitness.rootedKey key f) f
    before.1.1.2 before.1.2 (result.before * result.after) before.1.1.1

noncomputable def referenceNearWitnessRest (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp Bool :=
  (fun before => decide (sourceNearWitness key f labels selections dummy before)) <$>
    referenceForgeryRest key f labels selections dummy adversary

theorem referenceNearWitnessRest_program (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let f := programmedHash key.parameter key.otsSecret key.ftsSecret labels
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed))
    referenceNearWitnessRest key f labels auxiliary.selections dummy adversary =
      (fun result => decide (completedNearGuess { key with root := canonicalGraphRoot labels } f result)) <$>
        simulateQ (fixedAnswers (referenceAnswers key.parameter (canonicalGraphRoot labels) key.otsSecret labels inputs hencoding auxiliary dummy)
          (FtsGuessSigning.secretTable key.ftsSecret)) (completedRun key.parameter (canonicalGraphRoot labels) labels adversary) := by
  dsimp only
  rw [fixed_reference_completedForgeryRest key inputs hencoding labels auxiliary hauxiliary dummy adversary,
    referenceNearWitnessRest, Functor.map_map]
  congr 1
  funext before
  rw [sourceNearWitness, rootedKey_programmedHash key labels _ dummy]
  simp only [completedReferenceContact, reference_root, completedNearGuess, completedAtRoot]
  exact decide_eq_decide.mpr Iff.rfl

theorem referenceNearWitnessRest_initial_bound (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : HasHashQueryBound scheme adversary budget) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support) :
    Pr[fun hit => hit = true | 𝒮[sampleFtsSecrets] >>= fun ftsSecret =>
      𝒮[referenceNearWitnessRest ⟨parameter, 0, otsSecret, ftsSecret⟩
        (programmedHash parameter otsSecret ftsSecret labels
          (finiteHashAnswer ∅ (canonicalGraphGameInputs adversary)
            (canonicalReferenceResidual parameter (canonicalGraphGameInputs adversary)
              (canonicalEncodingInputs_subset_gameInputs adversary parameter) labels auxiliary.rows auxiliary.seed)))
        labels auxiliary.selections dummy adversary]] ≤
      ((2 ^ 160 - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, forcedNearProbability dummy adversary slot parameter otsSecret labels auxiliary := by
  have h := (initial_reference_near_witnesses parameter otsSecret (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary parameter) labels auxiliary hauxiliary dummy adversary).trans
    (lazy_original_near_event_le dummy adversary budget hbudget parameter otsSecret labels auxiliary hauxiliary)
  have hprior := congrArg (fun law : SPMF (Coordinate → Digest) => law >>= fun secrets =>
      (fun result => (secrets, result)) <$> 𝒮[simulateQ
        (fixedAnswers (originalAnswers dummy adversary parameter otsSecret labels auxiliary) secrets)
        (completedRun parameter (canonicalGraphRoot labels) labels adversary)]) FtsGuessSigning.sampleFtsSecrets_table
  rw [bind_map_left] at hprior
  simp only [originalAnswers] at hprior
  rw [← hprior] at h
  have hprogram (ftsSecret : Index → FtsTree → FtsLeaf → Digest) := referenceNearWitnessRest_program
    ⟨parameter, 0, otsSecret, ftsSecret⟩ (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary parameter) labels auxiliary hauxiliary dummy adversary
  simp only [hprogram, evalSPMF_map, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
    Equiv.symm_apply_apply, decide_eq_true_eq] at h ⊢
  exact h

noncomputable def forcedNearGame (dummy : OtsReferenceWords) (adversary : Adversary) (slot : Nat) : SPMF Bool := do
  let parameter ← 𝒮[sampleParameter]
  let otsSecret ← 𝒮[sampleOtsSecrets]
  let auxiliary ← 𝒮[referenceAuxiliarySample (canonicalGraphGameInputs adversary)]
  let labels ← 𝒮[PMF.uniformOfFintype CanonicalGraphLabels]
  (fun result => decide (completedNearCertificate parameter (canonicalGraphRoot labels) result.1)) <$>
    forcedRun (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary)) slot
      (completedRun parameter (canonicalGraphRoot labels) labels adversary) (initialState PUnit.unit)

theorem forcedNearGame_probability (dummy : OtsReferenceWords) (adversary : Adversary) (slot : Nat) :
    Pr[fun hit => hit = true | forcedNearGame dummy adversary slot] =
      ∑' parameter, Pr[= parameter | 𝒮[sampleParameter]] *
        ∑' otsSecret, Pr[= otsSecret | 𝒮[sampleOtsSecrets]] *
          ∑' auxiliary, Pr[= auxiliary | 𝒮[referenceAuxiliarySample (canonicalGraphGameInputs adversary)]] *
            ∑' labels, Pr[= labels | 𝒮[PMF.uniformOfFintype CanonicalGraphLabels]] *
              forcedNearProbability dummy adversary slot parameter otsSecret labels auxiliary := by
  simp only [forcedNearGame, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def, decide_eq_true_eq, forcedNearProbability]

private theorem weighted_sum {Index First : Type} (indices : Finset Index) (law : SPMF First)
    (value : Index → First → ENNReal) (rate : ENNReal) :
    rate * (∑ index ∈ indices, ∑' first, Pr[= first | law] * value index first) =
      ∑' first, Pr[= first | law] * (rate * ∑ index ∈ indices, value index first) := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro first
  rw [← Finset.mul_sum]
  ring

private theorem pmf_support_nonzero {Result : Type} (law : PMF Result) (result : Result) (hr : 𝒮[law] result ≠ 0) :
    result ∈ law.support := by
  simpa only [PMF.mem_support_iff, SPMF.liftM_apply] using hr

theorem referenceForgeryGame_near_guess_le_forced (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : HasHashQueryBound scheme adversary budget) :
    Pr[ReferenceForgerySample.nearGuess dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      ((2 ^ 160 - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, Pr[fun hit => hit = true | forcedNearGame dummy adversary slot] := by
  have hsource := referenceForgeryGame_bind_auxiliary (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary
    (fun key f labels selections before => pure (decide (sourceNearWitness key f labels selections dummy before)))
  simp only [evalSPMF_pure, bind_pure_comp] at hsource
  have hprojected := congrArg (fun law : SPMF Bool => Pr[fun hit => hit = true | law]) hsource
  simp only [probEvent_map, Function.comp_def, decide_eq_true_eq] at hprojected
  change Pr[ReferenceForgerySample.nearGuess dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] = _ at hprojected
  rw [hprojected]
  simp_rw [forcedNearGame_probability, weighted_sum]
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro otsSecret
  apply mul_le_mul' le_rfl
  rw [RetainedObservation.bind_comm 𝒮[sampleFtsSecrets] 𝒮[referenceAuxiliarySample (canonicalGraphGameInputs adversary)],
    probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro auxiliary
  by_cases hz : 𝒮[referenceAuxiliarySample (canonicalGraphGameInputs adversary)] auxiliary = 0
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul, le_refl]
  apply mul_le_mul' le_rfl
  rw [RetainedObservation.bind_comm 𝒮[sampleFtsSecrets] 𝒮[PMF.uniformOfFintype CanonicalGraphLabels],
    probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro labels
  apply mul_le_mul' le_rfl
  have h := referenceNearWitnessRest_initial_bound dummy adversary budget hbudget parameter otsSecret labels auxiliary
    (pmf_support_nonzero _ auxiliary hz)
  simpa only [referenceNearWitnessRest, evalSPMF_map] using h

end SphincsSecurity.Concrete.FtsGuessHash

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

theorem forgeAdvantage_le_forcedNear_small_budget (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf))
    (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q)
    (hsmall : q ≤ budgetSplit) :
    forgeAdvantage scheme adversary ≤
      primitiveCoefficient * ((q : ENNReal) / 2 ^ 144) + (q : ENNReal) * fullCertificateExcessRate +
      proposalPrefixExceptionBound + ((q : ENNReal) / 2 ^ 128) ^ 2 / (2 * (1 - (q : ENNReal) / 2 ^ 128) ^ 2) +
      ((2 ^ 160 - q : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range q, Pr[fun hit => hit = true | FtsGuessHash.forcedNearGame dummy adversary slot] :=
  (forgeAdvantage_le_nearGuess_normalized_small_budget dummy hdummy adversary q hbound hsmall).trans
    (add_le_add le_rfl (FtsGuessHash.referenceForgeryGame_near_guess_le_forced dummy adversary q hbound))

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete.FtsGuessHash
open _root_.OracleComp OracleSpec OtsContactTrace ENNReal UniformTableCompletion
open FtsGuessSigning (Coordinate)
attribute [local instance] Classical.propDecidable

theorem initial_original_near_witnesses_budget_event
    (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈
      (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support) :
    let inputs := canonicalGraphGameInputs adversary
    let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
    let residual := finiteHashAnswer ∅ inputs
      (canonicalReferenceResidual parameter inputs hencoding labels
        auxiliary.rows auxiliary.seed)
    Pr[fun result => completedNearGuess
      ⟨parameter, canonicalGraphRoot labels, otsSecret,
        FtsGuessSigning.secretTable.symm result.1⟩
      (programmedHash parameter otsSecret
        (FtsGuessSigning.secretTable.symm result.1) labels residual) result.2 ∧
      keygenHashCost + completedWork result.2 ≤ budget |
      complete (fun _ : Coordinate => (Finset.univ : Finset Digest)) >>= fun secrets =>
        (fun value => (secrets, value)) <$> 𝒮[simulateQ
          (fixedAnswers (originalAnswers dummy adversary parameter otsSecret
            labels auxiliary) secrets)
          (completedRun parameter (canonicalGraphRoot labels) labels adversary)]] ≤
      ((2 ^ 160 - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget,
          forcedNearProbability dummy adversary slot parameter otsSecret labels auxiliary := by
  exact (initial_reference_near_witnesses_budget_event parameter otsSecret
    (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary parameter)
    labels auxiliary hauxiliary dummy adversary budget).trans
    (lazy_original_near_event_budget_le dummy adversary budget parameter
      otsSecret labels auxiliary)

end SphincsSecurity.Concrete.FtsGuessHash

/-- info: 'SphincsSecurity.Concrete.FtsGuessHash.initial_original_near_witnesses_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.FtsGuessHash.initial_original_near_witnesses_budget_event

namespace SphincsSecurity.Concrete.FtsGuessHash
open _root_.OracleComp OracleSpec OtsContactTrace ENNReal UniformTableCompletion
open FtsGuessSigning (Coordinate)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
noncomputable def referenceNearWitnessRestCost (key : SecretKey)
    (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (fun before =>
    (decide (sourceNearWitness key f labels selections dummy before),
      (completedReferenceContact key.parameter f
        (referenceFamilyWords selections dummy)
        (canonicalGraphFrontier key.otsSecret labels
          (referenceFamilyWords selections dummy)) before).output.2.hashCalls)) <$>
    referenceForgeryRest key f labels selections dummy adversary

theorem referenceNearWitnessRestCost_program (key : SecretKey)
    (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs)
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let f := programmedHash key.parameter key.otsSecret key.ftsSecret labels
      (finiteHashAnswer ∅ inputs
        (canonicalReferenceResidual key.parameter inputs hencoding labels
          auxiliary.rows auxiliary.seed))
    referenceNearWitnessRestCost key f labels auxiliary.selections dummy adversary =
      (fun result =>
        (decide (completedNearGuess { key with root := canonicalGraphRoot labels } f result),
          keygenHashCost + completedWork result)) <$>
        simulateQ (fixedAnswers
          (referenceAnswers key.parameter (canonicalGraphRoot labels)
            key.otsSecret labels inputs hencoding auxiliary dummy)
          (FtsGuessSigning.secretTable key.ftsSecret))
          (completedRun key.parameter (canonicalGraphRoot labels) labels adversary) := by
  dsimp only
  rw [fixed_reference_completedForgeryRest key inputs hencoding labels auxiliary
    hauxiliary dummy adversary, referenceNearWitnessRestCost, Functor.map_map]
  congr 1
  funext before
  have hfirst :
      sourceNearWitness key
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs
            (canonicalReferenceResidual key.parameter inputs hencoding labels
              auxiliary.rows auxiliary.seed))) labels auxiliary.selections dummy before =
      completedNearGuess { key with root := canonicalGraphRoot labels }
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs
            (canonicalReferenceResidual key.parameter inputs hencoding labels
              auxiliary.rows auxiliary.seed)))
        (completedAtRoot key.parameter (canonicalGraphRoot labels)
          (programmedHash key.parameter key.otsSecret key.ftsSecret labels
            (finiteHashAnswer ∅ inputs
              (canonicalReferenceResidual key.parameter inputs hencoding labels
                auxiliary.rows auxiliary.seed))) before) := by
    rw [sourceNearWitness, rootedKey_programmedHash key labels _ dummy]
    simp only [completedReferenceContact, reference_root, completedNearGuess, completedAtRoot]
  simp only [hfirst, completedReferenceContact_programmed_cost]

end SphincsSecurity.Concrete.FtsGuessHash

/-- info: 'SphincsSecurity.Concrete.FtsGuessHash.referenceNearWitnessRestCost_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.FtsGuessHash.referenceNearWitnessRestCost_program

namespace SphincsSecurity.Concrete.FtsGuessHash
open _root_.OracleComp OracleSpec OtsContactTrace ENNReal UniformTableCompletion
open FtsGuessSigning (Coordinate)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

noncomputable def referenceNearWitnessCostGame (dummy : OtsReferenceWords)
    (adversary : Adversary) : SPMF (Bool × Nat) := do
  let parameter ← 𝒮[sampleParameter]
  let otsSecret ← 𝒮[sampleOtsSecrets]
  let ftsSecret ← 𝒮[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  let auxiliary ← 𝒮[referenceAuxiliarySample (canonicalGraphGameInputs adversary)]
  let labels ← 𝒮[PMF.uniformOfFintype CanonicalGraphLabels]
  let f := programmedHash parameter otsSecret ftsSecret labels
    (finiteHashAnswer ∅ (canonicalGraphGameInputs adversary)
      (canonicalReferenceResidual parameter (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary parameter)
        labels auxiliary.rows auxiliary.seed))
  let before ← 𝒮[referenceForgeryRest key f labels auxiliary.selections dummy adversary]
  pure (decide (sourceNearWitness key f labels auxiliary.selections dummy before),
    (completedReferenceContact key.parameter f
      (referenceFamilyWords auxiliary.selections dummy)
      (canonicalGraphFrontier key.otsSecret labels
        (referenceFamilyWords auxiliary.selections dummy)) before).output.2.hashCalls)

theorem referenceForgeryGame_near_guess_cost_law (dummy : OtsReferenceWords)
    (adversary : Adversary) :
    (fun sample : ReferenceForgerySample (canonicalGraphGameInputs adversary) =>
      (decide (ReferenceForgerySample.nearGuess dummy sample),
        (sample.context dummy).2.2.2.output.2.hashCalls)) <$>
      referenceForgeryGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary =
    referenceNearWitnessCostGame dummy adversary := by
  have hsource := referenceForgeryGame_bind_auxiliary
    (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary)
    (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary
    (fun key f labels selections before => pure
      (decide (sourceNearWitness key f labels selections dummy before),
        (completedReferenceContact key.parameter f
          (referenceFamilyWords selections dummy)
          (canonicalGraphFrontier key.otsSecret labels
            (referenceFamilyWords selections dummy)) before).output.2.hashCalls))
  simp only [evalSPMF_pure, bind_pure_comp] at hsource
  exact hsource

theorem referenceNearWitnessRestCost_initial_bound
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈
      (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q |
      𝒮[sampleFtsSecrets] >>= fun ftsSecret =>
        𝒮[referenceNearWitnessRestCost
          ⟨parameter, 0, otsSecret, ftsSecret⟩
          (programmedHash parameter otsSecret ftsSecret labels
            (finiteHashAnswer ∅ (canonicalGraphGameInputs adversary)
              (canonicalReferenceResidual parameter (canonicalGraphGameInputs adversary)
                (canonicalEncodingInputs_subset_gameInputs adversary parameter)
                labels auxiliary.rows auxiliary.seed)))
          labels auxiliary.selections dummy adversary]] ≤
      ((2 ^ 160 - q : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range q,
          forcedNearProbability dummy adversary slot parameter otsSecret labels auxiliary := by
  have h := initial_original_near_witnesses_budget_event dummy adversary q
    parameter otsSecret labels auxiliary hauxiliary
  dsimp only at h
  have hprior := congrArg (fun law : SPMF (Coordinate → Digest) =>
    law >>= fun secrets =>
      (fun result => (secrets, result)) <$> 𝒮[simulateQ
        (fixedAnswers (originalAnswers dummy adversary parameter otsSecret
          labels auxiliary) secrets)
        (completedRun parameter (canonicalGraphRoot labels) labels adversary)])
    FtsGuessSigning.sampleFtsSecrets_table
  rw [bind_map_left] at hprior
  rw [← hprior] at h
  have hprogram (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
    referenceNearWitnessRestCost_program
      ⟨parameter, 0, otsSecret, ftsSecret⟩
      (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary parameter)
      labels auxiliary hauxiliary dummy adversary
  simp only [hprogram, evalSPMF_map, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def, Equiv.symm_apply_apply, decide_eq_true_eq] at h ⊢
  exact h

end SphincsSecurity.Concrete.FtsGuessHash

/-- info: 'SphincsSecurity.Concrete.FtsGuessHash.referenceForgeryGame_near_guess_cost_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.FtsGuessHash.referenceForgeryGame_near_guess_cost_law

/-- info: 'SphincsSecurity.Concrete.FtsGuessHash.referenceNearWitnessRestCost_initial_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.FtsGuessHash.referenceNearWitnessRestCost_initial_bound
namespace SphincsSecurity.Concrete.FtsGuessHash
open _root_.OracleComp OracleSpec OtsContactTrace ENNReal UniformTableCompletion
open FtsGuessSigning (Coordinate)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

theorem referenceForgeryGame_near_guess_budget_event
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) :
    Pr[fun sample => ReferenceForgerySample.nearGuess dummy sample ∧
      (sample.context dummy).2.2.2.output.2.hashCalls ≤ q |
      referenceForgeryGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      ((2 ^ 160 - q : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range q,
          Pr[fun hit => hit = true | forcedNearGame dummy adversary slot] := by
  have hsource := referenceForgeryGame_near_guess_cost_law dummy adversary
  have hprojected := congrArg
    (fun law : SPMF (Bool × Nat) =>
      Pr[fun result => result.1 = true ∧ result.2 ≤ q | law]) hsource
  simp only [probEvent_map, Function.comp_def, decide_eq_true_eq] at hprojected
  change Pr[fun sample => ReferenceForgerySample.nearGuess dummy sample ∧
      (sample.context dummy).2.2.2.output.2.hashCalls ≤ q |
      referenceForgeryGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] = _
    at hprojected
  rw [hprojected]
  unfold referenceNearWitnessCostGame
  simp_rw [forcedNearGame_probability, weighted_sum]
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro otsSecret
  apply mul_le_mul' le_rfl
  rw [RetainedObservation.bind_comm 𝒮[sampleFtsSecrets]
    𝒮[referenceAuxiliarySample (canonicalGraphGameInputs adversary)],
    probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro auxiliary
  rcases Classical.em (𝒮[referenceAuxiliarySample (canonicalGraphGameInputs adversary)] auxiliary = 0) with hz | hz
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul, le_refl]
  apply mul_le_mul' le_rfl
  rw [RetainedObservation.bind_comm 𝒮[sampleFtsSecrets]
    𝒮[PMF.uniformOfFintype CanonicalGraphLabels],
    probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro labels
  apply mul_le_mul' le_rfl
  have h := referenceNearWitnessRestCost_initial_bound dummy adversary q
    parameter otsSecret labels auxiliary (pmf_support_nonzero _ auxiliary hz)
  simpa only [referenceNearWitnessRestCost, evalSPMF_map, evalSPMF_pure,
    bind_pure_comp] using h

end SphincsSecurity.Concrete.FtsGuessHash

/-- info: 'SphincsSecurity.Concrete.FtsGuessHash.referenceForgeryGame_near_guess_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.FtsGuessHash.referenceForgeryGame_near_guess_budget_event

namespace SphincsSecurity.Concrete.FtsGuessHash
open _root_.OracleComp OracleSpec OtsContactTrace ENNReal UniformTableCompletion
open FtsGuessSigning (Coordinate)
attribute [local instance] Classical.propDecidable
theorem initial_original_near_witnesses_budget_event_cost
    (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈
      (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support) :
    let inputs := canonicalGraphGameInputs adversary
    let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
    let residual := finiteHashAnswer ∅ inputs
      (canonicalReferenceResidual parameter inputs hencoding labels
        auxiliary.rows auxiliary.seed)
    Pr[fun result => completedNearGuess
      ⟨parameter, canonicalGraphRoot labels, otsSecret,
        FtsGuessSigning.secretTable.symm result.1⟩
      (programmedHash parameter otsSecret
        (FtsGuessSigning.secretTable.symm result.1) labels residual) result.2 ∧
      keygenHashCost + completedWork result.2 ≤ budget |
      complete (fun _ : Coordinate => (Finset.univ : Finset Digest)) >>= fun secrets =>
        (fun value => (secrets, value)) <$> 𝒮[simulateQ
          (fixedAnswers (originalAnswers dummy adversary parameter otsSecret
            labels auxiliary) secrets)
          (completedRun parameter (canonicalGraphRoot labels) labels adversary)]] ≤
      ((2 ^ 160 - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget,
          forcedNearProbabilityBudget dummy adversary slot budget parameter otsSecret labels auxiliary := by
  exact (initial_reference_near_witnesses_budget_event parameter otsSecret
    (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary parameter)
    labels auxiliary hauxiliary dummy adversary budget).trans
    (lazy_original_near_event_budget_le_cost_forced dummy adversary budget parameter
      otsSecret labels auxiliary)

end SphincsSecurity.Concrete.FtsGuessHash

/-- info: 'SphincsSecurity.Concrete.FtsGuessHash.initial_original_near_witnesses_budget_event_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.FtsGuessHash.initial_original_near_witnesses_budget_event_cost

namespace SphincsSecurity.Concrete.FtsGuessHash
open _root_.OracleComp OracleSpec OtsContactTrace ENNReal UniformTableCompletion
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (forcedRun initialState)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
noncomputable def forcedNearGameBudget (dummy : OtsReferenceWords) (adversary : Adversary) (slot q : Nat) : SPMF Bool := do
  let parameter ← 𝒮[sampleParameter]
  let otsSecret ← 𝒮[sampleOtsSecrets]
  let auxiliary ← 𝒮[referenceAuxiliarySample (canonicalGraphGameInputs adversary)]
  let labels ← 𝒮[PMF.uniformOfFintype CanonicalGraphLabels]
  (fun result => decide (completedNearCertificate parameter (canonicalGraphRoot labels) result.1 ∧ keygenHashCost + completedWork result.1 ≤ q)) <$>
    forcedRun (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary)) slot
      (completedRun parameter (canonicalGraphRoot labels) labels adversary) (initialState PUnit.unit)

theorem forcedNearGameBudget_probability (dummy : OtsReferenceWords) (adversary : Adversary) (slot q : Nat) :
    Pr[fun hit => hit = true | forcedNearGameBudget dummy adversary slot q] =
      ∑' parameter, Pr[= parameter | 𝒮[sampleParameter]] *
        ∑' otsSecret, Pr[= otsSecret | 𝒮[sampleOtsSecrets]] *
          ∑' auxiliary, Pr[= auxiliary | 𝒮[referenceAuxiliarySample (canonicalGraphGameInputs adversary)]] *
            ∑' labels, Pr[= labels | 𝒮[PMF.uniformOfFintype CanonicalGraphLabels]] *
              forcedNearProbabilityBudget dummy adversary slot q parameter otsSecret labels auxiliary := by
  simp only [forcedNearGameBudget, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def, decide_eq_true_eq, forcedNearProbabilityBudget]

theorem referenceNearWitnessRestCost_initial_bound_budget
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈
      (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q |
      𝒮[sampleFtsSecrets] >>= fun ftsSecret =>
        𝒮[referenceNearWitnessRestCost
          ⟨parameter, 0, otsSecret, ftsSecret⟩
          (programmedHash parameter otsSecret ftsSecret labels
            (finiteHashAnswer ∅ (canonicalGraphGameInputs adversary)
              (canonicalReferenceResidual parameter (canonicalGraphGameInputs adversary)
                (canonicalEncodingInputs_subset_gameInputs adversary parameter)
                labels auxiliary.rows auxiliary.seed)))
          labels auxiliary.selections dummy adversary]] ≤
      ((2 ^ 160 - q : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range q,
          forcedNearProbabilityBudget dummy adversary slot q parameter otsSecret labels auxiliary := by
  have h := initial_original_near_witnesses_budget_event_cost dummy adversary q
    parameter otsSecret labels auxiliary hauxiliary
  dsimp only at h
  have hprior := congrArg (fun law : SPMF (Coordinate → Digest) =>
    law >>= fun secrets =>
      (fun result => (secrets, result)) <$> 𝒮[simulateQ
        (fixedAnswers (originalAnswers dummy adversary parameter otsSecret
          labels auxiliary) secrets)
        (completedRun parameter (canonicalGraphRoot labels) labels adversary)])
    FtsGuessSigning.sampleFtsSecrets_table
  rw [bind_map_left] at hprior
  rw [← hprior] at h
  have hprogram (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :=
    referenceNearWitnessRestCost_program
      ⟨parameter, 0, otsSecret, ftsSecret⟩
      (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary parameter)
      labels auxiliary hauxiliary dummy adversary
  simp only [hprogram, evalSPMF_map, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def, Equiv.symm_apply_apply, decide_eq_true_eq] at h ⊢
  exact h

theorem referenceForgeryGame_near_guess_budget_event_forced_cost
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) :
    Pr[fun sample => ReferenceForgerySample.nearGuess dummy sample ∧
      (sample.context dummy).2.2.2.output.2.hashCalls ≤ q |
      referenceForgeryGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      ((2 ^ 160 - q : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range q,
          Pr[fun hit => hit = true | forcedNearGameBudget dummy adversary slot q] := by
  have hsource := referenceForgeryGame_near_guess_cost_law dummy adversary
  have hprojected := congrArg
    (fun law : SPMF (Bool × Nat) =>
      Pr[fun result => result.1 = true ∧ result.2 ≤ q | law]) hsource
  simp only [probEvent_map, Function.comp_def, decide_eq_true_eq] at hprojected
  change Pr[fun sample => ReferenceForgerySample.nearGuess dummy sample ∧
      (sample.context dummy).2.2.2.output.2.hashCalls ≤ q |
      referenceForgeryGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] = _
    at hprojected
  rw [hprojected]
  unfold referenceNearWitnessCostGame
  simp_rw [forcedNearGameBudget_probability, weighted_sum]
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro otsSecret
  apply mul_le_mul' le_rfl
  rw [RetainedObservation.bind_comm 𝒮[sampleFtsSecrets]
    𝒮[referenceAuxiliarySample (canonicalGraphGameInputs adversary)],
    probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro auxiliary
  rcases Classical.em (𝒮[referenceAuxiliarySample (canonicalGraphGameInputs adversary)] auxiliary = 0) with hz | hz
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul, le_refl]
  apply mul_le_mul' le_rfl
  rw [RetainedObservation.bind_comm 𝒮[sampleFtsSecrets]
    𝒮[PMF.uniformOfFintype CanonicalGraphLabels],
    probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro labels
  apply mul_le_mul' le_rfl
  have h := referenceNearWitnessRestCost_initial_bound_budget dummy adversary q
    parameter otsSecret labels auxiliary (pmf_support_nonzero _ auxiliary hz)
  simpa only [referenceNearWitnessRestCost, evalSPMF_map, evalSPMF_pure,
    bind_pure_comp] using h

end SphincsSecurity.Concrete.FtsGuessHash

/-- info: 'SphincsSecurity.Concrete.FtsGuessHash.forcedNearGameBudget_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.FtsGuessHash.forcedNearGameBudget_probability

/-- info: 'SphincsSecurity.Concrete.FtsGuessHash.referenceNearWitnessRestCost_initial_bound_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.FtsGuessHash.referenceNearWitnessRestCost_initial_bound_budget

/-- info: 'SphincsSecurity.Concrete.FtsGuessHash.referenceForgeryGame_near_guess_budget_event_forced_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.FtsGuessHash.referenceForgeryGame_near_guess_budget_event_forced_cost

namespace SphincsSecurity.Concrete.FtsGuessHash
open _root_.OracleComp ENNReal

theorem referenceForgeryGame_near_guess_budget_le_uniform
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hq : q ≤ 2 ^ 159) :
    Pr[fun sample => ReferenceForgerySample.nearGuess dummy sample ∧
      (sample.context dummy).2.2.2.output.2.hashCalls ≤ q |
      referenceForgeryGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (q : ENNReal) / 2 ^ 159 := by
  have h := referenceForgeryGame_near_guess_budget_event dummy adversary q
  have hsum :
      (∑ slot ∈ Finset.range q,
        Pr[fun hit => hit = true | forcedNearGame dummy adversary slot]) ≤
      (q : ENNReal) := by
    calc
      _ ≤ ∑ _slot ∈ Finset.range q, (1 : ENNReal) := by
        apply Finset.sum_le_sum
        intro slot _
        exact probEvent_le_one
      _ = (q : ENNReal) := by simp
  have hdenom : (2 ^ 159 : Nat) ≤ 2 ^ 160 - q := by omega
  have hinv : ((2 ^ 160 - q : Nat) : ENNReal)⁻¹ ≤
      ((2 ^ 159 : Nat) : ENNReal)⁻¹ :=
    ENNReal.inv_le_inv.mpr (by exact_mod_cast hdenom)
  calc
    _ ≤ ((2 ^ 160 - q : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range q,
          Pr[fun hit => hit = true | forcedNearGame dummy adversary slot] := h
    _ ≤ ((2 ^ 159 : Nat) : ENNReal)⁻¹ * (q : ENNReal) :=
      mul_le_mul' hinv hsum
    _ = (q : ENNReal) / 2 ^ 159 := by simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, mul_comm]

end SphincsSecurity.Concrete.FtsGuessHash

/-- info: 'SphincsSecurity.Concrete.FtsGuessHash.referenceForgeryGame_near_guess_budget_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.FtsGuessHash.referenceForgeryGame_near_guess_budget_le_uniform
