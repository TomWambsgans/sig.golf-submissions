import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsTwoEdgeSource
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition Finset.univ

theorem referenceContactGame_twoEdge_law (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result => decide (result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address)) <$>
      referenceContactGame inputs hencoding dummy adversary = prefixTwoEdgeGame inputs hencoding hgraph address dummy adversary := by
  rw [← prefixContactObservedGame_original inputs hencoding hgraph address dummy adversary]
  unfold prefixContactObservedGame prefixInstrumentedObservedGame prefixTwoEdgeGame
  simp only [map_bind, map_pure]
  apply congrArg (𝒮[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒮[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒮[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  apply congrArg (𝒮[PMF.uniformOfFintype segment.ErasedSecrets] >>= ·)
  funext other
  apply congrArg (𝒮[segment.referenceAuxSeedLaw inputs (hencoding parameter) (hgraph parameter) selections] >>= ·)
  funext auxiliary
  have h := congrArg (fun law : PMF Bool => 𝒮[law])
    (contactSeed_twoEdge_eq parameter words address inputs (hencoding parameter) (hgraph parameter) auxiliary other.val ftsSecret adversary)
  simpa only [← PMF.monad_map_eq_map, evalSPMF_map, bind_map_left, bind_pure_comp, Functor.map_map, Function.comp_def] using h

theorem referenceContactGame_twoEdge_eq (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address |
      referenceContactGame inputs hencoding dummy adversary] =
    Pr[= true | prefixTwoEdgeGame inputs hencoding hgraph address dummy adversary] := by
  rw [← referenceContactGame_twoEdge_law inputs hencoding hgraph address dummy adversary, ← probEvent_eq_eq_probOutput, probEvent_map]
  simp only [Function.comp_def, decide_eq_true_eq]

def ContactResult.TwoEdge (parameter : PublicParameter) (words : OtsReferenceWords) (result : ContactResult) : Prop :=
  ∃ address, result.TwoEdgeAt parameter words address

theorem referenceContactGame_twoEdge_le_sum (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => result.2.2.TwoEdge result.1 (referenceFamilyWords result.2.1 dummy) |
      referenceContactGame inputs hencoding dummy adversary] ≤
      ∑ address : OtsPrefix.ChainAddress, Pr[fun result => result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address |
        referenceContactGame inputs hencoding dummy adversary] := by
  let law := referenceContactGame inputs hencoding dummy adversary
  let event := fun address : OtsPrefix.ChainAddress => fun result : InstrumentedResult ContactResult =>
    result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address
  refine (_root_.probEvent_mono (mx := law) (q := fun result => ∃ address ∈ (Finset.univ : Finset OtsPrefix.ChainAddress), event address result) ?_).trans
    (probEvent_exists_finset_le_sum Finset.univ law event)
  rintro result _ ⟨address, ha⟩
  exact ⟨address, Finset.mem_univ address, ha⟩

theorem referenceContactGame_twoEdge_budget_le_sum (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) :
    Pr[fun result =>
      result.2.2.TwoEdge result.1 (referenceFamilyWords result.2.1 dummy) ∧
        result.2.2.output.2.hashCalls ≤ q |
      referenceContactGame inputs hencoding dummy adversary] ≤
      ∑ address : OtsPrefix.ChainAddress,
        Pr[fun result =>
          result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address ∧
            result.2.2.output.2.hashCalls ≤ q |
          referenceContactGame inputs hencoding dummy adversary] := by
  let law := referenceContactGame inputs hencoding dummy adversary
  let event := fun address : OtsPrefix.ChainAddress =>
    fun result : InstrumentedResult ContactResult =>
      result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address ∧
        result.2.2.output.2.hashCalls ≤ q
  refine (_root_.probEvent_mono (mx := law)
    (q := fun result => ∃ address ∈ (Finset.univ : Finset OtsPrefix.ChainAddress), event address result) ?_).trans
    (probEvent_exists_finset_le_sum Finset.univ law event)
  rintro result _ ⟨⟨address, ha⟩, hcost⟩
  exact ⟨address, Finset.mem_univ address, ha, hcost⟩

theorem referenceContactGame_twoEdge_sum_cost_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    (1 - (q : ENNReal) / Fintype.card Digest) *
      (∑ address : OtsPrefix.ChainAddress, Pr[fun result => result.2.2.TwoEdgeAt result.1 (referenceFamilyWords result.2.1 dummy) address |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary]) ≤
      prefixTwoEdgeRate q * (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) := by
  simp only [referenceContactGame_twoEdge_eq _ _ (canonicalGraphInputs_subset_gameInputs adversary)]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    fun address _ => prefixTwoEdgeGame_le address dummy adversary q hbound hsmall
  rw [← Finset.mul_sum] at hsum
  have hlower := Finset.sum_le_sum (s := (Finset.univ : Finset OtsPrefix.ChainAddress))
    fun address _ => prefixIdealCostGame_lower address dummy adversary q hbound
  rw [← Finset.mul_sum] at hlower
  simp only [prefixCountedObservedGame_original, tsum_probOutput_map_mul, ReferenceRecordedResult.prefixCounted] at hlower
  conv at hlower =>
    rhs
    rw [← tsum_fintype (L := SummationFilter.unconditional OtsPrefix.ChainAddress), ENNReal.tsum_comm]
    simp only [tsum_fintype, ← Finset.mul_sum, ← Nat.cast_sum]
  have hscaled := mul_le_mul' (le_refl (1 - (q : ENNReal) / Fintype.card Digest)) hsum
  rw [mul_left_comm] at hscaled
  exact hscaled.trans (mul_le_mul' le_rfl hlower)

theorem referenceContactGame_twoEdge_cost_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    (1 - (q : ENNReal) / Fintype.card Digest) *
      Pr[fun result => result.2.2.TwoEdge result.1 (referenceFamilyWords result.2.1 dummy) |
        referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      prefixTwoEdgeRate q * (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) :=
  (mul_le_mul' le_rfl (referenceContactGame_twoEdge_le_sum _ _ dummy adversary)).trans
    (referenceContactGame_twoEdge_sum_cost_le dummy adversary q hbound hsmall)

theorem referenceContactGame_twoEdge_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    Pr[fun result => result.2.2.TwoEdge result.1 (referenceFamilyWords result.2.1 dummy) |
      referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (prefixTwoEdgeRate q * (∑' result : ReferenceRecordedResult, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal))) /
        (1 - (q : ENNReal) / Fintype.card Digest) := by
  have hcard : (Fintype.card Digest : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpositive : 0 < 1 - (q : ENNReal) / Fintype.card Digest := by
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl hcard) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast hsmall
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hpositive)) (Or.inl (by finiteness))).mpr
  simpa only [mul_comm] using referenceContactGame_twoEdge_cost_le dummy adversary q hbound hsmall

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.referenceContactGame_twoEdge_budget_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.referenceContactGame_twoEdge_budget_le_sum
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition Finset.univ

noncomputable def prefixTwoEdgeCostGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (adversary : Adversary) : SPMF (Bool × Nat) := do
  let parameter ← 𝒮[sampleParameter]
  let ftsSecret ← 𝒮[sampleFtsSecrets]
  let selections ← 𝒮[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  let other ← 𝒮[PMF.uniformOfFintype segment.ErasedSecrets]
  let auxiliary ← 𝒮[segment.referenceAuxSeedLaw inputs
    (hencoding parameter) (hgraph parameter) selections]
  let result ← 𝒮[PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl)
    (fun endpoint => segment.seedGame inputs (hencoding parameter)
      (hgraph parameter) auxiliary other.val ftsSecret words endpoint adversary)
    (fun _ _ => none)]
  pure (decide (PartialChainEndpoint.TwoEdgeEvent result.2.2 result.1),
    result.2.1.2.hashCalls)

theorem referenceContactGame_twoEdge_cost_law (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (adversary : Adversary) :
    (fun result =>
      (decide (result.2.2.TwoEdgeAt result.1
        (referenceFamilyWords result.2.1 dummy) address),
        result.2.2.output.2.hashCalls)) <$>
      referenceContactGame inputs hencoding dummy adversary =
      prefixTwoEdgeCostGame inputs hencoding hgraph address dummy adversary := by
  rw [← prefixContactObservedGame_original inputs hencoding hgraph address dummy adversary]
  unfold prefixContactObservedGame prefixInstrumentedObservedGame prefixTwoEdgeCostGame
  simp only [map_bind, map_pure]
  apply congrArg (𝒮[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒮[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg
    (𝒮[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  apply congrArg (𝒮[PMF.uniformOfFintype segment.ErasedSecrets] >>= ·)
  funext other
  apply congrArg (𝒮[segment.referenceAuxSeedLaw inputs
    (hencoding parameter) (hgraph parameter) selections] >>= ·)
  funext auxiliary
  have h := congrArg (fun law : PMF (Bool × Nat) => 𝒮[law])
    (contactSeed_twoEdge_cost_eq parameter words address inputs
      (hencoding parameter) (hgraph parameter) auxiliary other.val
      ftsSecret adversary)
  simpa only [← PMF.monad_map_eq_map, evalSPMF_map, bind_map_left,
    bind_pure_comp, Functor.map_map, Function.comp_def] using h

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.referenceContactGame_twoEdge_cost_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.referenceContactGame_twoEdge_cost_law
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition Finset.univ

theorem prefixTwoEdgeCostGame_budget_le (address : OtsPrefix.ChainAddress)
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q |
      prefixTwoEdgeCostGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary)
        (canonicalGraphInputs_subset_gameInputs adversary)
        address dummy adversary] ≤
      prefixTwoEdgeRate q * (q : ENNReal) := by
  unfold prefixTwoEdgeCostGame
  refine probEvent_bind_le_of_forall_le fun parameter _ => ?_
  refine probEvent_bind_le_of_forall_le fun ftsSecret _ => ?_
  refine probEvent_bind_le_of_forall_le fun selections _ => ?_
  refine probEvent_bind_le_of_forall_le fun other _ => ?_
  refine probEvent_bind_le_of_forall_le fun auxiliary _ => ?_
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  let inputs := canonicalGraphGameInputs adversary
  let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
  let hgraph := canonicalGraphInputs_subset_gameInputs adversary parameter
  let computation := fun endpoint =>
    segment.seedGame inputs hencoding hgraph auxiliary other.val
      ftsSecret words endpoint adversary
  let cost := fun result : Bool × SigningBoundaryTrace => result.2.hashCalls
  have hcharge : ∀ endpoint result,
      result ∈ support
        (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
          (computation endpoint)) →
      result.2 ≤ cost result.1 :=
    fun endpoint result hresult =>
      segment.seedGame_counted_le inputs hencoding hgraph auxiliary
        other.val ftsSecret words endpoint adversary result hresult
  have h := PartialChainEndpoint.realRun_twoEdgeEvent_cost_budget_le_linear_of_charge
    (fun _ => OtsPrefix.uniformImpl) computation cost q hcharge
  simpa only [prefixTwoEdgeRate, probEvent_map, Function.comp_def,
    decide_eq_true_eq, evalSPMF_pure, bind_pure_comp, PMF.evalSPMF_eq,
    SPMF.probEvent_liftM] using h

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.prefixTwoEdgeCostGame_budget_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.prefixTwoEdgeCostGame_budget_le
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem referenceContactGame_twoEdgeAt_budget_le
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (adversary : Adversary) (q : Nat) :
    Pr[fun result =>
      result.2.2.TwoEdgeAt result.1
        (referenceFamilyWords result.2.1 dummy) address ∧
      result.2.2.output.2.hashCalls ≤ q |
      referenceContactGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary)
        dummy adversary] ≤
      prefixTwoEdgeRate q * (q : ENNReal) := by
  have h := referenceContactGame_twoEdge_cost_law
    (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary)
    (canonicalGraphInputs_subset_gameInputs adversary)
    address dummy adversary
  have he := congrArg
    (fun law : SPMF (Bool × Nat) =>
      Pr[fun result => result.1 = true ∧ result.2 ≤ q | law]) h
  simp only [probEvent_map, Function.comp_def, decide_eq_true_eq] at he
  change Pr[fun result =>
      result.2.2.TwoEdgeAt result.1
        (referenceFamilyWords result.2.1 dummy) address ∧
      result.2.2.output.2.hashCalls ≤ q |
      referenceContactGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary)
        dummy adversary] = _ at he
  rw [he]
  exact prefixTwoEdgeCostGame_budget_le address dummy adversary q

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.referenceContactGame_twoEdgeAt_budget_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.referenceContactGame_twoEdgeAt_budget_le
