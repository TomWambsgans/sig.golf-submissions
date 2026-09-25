import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingContactMarkerStep
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingMarkerAccumulation
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingMarkerBound
namespace SphincsSecurity.Concrete.EncodingObservation

open _root_.OracleComp OracleSpec OtsEncodingMarker
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ canonicalEncodingInputs OtsContactTrace.contacts

theorem contactMarker_lazyRun_le {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld Result) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (ha : ∀ row, (allowed row).Nonempty) :
    (∑' result, Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] *
      (contactMarkerCount parameter (referenceFamilyWords selections dummy) frontier (history * result.1.2) : ENNReal)) ≤
      (contactMarkerCount parameter (referenceFamilyWords selections dummy) frontier history : ENNReal) +
        ((OtsCode.unitNeighborBound : ENNReal) / (Fintype.card Digest : ENNReal)) * ∑' result,
          Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] *
            (contactMarkerCost parameter (referenceFamilyWords selections dummy) frontier history result.1.2 : ENNReal) := by
  simp only [lazyRun_eq_simulate]
  apply QueryPause.traced_spmf_history_potential_le hashObservationTrace (lazyWorldImpl parameter inputs hencoding outside)
    (fun history allowed => TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed ∧
      ∀ row, (allowed row).Nonempty)
    _ _ (fun history _ => contactMarkerCount parameter (referenceFamilyWords selections dummy) frontier history)
    _ (contactMarkerCost parameter (referenceFamilyWords selections dummy) frontier) _
    (contactMarkerCost_one parameter (referenceFamilyWords selections dummy) frontier)
    (contactMarkerCost_step parameter (referenceFamilyWords selections dummy) frontier) _ computation history allowed ⟨hc, ha⟩
  · intro history allowed hi input result hr
    exact ⟨lazyWorldImpl_traceConsistent parameter inputs hencoding outside _ allowed history hi.1 input result hr,
      UniformTableObservation.lazyRun_nonempty (auxiliary parameter inputs hencoding outside) (translate parameter input)
        allowed hi.2 result hr⟩
  · intro computation history allowed hi
    rw [← lazyRun_eq_simulate]
    exact probFailure_eq_zero' (lazyRun_neverFail parameter inputs hencoding outside _ allowed hi.2)
  · intro history allowed hi input
    exact contactMarker_query_potential_le parameter inputs hencoding outside messages selections dummy frontier history allowed hi.1 input

theorem contactMarker_initial_lazyRun_le {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld Result) :
    (∑' result, Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation)
      (referenceEncodingAllowed parameter messages selections)] *
      (contactMarkerCount parameter (referenceFamilyWords selections dummy) frontier result.1.2 : ENNReal)) ≤
        ((OtsCode.unitNeighborBound : ENNReal) / (Fintype.card Digest : ENNReal)) * ∑' result,
          Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation)
            (referenceEncodingAllowed parameter messages selections)] *
              (contactMarkerCost parameter (referenceFamilyWords selections dummy) frontier 1 result.1.2 : ENNReal) := by
  simpa only [one_mul, contactMarkerCount_one, Nat.cast_zero, zero_add] using
    contactMarker_lazyRun_le parameter inputs hencoding outside messages selections dummy frontier computation 1 _
      (traceConsistent_one parameter _) (referenceEncodingAllowed_nonempty parameter messages selections)

end SphincsSecurity.Concrete.EncodingObservation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OtsEncodingMarker
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalGraphInputs canonicalEncodingInputs Finset.univ OtsContactTrace.contacts

theorem referenceEncodingLazyRest_frontier_statistic (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (outside : NonencodingRows key.parameter inputs hencoding)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary)
    (statistic : OtsFrontierValues → OtsContactTrace.Trace → ENNReal) :
    (∑' result, Pr[= result | referenceEncodingLazyRest contactObserver key inputs hencoding outside selections dummy adversary] *
      statistic result.1.frontier (result.1.before * result.1.after)) =
      let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
        (nonencodingAnswer key.parameter inputs hencoding outside)) (referenceFamilyWords selections dummy)
      ∑' result, Pr[= result | EncodingObservation.lazyRun key.parameter inputs hencoding outside
        (QueryPause.traced hashObservationTrace (referenceEncodingProgram key inputs hencoding outside selections dummy adversary))
        (referenceEncodingAllowed key.parameter (outsideGraphMessage key inputs hencoding outside) selections)] *
          statistic frontier result.1.2 := by
  dsimp only
  unfold referenceEncodingLazyRest
  have h := contactObserver_frontier_trace key.parameter (referenceFamilyWords selections dummy)
    (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
      (nonencodingAnswer key.parameter inputs hencoding outside)) (referenceFamilyWords selections dummy))
    (referenceEncodingProgram key inputs hencoding outside selections dummy adversary)
  have he := congrArg (fun computation => EncodingObservation.lazyRun key.parameter inputs hencoding outside computation
    (referenceEncodingAllowed key.parameter (outsideGraphMessage key inputs hencoding outside) selections)) h
  simp only [EncodingObservation.lazyRun_map] at he
  have hs := congrArg (fun law => ∑' result, Pr[= result | law] * statistic result.1.1 result.1.2.2) he
  simpa only [tsum_probOutput_map_mul] using hs

theorem referenceEncodingLazyRest_contactMarker_le (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (outside : NonencodingRows key.parameter inputs hencoding)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (∑' result, Pr[= result | referenceEncodingLazyRest contactObserver key inputs hencoding outside selections dummy adversary] *
      (contactMarkerCount key.parameter (referenceFamilyWords selections dummy) result.1.frontier (result.1.before * result.1.after) : ENNReal)) ≤
      ((OtsCode.unitNeighborBound : ENNReal) / (Fintype.card Digest : ENNReal)) * ∑' result,
        Pr[= result | referenceEncodingLazyRest contactObserver key inputs hencoding outside selections dummy adversary] *
          (contactMarkerCost key.parameter (referenceFamilyWords selections dummy) result.1.frontier 1 (result.1.before * result.1.after) : ENNReal) := by
  rw [referenceEncodingLazyRest_frontier_statistic key inputs hencoding outside selections dummy adversary
    (fun frontier trace => (contactMarkerCount key.parameter (referenceFamilyWords selections dummy) frontier trace : ENNReal)),
    referenceEncodingLazyRest_frontier_statistic key inputs hencoding outside selections dummy adversary
      (fun frontier trace => (contactMarkerCost key.parameter (referenceFamilyWords selections dummy) frontier 1 trace : ENNReal))]
  exact EncodingObservation.contactMarker_initial_lazyRun_le key.parameter inputs hencoding outside
    (outsideGraphMessage key inputs hencoding outside) selections dummy _
    (referenceEncodingProgram key inputs hencoding outside selections dummy adversary)

private theorem weighted_bound {Value : Type} (law : SPMF Value) (left right : Value → ENNReal) (rate : ENNReal)
    (h : ∀ value, left value ≤ rate * right value) :
    (∑' value, Pr[= value | law] * left value) ≤ rate * ∑' value, Pr[= value | law] * right value := by
  calc
    _ ≤ ∑' value, Pr[= value | law] * (rate * right value) :=
      ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (h value)
    _ = _ := by simp only [mul_left_comm _ rate, ENNReal.tsum_mul_left]

theorem referenceContactGame_contactMarker_count_le (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (∑' result, Pr[= result | referenceContactGame inputs hencoding dummy adversary] *
      (contactMarkerCount result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier (result.2.2.before * result.2.2.after) : ENNReal)) ≤
      ((OtsCode.unitNeighborBound : ENNReal) / (Fintype.card Digest : ENNReal)) * ∑' result,
        Pr[= result | referenceContactGame inputs hencoding dummy adversary] *
          (contactMarkerCost result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier 1 (result.2.2.before * result.2.2.after) : ENNReal) := by
  rw [referenceContactGame, ← referenceEncodingLazyGame_original contactObserver inputs hencoding hgraph dummy adversary]
  simp only [referenceEncodingLazyGame, tsum_probOutput_bind_mul, tsum_probOutput_map_mul, tsum_probOutput_pure_mul]
  apply weighted_bound
  intro parameter
  apply weighted_bound
  intro otsSecret
  apply weighted_bound
  intro ftsSecret
  apply weighted_bound
  intro selections
  apply weighted_bound
  intro outside
  exact referenceEncodingLazyRest_contactMarker_le ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter)
    outside selections dummy adversary

end SphincsSecurity.Concrete
