import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualBankCompleteness
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualStrongCoverage
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualPrimitivePotential
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualGameTransfer
import SigGolfCandidate.SphincsSecurity.Proof.Reference.ReferenceContactGame
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  signDigestLoop signAfterDigest gameInputs
set_option backward.isDefEq.respectTransparency false

theorem initialMonitoredSource_strong_certificate (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf))
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule) (stopped : Bool)
    (forgery : Forgery) (after : MonitoredState (gameInputs adversary))
    (hresult : initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped
      (some (forgery, true), after) ≠ 0)
    (hnew : ¬ SigningTranscript.Contains after.1.memory.log forgery) :
    TargetCertificateAt key Finset.univ (after.1.memory.external.cache, after.1.memory.log)
      (signingInput key forgery.message forgery.signature) := by
  have h := map_nonzero _ (fun result => (result.1, result.2.1)) (some (forgery, true), after) hresult
  rw [initialMonitoredSource, monitoredRun_erasure, hroot] at h
  rw [← run_erasure _ _ (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed)
    (initialAllowed_nonempty _ exposed), RetainedObservation.bind_nonzero] at h
  obtain ⟨labels, hlabels, h⟩ := h
  rw [initialState_completion] at hlabels
  rw [RetainedObservation.bind_nonzero] at h
  obtain ⟨seed, _, h⟩ := h
  let auxiliary : ReferenceAuxiliary (gameInputs adversary) := ⟨encoding.selections, encoding.rows, seed⟩
  have hauxiliary := referenceEncodingAuxiliary_support_seed (gameInputs adversary) encoding hencoding seed
  let context := initialContext key.parameter (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) auxiliary hauxiliary dummy exposed high labels
  have hrootContext : context.key.root = canonicalGraphRoot context.graph :=
    initialKnown_root (referenceFamilyWords encoding.selections dummy) exposed labels hlabels high
  have hcompatible : Compatible context (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed).memory := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [context, auxiliary, Context.words, Context.actual, initialContext, coordinateGraphLabels_value,
        initialState, initialMemory] using initialKnown_agrees (referenceFamilyWords encoding.selections dummy) exposed labels hlabels
    · exact initialKnown_graphReplies (referenceFamilyWords encoding.selections dummy) exposed labels hlabels high
    · intro input answer hanswer; cases hanswer
    · intro input answer hanswer; cases hanswer
    · intro input answer hanswer; cases hanswer
  have hrun : observedRun context.environment context.actual context.auxiliary.seed
      (simulateQ (adversaryImpl (gameInputs adversary) context.key.parameter context.key.root context.words context.auxiliary.selections)
        (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩))
      (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed)
      (some (forgery, true), after.1) ≠ 0 := by
    simpa only [context, auxiliary, Context.environment, Context.actual, Context.words, initialContext, coordinateGraphLabels_value] using h
  have hcertificate := observedRun_rest_certificate context adversary (sourceInputs_unlogged_subset_gameInputs adversary context.key)
    (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed) (initialState_rowsCovered _ _ exposed)
    hcompatible (signingHistory_initial context.key context.oracle _ exposed) hdummy hrootContext forgery after.1 hrun hnew
  have hparameter : context.key.parameter = key.parameter := rfl
  have hpublicRoot : context.key.root = key.root := hroot.symm
  simpa only [TargetCertificateAt, TargetCoveredOn, signingInput, hparameter, hpublicRoot] using hcertificate

theorem initialMonitoredSource_strong_count (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf))
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (budget : Nat) (stopAfter : CertificateStopRule) (stopped : Bool)
    (forgery : Forgery) (after : MonitoredState (gameInputs adversary))
    (hresult : initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ stopAfter stopped
      (some (forgery, true), after) ≠ 0)
    (hnew : ¬ SigningTranscript.Contains after.1.memory.log forgery) (halive : after.2.stopped = false) :
    1 ≤ certificateBankCount after.2.bank := by
  apply initialMonitoredSource_certificate_count key budget Finset.univ stopAfter adversary encoding dummy exposed high stopped
    (some (forgery, true), after) hresult halive (signingInput key forgery.message forgery.signature)
  exact initialMonitoredSource_strong_certificate key adversary encoding hencoding dummy hdummy exposed high hroot budget
    Finset.univ stopAfter stopped forgery after hresult hnew

def MonitoredStrongWin {inputs : Finset HashInput} (result : Option (Forgery × Bool) × MonitoredState inputs) : Prop :=
  ∃ value, result.1 = some value ∧ sourceVerdict value result.2.1.memory.log = true

def MonitoredStrongException {inputs : Finset HashInput} (result : Option (Forgery × Bool) × MonitoredState inputs) : Prop :=
  MonitoredStrongWin result ∧ result.2.2.stopped = true

theorem initialMonitoredSource_strong_le_count_add_exception (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf))
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (budget : Nat) (stopAfter : CertificateStopRule) (stopped : Bool) :
    Pr[MonitoredStrongWin | initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ stopAfter stopped] ≤
      (∑' result, Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ stopAfter stopped] *
        certificateBankCount result.2.2.bank) +
      Pr[MonitoredStrongException | initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ stopAfter stopped] := by
  let law := initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ stopAfter stopped
  have hcount : Pr[fun result => MonitoredStrongWin result ∧ result.2.2.stopped = false | law] ≤
      ∑' result, Pr[= result | law] * certificateBankCount result.2.2.bank := by
    apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
    rintro ⟨answer, after⟩ hsupport ⟨⟨⟨forgery, checked⟩, hanswer, hwin⟩, halive⟩
    simp only [sourceVerdict, Bool.and_eq_true, decide_eq_true_eq] at hwin
    obtain ⟨⟨_, hnew⟩, rfl⟩ := hwin
    dsimp only at hanswer halive hnew ⊢
    subst answer
    have hresult := probOutput_ne_zero_of_mem_support hsupport
    rw [SPMF.probOutput_eq_apply] at hresult
    exact initialMonitoredSource_strong_count key adversary encoding hencoding dummy hdummy exposed high hroot
      budget stopAfter stopped forgery after hresult hnew halive
  have hsplit : Pr[MonitoredStrongWin | law] ≤
      Pr[fun result => MonitoredStrongWin result ∧ result.2.2.stopped = false | law] + Pr[MonitoredStrongException | law] := by
    apply le_trans ?_ (probEvent_or_le law _ _)
    apply probEvent_mono
    intro result _ hwin
    cases hstop : result.2.2.stopped with
    | false => exact Or.inl ⟨hwin, rfl⟩
    | true => exact Or.inr ⟨hwin, hstop⟩
  exact hsplit.trans (add_le_add hcount le_rfl)

theorem initialMonitoredSource_stop_add_strong_le (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf))
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 128) :
    Pr[fun result => result.1 = none |
      initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped] +
      Pr[MonitoredStrongWin |
        initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped] ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) * fullCertificateTotalRate +
        Pr[MonitoredStrongException |
          initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped] := by
  have hwin := initialMonitoredSource_strong_le_count_add_exception key adversary encoding hencoding dummy hdummy exposed high hroot
    budget (proposalStop stopAfter) stopped
  have hbound := initialMonitoredSource_primitive_add_full_count_le key adversary encoding dummy exposed high budget stopAfter stopped
    hparameter hencoding hroot hcost hbudget
  exact (add_le_add le_rfl hwin).trans (by rw [← add_assoc]; exact add_le_add hbound le_rfl)

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private theorem probEvent_bind_le_constant {A B : Type} (law : SPMF A)
    (next : A → SPMF B) (event : B → Prop) (rate : ENNReal)
    (h : ∀ value, law value ≠ 0 → Pr[event | next value] ≤ rate) :
    Pr[event | law >>= next] ≤ rate := by
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' value, Pr[= value | law] * rate := by
      apply ENNReal.tsum_le_tsum
      intro value
      by_cases hv : law value = 0
      · simp only [SPMF.probOutput_eq_apply, hv, zero_mul, le_refl]
      · exact mul_le_mul' le_rfl (h value hv)
    _ ≤ rate := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem sourceGame_fault_within_budget_le (dummy : OtsReferenceWords)
    (adversary : Adversary) (budget : Nat)
    (hminimum : keygenHashCost ≤ budget) (hbudget : budget ≤ 2 ^ 128) :
    Pr[fun result => result.1 = none ∧ result.2.memory.external.hashCalls ≤ budget |
      sourceGame dummy adversary] ≤
    ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) -
      ((budget : ℝ) / 2 ^ digestBits) ^ 2) := by
  unfold sourceGame
  apply probEvent_bind_le_constant
  intro parameter _
  apply probEvent_bind_le_constant
  intro encoding hencoding
  have hencoding' : encoding ∈ referenceEncodingAuxiliarySample.support := by
    apply (PMF.mem_support_iff _ _).mpr
    simpa only [PMF.evalSPMF_eq, SPMF.liftM_apply] using hencoding
  apply probEvent_bind_le_constant
  intro high _
  apply probEvent_bind_le_constant
  intro exposed _
  let words := referenceFamilyWords encoding.selections dummy
  let key : SecretKey := ⟨parameter, knownRoot (initialKnown words exposed), default, default⟩
  exact initialSource_fault_within_budget_le key adversary encoding dummy exposed high budget
    hencoding' hminimum hbudget

end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.sourceGame_fault_within_budget_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.sourceGame_fault_within_budget_le

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sourceGame_fault_budget_eq_zero_of_lt (dummy : OtsReferenceWords)
    (adversary : Adversary) (budget : Nat) (hsmall : budget < keygenHashCost) :
    Pr[fun result => result.1 = none ∧ result.2.memory.external.hashCalls ≤ budget |
      sourceGame dummy adversary] = 0 := by
  apply le_antisymm ?_ bot_le
  unfold sourceGame
  apply probEvent_bind_le_constant
  intro parameter _
  apply probEvent_bind_le_constant
  intro encoding _
  apply probEvent_bind_le_constant
  intro high _
  apply probEvent_bind_le_constant
  intro exposed _
  let words := referenceFamilyWords encoding.selections dummy
  let key : SecretKey := ⟨parameter, knownRoot (initialKnown words exposed), default, default⟩
  let state := initialState (gameInputs adversary) words exposed
  let program := simulateQ
    (adversaryImpl (gameInputs adversary) parameter key.root words encoding.selections)
    (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, parameter⟩)
  let law := lazyRun (environment parameter (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary parameter)
    words (coordinateGraphLabels (initialKnown words exposed) high) encoding.selections encoding.rows)
    program state
  change Pr[fun result => result.1 = none ∧ result.2.memory.external.hashCalls ≤ budget | law] ≤ 0
  rw [probEvent_eq_tsum_ite]
  apply le_of_eq
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  by_cases hr : Pr[= result | law] = 0
  · simp [hr]
  have hmono := lazyRun_source_hashCalls_mono (gameInputs adversary) words
    (coordinateGraphLabels (initialKnown words exposed) high) encoding.selections encoding.rows key
    (canonicalEncodingInputs_subset_retainedGameInputs adversary parameter)
    (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, parameter⟩)
    (sourceInputs_unlogged_subset_gameInputs adversary key) state
    (initialAllowed_nonempty words exposed) (initialState_rowsCovered _ _ exposed) result
    (by simpa only [law, program, key, SPMF.probOutput_eq_apply] using hr)
  have hcost : keygenHashCost ≤ result.2.memory.external.hashCalls := by
    simpa only [state, initialState, initialMemory] using hmono
  have hnot : ¬(result.1 = none ∧ result.2.memory.external.hashCalls ≤ budget) := by omega
  simp [hnot]


theorem sourceGame_fault_within_budget_le_all (dummy : OtsReferenceWords)
    (adversary : Adversary) (budget : Nat) (hbudget : budget ≤ 2 ^ 128) :
    Pr[fun result => result.1 = none ∧ result.2.memory.external.hashCalls ≤ budget |
      sourceGame dummy adversary] ≤
    ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) -
      ((budget : ℝ) / 2 ^ digestBits) ^ 2) := by
  by_cases hminimum : keygenHashCost ≤ budget
  · exact sourceGame_fault_within_budget_le dummy adversary budget hminimum hbudget
  · rw [sourceGame_fault_budget_eq_zero_of_lt dummy adversary budget (by omega)]
    exact zero_le

end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.sourceGame_fault_budget_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.sourceGame_fault_budget_eq_zero_of_lt

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.sourceGame_fault_within_budget_le_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.sourceGame_fault_within_budget_le_all

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem originalGame_budget_eq_prefixPrior (dummy : OtsReferenceWords)
    (adversary : Adversary) (budget : Nat) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ budget |
      (simulateQ romImpl (countHashQueries (gameCore scheme adversary))).run' ∅] =
    Pr[fun result => result.2.1 = true ∧ result.2.2.hashCalls ≤ budget |
      referencePrefixJointPriorGame (gameInputs adversary)
        (canonicalEncodingInputs_subset_retainedGameInputs adversary) dummy adversary] := by
  conv_lhs => rw [← probEvent_evalSPMF]
  rw [← SigGolfCandidate.BoundaryCount.boundaryGameCore_count_law,
    boundaryGameCore_eq_retainedPrefixPrior, probEvent_map, probEvent_map]
  rfl

end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.originalGame_budget_eq_prefixPrior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.originalGame_budget_eq_prefixPrior

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem Context.frontierGame_counted {inputs : Finset HashInput} (context : Context inputs)
    (adversary : Adversary) (hroot : context.key.root = canonicalGraphRoot context.graph) :
    (fun result => (result.1, result.2.hashCalls)) <$>
      referenceFamilyFrontierRest context.key context.oracle context.graph
        context.auxiliary.selections context.dummy adversary =
    (fun result => (result.1, keygenHashCost + result.2)) <$>
      simulateQ (fixedHashWorld context.oracle)
        (countHashQueries
          (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key)) := by
  have hselection : referenceTableSelection context.key context.oracle = context.auxiliary.selections :=
    referenceTableSelection_prefix context.key inputs context.encoding context.graph context.auxiliary context.auxiliary_valid
  have hgraph : canonicalGraphLabels context.key.parameter context.key.otsSecret context.key.ftsSecret context.oracle =
      context.graph := canonicalGraphLabels_programmedHash _ _ _ _ _
  have hfrontier : referenceFamilyFrontierRest context.key context.oracle context.graph
      context.auxiliary.selections context.dummy adversary =
      fixedBoundaryRun context.key.parameter context.oracle
        (gameAfterSecrets adversary context.key.parameter context.key.otsSecret context.key.ftsSecret) := by
    rw [← hselection, referenceFamilyFrontierRest_selected, ← hgraph, graphFrontierGameRest_canonical]
  rw [hfrontier, gameAfterSecrets, fixedBoundaryRun_bind, context.keygen_record hroot, pure_bind]
  have hkey : (⟨context.key.parameter, context.key.root, context.key.otsSecret, context.key.ftsSecret⟩ : SecretKey) = context.key := by
    cases context.key
    rfl
  rw [hkey, ← fixedBoundaryRun_count context.key.parameter context.oracle
    (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key)]
  simp only [Functor.map_map, map_pure]
  simp only [SigningBoundaryTrace.hashCalls_mul, SigningBoundaryTrace.hashCalls_pow_none]

end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.Context.frontierGame_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.Context.frontierGame_counted
