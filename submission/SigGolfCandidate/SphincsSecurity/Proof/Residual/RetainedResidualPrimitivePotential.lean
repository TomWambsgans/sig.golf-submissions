import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualSigningCandidates
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualEncodingHistory
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualQueryPotential
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualTerminalCoverage
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open ResidualByteFrontend (HiddenCandidateBound)
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyRun_request_hiddenCandidateBound (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hbound : HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (result : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0) :
    HiddenCandidateBound words result.2.memory.routing.disclosed (project result.2) := by
  cases input with
  | inl input =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hresult
      rw [lazyRun_externalProgram] at hresult
      have hafter := lazyByteRun_hiddenCandidateBound key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing _ hinputs state ha hbound result hresult
      have hrouting := lazyRun_embed_routing key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing _ state ha result hresult
      rw [hrouting]
      exact hafter
  | inr message =>
      exact lazyRun_signingProgram_hiddenCandidateBound inputs words publicReplies selections rows key hencoding message hinputs state
        ha hcovered hbound result hresult

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

noncomputable def primitiveContinuation (budget : Nat) (memory : Memory) : ENNReal :=
  ENNReal.ofReal (PrimitiveMessagePotential.value (2 ^ digestBits) memory.external.probes
    ((budget : ℝ) - memory.external.hashCalls))

noncomputable def primitiveLivePotential (budget : Nat) (memory : Memory) : ENNReal :=
  (memory.messageCalls.length : ENNReal) / 2 ^ digestBits + primitiveContinuation budget memory

noncomputable def primitiveResultPotential {Result : Type} {inputs : Finset HashInput}
    (budget : Nat) (result : Option Result × State inputs) : ENNReal :=
  (result.2.memory.messageCalls.length : ENNReal) / 2 ^ digestBits +
    result.1.elim 1 (fun _ => primitiveContinuation budget result.2.memory)

theorem primitiveLivePotential_applyBoundary_le (budget : Nat) (memory : Memory) (trace : SigningBoundaryTrace)
    (hresources : ProbeMessageBound memory) (hcost : memory.external.hashCalls + trace.hashCalls ≤ budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    primitiveLivePotential budget (memory.applyBoundary trace) ≤ primitiveLivePotential budget memory := by
  have hp : (memory.external.probes : ℝ) ≤ memory.external.hashCalls := by
    exact_mod_cast (show memory.external.probes ≤ memory.external.hashCalls from
      (Nat.le_add_right _ _).trans hresources)
  have hc : (memory.external.hashCalls : ℝ) + trace.hashCalls ≤ budget := by exact_mod_cast hcost
  have hb : 2 * (budget : ℝ) ≤ 2 ^ digestBits := by exact_mod_cast hbudget
  have hr : (0 : ℝ) ≤ budget - (memory.external.hashCalls + trace.hashCalls) := by linarith
  have hs : (0 : ℝ) < 2 ^ digestBits := by positivity
  have hpay := PrimitiveMessagePotential.work_payment (2 ^ digestBits) memory.external.probes
    ((budget : ℝ) - (memory.external.hashCalls + trace.hashCalls)) trace.messageCalls.length trace.hashCalls hs
    (by positivity) hr (List.length_filterMap_le _ _) (by linarith)
  have hrestore : (budget : ℝ) - (memory.external.hashCalls + trace.hashCalls) + trace.hashCalls =
      budget - memory.external.hashCalls := by ring
  rw [hrestore] at hpay
  have hbounds := PrimitiveMessagePotential.bounds (2 ^ digestBits) memory.external.probes
    ((budget : ℝ) - (memory.external.hashCalls + trace.hashCalls)) hr (by linarith)
  have hpayment := ENNReal.ofReal_le_ofReal hpay
  rw [ENNReal.ofReal_add (by positivity) hbounds.1, ENNReal.ofReal_div_of_pos hs,
    ENNReal.ofReal_natCast] at hpayment
  norm_num only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at hpayment
  change (memory.messageCalls ++ trace.messageCalls).length / (2 ^ digestBits : ENNReal) +
      ENNReal.ofReal (PrimitiveMessagePotential.value (2 ^ digestBits) memory.external.probes
        ((budget : ℝ) - (memory.external.hashCalls + trace.hashCalls : Nat))) ≤ _
  rw [List.length_append, Nat.cast_add, ENNReal.add_div, Nat.cast_add, add_assoc]
  exact add_le_add le_rfl hpayment

theorem primitiveLivePotential_recordSigning (budget : Nat) (memory : Memory) (message : Message) (record : SigningRecord) :
    primitiveLivePotential budget (memory.recordSigning message record) = primitiveLivePotential budget memory := rfl

private theorem expected_indicator_value_le {Result : Type} (law : SPMF Result) (event : Result → Prop) [DecidablePred event]
    (cost value : ENNReal) :
    (∑' result, Pr[= result | law] * (cost + if event result then 1 else value)) ≤
      cost + Pr[event | law] + (1 - Pr[event | law]) * value := by
  have hcomplement : Pr[fun result => ¬event result | law] ≤ 1 - Pr[event | law] := by
    apply ENNReal.le_sub_of_add_le_left probEvent_ne_top
    rw [probEvent_compl]
    exact tsub_le_self
  have hsplit : (∑' result, Pr[= result | law] * (if event result then 1 else value)) =
      Pr[event | law] + Pr[fun result => ¬event result | law] * value := by
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases he : event result <;> simp [he]
  simp only [mul_add, ENNReal.tsum_add]
  rw [hsplit, ENNReal.tsum_mul_right, ← add_assoc]
  exact add_le_add (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl)
    (mul_le_mul' hcomplement le_rfl)

private theorem ennreal_mixture_le (probability : ENNReal) (hprobability : probability ≤ 1)
    (value bound : ℝ) (hvalue : 0 ≤ value) (hbound : 0 ≤ bound)
    (h : probability.toReal + (1 - probability.toReal) * value ≤ bound) :
    probability + (1 - probability) * ENNReal.ofReal value ≤ ENNReal.ofReal bound := by
  have hp : probability ≠ ⊤ := ne_top_of_le_ne_top (by simp) hprobability
  have hs : 1 - probability ≠ ⊤ := ne_top_of_le_ne_top (by simp) tsub_le_self
  apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hp, ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top⟩)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_add hp (ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le hprobability (by simp), ENNReal.toReal_one,
    ENNReal.toReal_ofReal hvalue, ENNReal.toReal_ofReal hbound]
  exact h

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyByteRun_hash_jointPotential (routing : Routing) (input : HashInput) (hin : input ∈ inputs)
    (state : State inputs) (budget : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory) (hquery : state.memory.external.hashCalls + 1 ≤ budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query (.inr input))) state] * primitiveResultPotential budget result) ≤
      primitiveLivePotential budget state.memory := by
  let law := lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
    (liftM (OracleWorld.query (.inr input))) state
  let afterProbes := (charge parameter words routing.disclosed routing.known input state.memory.external).probes
  let nextValue := PrimitiveMessagePotential.value (2 ^ digestBits) afterProbes
    ((budget : ℝ) - (state.memory.external.hashCalls + 1))
  let increment : ℝ := if FtsProbeSimulation.MessageHashInput parameter input then (2 ^ digestBits : ℝ)⁻¹ else 0
  have hlaw : law = lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.checkedHashQuery
          (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) ⟨input, hin⟩)) state := by
    simp only [law, lazyByteRun, simulateQ_spec_query, ResidualByteFrontend.checkedTranslate, dif_pos hin]
  have hp : (state.memory.external.probes : ℝ) ≤ state.memory.external.hashCalls := by
    exact_mod_cast (show state.memory.external.probes ≤ state.memory.external.hashCalls from
      (Nat.le_add_right _ _).trans hresources)
  have hc : (state.memory.external.hashCalls : ℝ) + 1 ≤ budget := by exact_mod_cast hquery
  have hb : 2 * (budget : ℝ) ≤ 2 ^ digestBits := by exact_mod_cast hbudget
  have hs : (0 : ℝ) < 2 ^ digestBits := by positivity
  have hap : (afterProbes : ℝ) ≤ state.memory.external.probes + 1 := by
    exact_mod_cast charge_probes_le parameter words routing.disclosed routing.known input state.memory.external
  have hn : 0 ≤ nextValue := (PrimitiveMessagePotential.bounds (2 ^ digestBits) afterProbes
    ((budget : ℝ) - (state.memory.external.hashCalls + 1)) (by linarith) (by linarith)).1
  have hi : 0 ≤ increment := by unfold increment; split <;> positivity
  have hbefore := (PrimitiveMessagePotential.bounds (2 ^ digestBits) state.memory.external.probes
    ((budget : ℝ) - state.memory.external.hashCalls) (by linarith) (by linarith)).1
  have hscalar := checkedHashQuery_joint_payment parameter inputs hencoding words publicReplies selections rows routing
    ⟨input, hin⟩ state budget hselect ha hcovered hcandidates hclean hresources hquery hbudget
  dsimp only at hscalar
  rw [← hlaw] at hscalar
  change (Pr[fun result => result.1 = none | law]).toReal +
    (1 - (Pr[fun result => result.1 = none | law]).toReal) * (increment + nextValue) ≤ _ at hscalar
  have hpayment := ennreal_mixture_le (Pr[fun result => result.1 = none | law]) probEvent_le_one _ _
    (add_nonneg hi hn) hbefore hscalar
  change (∑' result, Pr[= result | law] * primitiveResultPotential budget result) ≤ _
  calc
    _ ≤ ∑' result, Pr[= result | law] *
        ((state.memory.messageCalls.length : ENNReal) / 2 ^ digestBits +
          if result.1 = none then 1 else ENNReal.ofReal (increment + nextValue)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | law] = 0
      · simp only [hr, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        obtain ⟨actual, seed, heq⟩ := lazyByteRun_hash_result parameter inputs hencoding words publicReplies selections rows
          routing input hin state ha result hr
        have hhash := checkedHashResult_hashCalls parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state
        have hprobes := checkedHashResult_probes parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state
        have hmemory := checkedHashResult_memory parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state
        rw [← heq] at hhash hprobes hmemory
        have hmessages := congrArg (fun memory : Memory => memory.messageCalls.length) hmemory
        by_cases hnone : result.1 = none
        · simp only [hnone, Memory.afterReply, Option.elim_none] at hmessages
          simp only [primitiveResultPotential, hnone, Option.elim_none, hmessages, if_pos, le_refl]
        · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hnone
          simp only [hanswer, Memory.afterReply, Option.elim_some, Memory.observeMessage] at hmessages
          simp only [primitiveResultPotential, hanswer, Option.elim_some, reduceCtorEq, if_false,
            primitiveContinuation, hhash, Nat.cast_add, Nat.cast_one, hprobes]
          by_cases hm : FtsProbeSimulation.MessageHashInput parameter input
          · simp only [if_pos hm, List.length_append, List.length_singleton] at hmessages
            rw [hmessages, Nat.cast_add, Nat.cast_one, ENNReal.add_div, add_assoc]
            unfold increment
            rw [if_pos hm, ENNReal.ofReal_add (by positivity) hn]
            simp only [one_div, ENNReal.ofReal_inv_of_pos hs,
              ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, nextValue, afterProbes, le_refl]
          · simp only [if_neg hm] at hmessages
            rw [hmessages]
            simp only [increment, if_neg hm, zero_add, nextValue, afterProbes, le_refl]
    _ ≤ (state.memory.messageCalls.length : ENNReal) / 2 ^ digestBits +
        (Pr[fun result => result.1 = none | law] +
          (1 - Pr[fun result => result.1 = none | law]) * ENNReal.ofReal (increment + nextValue)) := by
      simpa only [add_assoc] using expected_indicator_value_le law (fun result => result.1 = none)
        ((state.memory.messageCalls.length : ENNReal) / 2 ^ digestBits) (ENNReal.ofReal (increment + nextValue))
    _ ≤ _ := add_le_add le_rfl hpayment

omit parameter hencoding in
theorem lazyRun_signingProgram_jointPotential (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (message : Message)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs) (state : State inputs) (budget : Nat)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hresources : ProbeMessageBound state.memory)
    (hbudget : 2 * budget ≤ 2 ^ digestBits)
    (hcost : ∀ result, lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (signingProgram inputs key.parameter key.root words selections message) state result ≠ 0 →
        result.2.memory.external.hashCalls ≤ budget) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (signingProgram inputs key.parameter key.root words selections message) state] * primitiveResultPotential budget result) ≤
      primitiveLivePotential budget state.memory := by
  calc
    _ ≤ ∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (signingProgram inputs key.parameter key.root words selections message) state] * primitiveLivePotential budget state.memory := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
          (signingProgram inputs key.parameter key.root words selections message) state] = 0
      · simp only [hr, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        have hc := hcost result hr
        rw [SPMF.probOutput_eq_apply] at hr
        rw [lazyRun_signingProgram key inputs hencoding words publicReplies selections rows message state,
          map_eq_bind_pure_comp] at hr
        obtain ⟨raw, hraw, hr⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hr
        have hloop := (ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key
          state.memory.routing.known words selections message).trans hinputs
        rw [ResidualByteFrontend.hashInputs_publicSigningWork] at hloop
        obtain ⟨record, hrecord, hmemory⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
          state.memory.routing key.root message hloop state ha hcovered raw hraw
        simp only [Function.comp_def, hrecord, Option.elim_some, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        subst result
        change primitiveLivePotential budget (raw.2.memory.recordSigning message record) ≤ _
        rw [primitiveLivePotential_recordSigning, hmemory]
        change raw.2.memory.external.hashCalls ≤ budget at hc
        rw [hmemory] at hc
        exact primitiveLivePotential_applyBoundary_le budget state.memory record.2 hresources hc hbudget
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem lazyByteRun_world_jointPotential (routing : Routing) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (state : State inputs) (budget : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory)
    (hquery : state.memory.external.hashCalls + (if input matches .inr _ then 1 else 0) ≤ budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query input)) state] * primitiveResultPotential budget result) ≤
      primitiveLivePotential budget state.memory := by
  cases input with
  | inr input =>
      have hin : input ∈ inputs := hinputs (by
        simpa only [bind_pure] using mem_hashInputs_hash_bind input pure)
      exact lazyByteRun_hash_jointPotential parameter inputs hencoding words publicReplies selections rows routing input hin state budget
        hselect ha hcovered hcandidates hclean hresources hquery hbudget
  | inl input =>
      rw [← bind_pure (liftM (OracleWorld.query (.inl input))), lazyByteRun_random_bind, tsum_probOutput_bind_mul]
      simp only [lazyByteRun_pure, tsum_probOutput_pure_mul, primitiveResultPotential, Option.elim_some]
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem lazyRun_supported_result {Result : Type} (computation : OracleComp (World inputs) Result)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    ∃ result, lazyRun (environment parameter inputs hencoding words publicReplies selections rows) computation state result ≠ 0 := by
  have h := lazyRun_bind_const (environment parameter inputs hencoding words publicReplies selections rows) computation state ha
    (pure () : SPMF Unit)
  have hh := congrArg (fun law : SPMF Unit => Pr[= () | law]) h
  simp only [probOutput_bind_eq_tsum, probOutput_pure_self, mul_one] at hh
  by_contra hn
  simp only [not_exists, not_not] at hn
  simp only [SPMF.probOutput_eq_apply, hn, tsum_zero] at hh
  exact zero_ne_one hh

omit parameter hencoding in
theorem lazyRun_request_jointPotential (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs) (budget : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.memory.routing.known) words selections) state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory) (hbudget : 2 * budget ≤ 2 ^ digestBits)
    (hcost : ∀ result, lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0 →
        result.2.memory.external.hashCalls ≤ budget) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (adversaryImpl inputs key.parameter key.root words selections input) state] * primitiveResultPotential budget result) ≤
      primitiveLivePotential budget state.memory := by
  cases input with
  | inr message =>
      exact lazyRun_signingProgram_jointPotential inputs words publicReplies selections rows key hencoding message hinputs state budget
        ha hcovered hresources hbudget hcost
  | inl input =>
      obtain ⟨result, hr⟩ := lazyRun_supported_result key.parameter inputs hencoding words publicReplies selections rows
        (adversaryImpl inputs key.parameter key.root words selections (.inl input)) state ha
      have hc := hcost result hr
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hr
      rw [lazyRun_externalProgram] at hr
      have hh := lazyByteRun_world_hashCalls key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing input hinputs state ha result hr
      rw [hh] at hc
      change (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state] * primitiveResultPotential budget result) ≤ _
      rw [lazyRun_externalProgram]
      exact lazyByteRun_world_jointPotential key.parameter inputs hencoding words publicReplies selections rows state.memory.routing input
        hinputs state budget hselect ha hcovered hcandidates hclean hresources (by cases input <;> exact hc) hbudget

omit parameter hencoding in
theorem lazyRun_request_hashCalls_mono (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0) :
    state.memory.external.hashCalls ≤ result.2.memory.external.hashCalls := by
  cases input with
  | inl input =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hresult
      rw [lazyRun_externalProgram] at hresult
      rw [lazyByteRun_world_hashCalls key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing input hinputs state ha result hresult]
      exact Nat.le_add_right _ _
  | inr message =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (signingProgram inputs key.parameter key.root words selections message) state result ≠ 0 at hresult
      rw [lazyRun_signingProgram key inputs hencoding words publicReplies selections rows message state,
        map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      have hloop := (ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key
        state.memory.routing.known words selections message).trans hinputs
      rw [ResidualByteFrontend.hashInputs_publicSigningWork] at hloop
      obtain ⟨record, hrecord, hmemory⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing key.root message hloop state ha hcovered raw hraw
      simp only [Function.comp_def, hrecord, Option.elim_some, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      change state.memory.external.hashCalls ≤ raw.2.memory.external.hashCalls
      rw [hmemory]
      exact Nat.le_add_right _ _

omit parameter hencoding in
theorem lazyRun_source_hashCalls_mono {Result : Type} (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (hinputs : sourceInputs key computation ⊆ inputs)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (result : Option Result × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation) state result ≠ 0) :
    state.memory.external.hashCalls ≤ result.2.memory.external.hashCalls := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, lazyRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, lazyRun_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨middle, hmiddle, hresult⟩ := hresult
      have hm := lazyRun_request_hashCalls_mono inputs words publicReplies selections rows key hencoding input
        ((requestInputs_subset key input next).trans hinputs) state ha hcovered middle hmiddle
      have ha' := lazyRun_nonempty (environment key.parameter inputs hencoding words publicReplies selections rows) _ state ha middle hmiddle
      have hc' := lazyRun_rowsCovered key.parameter inputs hencoding words publicReplies selections rows _ state ha hcovered middle hmiddle
      rcases middle with ⟨answer, after⟩
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hm
      | some answer =>
          exact hm.trans (ih answer ((sourceInputs_next_subset key input next answer).trans hinputs) after ha' hc' result hresult)

omit parameter hencoding in
theorem lazyRun_source_jointPotential {Result : Type} (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (hinputs : sourceInputs key computation ⊆ inputs)
    (state : State inputs) (budget : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.memory.routing.known) words selections) state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory) (hbudget : 2 * budget ≤ 2 ^ digestBits)
    (hcost : ∀ result, lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation) state result ≠ 0 →
        result.2.memory.external.hashCalls ≤ budget) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation) state] * primitiveResultPotential budget result) ≤
      primitiveLivePotential budget state.memory := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, lazyRun, runWith_pure, tsum_probOutput_pure_mul,
        primitiveResultPotential, Option.elim_some, primitiveLivePotential, le_refl]
  | query_bind input next ih =>
      have hin := (requestInputs_subset key input next).trans hinputs
      have hnext : ∀ answer, sourceInputs key (next answer) ⊆ inputs :=
        fun answer => (sourceInputs_next_subset key input next answer).trans hinputs
      have hjoined (middle : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
          (hmiddle : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
            (adversaryImpl inputs key.parameter key.root words selections input) state middle ≠ 0)
          (result : Option Result × State inputs)
          (hresult : middle.1.elim (pure (none, middle.2)) (fun answer =>
            lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
              (simulateQ (adversaryImpl inputs key.parameter key.root words selections) (next answer)) middle.2) result ≠ 0) :
          result.2.memory.external.hashCalls ≤ budget := by
        apply hcost result
        rw [simulateQ_bind, simulateQ_spec_query, lazyRun_bind, RetainedObservation.bind_nonzero]
        exact ⟨middle, hmiddle, hresult⟩
      have hstepcost (middle : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
          (hmiddle : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
            (adversaryImpl inputs key.parameter key.root words selections input) state middle ≠ 0) :
          middle.2.memory.external.hashCalls ≤ budget := by
        have ha' := lazyRun_nonempty (environment key.parameter inputs hencoding words publicReplies selections rows) _ state ha middle hmiddle
        have hc' := lazyRun_rowsCovered key.parameter inputs hencoding words publicReplies selections rows _ state ha hcovered middle hmiddle
        rcases middle with ⟨answer, after⟩
        cases answer with
        | none => exact hjoined (none, after) hmiddle (none, after) (by simp)
        | some answer =>
            obtain ⟨result, hr⟩ := lazyRun_supported_result key.parameter inputs hencoding words publicReplies selections rows
              (simulateQ (adversaryImpl inputs key.parameter key.root words selections) (next answer)) after ha'
            exact (lazyRun_source_hashCalls_mono inputs words publicReplies selections rows key hencoding (next answer)
              (hnext answer) after ha' hc' result hr).trans (hjoined (some answer, after) hmiddle result hr)
      apply le_trans ?_ (lazyRun_request_jointPotential inputs words publicReplies selections rows key hencoding input hin state budget
        hselect ha hcovered hcandidates hclean hresources hbudget hstepcost)
      rw [simulateQ_bind, simulateQ_spec_query, lazyRun_bind, tsum_probOutput_bind_mul]
      apply ENNReal.tsum_le_tsum
      intro middle
      by_cases hm : Pr[= middle | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
          (adversaryImpl inputs key.parameter key.root words selections input) state] = 0
      · simp only [hm, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        have ha' := lazyRun_nonempty (environment key.parameter inputs hencoding words publicReplies selections rows) _ state ha middle hm
        have hc' := lazyRun_rowsCovered key.parameter inputs hencoding words publicReplies selections rows _ state ha hcovered middle hm
        have hp' := lazyRun_request_hiddenCandidateBound key inputs hencoding words publicReplies selections rows input hin state
          ha hcovered hcandidates middle hm
        have hr' := lazyRun_request_probeMessageBound inputs words publicReplies selections rows key hencoding input hin state
          ha hcovered hresources middle hm
        rcases middle with ⟨answer, after⟩
        cases answer with
        | none => simp only [Option.elim_none, tsum_probOutput_pure_mul, primitiveResultPotential, Option.elim_none, le_refl]
        | some answer =>
            have he' := lazyRun_request_encodingClean inputs words publicReplies selections rows key hencoding input hin state
              ha hcovered hclean (some answer, after) hm (by simp)
            exact ih answer (hnext answer) after ha' hc' hp' he' hr' (hjoined (some answer, after) hm)

theorem stop_add_messages_le_expected_primitivePotential {Result : Type} {inputs : Finset HashInput}
    (budget : Nat) (law : SPMF (Option Result × State inputs)) :
    Pr[fun result => result.1 = none | law] +
      (∑' result, Pr[= result | law] * (result.2.memory.messageCalls.length : ENNReal)) / 2 ^ digestBits ≤
        ∑' result, Pr[= result | law] * primitiveResultPotential budget result := by
  rw [probEvent_eq_tsum_ite, div_eq_mul_inv, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [primitiveResultPotential, mul_add, div_eq_mul_inv, mul_assoc, add_comm]
  apply add_le_add le_rfl
  cases result.1 with
  | none => simp only [if_pos, Option.elim_none, mul_one, le_refl]
  | some answer => simp only [reduceCtorEq, if_false, zero_le]

theorem primitiveLivePotential_initial_le (inputs : Finset HashInput) (words : OtsReferenceWords)
    (exposed : InitialPublicLabels words) (budget : Nat) (hcost : keygenHashCost ≤ budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    primitiveLivePotential budget (initialState inputs words exposed).memory ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) := by
  have hc : (keygenHashCost : ℝ) ≤ budget := by exact_mod_cast hcost
  have hk : (0 : ℝ) ≤ keygenHashCost := Nat.cast_nonneg _
  have hb : 2 * (budget : ℝ) ≤ 2 ^ digestBits := by exact_mod_cast hbudget
  have hs : (0 : ℝ) < 2 ^ digestBits := by positivity
  have hm := PrimitiveMessagePotential.mono_remaining (2 ^ digestBits) 0 ((budget : ℝ) - keygenHashCost) budget
    (by linarith) (by linarith) (by linarith)
  rw [PrimitiveMessagePotential.initial _ (budget : ℝ) hs.ne'] at hm
  simpa only [primitiveLivePotential, primitiveContinuation, initialState, initialMemory, List.length_nil,
    Nat.cast_zero, Nat.cast_ofNat, ENNReal.zero_div, zero_add] using ENNReal.ofReal_le_ofReal hm

omit parameter inputs hencoding words publicReplies selections rows in
theorem initialMonitoredSource_joint_primitive_messages (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 128) :
    Pr[fun result => result.1 = none | initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped] +
      (∑' result, Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped] *
        (result.2.1.memory.messageCalls.length : ENNReal)) / 2 ^ digestBits ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) := by
  let inputs := gameInputs adversary
  let words := referenceFamilyWords encoding.selections dummy
  let publicReplies := coordinateGraphLabels (initialKnown words exposed) high
  let source := FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩
  let initial := initialState inputs words exposed
  let env := environment key.parameter inputs (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    words publicReplies encoding.selections encoding.rows
  let computation := simulateQ (adversaryImpl inputs key.parameter key.root words encoding.selections) source
  let native := lazyRun env computation initial
  have herasure : (fun result => (result.1, result.2.1)) <$>
      initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped = native := by
    exact monitoredRun_erasure key inputs (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
      words publicReplies encoding.selections encoding.rows budget required stopAfter source
      (initial, initialCertificateMonitor keygenHashCost stopped)
  have hnativeCost (result : Option (Forgery × Bool) × State inputs) (hr : native result ≠ 0) :
      result.2.memory.external.hashCalls ≤ budget := by
    rw [← herasure, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hr
    obtain ⟨full, hfull, hr⟩ := hr
    simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
    subst result
    exact initialMonitoredSource_hashCalls_le key adversary encoding dummy exposed high budget required stopAfter stopped
      hparameter hencoding hroot hcost full hfull
  have ha : ∀ coordinate, (initial.candidates coordinate).Nonempty := initialAllowed_nonempty words exposed
  have hc : ResidualByteFrontend.RowsCovered inputs (project initial) := initialState_rowsCovered inputs words exposed
  have hin : sourceInputs key source ⊆ inputs := sourceInputs_unlogged_subset_gameInputs adversary key
  have hd : 2 * budget ≤ 2 ^ digestBits := by
    norm_num only [digestBits]
    omega
  have hpotential := lazyRun_source_jointPotential inputs words publicReplies encoding.selections encoding.rows key
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) source hin initial budget
    (referenceEncodingAuxiliary_select encoding hencoding) ha hc (initialState_hiddenCandidateBound inputs words exposed)
    (ResidualByteFrontend.replyClean_empty _) (Nat.zero_le _) hd hnativeCost
  obtain ⟨result, hr⟩ := lazyRun_supported_result key.parameter inputs
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) words publicReplies encoding.selections encoding.rows computation initial ha
  have hminimum : keygenHashCost ≤ budget :=
    (lazyRun_source_hashCalls_mono inputs words publicReplies encoding.selections encoding.rows key
      (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) source hin initial ha hc result hr).trans (hnativeCost result hr)
  have h := (stop_add_messages_le_expected_primitivePotential budget native).trans
    (hpotential.trans (primitiveLivePotential_initial_le inputs words exposed budget hminimum hd))
  rw [← herasure, probEvent_map, tsum_probOutput_map_mul] at h
  exact h

omit parameter inputs hencoding words publicReplies selections rows in
theorem initialMonitoredSource_messageCalls_le (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hcost : HasHashQueryBound scheme adversary budget) :
    (∑' result, Pr[= result |
      initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped] *
        (result.2.1.memory.messageCalls.length : ENNReal)) ≤ budget := by
  let inputs := gameInputs adversary
  let words := referenceFamilyWords encoding.selections dummy
  let publicReplies := coordinateGraphLabels (initialKnown words exposed) high
  let source := FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩
  let initial := initialState inputs words exposed
  let law := initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped
  let native := lazyRun (environment key.parameter inputs
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) words publicReplies
    encoding.selections encoding.rows)
    (simulateQ (adversaryImpl inputs key.parameter key.root words encoding.selections) source) initial
  have herasure : (fun result => (result.1, result.2.1)) <$> law = native := by
    exact monitoredRun_erasure key inputs (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
      words publicReplies encoding.selections encoding.rows budget Finset.univ (proposalStop stopAfter) source
      (initial, initialCertificateMonitor keygenHashCost stopped)
  have hlength (result : Option (Forgery × Bool) × MonitoredState inputs) (hr : law result ≠ 0) :
      result.2.1.memory.messageCalls.length ≤ budget := by
    have hnative := map_nonzero law (fun result => (result.1, result.2.1)) result hr
    rw [herasure] at hnative
    have hresources := lazyRun_source_probeMessageBound inputs words publicReplies encoding.selections
      encoding.rows key (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) source
      (sourceInputs_unlogged_subset_gameInputs adversary key) initial
      (initialAllowed_nonempty words exposed) (initialState_rowsCovered inputs words exposed)
      (by exact Nat.zero_le _) (result.1, result.2.1) hnative
    have hbudget := initialMonitoredSource_hashCalls_le key adversary encoding dummy exposed high budget
      Finset.univ (proposalStop stopAfter) stopped hparameter hencoding hroot hcost result hr
    change result.2.1.memory.external.probes + result.2.1.memory.messageCalls.length ≤
      result.2.1.memory.external.hashCalls at hresources
    omega
  calc
    _ ≤ ∑' result, Pr[= result | law] * (budget : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support law
      · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (hlength result ((mem_support_iff _ _).mp hr)))
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ budget := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

omit parameter inputs hencoding words publicReplies selections rows in
theorem initialMonitoredSource_primitive_add_full_count_le (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 128) :
    Pr[fun result => result.1 = none |
      initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped] +
      (∑' result, Pr[= result |
        initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped] *
          certificateBankCount result.2.2.bank) ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) * fullCertificateTotalRate := by
  let law := initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped
  let messages : ENNReal := ∑' result, Pr[= result | law] * (result.2.1.memory.messageCalls.length : ENNReal)
  have hprimitive := initialMonitoredSource_joint_primitive_messages key adversary encoding dummy exposed high budget Finset.univ
    (proposalStop stopAfter) stopped hparameter hencoding hroot hcost hbudget
  have hcoverage := expected_initialMonitoredSource_full_unit_count_le key adversary encoding dummy exposed high budget
    stopAfter stopped hparameter hencoding hroot hcost hbudget
  have hmessages := initialMonitoredSource_messageCalls_le key adversary encoding dummy exposed high budget
    stopAfter stopped hparameter hencoding hroot hcost
  have hprimary : Pr[fun result => result.1 = none | law] ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) :=
    (le_self_add).trans hprimitive
  have hmessageRate : messages / 2 ^ 144 ≤ (budget : ENNReal) / 2 ^ 144 := by
    simpa only [div_eq_mul_inv] using mul_le_mul' hmessages (le_refl ((2 ^ 144 : ENNReal)⁻¹))
  calc
    _ ≤ Pr[fun result => result.1 = none | law] +
        ((2 ^ 144 : ENNReal)⁻¹ * messages + (budget : ENNReal) * fullCertificateExcessRate) :=
      add_le_add le_rfl hcoverage
    _ = Pr[fun result => result.1 = none | law] +
        (messages / 2 ^ 144 + (budget : ENNReal) * fullCertificateExcessRate) := by
      rw [div_eq_mul_inv, mul_comm (2 ^ 144 : ENNReal)⁻¹ messages]
    _ ≤ ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) / 2 ^ 144 + (budget : ENNReal) * fullCertificateExcessRate := by
      simpa only [add_assoc] using add_le_add hprimary (add_le_add hmessageRate le_rfl)
    _ = _ := by
      simp only [fullCertificateTotalRate_def, div_eq_mul_inv, mul_add, add_assoc]

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyRun_wrap_some {Result : Type} (program : OracleComp (World inputs) Result)
    (state : State inputs) :
    lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (do let x ← program; pure (some x)) state =
    (fun result : Option Result × State inputs => (result.1.map some, result.2)) <$>
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows) program state := by
  rw [lazyRun_bind]
  simp only [lazyRun, runWith_pure]
  rw [map_eq_bind_pure_comp]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨answer, after⟩
  cases answer <;> rfl

noncomputable def stoppedPrimitiveResultPotential {Result : Type} (budget : Nat)
    (result : Option (Option Result) × State inputs) : ENNReal :=
  match result.1 with
  | none => primitiveResultPotential budget ((none : Option Result), result.2)
  | some none => 0
  | some (some value) => primitiveResultPotential budget (some value, result.2)

theorem expected_wrap_some_potential {Result : Type} (program : OracleComp (World inputs) Result)
    (state : State inputs) (budget : Nat) :
    (∑' result, Pr[= result | lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (do let x ← program; pure (some x)) state] * stoppedPrimitiveResultPotential inputs budget result) =
    (∑' result, Pr[= result | lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      program state] * primitiveResultPotential budget result) := by
  rw [lazyRun_wrap_some, tsum_probOutput_map_mul]
  apply tsum_congr
  intro result
  rcases result with ⟨answer, after⟩
  cases answer <;> simp [stoppedPrimitiveResultPotential]

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- One budgeted checked hash pays the same primitive potential as the original
complete hash; a budget stop pays zero. -/
theorem lazyRun_stopped_checkedHash_jointPotential
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily)
    (rows : CanonicalEncodingRows) (routing : InterleavedResidual.Routing)
    (input : inputs) (state : State inputs) (budget remaining : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput
      (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections)
      state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        (simulateQ (embed inputs routing)
          (ResidualByteFrontend.checkedHashQuery
            (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input))
        remaining) state] * stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  rw [WeightedCutoff.residual_run_checkedHashQuery]
  by_cases allowed : 1 ≤ remaining
  · rw [if_pos allowed]
    rw [expected_wrap_some_potential]
    have hquery : state.memory.external.hashCalls + 1 ≤ budget := by omega
    have hlaw : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query (.inr input.val))) state =
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs routing)
          (ResidualByteFrontend.checkedHashQuery
            (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input)) state := by
      simp only [lazyByteRun, simulateQ_spec_query, ResidualByteFrontend.checkedTranslate,
        dif_pos input.property]
    rw [← hlaw]
    exact lazyByteRun_hash_jointPotential parameter inputs hencoding words publicReplies selections rows
      routing input.val input.property state budget hselect ha hcovered hcandidates hclean hresources hquery hbudget
  · rw [if_neg allowed]
    simp only [AdaptiveResidualLabels.lazyRun, AdaptiveResidualLabels.runWith_pure,
      tsum_probOutput_pure_mul]
    simp [stoppedPrimitiveResultPotential, primitiveLivePotential]

end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_wrap_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_wrap_some

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.expected_wrap_some_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.expected_wrap_some_potential

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_checkedHash_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_checkedHash_jointPotential

namespace SphincsSecurity.Concrete.RetainedResidual

theorem primitiveLivePotential_accountWork_le (budget : Nat) (memory : Memory) (cost : Nat)
    (hresources : ProbeMessageBound memory)
    (hcost : memory.external.hashCalls + cost ≤ budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    primitiveLivePotential budget (memory.accountWork cost) ≤ primitiveLivePotential budget memory := by
  rw [← applyBoundary_pow_none]
  apply primitiveLivePotential_applyBoundary_le budget memory _ hresources
  · simpa only [SigningBoundaryTrace.hashCalls_pow_none] using hcost
  · exact hbudget

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem lazyRun_completeWork_jointPotential
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily)
    (rows : CanonicalEncodingRows) (routing : InterleavedResidual.Routing)
    (work : PublicSigningRecord × Nat) (state : State inputs) (budget : Nat)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hresources : ProbeMessageBound state.memory)
    (hcost : state.memory.external.hashCalls + work.2 ≤ budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningWork work))
      state] * primitiveResultPotential budget result) ≤
      primitiveLivePotential budget state.memory := by
  calc
    _ ≤ ∑' result, Pr[= result | lazyRun
        (environment parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningWork work))
        state] * primitiveLivePotential budget state.memory := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | lazyRun
          (environment parameter inputs hencoding words publicReplies selections rows)
          (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningWork work))
          state] = 0
      · simp only [hr, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        obtain ⟨actual, hsome, hmemory⟩ := lazyRun_completeWork_support
          parameter inputs hencoding words publicReplies selections rows routing work state ha result hr
        have hpotential := primitiveLivePotential_accountWork_le budget state.memory work.2 hresources hcost hbudget
        simp only [primitiveResultPotential, hsome, Option.elim_some]
        rw [hmemory]
        change primitiveLivePotential budget (state.memory.accountWork work.2) ≤ _
        exact hpotential
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem lazyRun_stopped_completeWork_jointPotential
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily)
    (rows : CanonicalEncodingRows) (routing : InterleavedResidual.Routing)
    (work : PublicSigningRecord × Nat) (state : State inputs) (budget remaining : Nat)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hresources : ProbeMessageBound state.memory)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        (simulateQ (embed inputs routing)
          (ResidualByteFrontend.jointCompleteSigningWork work)) remaining) state] *
      stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  rw [WeightedCutoff.residual_run_completeSigningWork]
  by_cases allowed : work.2 ≤ remaining
  · rw [if_pos allowed]
    rw [expected_wrap_some_potential]
    have hcost : state.memory.external.hashCalls + work.2 ≤ budget := by omega
    exact lazyRun_completeWork_jointPotential parameter inputs hencoding words publicReplies selections rows
      routing work state budget ha hresources hcost hbudget
  · rw [if_neg allowed]
    simp only [AdaptiveResidualLabels.lazyRun, AdaptiveResidualLabels.runWith_pure,
      tsum_probOutput_pure_mul]
    simp [stoppedPrimitiveResultPotential, primitiveLivePotential]

end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.primitiveLivePotential_accountWork_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.primitiveLivePotential_accountWork_le

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_completeWork_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_completeWork_jointPotential

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_completeWork_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_completeWork_jointPotential

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

/-- A one-step potential payment composes with any continuation that preserves the
potential on every supported successful answer. -/
theorem lazyRun_stoppedPotential_bind_le {First Result : Type}
    (first : OracleComp (World inputs) First)
    (next : First → OracleComp (World inputs) (Option Result))
    (state : State inputs) (budget : Nat)
    (hnext : ∀ middle, Pr[= middle | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows) first state] ≠ 0 →
      ∀ answer, middle.1 = some answer →
      (∑' result, Pr[= result | lazyRun
        (environment parameter inputs hencoding words publicReplies selections rows)
        (next answer) middle.2] * stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget middle.2.memory) :
    (∑' result, Pr[= result | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (first >>= next) state] * stoppedPrimitiveResultPotential inputs budget result) ≤
    (∑' middle, Pr[= middle | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows) first state] *
      primitiveResultPotential budget middle) := by
  rw [lazyRun_bind, tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro middle
  by_cases hm : Pr[= middle | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows) first state] = 0
  · simp only [hm, zero_mul, le_refl]
  · apply mul_le_mul' le_rfl
    rcases middle with ⟨answer, after⟩
    cases answer with
    | none => simp [stoppedPrimitiveResultPotential, primitiveResultPotential]
    | some answer => exact hnext (some answer, after) hm answer rfl

end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stoppedPotential_bind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stoppedPotential_bind_le

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- One checked hash step composes the stopped continuation while preserving the
same global primitive potential. -/
theorem lazyRun_stopped_checkedHash_bind_jointPotential
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily)
    (rows : CanonicalEncodingRows) (routing : InterleavedResidual.Routing)
    (input : inputs) {Result : Type} (next : HashOutput → OracleComp (World inputs) Result)
    (state : State inputs) (budget remaining : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput
      (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections)
      state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits)
    (hnext : 1 ≤ remaining → ∀ middle, Pr[= middle | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.checkedHashQuery
          (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input))
      state] ≠ 0 →
      ∀ answer, middle.1 = some answer →
      (∑' result, Pr[= result | lazyRun
        (environment parameter inputs hencoding words publicReplies selections rows)
        (WeightedCutoff.run (WeightedCutoff.residualCharge inputs) (next answer)
          (remaining - 1)) middle.2] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget middle.2.memory) :
    (∑' result, Pr[= result | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        ((simulateQ (embed inputs routing)
          (ResidualByteFrontend.checkedHashQuery
            (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input)) >>=
          next) remaining) state] * stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  rw [WeightedCutoff.residual_run_checkedHashQuery_bind]
  by_cases allowed : 1 ≤ remaining
  · rw [if_pos allowed]
    apply (lazyRun_stoppedPotential_bind_le parameter inputs hencoding words publicReplies selections rows
      _ _ state budget (hnext allowed)).trans
    have hquery : state.memory.external.hashCalls + 1 ≤ budget := by omega
    have hlaw : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query (.inr input.val))) state =
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs routing)
          (ResidualByteFrontend.checkedHashQuery
            (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input)) state := by
      simp only [lazyByteRun, simulateQ_spec_query, ResidualByteFrontend.checkedTranslate,
        dif_pos input.property]
    rw [← hlaw]
    exact lazyByteRun_hash_jointPotential parameter inputs hencoding words publicReplies selections rows
      routing input.val input.property state budget hselect ha hcovered hcandidates hclean hresources hquery hbudget
  · rw [if_neg allowed]
    simp only [AdaptiveResidualLabels.lazyRun, AdaptiveResidualLabels.runWith_pure,
      tsum_probOutput_pure_mul]
    simp [stoppedPrimitiveResultPotential, primitiveLivePotential]
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_checkedHash_bind_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_checkedHash_bind_jointPotential

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- The account/disclosure step composes the stopped continuation while preserving
the same global primitive potential. -/
theorem lazyRun_stopped_completeWork_bind_jointPotential
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily)
    (rows : CanonicalEncodingRows) (routing : InterleavedResidual.Routing)
    (work : PublicSigningRecord × Nat)
    {Result : Type}
    (next : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) →
      OracleComp (World inputs) Result)
    (state : State inputs) (budget remaining : Nat)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hresources : ProbeMessageBound state.memory)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits)
    (hnext : work.2 ≤ remaining → ∀ middle, Pr[= middle | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.jointCompleteSigningWork work)) state] ≠ 0 →
      ∀ answer, middle.1 = some answer →
      (∑' result, Pr[= result | lazyRun
        (environment parameter inputs hencoding words publicReplies selections rows)
        (WeightedCutoff.run (WeightedCutoff.residualCharge inputs) (next answer)
          (remaining - work.2)) middle.2] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget middle.2.memory) :
    (∑' result, Pr[= result | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        ((simulateQ (embed inputs routing)
          (ResidualByteFrontend.jointCompleteSigningWork work)) >>= next) remaining) state] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  rw [WeightedCutoff.residual_run_completeSigningWork_bind]
  by_cases allowed : work.2 ≤ remaining
  · rw [if_pos allowed]
    apply (lazyRun_stoppedPotential_bind_le parameter inputs hencoding words publicReplies selections rows
      _ _ state budget (hnext allowed)).trans
    have hcost : state.memory.external.hashCalls + work.2 ≤ budget := by omega
    exact lazyRun_completeWork_jointPotential parameter inputs hencoding words publicReplies selections rows
      routing work state budget ha hresources hcost hbudget
  · rw [if_neg allowed]
    simp only [AdaptiveResidualLabels.lazyRun, AdaptiveResidualLabels.runWith_pure,
      tsum_probOutput_pure_mul]
    simp [stoppedPrimitiveResultPotential, primitiveLivePotential]
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_completeWork_bind_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_completeWork_bind_jointPotential

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- A zero-cost prefix may be followed by any globally stopped continuation
without spending the remaining hash-call budget. -/
theorem lazyRun_stopped_zeroCost_bind_jointPotential
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily)
    (rows : CanonicalEncodingRows)
    {First Result : Type}
    (first : OracleComp (World inputs) First)
    (next : First → OracleComp (World inputs) Result)
    (state : State inputs) (budget remaining : Nat)
    (hzero : AllQueriesSatisfy first
      (fun query => WeightedCutoff.residualCharge inputs query = 0))
    (hfirst : (∑' middle, Pr[= middle | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      first state] * primitiveResultPotential budget middle) ≤
      primitiveLivePotential budget state.memory)
    (hnext : ∀ middle, Pr[= middle | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      first state] ≠ 0 →
      ∀ answer, middle.1 = some answer →
      (∑' result, Pr[= result | lazyRun
        (environment parameter inputs hencoding words publicReplies selections rows)
        (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
          (next answer) remaining) middle.2] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget middle.2.memory) :
    (∑' result, Pr[= result | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        (first >>= next) remaining) state] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  rw [WeightedCutoff.run_bind_zero_prefix _ _ _ _ hzero]
  exact (lazyRun_stoppedPotential_bind_le parameter inputs hencoding words publicReplies selections rows
    first _ state budget hnext).trans hfirst
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_zeroCost_bind_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_zeroCost_bind_jointPotential

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- A random-world query is a zero-cost step in the stopped residual game. -/
theorem lazyRun_stopped_random_bind_jointPotential
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily)
    (rows : CanonicalEncodingRows) (routing : InterleavedResidual.Routing)
    (input : unifSpec.Domain) {Result : Type}
    (next : unifSpec.Range input → OracleComp (World inputs) Result)
    (state : State inputs) (budget remaining : Nat)
    (hinputs : hashInputs (liftM (OracleWorld.query (.inl input))) ⊆ inputs)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput
      (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections)
      state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits)
    (hnext : ∀ middle, Pr[= middle | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (simulateQ (ResidualByteFrontend.checkedTranslate inputs
          (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections))
          (liftM (OracleWorld.query (.inl input))))) state] ≠ 0 →
      ∀ answer, middle.1 = some answer →
      (∑' result, Pr[= result | lazyRun
        (environment parameter inputs hencoding words publicReplies selections rows)
        (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
          (next answer) remaining) middle.2] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget middle.2.memory) :
    (∑' result, Pr[= result | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        ((simulateQ (embed inputs routing)
          (simulateQ (ResidualByteFrontend.checkedTranslate inputs
            (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections))
            (liftM (OracleWorld.query (.inl input))))) >>= next) remaining) state] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  apply lazyRun_stopped_zeroCost_bind_jointPotential parameter inputs hencoding words
    publicReplies selections rows _ _ state budget remaining ?_ ?_ hnext
  · simp only [simulateQ_spec_query, ResidualByteFrontend.checkedTranslate,
      embed, allQueriesSatisfy_query_iff, WeightedCutoff.residualCharge]
  · change (∑' middle, Pr[= middle | lazyByteRun parameter inputs hencoding words
        publicReplies selections rows routing (liftM (OracleWorld.query (.inl input))) state] *
        primitiveResultPotential budget middle) ≤ primitiveLivePotential budget state.memory
    apply lazyByteRun_world_jointPotential parameter inputs hencoding words publicReplies
      selections rows routing (.inl input) hinputs state budget hselect ha hcovered hcandidates
      hclean hresources
    · simpa using (show state.memory.external.hashCalls ≤ budget by omega)
    · exact hbudget
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_random_bind_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_random_bind_jointPotential

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- A supported checked hash answer has spent exactly one global call. -/
theorem lazyByteRun_hash_remaining_invariant
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily)
    (rows : CanonicalEncodingRows) (routing : InterleavedResidual.Routing)
    (input : HashInput) (hin : input ∈ inputs)
    (state : State inputs) (budget remaining : Nat)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hallowed : 1 ≤ remaining)
    (result : Option HashOutput × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows
      routing (liftM (OracleWorld.query (.inr input))) state result ≠ 0) :
    result.2.memory.external.hashCalls + (remaining - 1) = budget := by
  rw [lazyByteRun_hash_hashCalls parameter inputs hencoding words publicReplies
    selections rows routing input hin state ha result hresult]
  omega
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyByteRun_hash_remaining_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyByteRun_hash_remaining_invariant

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- A supported random-world answer spends no global hash calls. -/
theorem lazyByteRun_random_remaining_invariant
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily)
    (rows : CanonicalEncodingRows) (routing : InterleavedResidual.Routing)
    (input : unifSpec.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query (.inl input))) ⊆ inputs)
    (state : State inputs) (budget remaining : Nat)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (result : Option (unifSpec.Range input) × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows
      routing (liftM (OracleWorld.query (.inl input))) state result ≠ 0) :
    result.2.memory.external.hashCalls + remaining = budget := by
  have hh := lazyByteRun_world_hashCalls parameter inputs hencoding words publicReplies
    selections rows routing (.inl input) hinputs state ha result hresult
  simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero] at hh
  rw [hh]
  exact hremaining
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyByteRun_random_remaining_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyByteRun_random_remaining_invariant

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

theorem lazyByteRun_stopped_publicWorld_jointPotential
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily)
    (rows : CanonicalEncodingRows) (routing : InterleavedResidual.Routing)
    {Result : Type} (computation : OracleComp OracleWorld Result)
    (hinputs : hashInputs computation ⊆ inputs)
    (state : State inputs) (budget remaining : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput
      (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections)
      state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        (simulateQ (embed inputs routing)
          (simulateQ (ResidualByteFrontend.checkedTranslate inputs
            (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections))
            computation)) remaining) state] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  induction computation using OracleComp.inductionOn generalizing state remaining with
  | pure value =>
      simp only [simulateQ_pure, WeightedCutoff.run_pure, lazyRun, runWith_pure,
        tsum_probOutput_pure_mul, stoppedPrimitiveResultPotential, primitiveResultPotential,
        Option.elim_some, primitiveLivePotential, le_refl]
  | query_bind input next ih =>
      have hnextInputs : ∀ answer, hashInputs (next answer) ⊆ inputs :=
        fun answer => (hashInputs_next_subset input next answer).trans hinputs
      cases input with
      | inl query =>
          have hfirstInputs : hashInputs (liftM (OracleWorld.query (.inl query))) ⊆ inputs := by
            rw [← bind_pure (liftM (OracleWorld.query (.inl query))), hashInputs_query_bind]
            simp [hashInputs_pure]
          convert (lazyRun_stopped_random_bind_jointPotential parameter inputs hencoding words publicReplies
              selections rows routing query
              (next := fun answer => simulateQ (embed inputs routing)
                (simulateQ (ResidualByteFrontend.checkedTranslate inputs
                  (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections))
                  (next answer))) state budget remaining hfirstInputs hselect ha hcovered hcandidates
              hclean hresources hremaining hbudget (by
                intro middle hmiddle answer hans
                change Pr[= middle | lazyByteRun parameter inputs hencoding words publicReplies
                  selections rows routing (liftM (OracleWorld.query (.inl query))) state] ≠ 0 at hmiddle
                have ha' := lazyRun_nonempty
                  (environment parameter inputs hencoding words publicReplies selections rows) _
                  state ha middle hmiddle
                have hc' := lazyRun_rowsCovered parameter inputs hencoding words publicReplies
                  selections rows _ state ha hcovered middle hmiddle
                have hb' := lazyByteRun_hiddenCandidateBound parameter inputs hencoding words
                  publicReplies selections rows routing _ hfirstInputs state ha hcandidates middle hmiddle
                have he' := lazyByteRun_encodingClean parameter inputs hencoding words
                  publicReplies selections rows routing _ hfirstInputs state ha hcovered hclean
                  middle hmiddle (by simp [hans])
                have hr' := lazyByteRun_world_probeMessageBound parameter inputs hencoding words
                  publicReplies selections rows routing (.inl query) hfirstInputs state ha hresources
                  middle hmiddle
                have hm' := lazyByteRun_random_remaining_invariant parameter inputs hencoding words
                  publicReplies selections rows routing query hfirstInputs state budget remaining ha
                  hremaining middle hmiddle
                exact ih answer (hnextInputs answer) middle.2 remaining ha' hc' hb' he' hr' hm')) using 1
          all_goals rfl
      | inr query =>
          have hin : query ∈ inputs := hinputs (mem_hashInputs_hash_bind query next)
          have hfirstInputs : hashInputs (liftM (OracleWorld.query (.inr query))) ⊆ inputs := by
            rw [← bind_pure (liftM (OracleWorld.query (.inr query))), hashInputs_query_bind]
            apply Finset.union_subset
            · exact Finset.singleton_subset_iff.mpr hin
            · apply Finset.biUnion_subset.mpr
              intro answer _
              simpa only [hashInputs_pure] using (Finset.empty_subset inputs)
          simp only [simulateQ_bind, simulateQ_spec_query,
            ResidualByteFrontend.checkedTranslate, dif_pos hin]
          apply (lazyRun_stopped_checkedHash_bind_jointPotential parameter inputs hencoding words
            publicReplies selections rows routing ⟨query, hin⟩
            (next := fun answer => simulateQ (embed inputs routing)
              (simulateQ (ResidualByteFrontend.checkedTranslate inputs
                (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections))
                (next answer))) state budget remaining hselect ha hcovered hcandidates hclean
            hresources hremaining hbudget (by
              intro allowed middle hmiddle answer hans
              have hmiddle' : Pr[= middle | lazyByteRun parameter inputs hencoding words
                  publicReplies selections rows routing
                  (liftM (OracleWorld.query (.inr query))) state] ≠ 0 := by
                simpa only [lazyByteRun, simulateQ_spec_query,
                  ResidualByteFrontend.checkedTranslate, dif_pos hin] using hmiddle
              have ha' := lazyRun_nonempty
                (environment parameter inputs hencoding words publicReplies selections rows) _
                state ha middle hmiddle'
              have hc' := lazyRun_rowsCovered parameter inputs hencoding words publicReplies
                selections rows _ state ha hcovered middle hmiddle'
              have hb' := lazyByteRun_hiddenCandidateBound parameter inputs hencoding words
                publicReplies selections rows routing _ hfirstInputs state ha hcandidates
                middle hmiddle'
              have he' := lazyByteRun_encodingClean parameter inputs hencoding words
                publicReplies selections rows routing _ hfirstInputs state ha hcovered hclean
                middle hmiddle' (by simp [hans])
              have hr' := lazyByteRun_world_probeMessageBound parameter inputs hencoding words
                publicReplies selections rows routing (.inr query) hfirstInputs state ha hresources
                middle hmiddle'
              have hm' := lazyByteRun_hash_remaining_invariant parameter inputs hencoding words
                publicReplies selections rows routing query hin state budget remaining ha
                hremaining allowed middle hmiddle'
              exact ih answer (hnextInputs answer) middle.2 (remaining - 1)
                ha' hc' hb' he' hr' hm'))
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyByteRun_stopped_publicWorld_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyByteRun_stopped_publicWorld_jointPotential

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem lazyByteRun_stopped_publicSigningWork_jointPotential
    (key : SecretKey) (known : Labels) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (message : Message)
    (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs)
    (publicReplies : CanonicalGraphLabels) (rows : CanonicalEncodingRows)
    (routing : InterleavedResidual.Routing)
    (state : State inputs) (budget remaining : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput
      (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage routing.known) words selections)
      state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyRun
      (environment key.parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        (simulateQ (embed inputs routing)
          (simulateQ (ResidualByteFrontend.checkedTranslate inputs
            (PublicEncodingMatch.Match key.parameter (knownEncodingMessage routing.known) words selections))
            (ResidualByteFrontend.publicSigningWork key.parameter key.root known words selections message)))
        remaining) state] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  exact lazyByteRun_stopped_publicWorld_jointPotential key.parameter inputs hencoding words
    publicReplies selections rows routing
    (ResidualByteFrontend.publicSigningWork key.parameter key.root known words selections message)
    ((ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key known words selections message).trans hinputs)
    state budget remaining hselect ha hcovered hcandidates hclean hresources hremaining hbudget
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyByteRun_stopped_publicSigningWork_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyByteRun_stopped_publicSigningWork_jointPotential

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

theorem lazyByteRun_stopped_publicWorld_bind_jointPotential
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily)
    (rows : CanonicalEncodingRows) (routing : InterleavedResidual.Routing)
    {Result Result₂ : Type} (computation : OracleComp OracleWorld Result)
    (hinputs : hashInputs computation ⊆ inputs)
    (tail : Result → OracleComp (World inputs) Result₂)
    (state : State inputs) (budget remaining : Nat)
    (hleaf : ∀ value (leafState : State inputs) (leafRemaining : Nat),
      (∀ coordinate, (leafState.candidates coordinate).Nonempty) →
      ProbeMessageBound leafState.memory →
      leafState.memory.external.hashCalls + leafRemaining = budget →
      (∑' result, Pr[= result | lazyRun
        (environment parameter inputs hencoding words publicReplies selections rows)
        (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
          (tail value) leafRemaining) leafState] *
          stoppedPrimitiveResultPotential inputs budget result) ≤
        primitiveLivePotential budget leafState.memory)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput
      (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections)
      state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        ((simulateQ (embed inputs routing)
          (simulateQ (ResidualByteFrontend.checkedTranslate inputs
            (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections))
            computation)) >>= tail) remaining) state] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  induction computation using OracleComp.inductionOn generalizing state remaining with
  | pure value =>
      simpa only [simulateQ_pure, pure_bind] using
        hleaf value state remaining ha hresources hremaining
  | query_bind input next ih =>
      have hnextInputs : ∀ answer, hashInputs (next answer) ⊆ inputs :=
        fun answer => (hashInputs_next_subset input next answer).trans hinputs
      cases input with
      | inl query =>
          have hfirstInputs : hashInputs (liftM (OracleWorld.query (.inl query))) ⊆ inputs := by
            rw [← bind_pure (liftM (OracleWorld.query (.inl query))), hashInputs_query_bind]
            simp [hashInputs_pure]
          convert (lazyRun_stopped_random_bind_jointPotential parameter inputs hencoding words publicReplies
              selections rows routing query
              (next := fun answer => simulateQ (embed inputs routing)
                (simulateQ (ResidualByteFrontend.checkedTranslate inputs
                  (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections))
                  (next answer)) >>= tail) state budget remaining hfirstInputs hselect ha hcovered hcandidates
              hclean hresources hremaining hbudget (by
                intro middle hmiddle answer hans
                change Pr[= middle | lazyByteRun parameter inputs hencoding words publicReplies
                  selections rows routing (liftM (OracleWorld.query (.inl query))) state] ≠ 0 at hmiddle
                have ha' := lazyRun_nonempty
                  (environment parameter inputs hencoding words publicReplies selections rows) _
                  state ha middle hmiddle
                have hc' := lazyRun_rowsCovered parameter inputs hencoding words publicReplies
                  selections rows _ state ha hcovered middle hmiddle
                have hb' := lazyByteRun_hiddenCandidateBound parameter inputs hencoding words
                  publicReplies selections rows routing _ hfirstInputs state ha hcandidates middle hmiddle
                have he' := lazyByteRun_encodingClean parameter inputs hencoding words
                  publicReplies selections rows routing _ hfirstInputs state ha hcovered hclean
                  middle hmiddle (by simp [hans])
                have hr' := lazyByteRun_world_probeMessageBound parameter inputs hencoding words
                  publicReplies selections rows routing (.inl query) hfirstInputs state ha hresources
                  middle hmiddle
                have hm' := lazyByteRun_random_remaining_invariant parameter inputs hencoding words
                  publicReplies selections rows routing query hfirstInputs state budget remaining ha
                  hremaining middle hmiddle
                exact ih answer (hnextInputs answer) middle.2 remaining ha' hc' hb' he' hr' hm')) using 1
          all_goals rfl
      | inr query =>
          have hin : query ∈ inputs := hinputs (mem_hashInputs_hash_bind query next)
          have hfirstInputs : hashInputs (liftM (OracleWorld.query (.inr query))) ⊆ inputs := by
            rw [← bind_pure (liftM (OracleWorld.query (.inr query))), hashInputs_query_bind]
            apply Finset.union_subset
            · exact Finset.singleton_subset_iff.mpr hin
            · apply Finset.biUnion_subset.mpr
              intro answer _
              simpa only [hashInputs_pure] using (Finset.empty_subset inputs)
          simp only [simulateQ_bind, simulateQ_spec_query,
            ResidualByteFrontend.checkedTranslate, dif_pos hin, bind_assoc]
          apply (lazyRun_stopped_checkedHash_bind_jointPotential parameter inputs hencoding words
            publicReplies selections rows routing ⟨query, hin⟩
            (next := fun answer => simulateQ (embed inputs routing)
              (simulateQ (ResidualByteFrontend.checkedTranslate inputs
                (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections))
                (next answer)) >>= tail) state budget remaining hselect ha hcovered hcandidates hclean
            hresources hremaining hbudget (by
              intro allowed middle hmiddle answer hans
              have hmiddle' : Pr[= middle | lazyByteRun parameter inputs hencoding words
                  publicReplies selections rows routing
                  (liftM (OracleWorld.query (.inr query))) state] ≠ 0 := by
                simpa only [lazyByteRun, simulateQ_spec_query,
                  ResidualByteFrontend.checkedTranslate, dif_pos hin] using hmiddle
              have ha' := lazyRun_nonempty
                (environment parameter inputs hencoding words publicReplies selections rows) _
                state ha middle hmiddle'
              have hc' := lazyRun_rowsCovered parameter inputs hencoding words publicReplies
                selections rows _ state ha hcovered middle hmiddle'
              have hb' := lazyByteRun_hiddenCandidateBound parameter inputs hencoding words
                publicReplies selections rows routing _ hfirstInputs state ha hcandidates
                middle hmiddle'
              have he' := lazyByteRun_encodingClean parameter inputs hencoding words
                publicReplies selections rows routing _ hfirstInputs state ha hcovered hclean
                middle hmiddle' (by simp [hans])
              have hr' := lazyByteRun_world_probeMessageBound parameter inputs hencoding words
                publicReplies selections rows routing (.inr query) hfirstInputs state ha hresources
                middle hmiddle'
              have hm' := lazyByteRun_hash_remaining_invariant parameter inputs hencoding words
                publicReplies selections rows routing query hin state budget remaining ha
                hremaining allowed middle hmiddle'
              exact ih answer (hnextInputs answer) middle.2 (remaining - 1)
                ha' hc' hb' he' hr' hm'))
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyByteRun_stopped_publicWorld_bind_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyByteRun_stopped_publicWorld_bind_jointPotential

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

theorem lazyByteRun_stopped_jointSigningProgram_jointPotential
    (key : SecretKey) (known : Labels) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (message : Message)
    (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs)
    (publicReplies : CanonicalGraphLabels) (rows : CanonicalEncodingRows)
    (routing : InterleavedResidual.Routing)
    (hknown : routing.known = known)
    (state : State inputs) (budget remaining : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput
      (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage routing.known) words selections)
      state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyRun
      (environment key.parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        (simulateQ (embed inputs routing)
          (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root known words selections message))
        remaining) state] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  subst known
  simpa only [ResidualByteFrontend.jointSigningProgram, simulateQ_bind] using
    (lazyByteRun_stopped_publicWorld_bind_jointPotential key.parameter inputs hencoding words
      publicReplies selections rows routing
      (ResidualByteFrontend.publicSigningWork key.parameter key.root routing.known words selections message)
      ((ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key routing.known words selections message).trans hinputs)
      (fun work => simulateQ (embed inputs routing)
        (ResidualByteFrontend.jointCompleteSigningWork work)) state budget remaining
      (by
        intro work leafState leafRemaining hleafNonempty hleafResources hleafRemaining
        exact lazyRun_stopped_completeWork_jointPotential key.parameter inputs hencoding words
          publicReplies selections rows routing work leafState budget leafRemaining hleafNonempty
          hleafResources hleafRemaining hbudget)
      hselect ha hcovered hcandidates hclean hresources hremaining hbudget)
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyByteRun_stopped_jointSigningProgram_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyByteRun_stopped_jointSigningProgram_jointPotential

namespace SphincsSecurity.WeightedCutoff
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Index : Type} {spec : OracleSpec Index}

theorem run_bind_zero_suffix {First Result : Type} (charge : spec.Domain → Nat)
    (program : OracleComp spec First) (tail : First → OracleComp spec Result)
    (budget : Nat)
    (hzero : ∀ value, AllQueriesSatisfy (tail value) (fun query => charge query = 0)) :
    run charge (program >>= tail) budget =
      (do
        let value ← run charge program budget
        match value with
        | none => pure none
        | some value => do let result ← tail value; pure (some result)) := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value =>
      simpa only [pure_bind, run_pure, pure_bind] using run_all_zero charge (tail value) budget (hzero value)
  | query_bind query next ih =>
      rw [bind_assoc, run_query_bind, run_query_bind]
      split_ifs <;> simp only [bind_assoc, pure_bind]
      congr 1
      funext answer
      exact ih answer (budget - charge query)
end SphincsSecurity.WeightedCutoff

/-- info: 'SphincsSecurity.WeightedCutoff.run_bind_zero_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.run_bind_zero_suffix

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable

theorem recordSigning_tail_all_zero (inputs : Finset HashInput) (message : Message)
    (result : InterleavedResidual.SigningRecord) :
    AllQueriesSatisfy
      (recordSigning inputs message result >>= fun _ => pure result.1.1)
      (fun query => WeightedCutoff.residualCharge inputs query = 0) := by
  unfold recordSigning
  apply allQueriesSatisfy_bind
  · exact (allQueriesSatisfy_query_iff _ _).2 rfl
  · intro _
    exact allQueriesSatisfy_pure _ _
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.recordSigning_tail_all_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.recordSigning_tail_all_zero

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable

theorem currentRouting_all_zero (inputs : Finset HashInput) :
    AllQueriesSatisfy (currentRouting inputs)
      (fun query => WeightedCutoff.residualCharge inputs query = 0) := by
  simp only [currentRouting, allQueriesSatisfy_query_iff, WeightedCutoff.residualCharge]
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.currentRouting_all_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.currentRouting_all_zero

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem lazyRun_stopped_signingProgram (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (message : Message) (state : State inputs) (remaining : Nat) :
    lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        (signingProgram inputs key.parameter key.root words selections message) remaining) state =
    (fun result : Option (Option InterleavedResidual.SigningRecord) × State inputs =>
      match result.1 with
      | none => (none, result.2)
      | some none => (some none, result.2)
      | some (some record) =>
          (some (some record.1.1),
            { result.2 with memory := result.2.memory.recordSigning message record })) <$>
      lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
          (simulateQ (embed inputs state.memory.routing)
            (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message))
          remaining) state := by
  rw [signingProgram]
  rw [WeightedCutoff.run_bind_zero_prefix (WeightedCutoff.residualCharge inputs)
    (currentRouting inputs) _ remaining (currentRouting_all_zero inputs)]
  rw [lazyRun_routing_bind]
  rw [WeightedCutoff.run_bind_zero_suffix (WeightedCutoff.residualCharge inputs)
    (simulateQ (embed inputs state.memory.routing)
      (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message))
    (fun result => recordSigning inputs message result >>= fun _ => pure result.1.1)
    remaining (recordSigning_tail_all_zero inputs message)]
  rw [lazyRun_bind, map_eq_bind_pure_comp]
  apply RetainedObservation.bind_congr
  rintro ⟨answer, after⟩ _
  cases answer with
  | none => rfl
  | some value =>
      cases value with
      | none => rfl
      | some record =>
          simp only [Option.elim_some, bind_assoc, pure_bind]
          rw [lazyRun_record_bind]
          exact runWith_pure _ _ _
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_signingProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_signingProgram

namespace SphincsSecurity.Concrete.RetainedResidual
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable

theorem stoppedPrimitiveResultPotential_signingMap (inputs : Finset HashInput)
    (message : Message) (budget : Nat)
    (raw : Option (Option InterleavedResidual.SigningRecord) × State inputs) :
    stoppedPrimitiveResultPotential inputs budget
      (match raw.1 with
      | none => (none, raw.2)
      | some none => (some none, raw.2)
      | some (some record) =>
          (some (some record.1.1),
            { raw.2 with memory := raw.2.memory.recordSigning message record })) =
      stoppedPrimitiveResultPotential inputs budget raw := by
  rcases raw with ⟨answer, after⟩
  cases answer with
  | none => rfl
  | some value =>
      cases value with
      | none => rfl
      | some record => rfl
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.stoppedPrimitiveResultPotential_signingMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.stoppedPrimitiveResultPotential_signingMap

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

theorem lazyRun_stopped_signingProgram_jointPotential
    (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (message : Message) (hinputs : hashInputs (signWithView key message) ⊆ inputs)
    (state : State inputs) (budget remaining : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput
      (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.memory.routing.known) words selections)
      state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyRun
      (environment key.parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        (signingProgram inputs key.parameter key.root words selections message) remaining) state] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  rw [lazyRun_stopped_signingProgram key inputs hencoding words publicReplies selections rows message state remaining,
    tsum_probOutput_map_mul]
  simp_rw [stoppedPrimitiveResultPotential_signingMap inputs message budget]
  exact lazyByteRun_stopped_jointSigningProgram_jointPotential key state.memory.routing.known words
    selections message inputs hencoding hinputs publicReplies rows state.memory.routing rfl
    state budget remaining hselect ha hcovered hcandidates hclean hresources hremaining hbudget
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_signingProgram_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_signingProgram_jointPotential

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

theorem lazyRun_stopped_externalProgram {Result : Type}
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (computation : OracleComp OracleWorld Result) (state : State inputs) (remaining : Nat) :
    lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        (externalProgram inputs parameter words selections computation) remaining) state =
    lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        (simulateQ (embed inputs state.memory.routing)
          (simulateQ (ResidualByteFrontend.checkedTranslate inputs
            (PublicEncodingMatch.Match parameter (knownEncodingMessage state.memory.routing.known) words selections))
            computation)) remaining) state := by
  rw [externalProgram]
  rw [WeightedCutoff.run_bind_zero_prefix (WeightedCutoff.residualCharge inputs)
    (currentRouting inputs) _ remaining (currentRouting_all_zero inputs)]
  exact lazyRun_routing_bind parameter inputs hencoding words publicReplies selections rows _ state

end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_externalProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_externalProgram

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

theorem lazyRun_stopped_request_jointPotential
    (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs)
    (state : State inputs) (budget remaining : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput
      (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.memory.routing.known) words selections)
      state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyRun
      (environment key.parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        (adversaryImpl inputs key.parameter key.root words selections input) remaining) state] *
        stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  cases input with
  | inl input =>
      change hashInputs (liftM (OracleWorld.query input)) ⊆ inputs at hinputs
      rw [show adversaryImpl inputs key.parameter key.root words selections (.inl input) =
        externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input)) from rfl,
        lazyRun_stopped_externalProgram]
      exact lazyByteRun_stopped_publicWorld_jointPotential key.parameter inputs hencoding words
        publicReplies selections rows state.memory.routing (liftM (OracleWorld.query input))
        hinputs state budget remaining hselect ha hcovered hcandidates hclean hresources hremaining hbudget
  | inr message =>
      change hashInputs (signWithView key message) ⊆ inputs at hinputs
      exact lazyRun_stopped_signingProgram_jointPotential key inputs hencoding words
        publicReplies selections rows message hinputs state budget remaining hselect ha
        hcovered hcandidates hclean hresources hremaining hbudget
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_request_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_request_jointPotential

namespace SphincsSecurity.WeightedCutoff
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
variable {Index : Type} {spec : OracleSpec Index}

theorem run_bind_counted {First Result : Type} (charge : spec.Domain → Nat)
    (first : OracleComp spec First) (next : First → OracleComp spec Result)
    (budget : Nat) :
    run charge (first >>= next) budget = (do
      let paid ← counted charge (run charge first budget)
      match paid.1 with
      | none => pure none
      | some answer => run charge (next answer) (budget - paid.2)) := by
  induction first using OracleComp.inductionOn generalizing budget with
  | pure value => simp only [pure_bind, run_pure, counted_pure, pure_bind, Nat.sub_zero]
  | query_bind query rest ih =>
      rw [bind_assoc, run_query_bind, run_query_bind]
      by_cases hallowed : charge query ≤ budget
      · rw [if_pos hallowed, if_pos hallowed]
        rw [counted_query_bind]
        simp only [bind_assoc, pure_bind]
        congr 1
        funext answer
        rw [ih answer (budget - charge query)]
        congr 1
        funext paid
        rcases paid with ⟨option, cost⟩
        cases option with
        | none => rfl
        | some value =>
            dsimp
            congr 1
            omega
      · rw [if_neg hallowed, if_neg hallowed]
        simp only [counted_pure, pure_bind]
end SphincsSecurity.WeightedCutoff

/-- info: 'SphincsSecurity.WeightedCutoff.run_bind_counted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.run_bind_counted

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

theorem lazyRun_counted_hashCalls_of_step {Result : Type}
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (program : OracleComp (World inputs) Result)
    (hstep : ∀ (query : (World inputs).Domain) (before : State inputs)
      (answer : (World inputs).Range query) (after : State inputs),
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (liftM ((World inputs).query query)) before (some answer, after) ≠ 0 →
      after.memory.external.hashCalls = before.memory.external.hashCalls +
        WeightedCutoff.residualCharge inputs query)
    (state : State inputs) (value : Result) (cost : Nat) (after : State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.counted (WeightedCutoff.residualCharge inputs) program) state
      (some (value, cost), after) ≠ 0) :
    after.memory.external.hashCalls = state.memory.external.hashCalls + cost := by
  induction program using OracleComp.inductionOn generalizing state value cost after with
  | pure value =>
      simp only [WeightedCutoff.counted_pure, lazyRun, runWith_pure,
        ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      cases hresult
      simp
  | query_bind query next ih =>
      rw [WeightedCutoff.counted_query_bind, lazyRun_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨middle, hmiddle, htail⟩ := hresult
      rcases middle with ⟨option, middleState⟩
      cases option with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at htail
          cases htail
      | some answer =>
          simp only [Option.elim_some] at htail
          rw [lazyRun_bind, RetainedObservation.bind_nonzero] at htail
          obtain ⟨countedResult, hcounted, hpure⟩ := htail
          rcases countedResult with ⟨optionResult, tailState⟩
          cases optionResult with
          | none =>
              simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hpure
              cases hpure
          | some pair =>
              rcases pair with ⟨tailValue, tailCost⟩
              have hfirst := hstep query state answer middleState hmiddle
              have hrest := ih answer middleState tailValue tailCost tailState hcounted
              simp only [Option.elim_some, lazyRun, runWith_pure, ne_eq,
                SPMF.pure_apply_eq_zero_iff, not_not] at hpure
              cases hpure
              omega
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_counted_hashCalls_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_counted_hashCalls_of_step

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem lazyRun_worldStep_hashCalls
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (query : (World inputs).Domain) (state : State inputs)
    (answer : (World inputs).Range query) (after : State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (liftM ((World inputs).query query)) state (some answer, after) ≠ 0) :
    after.memory.external.hashCalls = state.memory.external.hashCalls +
      WeightedCutoff.residualCharge inputs query := by
  cases query with
  | inl control =>
      cases control with
      | byte routing input =>
          cases input with
          | prepare input =>
              simp only [lazyRun, runWith, simulateQ_spec_query, lazyImpl, environment,
                ResidualByteFrontend.environment, OptionT.run_mk, StateT.run_mk] at hresult
              simp_all [WeightedCutoff.residualCharge, PMF.pure_map, SPMF.lift_pure,
                afterControl_external, project]
              exact ResidualByteFrontend.prepare_hashCalls parameter inputs words
                routing.disclosed routing.known
                (ResidualByteAction.freshPrefix parameter inputs hencoding words routing.disclosed
                  routing.known publicReplies selections rows) input state.memory.external
          | random input =>
              simp only [lazyRun, runWith, simulateQ_spec_query, lazyImpl, environment,
                ResidualByteFrontend.environment, OptionT.run_mk, StateT.run_mk,
                ← PMF.monad_map_eq_map, liftM_map, bind_map_left] at hresult
              obtain ⟨sample, _, hpure⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
              simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hpure
              cases hpure
              rfl
          | account cost =>
              simp only [lazyRun, runWith, simulateQ_spec_query, lazyImpl, environment,
                ResidualByteFrontend.environment, OptionT.run_mk, StateT.run_mk,
                ne_eq] at hresult
              simp_all [afterControl, WeightedCutoff.residualCharge, project,
                PMF.pure_map, SPMF.lift_pure]
          | stop =>
              simp_all [lazyRun, runWith, lazyImpl, environment,
                ResidualByteFrontend.environment, PMF.pure_map, SPMF.lift_pure]
      | routing =>
          simp only [lazyRun, runWith, simulateQ_spec_query, lazyImpl, environment,
            OptionT.run_mk, StateT.run_mk, SPMF.lift_pure, pure_bind,
            ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          cases hresult
          rfl
      | transcript =>
          simp_all [lazyRun, runWith, lazyImpl, environment, WeightedCutoff.residualCharge]
      | record message result =>
          simp_all [lazyRun, runWith, lazyImpl, environment, WeightedCutoff.residualCharge]
          rcases hresult with ⟨_, rfl⟩
          rfl
  | inr action =>
      cases action with
      | read input =>
          simp only [lazyRun, runWith, simulateQ_spec_query, lazyImpl,
            OptionT.run_mk, StateT.run_mk] at hresult
          obtain ⟨sample, _, hpure⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hpure
          cases hpure
          simp [readState, environment, WeightedCutoff.residualCharge,
            observeMessage_external, CanonicalProbeRouting.storeReply]
      | probe input test =>
          simp only [lazyRun, runWith, simulateQ_spec_query, lazyImpl,
            OptionT.run_mk, StateT.run_mk] at hresult
          cases hrow : state.rows input with
          | some known =>
              simp only [hrow, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
              cases hresult
              simp [readState, environment, WeightedCutoff.residualCharge,
                observeMessage_external, CanonicalProbeRouting.storeReply]
          | none =>
              simp only [hrow] at hresult
              rw [RetainedObservation.observe_nonzero] at hresult
              rcases hresult with ⟨_, hstop⟩ | ⟨sample, _, hpure⟩
              · simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hstop
                cases hstop
              · simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hpure
                cases hpure
                simp [probeState, environment, WeightedCutoff.residualCharge,
                  observeMessage_external, CanonicalProbeRouting.storeReply]
      | disclose coordinate =>
          simp only [lazyRun, runWith, simulateQ_spec_query, lazyImpl,
            OptionT.run_mk, StateT.run_mk] at hresult
          obtain ⟨sample, _, hpure⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hpure
          cases hpure
          simp [disclosedState, environment, WeightedCutoff.residualCharge]
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_worldStep_hashCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_worldStep_hashCalls

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable

theorem lazyRun_counted_hashCalls {Result : Type}
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (program : OracleComp (World inputs) Result)
    (state : State inputs) (value : Result) (cost : Nat) (after : State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.counted (WeightedCutoff.residualCharge inputs) program) state
      (some (value, cost), after) ≠ 0) :
    after.memory.external.hashCalls = state.memory.external.hashCalls + cost := by
  exact lazyRun_counted_hashCalls_of_step parameter inputs hencoding words publicReplies
    selections rows program (lazyRun_worldStep_hashCalls parameter inputs hencoding words
      publicReplies selections rows) state value cost after hresult
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_counted_hashCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_counted_hashCalls

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

theorem lazyRun_counted_stopped_cost_le {Result : Type}
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (program : OracleComp (World inputs) Result)
    (state : State inputs) (remaining : Nat) (value : Option Result)
    (cost : Nat) (after : State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.counted (WeightedCutoff.residualCharge inputs)
        (WeightedCutoff.run (WeightedCutoff.residualCharge inputs) program remaining)) state
      (some (value, cost), after) ≠ 0) :
    cost ≤ remaining := by
  induction program using OracleComp.inductionOn generalizing state remaining value cost after with
  | pure value =>
      simp only [WeightedCutoff.run_pure, WeightedCutoff.counted_pure, lazyRun, runWith_pure,
        ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      cases hresult
      exact Nat.zero_le _
  | query_bind query next ih =>
      rw [WeightedCutoff.run_query_bind] at hresult
      by_cases allowed : WeightedCutoff.residualCharge inputs query ≤ remaining
      · rw [if_pos allowed, WeightedCutoff.counted_query_bind, lazyRun_bind,
          RetainedObservation.bind_nonzero] at hresult
        obtain ⟨middle, hmiddle, htail⟩ := hresult
        rcases middle with ⟨option, middleState⟩
        cases option with
        | none =>
            simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff,
              not_not] at htail
            cases htail
        | some answer =>
            simp only [Option.elim_some] at htail
            rw [lazyRun_bind, RetainedObservation.bind_nonzero] at htail
            obtain ⟨countedResult, hcounted, hpure⟩ := htail
            rcases countedResult with ⟨optionResult, tailState⟩
            cases optionResult with
            | none =>
                simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff,
                  not_not] at hpure
                cases hpure
            | some pair =>
                rcases pair with ⟨tailValue, tailCost⟩
                have hrest := ih answer middleState
                  (remaining - WeightedCutoff.residualCharge inputs query)
                  tailValue tailCost tailState hcounted
                simp only [Option.elim_some, lazyRun, runWith_pure, ne_eq,
                  SPMF.pure_apply_eq_zero_iff, not_not] at hpure
                cases hpure
                omega
      · rw [if_neg allowed, WeightedCutoff.counted_pure, lazyRun,
          runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
        cases hresult
        exact Nat.zero_le _
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_counted_stopped_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_counted_stopped_cost_le

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable

theorem lazyRun_counted_stopped_remaining {Result : Type}
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (program : OracleComp (World inputs) Result)
    (state : State inputs) (budget remaining : Nat) (value : Option Result)
    (cost : Nat) (after : State inputs)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.counted (WeightedCutoff.residualCharge inputs)
        (WeightedCutoff.run (WeightedCutoff.residualCharge inputs) program remaining)) state
      (some (value, cost), after) ≠ 0) :
    after.memory.external.hashCalls + (remaining - cost) = budget := by
  have hspent := lazyRun_counted_hashCalls parameter inputs hencoding words publicReplies
    selections rows _ state value cost after hresult
  have hcap := lazyRun_counted_stopped_cost_le parameter inputs hencoding words publicReplies
    selections rows program state remaining value cost after hresult
  omega
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_counted_stopped_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_counted_stopped_remaining

namespace SphincsSecurity.WeightedCutoff
open _root_.OracleComp OracleSpec
variable {Index : Type} {spec : OracleSpec Index}

theorem counted_forget {Result : Type} (charge : spec.Domain → Nat)
    (program : OracleComp spec Result) :
    Prod.fst <$> counted charge program = program := by
  induction program using OracleComp.inductionOn with
  | pure value => simp only [counted_pure, map_pure]
  | query_bind query next ih =>
      simp only [counted_query_bind, map_bind, bind_pure_comp, Functor.map_map, ih]
end SphincsSecurity.WeightedCutoff

/-- info: 'SphincsSecurity.WeightedCutoff.counted_forget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.WeightedCutoff.counted_forget

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable

theorem lazyRun_map_value {Result Next : Type}
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (program : OracleComp (World inputs) Result) (f : Result → Next)
    (state : State inputs) :
    lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (f <$> program) state =
    (fun result : Option Result × State inputs => (result.1.map f, result.2)) <$>
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        program state := by
  simp only [lazyRun, runWith, simulateQ_map, OptionT.run_map, StateT.run_map]
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_map_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_map_value

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable

theorem lazyRun_counted_forget {Result : Type}
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (program : OracleComp (World inputs) Result) (state : State inputs) :
    (fun result : Option (Result × Nat) × State inputs =>
      (result.1.map Prod.fst, result.2)) <$>
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (WeightedCutoff.counted (WeightedCutoff.residualCharge inputs) program) state =
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        program state := by
  rw [← lazyRun_map_value]
  exact congrArg (fun p => lazyRun
    (environment parameter inputs hencoding words publicReplies selections rows) p state)
    (WeightedCutoff.counted_forget (WeightedCutoff.residualCharge inputs) program)
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_counted_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_counted_forget

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable

theorem expected_stoppedPotential_counted_forget {Result : Type}
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (program : OracleComp (World inputs) (Option Result)) (state : State inputs) (budget : Nat) :
    (∑' result, Pr[= result | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.counted (WeightedCutoff.residualCharge inputs) program) state] *
      stoppedPrimitiveResultPotential inputs budget
        (result.1.map Prod.fst, result.2)) =
    (∑' result, Pr[= result | lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      program state] * stoppedPrimitiveResultPotential inputs budget result) := by
  rw [← lazyRun_counted_forget parameter inputs hencoding words publicReplies selections rows
    program state, tsum_probOutput_map_mul]
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.expected_stoppedPotential_counted_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.expected_stoppedPotential_counted_forget

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

theorem lazyRun_stopped_success_support {Result : Type}
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (program : OracleComp (World inputs) Result) (remaining : Nat)
    (state : State inputs) (value : Result) (after : State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs) program remaining) state
      (some (some value), after) ≠ 0) :
    lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      program state (some value, after) ≠ 0 := by
  induction program using OracleComp.inductionOn generalizing remaining state value after with
  | pure result =>
      simp only [WeightedCutoff.run_pure, lazyRun, runWith_pure,
        ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult ⊢
      cases hresult
      rfl
  | query_bind query next ih =>
      rw [WeightedCutoff.run_query_bind] at hresult
      by_cases allowed : WeightedCutoff.residualCharge inputs query ≤ remaining
      · rw [if_pos allowed, lazyRun_bind, RetainedObservation.bind_nonzero] at hresult
        obtain ⟨middle, hmiddle, htail⟩ := hresult
        rcases middle with ⟨option, middleState⟩
        cases option with
        | none =>
            simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff,
              not_not] at htail
            cases htail
        | some answer =>
            simp only [Option.elim_some] at htail
            have htail' := ih answer
              (remaining - WeightedCutoff.residualCharge inputs query)
              middleState value after htail
            rw [lazyRun, runWith_query_bind, RetainedObservation.bind_nonzero]
            exact ⟨(some answer, middleState),
              by simpa only [lazyRun, runWith, simulateQ_spec_query] using hmiddle, htail'⟩
      · rw [if_neg allowed, lazyRun, runWith_pure, ne_eq,
          SPMF.pure_apply_eq_zero_iff, not_not] at hresult
        cases hresult
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_success_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_success_support

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable

theorem lazyRun_counted_stopped_success_support {Result : Type}
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (program : OracleComp (World inputs) Result) (remaining : Nat)
    (state : State inputs) (value : Result) (cost : Nat) (after : State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.counted (WeightedCutoff.residualCharge inputs)
        (WeightedCutoff.run (WeightedCutoff.residualCharge inputs) program remaining)) state
      (some (some value, cost), after) ≠ 0) :
    lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      program state (some value, after) ≠ 0 := by
  have hstopped : ((fun result : Option (Option Result × Nat) × State inputs =>
      (result.1.map Prod.fst, result.2)) <$> lazyRun
      (environment parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.counted (WeightedCutoff.residualCharge inputs)
        (WeightedCutoff.run (WeightedCutoff.residualCharge inputs) program remaining)) state)
      (some (some value), after) ≠ 0 := by
    rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero]
    exact ⟨(some (some value, cost), after), hresult, by
      simpa only [Function.comp_def, Option.map_some, Prod.fst, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]⟩
  rw [lazyRun_counted_forget parameter inputs hencoding words publicReplies selections rows
    (WeightedCutoff.run (WeightedCutoff.residualCharge inputs) program remaining) state] at hstopped
  exact lazyRun_stopped_success_support parameter inputs hencoding words publicReplies
    selections rows program remaining state value after hstopped
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_counted_stopped_success_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_counted_stopped_success_support

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

theorem lazyRun_stopped_source_jointPotential {Result : Type} (key : SecretKey)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (hinputs : sourceInputs key computation ⊆ inputs)
    (state : State inputs) (budget remaining : Nat)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput
      (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.memory.routing.known) words selections)
      state.memory.external.cache)
    (hresources : ProbeMessageBound state.memory)
    (hremaining : state.memory.external.hashCalls + remaining = budget)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | lazyRun
      (environment key.parameter inputs hencoding words publicReplies selections rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
        (simulateQ (adversaryImpl inputs key.parameter key.root words selections) computation)
        remaining) state] * stoppedPrimitiveResultPotential inputs budget result) ≤
      primitiveLivePotential budget state.memory := by
  induction computation using OracleComp.inductionOn generalizing state remaining with
  | pure value =>
      simp only [simulateQ_pure, WeightedCutoff.run_pure, lazyRun, runWith_pure,
        tsum_probOutput_pure_mul, stoppedPrimitiveResultPotential,
        primitiveResultPotential, Option.elim_some, primitiveLivePotential, le_refl]
  | query_bind input next ih =>
      have hin := (requestInputs_subset key input next).trans hinputs
      have hnext : ∀ answer, sourceInputs key (next answer) ⊆ inputs :=
        fun answer => (sourceInputs_next_subset key input next answer).trans hinputs
      apply le_trans ?_ (lazyRun_stopped_request_jointPotential key inputs hencoding words
        publicReplies selections rows input hin state budget remaining hselect ha hcovered
        hcandidates hclean hresources hremaining hbudget)
      rw [simulateQ_bind, simulateQ_spec_query, WeightedCutoff.run_bind_counted,
        lazyRun_bind, tsum_probOutput_bind_mul]
      rw [← expected_stoppedPotential_counted_forget key.parameter inputs hencoding words
        publicReplies selections rows
        (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
          (adversaryImpl inputs key.parameter key.root words selections input) remaining)
        state budget]
      apply ENNReal.tsum_le_tsum
      intro middle
      by_cases hm : Pr[= middle | lazyRun
          (environment key.parameter inputs hencoding words publicReplies selections rows)
          (WeightedCutoff.counted (WeightedCutoff.residualCharge inputs)
            (WeightedCutoff.run (WeightedCutoff.residualCharge inputs)
              (adversaryImpl inputs key.parameter key.root words selections input) remaining)) state] = 0
      · simp only [hm, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        rcases middle with ⟨option, after⟩
        cases option with
        | none =>
            simp only [Option.elim_none, tsum_probOutput_pure_mul, Option.map_none]
            rfl
        | some pair =>
            rcases pair with ⟨answer, cost⟩
            cases answer with
            | none =>
                simp only [Option.elim_some, lazyRun, runWith_pure,
                  tsum_probOutput_pure_mul, Option.map_some,
                  stoppedPrimitiveResultPotential, le_refl]
            | some answer =>
                have hsource := lazyRun_counted_stopped_success_support
                  key.parameter inputs hencoding words publicReplies selections rows
                  (adversaryImpl inputs key.parameter key.root words selections input)
                  remaining state answer cost after hm
                have ha' := lazyRun_nonempty
                  (environment key.parameter inputs hencoding words publicReplies selections rows)
                  _ state ha (some answer, after) hsource
                have hc' := lazyRun_rowsCovered key.parameter inputs hencoding words
                  publicReplies selections rows _ state ha hcovered (some answer, after) hsource
                have hp' := lazyRun_request_hiddenCandidateBound key inputs hencoding words
                  publicReplies selections rows input hin state ha hcovered hcandidates
                  (some answer, after) hsource
                have hr' := lazyRun_request_probeMessageBound inputs words publicReplies
                  selections rows key hencoding input hin state ha hcovered hresources
                  (some answer, after) hsource
                have he' := lazyRun_request_encodingClean inputs words publicReplies
                  selections rows key hencoding input hin state ha hcovered hclean
                  (some answer, after) hsource (by simp)
                have hrem := lazyRun_counted_stopped_remaining key.parameter inputs
                  hencoding words publicReplies selections rows
                  (adversaryImpl inputs key.parameter key.root words selections input)
                  state budget remaining (some answer) cost after hremaining hm
                convert ih answer (hnext answer) after (remaining - cost) ha' hc' hp' he'
                    hr' hrem using 1 <;> rfl
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_source_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_source_jointPotential

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

theorem initialStoppedSource_jointPotential (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy))
    (high : CanonicalGraphHighHalves) (budget : Nat)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hminimum : keygenHashCost ≤ budget) (hbudget : budget ≤ 2 ^ 128) :
    (∑' result, Pr[= result | lazyRun
      (environment key.parameter (gameInputs adversary)
        (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
        (referenceFamilyWords encoding.selections dummy)
        (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
        encoding.selections encoding.rows)
      (WeightedCutoff.run (WeightedCutoff.residualCharge (gameInputs adversary))
        (simulateQ (adversaryImpl (gameInputs adversary) key.parameter key.root
          (referenceFamilyWords encoding.selections dummy) encoding.selections)
          (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩))
        (budget - keygenHashCost))
      (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed)] *
      stoppedPrimitiveResultPotential (gameInputs adversary) budget result) ≤
    ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) -
      ((budget : ℝ) / 2 ^ digestBits) ^ 2) := by
  let inputs := gameInputs adversary
  let words := referenceFamilyWords encoding.selections dummy
  let publicReplies := coordinateGraphLabels (initialKnown words exposed) high
  let source := FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩
  let initial := initialState inputs words exposed
  have hd : 2 * budget ≤ 2 ^ digestBits := by
    norm_num only [digestBits]
    omega
  have hremaining : initial.memory.external.hashCalls + (budget - keygenHashCost) = budget := by
    simp only [initial, initialState, initialMemory]
    omega
  exact (lazyRun_stopped_source_jointPotential key inputs
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    words publicReplies encoding.selections encoding.rows source
    (sourceInputs_unlogged_subset_gameInputs adversary key) initial budget
    (budget - keygenHashCost) (referenceEncodingAuxiliary_select encoding hencoding)
    (initialAllowed_nonempty words exposed) (initialState_rowsCovered inputs words exposed)
    (initialState_hiddenCandidateBound inputs words exposed)
    (ResidualByteFrontend.replyClean_empty _) (Nat.zero_le _) hremaining hd).trans
    (primitiveLivePotential_initial_le inputs words exposed budget hminimum hd)
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.initialStoppedSource_jointPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.initialStoppedSource_jointPotential

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

theorem lazyRun_stopped_success_event_eq_counted {Result : Type}
    (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (program : OracleComp (World inputs) Result)
    (state : State inputs) (remaining : Nat)
    (event : Result → State inputs → Prop) :
    Pr[fun result => ∃ value, result.1 = some (some value) ∧ event value result.2 |
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (WeightedCutoff.run (WeightedCutoff.residualCharge inputs) program remaining) state] =
    Pr[fun result => ∃ value cost, result.1 = some (value, cost) ∧
      cost ≤ remaining ∧ event value result.2 |
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (WeightedCutoff.counted (WeightedCutoff.residualCharge inputs) program) state] := by
  induction program using OracleComp.inductionOn generalizing state remaining with
  | pure value =>
      simp [WeightedCutoff.run_pure, WeightedCutoff.counted_pure, lazyRun, runWith_pure,
        probEvent_pure]
  | query_bind query next ih =>
      rw [WeightedCutoff.run_query_bind, WeightedCutoff.counted_query_bind]
      by_cases allowed : WeightedCutoff.residualCharge inputs query ≤ remaining
      · rw [if_pos allowed, lazyRun_bind, lazyRun_bind,
          probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply tsum_congr
        intro middle
        rcases middle with ⟨option, after⟩
        cases option with
        | none =>
            simp [probEvent_pure]
        | some answer =>
            simp only [Option.elim_some]
            congr 1
            rw [ih answer after (remaining - WeightedCutoff.residualCharge inputs query)]
            have hmap : (do
              let result ← WeightedCutoff.counted (WeightedCutoff.residualCharge inputs) (next answer)
              pure (result.1, result.2 + WeightedCutoff.residualCharge inputs query)) =
              ((fun result : Result × Nat =>
                (result.1, result.2 + WeightedCutoff.residualCharge inputs query)) <$>
                WeightedCutoff.counted (WeightedCutoff.residualCharge inputs) (next answer)) := by
              rw [map_eq_bind_pure_comp]
              rfl
            rw [hmap, lazyRun_map_value, probEvent_map]
            congr 1
            funext result
            apply propext
            rcases result with ⟨option, final⟩
            cases option with
            | none => simp
            | some pair =>
                rcases pair with ⟨value, cost⟩
                simp only [Function.comp_def, Option.map_some,
                  Option.some.injEq, Prod.mk.injEq]
                constructor
                · rintro ⟨target, total, ⟨hv, hc⟩, hle, he⟩
                  subst target
                  subst total
                  exact ⟨value, cost + WeightedCutoff.residualCharge inputs query,
                    ⟨rfl, rfl⟩, by omega, he⟩
                · rintro ⟨target, total, ⟨hv, hc⟩, hle, he⟩
                  subst target
                  subst total
                  exact ⟨value, cost, ⟨rfl, rfl⟩, by omega, he⟩
      · rw [if_neg allowed]
        simp only [lazyRun, runWith_pure, probEvent_pure]
        rw [← lazyRun, lazyRun_bind, probEvent_bind_eq_tsum]
        have hfalse : (∃ value, some none = some (some value) ∧ event value state) = False := by simp
        rw [hfalse]
        simp only [↓reduceIte]
        symm
        rw [ENNReal.tsum_eq_zero]
        intro middle
        rcases middle with ⟨option, after⟩
        cases option with
        | none => simp [probEvent_pure]
        | some answer =>
            simp only [Option.elim_some]
            have hmap : (do
              let result ← WeightedCutoff.counted (WeightedCutoff.residualCharge inputs) (next answer)
              pure (result.1, result.2 + WeightedCutoff.residualCharge inputs query)) =
              ((fun result : Result × Nat =>
                (result.1, result.2 + WeightedCutoff.residualCharge inputs query)) <$>
                WeightedCutoff.counted (WeightedCutoff.residualCharge inputs) (next answer)) := by
              rw [map_eq_bind_pure_comp]
              rfl
            rw [hmap, lazyRun_map_value, probEvent_map]
            have hnever (result : Option (Result × Nat) × State inputs) :
                ¬(∃ value cost,
                  (result.1.map (fun pair =>
                    (pair.1, pair.2 + WeightedCutoff.residualCharge inputs query))) =
                    some (value, cost) ∧ cost ≤ remaining ∧ event value result.2) := by
              rcases result with ⟨option, final⟩
              cases option with
              | none => simp
              | some pair =>
                  rcases pair with ⟨value, cost⟩
                  intro hex
                  obtain ⟨target, total, heq, htotal, _⟩ := hex
                  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
                  exact allowed (by omega)
            simp only [Function.comp_def, probEvent_eq_tsum_ite]
            simp only [hnever, ↓reduceIte, tsum_zero, mul_zero]
end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_success_event_eq_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.lazyRun_stopped_success_event_eq_counted
