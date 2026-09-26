import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualCacheKernels
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualExceptionHistory
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  certificateCacheExceptionWeight
set_option backward.isDefEq.respectTransparency false

noncomputable def cacheHistoryWeight {inputs : Finset HashInput} (key : SecretKey) (state : ExceptionHistoryState inputs) : ENNReal :=
  if state.2.1 then 1 else certificateCacheExceptionWeight key state.1.1.memory.external.cache

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem expected_exceptionHistoryStep_cacheWeight_le (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionHistoryState inputs)
    (hvalid : MonitoredValid inputs state.1) (hinputs : requestInputs key input ⊆ inputs) (hbound : CacheSizeBound state.1.1.memory) :
    (∑' result, Pr[= result | exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      cacheHistoryWeight key result.2) ≤ cacheHistoryWeight key state +
        nativeMessageCharge key input (monitorView state.1) * certificateCacheExceptionRate := by
  rw [exceptionHistoryStep, tsum_probOutput_map_mul]
  cases hflag : state.2.1 with
  | true =>
      simp only [cacheHistoryWeight, exceptionHistoryUpdate, hflag, Bool.true_or, ite_true, mul_one]
      exact tsum_probOutput_le_one.trans le_self_add
  | false =>
      conv_rhs => simp only [cacheHistoryWeight, hflag, Bool.false_eq_true, if_false]
      by_cases hbefore : CertificateCacheExceptional key state.1.1.memory.external.cache
      · simp only [cacheHistoryWeight, exceptionHistoryUpdate, hflag, Bool.false_or, decide_eq_true hbefore, Bool.true_or, ite_true, mul_one]
        exact tsum_probOutput_le_one.trans ((certificateCacheExceptionWeight_bad key _ (Finite.of_enncard_le hbound) hbefore).trans le_self_add)
      · apply le_trans ?_ (expected_monitoredStep_cacheWeight_le key inputs hencoding words publicReplies selections rows budget required stopAfter
          input state.1 hvalid hinputs hbound)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1] = 0
        · simp only [hr, zero_mul, le_refl]
        · rw [SPMF.probOutput_eq_apply] at hr
          apply mul_le_mul' le_rfl
          have hb := monitoredStep_cacheSizeBound key inputs hencoding words publicReplies selections rows budget required stopAfter
            input state.1 hvalid hinputs hbound result hr
          simp only [cacheHistoryWeight, exceptionHistoryUpdate, hflag, Bool.false_or, decide_eq_false hbefore, Bool.false_or, decide_eq_true_eq]
          split
          · exact certificateCacheExceptionWeight_bad key _ (Finite.of_enncard_le hb) (by assumption)
          · exact le_rfl

theorem expected_exceptionHistoryRun_cacheWeight_le {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs) (hbound : CacheSizeBound state.1.1.memory) :
    (∑' result, Pr[= result | exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] *
      cacheHistoryWeight key result.2) ≤ cacheHistoryWeight key state +
        expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter
          (fun input current => nativeMessageCharge key input current * certificateCacheExceptionRate) computation state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [exceptionHistoryRun_pure, tsum_probOutput_pure_mul, expectedMonitoredPayment, construct_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [exceptionHistoryRun_query_bind, tsum_probOutput_bind_mul]
      let payment (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs) : ENNReal :=
        result.1.elim 0 (fun answer => expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter
          (fun input current => nativeMessageCharge key input current * certificateCacheExceptionRate) (next answer) result.2)
      have herasure := congrArg (fun law : SPMF (Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs) =>
          ∑' result, Pr[= result | law] * payment result)
        (exceptionHistoryStep_erasure key inputs hencoding words publicReplies selections rows budget required stopAfter input state)
      rw [tsum_probOutput_map_mul] at herasure
      calc
        _ ≤ ∑' result, Pr[= result | exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
            (cacheHistoryWeight key result.2 + payment (result.1, result.2.1)) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : Pr[= result | exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] = 0
          · simp only [hr, zero_mul, le_refl]
          · rw [SPMF.probOutput_eq_apply] at hr
            have hn := (exceptionHistoryStep_support key inputs hencoding words publicReplies selections rows budget required stopAfter input state result hr).1
            have hv := monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1 hvalid _ hn
            have hb := monitoredStep_cacheSizeBound key inputs hencoding words publicReplies selections rows budget required stopAfter
              input state.1 hvalid ((requestInputs_subset key input next).trans hinputs) hbound _ hn
            apply mul_le_mul' le_rfl
            rcases result with ⟨answer, after⟩
            cases answer with
            | none => simp only [payment, Option.elim_none, tsum_probOutput_pure_mul, add_zero, le_refl]
            | some answer => exact ih answer after hv ((sourceInputs_next_subset key input next answer).trans hinputs) hb
        _ ≤ (cacheHistoryWeight key state + nativeMessageCharge key input (monitorView state.1) * certificateCacheExceptionRate) +
            ∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state.1] * payment result := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [herasure]
          exact add_le_add (expected_exceptionHistoryStep_cacheWeight_le key inputs hencoding words publicReplies selections rows budget required stopAfter
            input state hvalid ((requestInputs_subset key input next).trans hinputs) hbound) le_rfl
        _ = _ := by
          change (cacheHistoryWeight key state + _) + _ = cacheHistoryWeight key state + (_ + _)
          exact add_assoc _ _ _

theorem exceptionHistoryRun_cache_le {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs) (hbound : CacheSizeBound state.1.1.memory) :
    Pr[fun result => result.2.2.1 = true |
      exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] ≤
      cacheHistoryWeight key state + expectedMonitoredPayment key inputs hencoding words publicReplies selections rows budget required stopAfter
        (fun input current => nativeMessageCharge key input current * certificateCacheExceptionRate) computation state.1 := by
  apply le_trans ?_ (expected_exceptionHistoryRun_cacheWeight_le key inputs hencoding words publicReplies selections rows budget required stopAfter
    computation state hvalid hinputs hbound)
  apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
  intro result _ hflag
  simp only [cacheHistoryWeight, hflag, ite_true, le_refl]

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec ENNReal
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

variable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

/-- Stop at the first outer query after the actual HASH count exceeds `q`.
One signing query may overshoot; no subsequent query is executed. -/
noncomputable def macroStoppedExceptionStep (q : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : ExceptionHistoryState inputs) :
    SPMF (Option ((OracleWorld + SigningSpec).Range input) × ExceptionHistoryState inputs) :=
  if state.1.1.memory.external.hashCalls ≤ q then
    exceptionHistoryStep key inputs hencoding words publicReplies selections rows
      budget required stopAfter input state
  else pure (none, state)

noncomputable def macroStoppedExceptionRun {Result : Type} (q : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) :
    SPMF (Option Result × ExceptionHistoryState inputs) :=
  (simulateQ (fun input => OptionT.mk (StateT.mk
    (macroStoppedExceptionStep key inputs hencoding words publicReplies selections rows
      budget required stopAfter q input))) computation).run.run state

theorem macroStoppedExceptionRun_pure {Result : Type} (q : Nat)
    (value : Result) (state : ExceptionHistoryState inputs) :
    macroStoppedExceptionRun key inputs hencoding words publicReplies selections rows
      budget required stopAfter q (pure value) state = pure (some value, state) := by
  simp only [macroStoppedExceptionRun, simulateQ_pure, OptionT.run_pure, StateT.run_pure]

theorem macroStoppedExceptionRun_query_bind {Result : Type} (q : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) :
    macroStoppedExceptionRun key inputs hencoding words publicReplies selections rows
      budget required stopAfter q
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
    (macroStoppedExceptionStep key inputs hencoding words publicReplies selections rows
      budget required stopAfter q input state >>= fun result =>
        result.1.elim (pure (none, result.2)) fun answer =>
          macroStoppedExceptionRun key inputs hencoding words publicReplies selections rows
            budget required stopAfter q (next answer) result.2) := by
  simp only [macroStoppedExceptionRun, simulateQ_bind, simulateQ_spec_query,
    OptionT.run_bind, Option.elimM, StateT.run_bind, OptionT.run_mk, StateT.run_mk]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨answer, after⟩
  cases answer <;> rfl

theorem exceptionHistoryRun_hashCalls_mono {Result : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs)
    (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs)
    (haccount : MonitoredAccounting state.1)
    (result : Option Result × ExceptionHistoryState inputs)
    (hresult : exceptionHistoryRun key inputs hencoding words publicReplies
      selections rows budget required stopAfter computation state result ≠ 0) :
    state.1.1.memory.external.hashCalls ≤
      result.2.1.1.memory.external.hashCalls := by
  have hproject := exceptionHistoryRun_support key inputs hencoding words
    publicReplies selections rows budget required stopAfter computation state result hresult
  exact (monitoredRun_accounting key inputs hencoding words publicReplies
    selections rows budget required stopAfter computation state.1 hvalid
    hinputs haccount (result.1, result.2.1) hproject).2.1

theorem macroStoppedExceptionRun_budget_event_eq {Result : Type} (q : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs)
    (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs)
    (haccount : MonitoredAccounting state.1)
    (event : Option Result × ExceptionHistoryState inputs → Prop) :
    Pr[fun result => event result ∧ result.2.1.1.memory.external.hashCalls ≤ q |
      macroStoppedExceptionRun key inputs hencoding words publicReplies selections
        rows budget required stopAfter q computation state] =
    Pr[fun result => event result ∧ result.2.1.1.memory.external.hashCalls ≤ q |
      exceptionHistoryRun key inputs hencoding words publicReplies selections
        rows budget required stopAfter computation state] := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [macroStoppedExceptionRun_pure, exceptionHistoryRun_pure]
  | query_bind input next ih =>
      rw [macroStoppedExceptionRun_query_bind, exceptionHistoryRun_query_bind]
      by_cases hwithin : state.1.1.memory.external.hashCalls ≤ q
      · simp only [macroStoppedExceptionStep, if_pos hwithin]
        rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply tsum_congr
        intro raw
        by_cases hraw : exceptionHistoryStep key inputs hencoding words
            publicReplies selections rows budget required stopAfter input state raw = 0
        · simp only [SPMF.probOutput_eq_apply, hraw, zero_mul]
        rcases raw with ⟨answer, after⟩
        cases answer with
        | none => rfl
        | some answer =>
            apply congrArg ((Pr[= (some answer, after) |
              exceptionHistoryStep key inputs hencoding words publicReplies selections
                rows budget required stopAfter input state]) * ·)
            have hstep := (exceptionHistoryStep_support key inputs hencoding words
              publicReplies selections rows budget required stopAfter input state
              (some answer, after) hraw).1
            have hvalid' := monitoredStep_valid key inputs hencoding words
              publicReplies selections rows budget required stopAfter input state.1
              hvalid (some answer, after.1) hstep
            have hinputs' := (sourceInputs_next_subset key input next answer).trans hinputs
            have haccount' := (monitoredStep_accounting key inputs hencoding words
              publicReplies selections rows budget required stopAfter input state.1
              hvalid ((requestInputs_subset key input next).trans hinputs) haccount
              (some answer, after.1) hstep).1
            exact ih answer after hvalid' hinputs' haccount'
      · simp only [macroStoppedExceptionStep, if_neg hwithin, pure_bind,
          Option.elim_none]
        have hzero :
            Pr[fun result => event result ∧
              result.2.1.1.memory.external.hashCalls ≤ q |
              exceptionHistoryStep key inputs hencoding words publicReplies
                selections rows budget required stopAfter input state >>= fun raw =>
                raw.1.elim (pure (none, raw.2)) fun answer =>
                  exceptionHistoryRun key inputs hencoding words publicReplies
                    selections rows budget required stopAfter (next answer) raw.2] = 0 := by
          rw [← exceptionHistoryRun_query_bind]
          apply (probEvent_eq_zero_iff).2
          intro result hresult hevent
          have hmono := exceptionHistoryRun_hashCalls_mono key inputs hencoding
            words publicReplies selections rows budget required stopAfter
            (liftM ((OracleWorld + SigningSpec).query input) >>= next) state
            hvalid hinputs haccount result hresult
          omega
        rw [hzero]
        simp only [probEvent_pure]
        simp only [hwithin, and_false, if_false]

theorem expected_macroStoppedExceptionStep_cacheWeight_le (q : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : ExceptionHistoryState inputs)
    (hvalid : MonitoredValid inputs state.1)
    (hinputs : requestInputs key input ⊆ inputs)
    (hbound : CacheSizeBound state.1.1.memory) :
    (∑' result, Pr[= result |
      macroStoppedExceptionStep key inputs hencoding words publicReplies selections rows
        budget required stopAfter q input state] *
      cacheHistoryWeight key result.2) ≤
      cacheHistoryWeight key state +
        (if state.1.1.memory.external.hashCalls ≤ q then
          nativeMessageCharge key input (monitorView state.1) * certificateCacheExceptionRate
        else 0) := by
  by_cases h : state.1.1.memory.external.hashCalls ≤ q
  · simpa only [macroStoppedExceptionStep, if_pos h] using
      expected_exceptionHistoryStep_cacheWeight_le key inputs hencoding words
        publicReplies selections rows budget required stopAfter input state
        hvalid hinputs hbound
  · simp only [macroStoppedExceptionStep, if_neg h, tsum_probOutput_pure_mul,
      add_zero, le_refl]

end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.expected_macroStoppedExceptionStep_cacheWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.expected_macroStoppedExceptionStep_cacheWeight_le

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.macroStoppedExceptionRun_budget_event_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.macroStoppedExceptionRun_budget_event_eq

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec ENNReal
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
theorem macroStoppedExceptionRun_hashCalls_le {Result : Type} (q overshoot : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs)
    (hinitial : state.1.1.memory.external.hashCalls ≤ q + overshoot)
    (hstep : ∀ (input : (OracleWorld + SigningSpec).Domain)
      (before : ExceptionHistoryState inputs)
      (after : Option ((OracleWorld + SigningSpec).Range input) ×
        ExceptionHistoryState inputs),
      exceptionHistoryStep key inputs hencoding words publicReplies selections rows
        budget required stopAfter input before after ≠ 0 →
      after.2.1.1.memory.external.hashCalls ≤
        before.1.1.memory.external.hashCalls + overshoot)
    (result : Option Result × ExceptionHistoryState inputs)
    (hresult : macroStoppedExceptionRun key inputs hencoding words publicReplies
      selections rows budget required stopAfter q computation state result ≠ 0) :
    result.2.1.1.memory.external.hashCalls ≤ q + overshoot := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [macroStoppedExceptionRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hinitial
  | query_bind input next ih =>
      rw [macroStoppedExceptionRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, after⟩, hfirst, htail⟩ := hresult
      have hafter : after.1.1.memory.external.hashCalls ≤ q + overshoot := by
        by_cases hactive : state.1.1.memory.external.hashCalls ≤ q
        · have hraw : exceptionHistoryStep key inputs hencoding words
              publicReplies selections rows budget required stopAfter input state
              (answer, after) ≠ 0 := by
            simpa only [macroStoppedExceptionStep, if_pos hactive] using hfirst
          exact (hstep input state (answer, after) hraw).trans
            (Nat.add_le_add_right hactive overshoot)
        · simp only [macroStoppedExceptionStep, if_neg hactive,
            ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hfirst
          cases hfirst
          exact hinitial
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff,
            not_not] at htail
          subst result
          exact hafter
      | some answer =>
          exact ih answer after hafter htail


end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.macroStoppedExceptionRun_hashCalls_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.macroStoppedExceptionRun_hashCalls_le

namespace SphincsSecurity.Concrete.RetainedResidual
open _root_.OracleComp OracleSpec ENNReal
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

variable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

def outerHashSlot : (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 1

theorem outerHashSlot_le_macroCost (input : (OracleWorld + SigningSpec).Domain) :
    outerHashSlot input ≤ signingMacroHashCost input := by
  cases input with
  | inl input => cases input <;> simp [outerHashSlot, signingMacroHashCost]
  | inr message => norm_num [outerHashSlot, signingMacroHashCost, ftsTreeHeight]

theorem digestAttemptExpectation_le_attempts (attempts : Nat)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    digestAttemptExpectation attempts key message cache ≤ attempts := by
  induction attempts generalizing cache with
  | zero => simp [digestAttemptExpectation]
  | succ attempts ih =>
      simp only [digestAttemptExpectation, Nat.cast_add, Nat.cast_one]
      rw [add_comm (attempts : ENNReal) 1]
      apply add_le_add_right
      calc
        _ ≤ ∑' result,
          Pr[= result | signDigestAttemptPrefix key message cache] * (attempts : ENNReal) := by
            apply ENNReal.tsum_le_tsum
            intro result
            apply mul_le_mul' le_rfl
            split_ifs
            · exact ih result.2.2
            · exact zero_le
        _ ≤ attempts := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem nativeMessageCharge_le_outerSlot (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateMonitorState) :
    nativeMessageCharge key input state ≤
      (outerHashSlot input : ENNReal) * digestAttemptLimit := by
  cases input with
  | inl input =>
      cases input with
      | inl sample => simp [nativeMessageCharge, outerHashSlot, hashQueryCharge]
      | inr hash =>
          simp only [nativeMessageCharge, outerHashSlot, hashQueryCharge,
            Sum.elim_inr]
          unfold FtsProbeSimulation.messageHashCharge
          split_ifs <;> norm_num [digestAttemptLimit]
  | inr message =>
      simpa only [nativeMessageCharge, outerHashSlot, Nat.cast_one, one_mul] using
        digestAttemptExpectation_le_attempts digestAttemptLimit key message state.1

noncomputable def outerSlotCachePotential (q : Nat)
    (state : ExceptionHistoryState inputs) : ENNReal :=
  cacheHistoryWeight key state +
    ((q + 1 - state.1.1.memory.external.hashCalls : Nat) : ENNReal) *
      ((digestAttemptLimit : ENNReal) * certificateCacheExceptionRate)

theorem exceptionHistoryStep_remaining_drop (q : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : ExceptionHistoryState inputs)
    (hactive : state.1.1.memory.external.hashCalls ≤ q)
    (hvalid : MonitoredValid inputs state.1)
    (hinputs : requestInputs key input ⊆ inputs)
    (haccount : MonitoredAccounting state.1)
    (result : Option ((OracleWorld + SigningSpec).Range input) ×
      ExceptionHistoryState inputs)
    (hresult : exceptionHistoryStep key inputs hencoding words publicReplies
      selections rows budget required stopAfter input state result ≠ 0) :
    (q + 1 - result.2.1.1.memory.external.hashCalls) + outerHashSlot input ≤
      q + 1 - state.1.1.memory.external.hashCalls := by
  have hstep := (exceptionHistoryStep_support key inputs hencoding words
    publicReplies selections rows budget required stopAfter input state result hresult).1
  have hcost := (monitoredStep_accounting key inputs hencoding words
    publicReplies selections rows budget required stopAfter input state.1
    hvalid hinputs haccount (result.1, result.2.1) hstep).2.1
  change state.1.1.memory.external.hashCalls + signingMacroHashCost input ≤
    result.2.1.1.memory.external.hashCalls at hcost
  have hminimum := outerHashSlot_le_macroCost input
  have hroom : outerHashSlot input ≤
      q + 1 - state.1.1.memory.external.hashCalls := by
    have hslot : outerHashSlot input ≤ 1 := by
      cases input with
      | inl input => cases input <;> simp [outerHashSlot]
      | inr message => simp [outerHashSlot]
    omega
  omega


theorem exceptionHistoryStep_remaining_price_le (q : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : ExceptionHistoryState inputs)
    (hactive : state.1.1.memory.external.hashCalls ≤ q)
    (hvalid : MonitoredValid inputs state.1)
    (hinputs : requestInputs key input ⊆ inputs)
    (haccount : MonitoredAccounting state.1)
    (result : Option ((OracleWorld + SigningSpec).Range input) ×
      ExceptionHistoryState inputs)
    (hresult : exceptionHistoryStep key inputs hencoding words publicReplies
      selections rows budget required stopAfter input state result ≠ 0) :
    ((q + 1 - result.2.1.1.memory.external.hashCalls : Nat) : ENNReal) *
        ((digestAttemptLimit : ENNReal) * certificateCacheExceptionRate) ≤
      ((q + 1 - state.1.1.memory.external.hashCalls - outerHashSlot input : Nat) : ENNReal) *
        ((digestAttemptLimit : ENNReal) * certificateCacheExceptionRate) := by
  have hdrop := exceptionHistoryStep_remaining_drop key inputs hencoding words
    publicReplies selections rows budget required stopAfter q input state
    hactive hvalid hinputs haccount result hresult
  have hnat : q + 1 - result.2.1.1.memory.external.hashCalls ≤
      q + 1 - state.1.1.memory.external.hashCalls - outerHashSlot input := by omega
  exact mul_le_mul' (by exact_mod_cast hnat) le_rfl

theorem expected_macroStoppedExceptionStep_potential_le (q : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : ExceptionHistoryState inputs)
    (hvalid : MonitoredValid inputs state.1)
    (hinputs : requestInputs key input ⊆ inputs)
    (hbound : CacheSizeBound state.1.1.memory)
    (haccount : MonitoredAccounting state.1) :
    (∑' result, Pr[= result |
      macroStoppedExceptionStep key inputs hencoding words publicReplies selections rows
        budget required stopAfter q input state] *
      outerSlotCachePotential key inputs q result.2) ≤
      outerSlotCachePotential key inputs q state := by
  by_cases hactive : state.1.1.memory.external.hashCalls ≤ q
  · simp only [macroStoppedExceptionStep, if_pos hactive]
    let price : ENNReal := (digestAttemptLimit : ENNReal) * certificateCacheExceptionRate
    let rem : Nat := q + 1 - state.1.1.memory.external.hashCalls
    let slot : Nat := outerHashSlot input
    have hslot : slot ≤ rem := by
      have hs : slot ≤ 1 := by
        cases input with
        | inl input => cases input <;> simp [slot, outerHashSlot]
        | inr message => simp [slot, outerHashSlot]
      dsimp [rem]
      omega
    have hsplit : rem = slot + (rem - slot) := by omega
    calc
      _ ≤ ∑' result, Pr[= result |
          exceptionHistoryStep key inputs hencoding words publicReplies selections rows
            budget required stopAfter input state] *
          (cacheHistoryWeight key result.2 + ((rem - slot : Nat) : ENNReal) * price) := by
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : Pr[= result | exceptionHistoryStep key inputs hencoding words
            publicReplies selections rows budget required stopAfter input state] = 0
        · simp [hr]
        rw [SPMF.probOutput_eq_apply] at hr
        apply mul_le_mul' le_rfl
        unfold outerSlotCachePotential
        apply add_le_add le_rfl
        simpa only [price, rem, slot] using
          exceptionHistoryStep_remaining_price_le key inputs hencoding words
            publicReplies selections rows budget required stopAfter q input state
            hactive hvalid hinputs haccount result hr
      _ ≤ (cacheHistoryWeight key state +
            nativeMessageCharge key input (monitorView state.1) * certificateCacheExceptionRate) +
          ((rem - slot : Nat) : ENNReal) * price := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        exact add_le_add
          (expected_exceptionHistoryStep_cacheWeight_le key inputs hencoding words
            publicReplies selections rows budget required stopAfter input state
            hvalid hinputs hbound)
          (mul_le_of_le_one_left' tsum_probOutput_le_one)
      _ ≤ outerSlotCachePotential key inputs q state := by
        have hcharge := nativeMessageCharge_le_outerSlot key input (monitorView state.1)
        have hcharged : nativeMessageCharge key input (monitorView state.1) *
            certificateCacheExceptionRate ≤ (slot : ENNReal) * price := by
          calc
            _ ≤ ((slot : ENNReal) * digestAttemptLimit) * certificateCacheExceptionRate :=
              mul_le_mul' hcharge le_rfl
            _ = (slot : ENNReal) * price := by rw [mul_assoc]
        unfold outerSlotCachePotential
        dsimp [price, rem, slot] at *
        calc
          _ ≤ (cacheHistoryWeight key state +
                ((slot : ENNReal) * (digestAttemptLimit * certificateCacheExceptionRate))) +
              (((q + 1 - state.1.1.memory.external.hashCalls - slot : Nat) : ENNReal) *
                (digestAttemptLimit * certificateCacheExceptionRate)) :=
              add_le_add (add_le_add le_rfl hcharged) le_rfl
          _ = _ := by
            rw [add_assoc, ← add_mul, ← Nat.cast_add]
            congr 1
            exact congrArg (fun n : Nat => (n : ENNReal) *
              (digestAttemptLimit * certificateCacheExceptionRate)) hsplit.symm
  · simp only [macroStoppedExceptionStep, if_neg hactive,
      tsum_probOutput_pure_mul, le_refl]


theorem expected_macroStoppedExceptionRun_potential_le {Result : Type}
    (q : Nat) (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs)
    (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs)
    (hbound : CacheSizeBound state.1.1.memory)
    (haccount : MonitoredAccounting state.1) :
    (∑' result, Pr[= result |
      macroStoppedExceptionRun key inputs hencoding words publicReplies selections rows
        budget required stopAfter q computation state] *
      outerSlotCachePotential key inputs q result.2) ≤
      outerSlotCachePotential key inputs q state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [macroStoppedExceptionRun_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [macroStoppedExceptionRun_query_bind, tsum_probOutput_bind_mul]
      calc
        _ ≤ ∑' raw, Pr[= raw | macroStoppedExceptionStep key inputs
            hencoding words publicReplies selections rows budget required stopAfter
            q input state] * outerSlotCachePotential key inputs q raw.2 := by
          apply ENNReal.tsum_le_tsum
          intro raw
          by_cases hr : Pr[= raw | macroStoppedExceptionStep key inputs
              hencoding words publicReplies selections rows budget required stopAfter
              q input state] = 0
          · simp only [hr, zero_mul, le_refl]
          rw [SPMF.probOutput_eq_apply] at hr
          apply mul_le_mul' le_rfl
          rcases raw with ⟨answer, after⟩
          cases answer with
          | none => simp only [Option.elim_none, tsum_probOutput_pure_mul, le_refl]
          | some answer =>
              have hactive : state.1.1.memory.external.hashCalls ≤ q := by
                by_contra hneg
                have hs : macroStoppedExceptionStep key inputs hencoding words
                    publicReplies selections rows budget required stopAfter q input state
                    (some answer, after) = 0 := by
                  simp only [macroStoppedExceptionStep, if_neg hneg]
                  rw [SPMF.pure_apply_eq_zero_iff]
                  intro hwrong
                  have hfirst := congrArg Prod.fst hwrong
                  cases hfirst
                exact hr hs
              have hstep : exceptionHistoryStep key inputs hencoding words
                  publicReplies selections rows budget required stopAfter input state
                  (some answer, after) ≠ 0 := by
                simpa only [macroStoppedExceptionStep, if_pos hactive] using hr
              have hmon := (exceptionHistoryStep_support key inputs hencoding words
                publicReplies selections rows budget required stopAfter input state
                (some answer, after) hstep).1
              have hv := monitoredStep_valid key inputs hencoding words
                publicReplies selections rows budget required stopAfter input state.1
                hvalid (some answer, after.1) hmon
              have hb := monitoredStep_cacheSizeBound key inputs hencoding words
                publicReplies selections rows budget required stopAfter input state.1
                hvalid ((requestInputs_subset key input next).trans hinputs)
                hbound (some answer, after.1) hmon
              have ha := (monitoredStep_accounting key inputs hencoding words
                publicReplies selections rows budget required stopAfter input state.1
                hvalid ((requestInputs_subset key input next).trans hinputs)
                haccount (some answer, after.1) hmon).1
              exact ih answer after hv
                ((sourceInputs_next_subset key input next answer).trans hinputs) hb ha
        _ ≤ _ := expected_macroStoppedExceptionStep_potential_le key inputs
          hencoding words publicReplies selections rows budget required stopAfter
          q input state hvalid ((requestInputs_subset key input next).trans hinputs)
          hbound haccount


theorem exceptionHistoryRun_budget_hit_le_outerSlots {Result : Type}
    (q : Nat) (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs)
    (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs)
    (hbound : CacheSizeBound state.1.1.memory)
    (haccount : MonitoredAccounting state.1) :
    Pr[fun result => result.2.2.1 = true ∧
      result.2.1.1.memory.external.hashCalls ≤ q |
      exceptionHistoryRun key inputs hencoding words publicReplies selections rows
        budget required stopAfter computation state] ≤
      outerSlotCachePotential key inputs q state := by
  rw [← macroStoppedExceptionRun_budget_event_eq key inputs hencoding words
    publicReplies selections rows budget required stopAfter q computation state
    hvalid hinputs haccount (fun result => result.2.2.1 = true)]
  apply le_trans ?_ (expected_macroStoppedExceptionRun_potential_le key inputs
    hencoding words publicReplies selections rows budget required stopAfter
    q computation state hvalid hinputs hbound haccount)
  apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
  intro result _ hhit
  change result.2.2.1 = true ∧
    result.2.1.1.memory.external.hashCalls ≤ q at hhit
  have hweight : cacheHistoryWeight key result.2 = 1 := by
    simp only [cacheHistoryWeight, hhit.1, ite_true]
  unfold outerSlotCachePotential
  rw [hweight]
  exact le_self_add

end SphincsSecurity.Concrete.RetainedResidual

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.expected_macroStoppedExceptionRun_potential_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.expected_macroStoppedExceptionRun_potential_le

/-- info: 'SphincsSecurity.Concrete.RetainedResidual.exceptionHistoryRun_budget_hit_le_outerSlots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.RetainedResidual.exceptionHistoryRun_budget_hit_le_outerSlots
