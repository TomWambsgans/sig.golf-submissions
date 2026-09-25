import SigGolfCandidate.SphincsSecurity.Proof.Reference.QueryClassAllocation
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixIdealAllocation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs

theorem referenceRecordedRest_nonmessage_le (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary)
    (result : (Bool × SigningBoundaryTrace) × List OracleWorld.Domain)
    (hresult : result ∈ support (referenceRecordedRest key f labels selections dummy adversary)) :
    QueryCap.calls (CausalFrontierProgram.NonmessageHash key.parameter) result.2 + result.1.2.messageCalls.length ≤
      result.1.2.hashCalls :=
  CausalFrontierProgram.game_nonmessage_recorded_le _ _ _ _ _ _ result (QueryCap.simulate_oracle_mem_support _ _ result hresult)

private theorem probComp_mem_of_evalSPMF {Result : Type} (computation : ProbComp Result) (result : Result)
    (hresult : result ∈ support 𝒮[computation]) : result ∈ support computation :=
  (mem_support_iff_of_evalSPMF_eq (mx := computation) (mx' := 𝒮[computation]) rfl result).mpr hresult

theorem referenceRecordedGame_nonmessage_le (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame inputs hencoding dummy adversary)) :
    QueryCap.calls (CausalFrontierProgram.NonmessageHash result.1) result.2.2.2 + result.2.2.1.2.messageCalls.length ≤
      result.2.2.1.2.hashCalls := by
  simp only [referenceRecordedGame, mem_support_bind_iff] at hresult
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, reference, _, output, houtput, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  exact referenceRecordedRest_nonmessage_le ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs reference.2)
    (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs reference.2)) reference.1 dummy adversary output
    (probComp_mem_of_evalSPMF _ output houtput)

noncomputable def ReferenceRecordedResult.prefixCalls (dummy : OtsReferenceWords) (result : ReferenceRecordedResult) : Nat :=
  ∑ address : OtsPrefix.ChainAddress,
    QueryCap.calls (OtsPrefix.atAddress result.1 (referenceFamilyWords result.2.1 dummy) address).Selects result.2.2.2

noncomputable def ReferenceRecordedResult.encodingCalls (result : ReferenceRecordedResult) : Nat :=
  QueryCap.calls (QueryClass.EncodingHash result.1) result.2.2.2

noncomputable def ReferenceRecordedResult.otherCalls (dummy : OtsReferenceWords) (result : ReferenceRecordedResult) : Nat :=
  QueryCap.calls (QueryClass.OtherHash result.1 (referenceFamilyWords result.2.1 dummy)) result.2.2.2

def ReferenceRecordedResult.messageCalls (result : ReferenceRecordedResult) : Nat := result.2.2.1.2.messageCalls.length

noncomputable def ReferenceRecordedResult.remainingCalls (dummy : OtsReferenceWords) (result : ReferenceRecordedResult) : Nat :=
  result.encodingCalls + result.otherCalls dummy + result.messageCalls

theorem referenceRecordedGame_joint_budget_of_result_cost
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary))
    (hbudget : result.2.2.1.2.hashCalls ≤ q) :
    result.prefixCalls dummy + result.remainingCalls dummy ≤ q := by
  have hpartition := QueryClass.allocation_calls result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.2
  have hslots := referenceRecordedGame_nonmessage_le _ _ dummy adversary result hresult
  dsimp only [ReferenceRecordedResult.prefixCalls, ReferenceRecordedResult.remainingCalls,
    ReferenceRecordedResult.encodingCalls, ReferenceRecordedResult.otherCalls, ReferenceRecordedResult.messageCalls]
  omega

theorem referenceRecordedGame_joint_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) :
    result.prefixCalls dummy + result.remainingCalls dummy ≤ q :=
  referenceRecordedGame_joint_budget_of_result_cost dummy adversary q result hresult
    (referenceRecordedGame_hashCalls_le dummy adversary q hbound result hresult)

theorem referenceRecordedGame_budgeted_expected_calls_le
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) :
    (∑' result : ReferenceRecordedResult,
      Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
        ((if result.2.2.1.2.hashCalls ≤ q then
            result.prefixCalls dummy + result.remainingCalls dummy else 0 : Nat) : ENNReal)) ≤ q := by
  classical
  let law := referenceRecordedGame (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
  calc
    _ ≤ ∑' result : ReferenceRecordedResult, Pr[= result | law] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hcost : result.2.2.1.2.hashCalls ≤ q
      · by_cases hresult : result ∈ support law
        · simpa only [if_pos hcost] using
            (mul_le_mul' (le_refl (Pr[= result | law]))
              (Nat.cast_le.mpr (referenceRecordedGame_joint_budget_of_result_cost
                dummy adversary q result hresult hcost)))
        · have hzero : Pr[= result | law] = 0 := probOutput_eq_zero_of_not_mem_support hresult
          rw [hzero]
          simp only [zero_mul, le_refl]
      · simp only [if_neg hcost, Nat.cast_zero, mul_zero, zero_le]
    _ ≤ q := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.referenceRecordedGame_joint_budget_of_result_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.referenceRecordedGame_joint_budget_of_result_cost

/-- info: 'SphincsSecurity.Concrete.referenceRecordedGame_budgeted_expected_calls_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.referenceRecordedGame_budgeted_expected_calls_le
