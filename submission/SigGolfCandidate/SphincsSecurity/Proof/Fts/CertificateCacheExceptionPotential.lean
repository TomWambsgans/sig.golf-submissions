import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CachedIndexHashMoments
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def cachedIndexExcessMoment (parameter : PublicParameter) (cache : QueryCache HashSpec) : ENNReal :=
  ∑ index : Index, positiveScoreMoment (cachedIndexExcessScore parameter cache index) 2

theorem cachedIndexExcessExceptional_moment_ge (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hbad : CachedIndexExcessExceptional parameter cache) :
    (2 ^ 148 : ENNReal) ≤ cachedIndexExcessMoment parameter cache := by
  obtain ⟨index, hindex⟩ := hbad
  have hpower : (2 ^ 148 : ℝ) ≤ max (cachedIndexExcessScore parameter cache index) 0 ^ 2 := by
    calc
      _ = (2 ^ 74 : ℝ) ^ 2 := by rw [← pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (hindex.le.trans (le_max_left _ _)) 2
  have hreal := ENNReal.ofReal_le_ofReal hpower
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_ofNat] at hreal
  exact hreal.trans (Finset.single_le_sum (s := Finset.univ)
    (f := fun index => positiveScoreMoment (cachedIndexExcessScore parameter cache index) 2)
    (fun _ _ => zero_le) (Finset.mem_univ index))

theorem cachedIndexExcessMoment_zero_of_no_message (parameter : PublicParameter)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput parameter input → cache input = none) :
    cachedIndexExcessMoment parameter cache = 0 := by
  apply Finset.sum_eq_zero
  intro index _
  exact positiveScoreMoment_zero_of_nonpos _
    (cachedIndexExcessScore_nonpos_of_no_message parameter cache hnone index) 2 (by decide)

theorem expected_cachedIndexExcessMoment_le (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      cachedIndexExcessMoment parameter (cache.cacheQuery input output)) ≤
        cachedIndexExcessMoment parameter cache + (2 ^ 8 : ENNReal)⁻¹ := by
  calc
    _ = ∑ index : Index, ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        positiveScoreMoment (cachedIndexExcessScore parameter (cache.cacheQuery input output) index) 2 := by
      simp only [cachedIndexExcessMoment, Finset.mul_sum]
      exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ ≤ ∑ index : Index, (positiveScoreMoment (cachedIndexExcessScore parameter cache index) 2 +
        ((2 ^ 42 : Nat) : ENNReal)⁻¹) :=
      Finset.sum_le_sum (fun index _ => expected_cachedIndexScore_second_le parameter cache hfinite input hfresh index)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      have hcard : Fintype.card Index = 2 ^ 34 := Fintype.card_fin _
      rw [hcard]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

end SphincsSecurity.Concrete

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

noncomputable def fourthMomentBudget (q : Nat) (second fourth : ENNReal) : ENNReal :=
  fourth + 6138 * q * second + 6279174 * q.choose 2 + (2 : ENNReal) ^ 30 * q

theorem fourth_le_fourthMomentBudget (q : Nat) (second fourth : ENNReal) :
    fourth ≤ fourthMomentBudget q second fourth := by
  exact ((le_self_add.trans le_self_add).trans le_self_add)

theorem fourthMomentBudget_zero_le (q : Nat) (hq : q ≤ 2 ^ 127) :
    fourthMomentBudget q 0 0 / (2 : ENNReal) ^ 364 ≤ (q : ENNReal) / 2 ^ 215 := by
  have hchoose : 2 * q.choose 2 + q = q * q := by
    clear hq
    induction q with
    | zero => simp
    | succ q ih =>
        have hstep : (q + 1).choose 2 = q + q.choose 2 := by
          simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' q 1
        rw [hstep]
        nlinarith
  have hchooseReal : 2 * (q.choose 2 : ℝ) + q = (q : ℝ) * q := by exact_mod_cast hchoose
  have hqReal : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq
  have hqNonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hproduct : (q : ℝ) * q ≤ q * 2 ^ 127 := mul_le_mul_of_nonneg_left hqReal hqNonneg
  apply (ENNReal.toReal_le_toReal (by simp [fourthMomentBudget]; finiteness) (by finiteness)).mp
  simp only [fourthMomentBudget, mul_zero, add_zero, zero_add]
  rw [ENNReal.toReal_div, ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_div]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, pow_succ] at hproduct ⊢
  nlinarith

end SphincsSecurity

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

def CertificateCacheExceptional (key : SecretKey) (cache : QueryCache HashSpec) : Prop :=
  MessageDeficitExceptional key cache ∨ CachedIndexExcessExceptional key.parameter cache

noncomputable def certificateCacheExceptionPotential (key : SecretKey) (remaining : Nat)
    (cache : QueryCache HashSpec) : ENNReal :=
  fourthMomentBudget remaining (messageDeficitMoment key.parameter key.root cache 2)
      (messageDeficitMoment key.parameter key.root cache 4) / 2 ^ 364 +
    (cachedIndexExcessMoment key.parameter cache + (remaining : ENNReal) * (2 ^ 8 : ENNReal)⁻¹) / 2 ^ 148

theorem certificateCacheExceptionPotential_bad (key : SecretKey) (remaining : Nat)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (hbad : CertificateCacheExceptional key cache) :
    1 ≤ certificateCacheExceptionPotential key remaining cache := by
  rcases hbad with hdeficit | hindex
  · apply le_trans (b := fourthMomentBudget remaining (messageDeficitMoment key.parameter key.root cache 2)
      (messageDeficitMoment key.parameter key.root cache 4) / 2 ^ 364) _ le_self_add
    calc
      1 = (2 ^ 364 : ENNReal) / 2 ^ 364 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right
        ((messageDeficitExceptional_fourthMoment_le key cache hfinite hdeficit).trans
          (fourth_le_fourthMomentBudget remaining _ _)) _
  · apply le_trans (b := (cachedIndexExcessMoment key.parameter cache +
      (remaining : ENNReal) * (2 ^ 8 : ENNReal)⁻¹) / 2 ^ 148) _ le_add_self
    calc
      1 = (2 ^ 148 : ENNReal) / 2 ^ 148 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right
        ((cachedIndexExcessExceptional_moment_ge key.parameter cache hindex).trans le_self_add) _

theorem certificateCacheExceptionPotential_initial_le (key : SecretKey) (q : Nat) (hq : q ≤ 2 ^ 127)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    certificateCacheExceptionPotential key q cache ≤ (q : ENNReal) / 2 ^ 215 + (q : ENNReal) / 2 ^ 156 := by
  have hcells : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none :=
    fun payload => hnone _ ⟨payload, rfl⟩
  have hcounts := cachedMessageEntryCount_zero_of_no_inputs key.parameter key.root cache hcells
  rw [certificateCacheExceptionPotential,
    messageDeficitMoment_zero_of_no_inputs key.parameter key.root cache hcounts 2 (by decide),
    messageDeficitMoment_zero_of_no_inputs key.parameter key.root cache hcounts 4 (by decide),
    cachedIndexExcessMoment_zero_of_no_message key.parameter cache hnone, zero_add]
  apply add_le_add (fourthMomentBudget_zero_le q hq)
  apply le_of_eq
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

end SphincsSecurity.Concrete
