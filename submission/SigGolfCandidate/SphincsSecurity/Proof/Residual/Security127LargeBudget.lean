import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualCacheTail
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option exponentiation.threshold 1024

private theorem largeRangeClosing (x : ℝ) (hx : 3 / 16384 ≤ x) :
    2 * (x / 2 ^ 32) - (x / 2 ^ 32) ^ 2 + (12 / 65536) * x +
      (x / 2 ^ 27 + 1 / 2 ^ 700) ≤ x := by
  have hn : 0 ≤ x := le_trans (by norm_num) hx
  have htail : (1 : ℝ) / 2 ^ 700 ≤ x / 2 ^ 40 := by
    have hsmall : (1 : ℝ) / 2 ^ 700 ≤ (3 / 16384) / 2 ^ 40 := by norm_num
    nlinarith
  have hsquare := sq_nonneg (x / 2 ^ 32)
  norm_num at hx htail ⊢
  nlinarith [hn, htail, hsquare]

theorem native_bound_le_security128 (q : Nat) (hlarge : budgetSplit ≤ q) (hsmall : q ≤ 2 ^ 128) :
    ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ digestBits) - ((q : ℝ) / 2 ^ digestBits) ^ 2) +
      (q : ENNReal) * fullCertificateTotalRate +
      ((q : ENNReal) * certificateCacheExceptionRate + proposalPrefixExceptionBound) ≤ (q : ENNReal) / 2 ^ 128 := by
  rw [budgetSplit_def] at hlarge
  refine le_trans (add_le_add le_rfl (add_le_add (mul_le_mul' le_rfl certificateCacheExceptionRate_le) le_rfl)) ?_
  rw [fullCertificateTotalRate_def, fullCertificateExcessRate_def, proposalPrefixExceptionBound_def]
  have hrate : (2 ^ 144 : ENNReal)⁻¹ + 11 / 2 ^ 144 = 12 / 2 ^ 144 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_inv, ENNReal.toReal_div]
  rw [hrate]
  let x : ℝ := (q : ℝ) / 2 ^ 128
  have hx : 3 / 16384 ≤ x := by
    have hq : (3 * 2 ^ 114 : ℝ) ≤ q := by exact_mod_cast hlarge
    apply (le_div_iff₀ (by positivity)).mpr
    norm_num at hq ⊢
    exact hq
  have hn : 0 ≤ x := by positivity
  have hp : 0 ≤ 2 * ((q : ℝ) / 2 ^ digestBits) - ((q : ℝ) / 2 ^ digestBits) ^ 2 := by
    have hq' : (q : ℝ) / 2 ^ digestBits ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      simpa only [one_mul] using (calc
        (q : ℝ) ≤ 2 ^ 128 := by exact_mod_cast hsmall
        _ ≤ 2 ^ digestBits := by norm_num [digestBits])
    have hq : 0 ≤ (q : ℝ) / 2 ^ digestBits := by positivity
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hq')]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_ofReal hp]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  convert largeRangeClosing x hx using 1 <;> dsimp only [x, digestBits] <;> norm_num <;> ring

theorem security128_of_large_budget (q : Nat) (hlarge : budgetSplit ≤ q) (hsmall : q ≤ 2 ^ 128)
    (adversary : Adversary) (hcost : HasHashQueryBound scheme adversary q) :
    forgeAdvantage scheme adversary ≤ (q : ENNReal) / 2 ^ 128 :=
  (RetainedResidual.forgeAdvantage_le_native_bound fixedReferenceDummy
    (fun _ _ _ => fixedReferenceDummyWord_valid) adversary q hcost hsmall).trans
      (native_bound_le_security128 q hlarge hsmall)

theorem security127_of_large_budget (q : Nat) (hlarge : budgetSplit ≤ q) (adversary : Adversary)
    (hcost : HasHashQueryBound scheme adversary q) : forgeAdvantage scheme adversary ≤ (q : ENNReal) / 2 ^ 127 := by
  by_cases hsmall : q ≤ 2 ^ 128
  · exact (security128_of_large_budget q hlarge hsmall adversary hcost).trans (by
          apply ENNReal.div_le_div_left
          norm_num)
  · apply probOutput_le_one.trans
    calc
      (1 : ENNReal) = (2 ^ 127 : ENNReal) / 2 ^ 127 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast (show 2 ^ 127 ≤ q by omega)) _

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option exponentiation.threshold 1024

theorem native_actual_budget_bound_le_security127 (q : Nat)
    (hq : 1 ≤ q) (hsmall : q ≤ 2 ^ 128) :
    ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ digestBits) -
      ((q : ℝ) / 2 ^ digestBits) ^ 2) +
      ((q : ENNReal) * fullCertificateTotalRate +
        ((q : ENNReal) * certificateCacheExceptionRate +
          proposalPrefixExceptionBound)) ≤
      (q : ENNReal) / 2 ^ 127 := by
  rw [fullCertificateTotalRate_def, fullCertificateExcessRate_def,
    certificateCacheExceptionRate, proposalPrefixExceptionBound_def]
  have hqreal : (0 : ℝ) ≤ q := by exact_mod_cast Nat.zero_le q
  have hratio : (q : ℝ) / 2 ^ digestBits ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [one_mul] using (calc
      (q : ℝ) ≤ 2 ^ 128 := by exact_mod_cast hsmall
      _ ≤ 2 ^ digestBits := by norm_num [digestBits])
  have hnonneg : 0 ≤ 2 * ((q : ℝ) / 2 ^ digestBits) -
      ((q : ℝ) / 2 ^ digestBits) ^ 2 := by
    have hn : 0 ≤ (q : ℝ) / 2 ^ digestBits := by positivity
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hratio)]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_ofReal hnonneg]
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpositive : 0 ≤ (q : ℝ) / 2 ^ digestBits := by positivity
  have htail : (1 : ℝ) / 2 ^ 700 ≤ (q : ℝ) / 2 ^ 700 :=
    div_le_div_of_nonneg_right hqone (by positivity)
  norm_num [digestBits] at *
  nlinarith [sq_nonneg ((q : ℝ) / 2 ^ 256), htail]

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.native_actual_budget_bound_le_security127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.native_actual_budget_bound_le_security127

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option exponentiation.threshold 1024

theorem actual_outer_slot_bound_le_security127 (q : Nat)
    (hq : 1 ≤ q) (hsmall : q ≤ 2 ^ 128) :
    ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ digestBits) -
      ((q : ℝ) / 2 ^ digestBits) ^ 2) +
      ((q : ENNReal) * fullCertificateTotalRate +
        (((q + 1 - keygenHashCost : Nat) : ENNReal) *
          ((digestAttemptLimit : ENNReal) * certificateCacheExceptionRate) +
          proposalPrefixExceptionBound)) ≤
      (q : ENNReal) / 2 ^ 127 := by
  have hslots : q + 1 - keygenHashCost ≤ 2 * q := by omega
  have hupper : ((q + 1 - keygenHashCost : Nat) : ENNReal) *
      ((digestAttemptLimit : ENNReal) * certificateCacheExceptionRate) ≤
      (2 * q : ENNReal) *
        ((digestAttemptLimit : ENNReal) * (2 ^ 155 : ENNReal)⁻¹) := by
    apply mul_le_mul'
    · exact_mod_cast hslots
    · exact mul_le_mul' le_rfl certificateCacheExceptionRate_le
  refine le_trans (add_le_add le_rfl (add_le_add le_rfl (add_le_add hupper le_rfl))) ?_
  rw [fullCertificateTotalRate_def, fullCertificateExcessRate_def,
    proposalPrefixExceptionBound_def, digestAttemptLimit]
  have hqreal : (0 : ℝ) ≤ q := by exact_mod_cast Nat.zero_le q
  have hratio : (q : ℝ) / 2 ^ digestBits ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [one_mul] using (calc
      (q : ℝ) ≤ 2 ^ 128 := by exact_mod_cast hsmall
      _ ≤ 2 ^ digestBits := by norm_num [digestBits])
  have hnonneg : 0 ≤ 2 * ((q : ℝ) / 2 ^ digestBits) -
      ((q : ℝ) / 2 ^ digestBits) ^ 2 := by
    have hn : 0 ≤ (q : ℝ) / 2 ^ digestBits := by positivity
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hratio)]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_ofReal hnonneg]
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpositive : 0 ≤ (q : ℝ) / 2 ^ digestBits := by positivity
  have htail : (1 : ℝ) / 2 ^ 700 ≤ (q : ℝ) / 2 ^ 700 :=
    div_le_div_of_nonneg_right hqone (by positivity)
  norm_num [digestBits] at *
  nlinarith [sq_nonneg ((q : ℝ) / 2 ^ 256), htail]

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal

theorem originalGame_actual_budget_le_security127
    (adversary : Adversary) (q : Nat)
    (hq : 1 ≤ q) (hsmall : q ≤ 2 ^ 128) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q |
      (simulateQ romImpl (countHashQueries (gameCore scheme adversary))).run' ∅] ≤
    (q : ENNReal) / 2 ^ 127 := by
  apply le_trans (RetainedResidual.originalGame_budget_le_fault_rate_add_history
    fixedReferenceDummy (fun _ _ _ => fixedReferenceDummyWord_valid)
    adversary q hsmall)
  apply le_trans (add_le_add le_rfl (add_le_add le_rfl
    (add_le_add
      (RetainedResidual.exceptionHistorySourceGame_budget_cache_le_outerSlots
        fixedReferenceDummy adversary q)
      (RetainedResidual.exceptionHistorySourceGame_prefix_le
        fixedReferenceDummy adversary q))))
  exact actual_outer_slot_bound_le_security127 q hq hsmall

theorem originalGame_actual_budget_le_security127_all
    (adversary : Adversary) (q : Nat) (hq : 1 ≤ q) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q |
      (simulateQ romImpl (countHashQueries (gameCore scheme adversary))).run' ∅] ≤
    (q : ENNReal) / 2 ^ 127 := by
  by_cases hsmall : q ≤ 2 ^ 128
  · exact originalGame_actual_budget_le_security127 adversary q hq hsmall
  · apply probEvent_le_one.trans
    calc
      (1 : ENNReal) = (2 ^ 127 : ENNReal) / 2 ^ 127 :=
        (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right
        (by exact_mod_cast (show 2 ^ 127 ≤ q by omega)) _

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.originalGame_actual_budget_le_security127_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.originalGame_actual_budget_le_security127_all

/-- info: 'SphincsSecurity.Concrete.originalGame_actual_budget_le_security127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.originalGame_actual_budget_le_security127

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option exponentiation.threshold 1024

theorem actual_outer_slot_bound_le_security128 (q : Nat)
    (hq : 1 ≤ q) (hsmall : q ≤ 2 ^ 127) :
    ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ digestBits) -
      ((q : ℝ) / 2 ^ digestBits) ^ 2) +
      ((q : ENNReal) * fullCertificateTotalRate +
        (((q + 1 - keygenHashCost : Nat) : ENNReal) *
          ((digestAttemptLimit : ENNReal) * certificateCacheExceptionRate) +
          proposalPrefixExceptionBound)) ≤
      (q : ENNReal) / 2 ^ 128 := by
  have hslots : q + 1 - keygenHashCost ≤ 2 * q := by omega
  have hupper : ((q + 1 - keygenHashCost : Nat) : ENNReal) *
      ((digestAttemptLimit : ENNReal) * certificateCacheExceptionRate) ≤
      (2 * q : ENNReal) *
        ((digestAttemptLimit : ENNReal) * (2 ^ 155 : ENNReal)⁻¹) := by
    apply mul_le_mul'
    · exact_mod_cast hslots
    · exact mul_le_mul' le_rfl certificateCacheExceptionRate_le
  refine le_trans (add_le_add le_rfl (add_le_add le_rfl (add_le_add hupper le_rfl))) ?_
  rw [fullCertificateTotalRate_def, fullCertificateExcessRate_def,
    proposalPrefixExceptionBound_def, digestAttemptLimit]
  have hqreal : (0 : ℝ) ≤ q := by exact_mod_cast Nat.zero_le q
  have hratio : (q : ℝ) / 2 ^ digestBits ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [one_mul] using (calc
      (q : ℝ) ≤ 2 ^ 128 := by exact_mod_cast (hsmall.trans (by norm_num : 2 ^ 127 ≤ 2 ^ 128))
      _ ≤ 2 ^ digestBits := by norm_num [digestBits])
  have hnonneg : 0 ≤ 2 * ((q : ℝ) / 2 ^ digestBits) -
      ((q : ℝ) / 2 ^ digestBits) ^ 2 := by
    have hn : 0 ≤ (q : ℝ) / 2 ^ digestBits := by positivity
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hratio)]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_ofReal hnonneg]
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpositive : 0 ≤ (q : ℝ) / 2 ^ digestBits := by positivity
  have htail : (1 : ℝ) / 2 ^ 700 ≤ (q : ℝ) / 2 ^ 700 :=
    div_le_div_of_nonneg_right hqone (by positivity)
  norm_num [digestBits] at *
  nlinarith [sq_nonneg ((q : ℝ) / 2 ^ 256), htail]

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal

theorem originalGame_actual_budget_le_security128
    (adversary : Adversary) (q : Nat)
    (hq : 1 ≤ q) (hsmall : q ≤ 2 ^ 127) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q |
      (simulateQ romImpl (countHashQueries (gameCore scheme adversary))).run' ∅] ≤
    (q : ENNReal) / 2 ^ 128 := by
  apply le_trans (RetainedResidual.originalGame_budget_le_fault_rate_add_history
    fixedReferenceDummy (fun _ _ _ => fixedReferenceDummyWord_valid)
    adversary q (hsmall.trans (by norm_num : 2 ^ 127 ≤ 2 ^ 128)))
  apply le_trans (add_le_add le_rfl (add_le_add le_rfl
    (add_le_add
      (RetainedResidual.exceptionHistorySourceGame_budget_cache_le_outerSlots
        fixedReferenceDummy adversary q)
      (RetainedResidual.exceptionHistorySourceGame_prefix_le
        fixedReferenceDummy adversary q))))
  exact actual_outer_slot_bound_le_security128 q hq hsmall

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.originalGame_actual_budget_le_security128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.originalGame_actual_budget_le_security128


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal

theorem actual_budget_with_cache_seed_margin
    (adversary : Adversary) (q : Nat)
    (hq : 1 ≤ q) (hsmall : q ≤ 2 ^ 127) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q |
      (simulateQ romImpl (countHashQueries (gameCore scheme adversary))).run' ∅] +
      (q : ENNReal) / 2 ^ 160 + (q : ENNReal) / 2 ^ 256 ≤
      (q : ENNReal) / 2 ^ 127 := by
  have href := originalGame_actual_budget_le_security128 adversary q hq hsmall
  apply le_trans (add_le_add (add_le_add href le_rfl) le_rfl)
  simp only [div_eq_mul_inv]
  rw [← mul_add, ← mul_add]
  gcongr
  have hnn : ((2 ^ 128 : NNReal)⁻¹ +
    (2 ^ 160 : NNReal)⁻¹ + (2 ^ 256 : NNReal)⁻¹) ≤
      (2 ^ 127 : NNReal)⁻¹ := by
    apply NNReal.coe_le_coe.mpr
    norm_num [div_le_div_iff₀]
  have henn := ENNReal.coe_le_coe.mpr hnn
  have hcast (n : Nat) : (↑((2 ^ n : NNReal)⁻¹) : ENNReal) =
      (2 ^ n : ENNReal)⁻¹ := by
    rw [ENNReal.coe_inv (by positivity), ENNReal.coe_pow]
    norm_num
  simpa only [ENNReal.coe_add, hcast] using henn

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.actual_budget_with_cache_seed_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.actual_budget_with_cache_seed_margin
