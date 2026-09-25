import Mathlib
import VCVio.EvalDist.Expectation

/-! Scratch lemmas for capped search moments. No claim about any program image. -/

namespace SigGolfCandidate.SphincsMomentGeneric
open scoped BigOperators
open Finset

/-- Writing a bounded power as a sum of its tail increments. -/
theorem pow_eq_tail_sum (r : ℝ) (N k : ℕ) (hk : k ≤ N) :
    r ^ k = 1 + (r - 1) * ∑ n ∈ range N, if n < k then r ^ n else 0 := by
  have hs : (∑ n ∈ range N, if n < k then r ^ n else 0) =
      ∑ n ∈ range k, r ^ n := by
    rw [← sum_filter]
    congr 1
    ext n
    simp only [mem_filter, mem_range]
    omega
  rw [hs, mul_geom_sum]
  ring

/-- A finite geometric sum bounded without infinite sums. -/
theorem geom_sum_le_inv (x : ℝ) (N : ℕ) (hx : 0 ≤ x) (hsmall : x < 1) :
    (∑ n ∈ range N, x ^ n) ≤ 1 / (1 - x) := by
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).mpr
  rw [geom_sum_mul_neg]
  exact sub_le_self _ (pow_nonneg hx _)

/-- Any finite probability distribution with geometric attempt tails obeys the
geometric moment bound. This permits zero attempts and includes capped failures.
There is no independence hypothesis. Apply at each reachable search-entry state. -/
theorem capped_geometric_moment {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (attempts : Ω → ℕ) (N : ℕ) (a r : ℝ)
    (_hweight : ∀ ω, 0 ≤ weight ω) (hmass : ∑ ω, weight ω = 1)
    (hcap : ∀ ω, attempts ω ≤ N) (ha : 0 ≤ a) (hr : 1 ≤ r)
    (har : a * r < 1)
    (htail : ∀ n < N, (∑ ω, if n < attempts ω then weight ω else 0) ≤ a ^ n) :
    (∑ ω, weight ω * r ^ attempts ω) ≤ r * (1 - a) / (1 - a * r) := by
  have hident : (∑ ω, weight ω * r ^ attempts ω) =
      1 + (r - 1) * ∑ n ∈ range N,
        r ^ n * ∑ ω, if n < attempts ω then weight ω else 0 := by
    simp_rw [pow_eq_tail_sum r N _ (hcap _), mul_add, mul_one]
    rw [sum_add_distrib, hmass]
    congr 1
    simp_rw [← mul_assoc, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro ω hω
    split_ifs <;> ring
  rw [hident]
  have hsum : (∑ n ∈ range N, r ^ n * ∑ ω, if n < attempts ω then weight ω else 0)
      ≤ ∑ n ∈ range N, (a * r) ^ n := by
    apply sum_le_sum
    intro n hn
    rw [mul_pow, mul_comm (a ^ n)]
    exact mul_le_mul_of_nonneg_left (htail n (mem_range.mp hn))
      (pow_nonneg (by linarith) _)
  have hbound := geom_sum_le_inv (a * r) N (mul_nonneg ha (by linarith)) har
  calc
    _ ≤ 1 + (r - 1) * (1 / (1 - a * r)) := by
      gcongr
      exact hsum.trans hbound
    _ = r * (1 - a) / (1 - a * r) := by
      have hden : 1 - a * r ≠ 0 := ne_of_gt (sub_pos.mpr har)
      apply (eq_div_iff hden).mpr
      rw [add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hden, mul_one]
      ring

/-- The same bound with nonnegative extended-real weights, matching the
organizer's expectation arithmetic. -/
theorem capped_geometric_moment_ennreal {Ω : Type*} [Fintype Ω]
    (weight : Ω → ENNReal) (attempts : Ω → ℕ) (N : ℕ) (a r : ℝ)
    (hfinite : ∀ ω, weight ω ≠ ⊤) (hmass : ∑ ω, weight ω = 1)
    (hcap : ∀ ω, attempts ω ≤ N) (ha : 0 ≤ a) (hr : 1 ≤ r)
    (har : a * r < 1)
    (htail : ∀ n < N, (∑ ω, if n < attempts ω then weight ω else 0)
      ≤ ENNReal.ofReal (a ^ n)) :
    (∑ ω, weight ω * ENNReal.ofReal (r ^ attempts ω))
      ≤ ENNReal.ofReal (r * (1 - a) / (1 - a * r)) := by
  have ha1 : a < 1 := by nlinarith
  have hbound0 : 0 ≤ r * (1 - a) / (1 - a * r) := by positivity
  have hmassR : ∑ ω, (weight ω).toReal = 1 := by
    have h := congrArg ENNReal.toReal hmass
    simpa [ENNReal.toReal_sum (fun ω _ => hfinite ω)] using h
  have htailR : ∀ n < N,
      (∑ ω, if n < attempts ω then (weight ω).toReal else 0) ≤ a ^ n := by
    intro n hn
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail n hn)
    rw [ENNReal.toReal_sum (by intro ω hω; split_ifs <;> simp_all)] at h
    simpa [apply_ite, ENNReal.toReal_ofReal (pow_nonneg ha n)] using h
  have h := capped_geometric_moment (fun ω => (weight ω).toReal) attempts N a r
    (fun _ => ENNReal.toReal_nonneg) hmassR hcap ha hr har htailR
  have hterms : ∀ ω, weight ω * ENNReal.ofReal (r ^ attempts ω) ≠ ⊤ :=
    fun ω => ENNReal.mul_ne_top (hfinite ω) ENNReal.ofReal_ne_top
  apply (ENNReal.toReal_le_toReal (ENNReal.sum_ne_top.mpr (fun ω _ => hterms ω))
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_sum (fun ω _ => hterms ω), ENNReal.toReal_ofReal hbound0]
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (by linarith : 0 ≤ r) _)] using h

open OracleComp.EvalDist in
/-- Capped attempt counts in an actual probability computation. `hmass` rules
out semantic divergence; ordinary search exhaustion must return its count. -/
theorem capped_search_expectedValue (N : ℕ) (mx : SPMF (Fin (N + 1))) (a r : ℝ)
    (hmass : Pr[⊥ | mx] = 0) (ha : 0 ≤ a) (hr : 1 ≤ r) (har : a * r < 1)
    (htail : ∀ n < N, Pr[fun k => n < k.val | mx] ≤ ENNReal.ofReal (a ^ n)) :
    expectedValue mx (fun k => ENNReal.ofReal (r ^ k.val))
      ≤ ENNReal.ofReal (r * (1 - a) / (1 - a * r)) := by
  rw [expectedValue_def, tsum_fintype]
  refine capped_geometric_moment_ennreal (fun k => Pr[= k | mx]) (fun k => k.val) N a r
    (fun _ => probOutput_ne_top) ?_ (fun k => by omega) ha hr har ?_
  · simpa only [tsum_fintype] using tsum_probOutput_eq_one' hmass
  · intro n hn
    simpa only [probEvent_eq_tsum_ite, tsum_fintype] using htail n hn

/-- The elementary rational envelope used for each small exponent. -/
theorem two_rpow_le_one_add (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.rpow 2 x ≤ 1 + x := by
  have h := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) hx hx1
  norm_num at h
  simpa only [Real.rpow_eq_pow] using h

open OracleComp.EvalDist in
/-- A directly usable exponential-moment bound with a rational denominator. -/
theorem capped_search_exponentialMoment (N : ℕ) (mx : SPMF (Fin (N + 1))) (a c : ℝ)
    (hmass : Pr[⊥ | mx] = 0) (ha : 0 ≤ a) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hac : a * (1 + c) < 1)
    (htail : ∀ n < N, Pr[fun k => n < k.val | mx] ≤ ENNReal.ofReal (a ^ n)) :
    expectedValue mx (fun k => ENNReal.ofReal (Real.rpow 2 (c * k.val)))
      ≤ ENNReal.ofReal ((1 + c) * (1 - a) / (1 - a * (1 + c))) := by
  refine (expectedValue_mono mx (fun k => ?_)).trans
    (capped_search_expectedValue N mx a (1 + c) hmass ha (by linarith) hac htail)
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_eq_pow, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
    (two_rpow_le_one_add c hc hc1) _

open OracleComp.EvalDist in
/-- Two adaptive stages compose by their conditional moment bounds. The second
stage may depend arbitrarily on the first result; no independence is needed. -/
theorem conditional_moment_product {α β : Type} (mx : SPMF α) (next : α → SPMF β)
    (first : α → ENNReal) (second : α → β → ENNReal) (A B : ENNReal)
    (hfirst : expectedValue mx first ≤ A)
    (hsecond : ∀ x ∈ support mx, expectedValue (next x) (second x) ≤ B) :
    expectedValue (mx >>= fun x => (fun y => first x * second x y) <$> next x) id
      ≤ A * B := by
  rw [expectedValue_bind]
  simp only [expectedValue_map, id_eq]
  have hfactor : ∀ x,
      expectedValue (next x) (fun y => first x * second x y) =
        first x * expectedValue (next x) (second x) := by
    intro x
    simpa only [mul_comm] using expectedValue_mul_const (next x) (second x) (first x)
  simp_rw [hfactor]
  calc
    _ ≤ expectedValue mx (fun x => first x * B) :=
      expectedValue_mono_of_support (fun x hx => mul_le_mul' le_rfl (hsecond x hx))
    _ = expectedValue mx first * B := expectedValue_mul_const mx first B
    _ ≤ A * B := mul_le_mul' hfirst le_rfl

open OracleComp.EvalDist in
theorem digest_search_moment (N : ℕ) (mx : SPMF (Fin (N + 1)))
    (hmass : Pr[⊥ | mx] = 0)
    (htail : ∀ n < N, Pr[fun k => n < k.val | mx] ≤ ENNReal.ofReal ((511 / 512 : ℝ) ^ n)) :
    expectedValue mx (fun k => ENNReal.ofReal (Real.rpow 2 ((4 / 131072 : ℝ) * k.val)))
      ≤ ENNReal.ofReal (32769 / 32257 : ℝ) := by
  have h := capped_search_exponentialMoment N mx (511 / 512) (4 / 131072)
    hmass (by norm_num) (by norm_num) (by norm_num) (by norm_num) htail
  norm_num at h ⊢
  exact h

open OracleComp.EvalDist in
theorem encoding_search_moment (N : ℕ) (mx : SPMF (Fin (N + 1)))
    (hmass : Pr[⊥ | mx] = 0)
    (htail : ∀ n < N, Pr[fun k => n < k.val | mx] ≤ ENNReal.ofReal ((1023 / 1024 : ℝ) ^ n)) :
    expectedValue mx (fun k => ENNReal.ofReal (Real.rpow 2 ((1 / 131072 : ℝ) * k.val)))
      ≤ ENNReal.ofReal (131073 / 130049 : ℝ) := by
  have h := capped_search_exponentialMoment N mx (1023 / 1024) (1 / 131072)
    hmass (by norm_num) (by norm_num) (by norm_num) (by norm_num) htail
  norm_num at h ⊢
  exact h

/-- A wholly rational upper bound for the corrected masked-cache signer's
proposed moment proof, once its cost and conditional-tail refinements are supplied. -/
theorem signing_rational_closure :
    (1 + (97128 : ℝ) / 131072) * (32769 / 32257) * (131073 / 130049) ^ 6 < 2 := by
  norm_num

theorem signing_exponential_closure :
    Real.rpow 2 ((97128 : ℝ) / 131072) * (32769 / 32257) * (131073 / 130049) ^ 6 < 2 := by
  calc
    _ ≤ (1 + (97128 : ℝ) / 131072) * (32769 / 32257) * (131073 / 130049) ^ 6 := by
      gcongr
      exact two_rpow_le_one_add _ (by norm_num) (by norm_num)
    _ < 2 := signing_rational_closure

/-- info: 'SigGolfCandidate.SphincsMomentGeneric.capped_search_exponentialMoment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms capped_search_exponentialMoment

/-- info: 'SigGolfCandidate.SphincsMomentGeneric.conditional_moment_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conditional_moment_product

/-- info: 'SigGolfCandidate.SphincsMomentGeneric.digest_search_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms digest_search_moment

/-- info: 'SigGolfCandidate.SphincsMomentGeneric.encoding_search_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encoding_search_moment

/-- info: 'SigGolfCandidate.SphincsMomentGeneric.signing_exponential_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signing_exponential_closure

end SigGolfCandidate.SphincsMomentGeneric
