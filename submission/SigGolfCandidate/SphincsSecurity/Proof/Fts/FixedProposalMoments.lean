import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.UniformProposalMixedMoments
import SigGolfCandidate.SphincsSecurity.Proof.Fts.UniformProposalVariance
namespace SphincsSecurity.Concrete

open ENNReal

theorem stirlingPowerMoment_ne_top (rate : ENNReal) (hrate : rate ≠ ⊤) (degree : Nat) :
    stirlingPowerMoment rate degree ≠ ⊤ := by
  unfold stirlingPowerMoment
  apply ENNReal.sum_ne_top.mpr
  intro order _
  exact ENNReal.mul_ne_top (by finiteness) (ENNReal.pow_ne_top hrate)

set_option maxHeartbeats 5000000 in
theorem stirlingPowerMoment_full_mean_le :
    (2 ^ 34 : ENNReal) * (2 ^ 90 : ENNReal)⁻¹ * stirlingPowerMoment (19 / 50) 24 ≤ 1 / 5 := by
  have hm := stirlingPowerMoment_ne_top (19 / 50) (by finiteness) 24
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_one]
  unfold stirlingPowerMoment
  rw [ENNReal.toReal_sum (fun order _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

set_option maxHeartbeats 5000000 in
theorem stirlingPowerMoment_full_variance_le :
    (2 ^ 34 : ENNReal) * (2 ^ 180 : ENNReal)⁻¹ * stirlingPowerMoment (19 / 50) 48 ≤ 13 / 25000 := by
  have hm := stirlingPowerMoment_ne_top (19 / 50) (by finiteness) 48
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat]
  unfold stirlingPowerMoment
  rw [ENNReal.toReal_sum (fun order _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open ENNReal

noncomputable def fixedFullProposalPrice (word : List Index) : ENNReal :=
  (2 ^ 90 : ENNReal)⁻¹ * proposalPowerSum 24 word

theorem fixedProposalLength_rate_le :
    (fixedProposalLength : ENNReal) * (Fintype.card Index : ENNReal)⁻¹ ≤ 19 / 50 := by
  have hcard : Fintype.card Index = 2 ^ 34 := Fintype.card_fin _
  rw [hcard]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [fixedProposalLength_def, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]

theorem fixedFullProposalPrice_ne_top (word : List Index) : fixedFullProposalPrice word ≠ ⊤ := by
  apply ENNReal.mul_ne_top (by finiteness)
  apply ENNReal.sum_ne_top.mpr
  intro index _
  finiteness

theorem uniformWordAverage_fixedFull_mean_le :
    uniformWordAverage fixedProposalLength fixedFullProposalPrice ≤ 1 / 5 := by
  unfold fixedFullProposalPrice
  rw [uniformWordAverage_mul_left]
  have h := mul_le_mul' (a := (2 ^ 90 : ENNReal)⁻¹) le_rfl
    (uniformWordAverage_powerSum_le (α := Index) fixedProposalLength 24 (19 / 50) fixedProposalLength_rate_le)
  have hcard : Fintype.card Index = 2 ^ 34 := Fintype.card_fin _
  rw [hcard] at h
  apply h.trans
  calc
    _ = (2 ^ 34 : ENNReal) * (2 ^ 90 : ENNReal)⁻¹ * stirlingPowerMoment (19 / 50) 24 := by
      push_cast
      ring
    _ ≤ _ := stirlingPowerMoment_full_mean_le

theorem uniformWordAverage_fixedFull_secondMoment_le :
    uniformWordAverage fixedProposalLength (fun word => fixedFullProposalPrice word ^ 2) ≤
      uniformWordAverage fixedProposalLength fixedFullProposalPrice ^ 2 + 13 / 25000 := by
  unfold fixedFullProposalPrice
  simp only [mul_pow, uniformWordAverage_mul_left]
  have h := mul_le_mul' (a := ((2 ^ 90 : ENNReal)⁻¹) ^ 2) le_rfl
    (uniformWordAverage_powerSum_square_le (α := Index) fixedProposalLength 24 (19 / 50) fixedProposalLength_rate_le)
  have hcard : Fintype.card Index = 2 ^ 34 := Fintype.card_fin _
  rw [hcard, mul_add] at h
  apply h.trans
  apply add_le_add le_rfl
  have hscale : ((2 ^ 90 : ENNReal)⁻¹) ^ 2 = (2 ^ 180 : ENNReal)⁻¹ := by
    rw [← ENNReal.inv_pow, ← pow_mul]
  rw [hscale]
  calc
    _ = (2 ^ 34 : ENNReal) * (2 ^ 180 : ENNReal)⁻¹ * stirlingPowerMoment (19 / 50) 48 := by
      push_cast
      ring
    _ ≤ _ := stirlingPowerMoment_full_variance_le

end SphincsSecurity.Concrete
