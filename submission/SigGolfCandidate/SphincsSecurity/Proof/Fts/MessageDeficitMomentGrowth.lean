import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.MessageAdmissibleDeficit
namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem cachedMessageEntryCount_ne_top_of_finite (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    cachedMessageEntryCount cache parameter root message ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedMessageEntryCount_le_enncard cache parameter root message)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness

theorem cachedMessageEntryCountWhere_ne_top_of_finite (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere cache parameter root message P ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedMessageEntryCountWhere_le_enncard cache parameter root message P)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness

noncomputable def messageDeficitScore (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) : ℝ :=
  (cachedMessageEntryCount cache parameter root message).toReal -
    256 * (cachedMessageEntryCountWhere cache parameter root message (fun _ => True)).toReal

theorem messageDeficitScore_of_no_inputs (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hcount : cachedMessageEntryCount cache parameter root message = 0) :
    messageDeficitScore parameter root message cache ≤ 0 := by
  simp only [messageDeficitScore, hcount, ENNReal.toReal_zero, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)

theorem messageDeficitScore_ofReal_eq (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    ENNReal.ofReal (messageDeficitScore key.parameter key.root message cache) =
      256 * Concrete.messageAdmissibleDeficit key message cache := by
  have hcount := cachedMessageEntryCount_ne_top_of_finite key.parameter key.root message cache hfinite
  have hadmissible := cachedMessageEntryCountWhere_ne_top_of_finite key.parameter key.root message cache hfinite (fun _ => True)
  rw [messageDeficitScore, ENNReal.ofReal_sub _ (mul_nonneg (by norm_num) ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hcount, ENNReal.ofReal_toReal hadmissible]
  norm_num only [ENNReal.ofReal_ofNat]
  unfold Concrete.messageAdmissibleDeficit
  rw [ENNReal.mul_sub (by intros; finiteness)]
  norm_num [ftsTreeHeight]
  congr 1
  calc
    _ = cachedMessageEntryCount cache key.parameter key.root message * ((256 : ENNReal)⁻¹ * 256) := by
      rw [ENNReal.inv_mul_cancel (by norm_num) (by finiteness), mul_one]
    _ = _ := by ring

end SphincsSecurity


/-! ## AdmissibleHashMoments -/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def positiveScoreMoment (score : ℝ) (power : Nat) : ENNReal :=
  ENNReal.ofReal (max score 0 ^ power)

theorem positiveScoreMoment_ne_top (score : ℝ) (power : Nat) : positiveScoreMoment score power ≠ ⊤ := by
  exact ENNReal.ofReal_ne_top

theorem positiveScoreMoment_zero_of_nonpos (score : ℝ) (hscore : score ≤ 0) (power : Nat) (hpower : power ≠ 0) :
    positiveScoreMoment score power = 0 := by
  simp [positiveScoreMoment, max_eq_right hscore, zero_pow hpower]

end SphincsSecurity

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def messageDeficitMoment (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (power : Nat) : ENNReal :=
  ∑ message : Message, positiveScoreMoment (messageDeficitScore parameter root message cache) power

theorem positiveScoreMoment_le_messageDeficitMoment (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (power : Nat) (message : Message) :
    positiveScoreMoment (messageDeficitScore parameter root message cache) power ≤
      messageDeficitMoment parameter root cache power := by
  unfold messageDeficitMoment
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun message : Message => positiveScoreMoment (messageDeficitScore parameter root message cache) power)
    (fun _ _ => zero_le) (Finset.mem_univ message)

theorem messageDeficitMoment_zero_of_no_inputs (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hcount : ∀ message, cachedMessageEntryCount cache parameter root message = 0)
    (power : Nat) (hpower : power ≠ 0) : messageDeficitMoment parameter root cache power = 0 := by
  apply Finset.sum_eq_zero
  intro message _
  exact positiveScoreMoment_zero_of_nonpos _
    (messageDeficitScore_of_no_inputs parameter root message cache (hcount message)) power hpower

end SphincsSecurity
