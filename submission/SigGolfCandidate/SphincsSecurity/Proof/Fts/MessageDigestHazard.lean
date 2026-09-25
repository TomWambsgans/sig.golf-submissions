import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeUniform
import SigGolfCandidate.SphincsSecurity.Proof.Fts.MessagePrehit
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CachedDigestRate
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeWeightedOriginRace
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FreshDigestHazard
import SigGolfCandidate.SphincsSecurity.Proof.Fts.MessageInputMiss
namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem cachedMessageEntryCount_cacheQuery_le (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput) :
    cachedMessageEntryCount (cache.cacheQuery input output) parameter root message ≤
      cachedMessageEntryCount cache parameter root message + 1 := by
  have hsubset : cachedMessageInputSet (cache.cacheQuery input output) parameter root message ⊆
      insert ⟨input, output⟩ (cachedMessageInputSet cache parameter root message) := by
    intro entry hentry
    rcases QueryCache.toSet_cacheQuery_subset_insert cache input output hentry.1 with heq | hold
    · exact Or.inl heq
    · exact Or.inr ⟨hold, hentry.2⟩
  exact (ENat.toENNReal_mono (Set.encard_le_encard hsubset)).trans
    (by simpa only [cachedMessageEntryCount, ENat.toENNReal_add, ENat.toENNReal_one] using
      ENat.toENNReal_mono (Set.encard_insert_le (cachedMessageInputSet cache parameter root message) ⟨input, output⟩))

theorem randomOracle_cachedMessageEntryCount_le (parameter : PublicParameter) (root : Digest) (message : Message)
    (input : HashInput) (cache : QueryCache HashSpec) (result : HashOutput × QueryCache HashSpec)
    (hr : result ∈ support ((randomOracle input).run cache)) :
    cachedMessageEntryCount result.2 parameter root message ≤ cachedMessageEntryCount cache parameter root message + 1 := by
  cases hc : cache input with
  | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc, support_map] at hr
      obtain ⟨output, _, rfl⟩ := hr
      exact cachedMessageEntryCount_cacheQuery_le parameter root message cache input output
  | some output =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at hr
      subst result
      exact le_self_add

namespace Concrete

theorem signAttempt_cachedMessageEntryCount_le (key : SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) (result : Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache)) :
    cachedMessageEntryCount result.2 key.parameter key.root message ≤ cachedMessageEntryCount cache key.parameter key.root message + 1 := by
  rw [simulateQ_signAttempt_run_eq, mem_support_bind_iff] at hr
  obtain ⟨oracleResult, horacle, hpure⟩ := hr
  simp only [mem_support_pure_iff] at hpure
  subst result
  exact randomOracle_cachedMessageEntryCount_le key.parameter key.root message
    (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) cache oracleResult horacle

end Concrete
end SphincsSecurity

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_6 : SampleableType Randomness := Concrete.randomnessSampleableType

attribute [local irreducible] signAttempt signDigestAttemptPrefix signDigestLoop

theorem probEvent_signDigestAttemptPrefix_fresh_ge_messageMiss
    (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec) (hreference : reference ≤ cache) :
    messageInputMissProbability key message cache * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≤
      Pr[FreshDigestAttempt reference key message | signDigestAttemptPrefix key message cache] := by
  rw [signDigestAttemptPrefix]
  apply mul_le_probEvent_bind
  · exact le_rfl
  · intro randomness _ hmiss
    have hrefMiss : reference (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) = none := by
      cases hc : reference (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) with
      | none => rfl
      | some output => simpa only [hmiss, reduceCtorEq] using hreference hc
    rw [show (fun result => pure (randomness, result)) = pure ∘ fun result => (randomness, result) from rfl,
      probEvent_bind_pure_comp]
    change ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≤
      Pr[fun result => reference (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) = none ∧ result.1 ≠ none |
        (simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache]
    simpa only [hrefMiss, true_and] using (probEvent_signAttempt_fresh_success_eq key message randomness cache hmiss).ge

theorem digestAttemptExpectation_mul_message_rate_le_freshSelection
    (attempts : Nat) (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hreference : reference ≤ cache) (budget rate : ENNReal)
    (hrate : rate ≤ (1 - budget * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹)
    (hbudget : cachedMessageEntryCount cache key.parameter key.root message + (attempts : ENNReal) ≤ budget) :
    digestAttemptExpectation attempts key message cache * rate ≤
      Pr[fun result => freshSelectedLoopView? reference key message result ≠ none |
        (simulateQ romImpl (signDigestLoop attempts key message)).run cache] := by
  induction attempts generalizing cache with
  | zero => simp only [digestAttemptExpectation, zero_mul]; exact zero_le
  | succ attempts ih =>
      rw [digestAttemptExpectation, add_mul, one_mul, ← ENNReal.tsum_mul_right, probEvent_signDigestLoop_fresh_recurrence]
      apply add_le_add
      · apply hrate.trans (le_trans ?_ (probEvent_signDigestAttemptPrefix_fresh_ge_messageMiss key message reference cache hreference))
        rw [messageInputMissProbability_eq_count]
        exact mul_le_mul' (tsub_le_tsub_left (mul_le_mul' (le_self_add.trans hbudget) le_rfl) _) le_rfl
      · apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support (signDigestAttemptPrefix key message cache)
        · by_cases hnone : result.2.1 = none
          · rw [if_pos hnone, if_pos hnone, mul_assoc]
            apply mul_le_mul' le_rfl
            apply ih result.2.2 (hreference.trans (signDigestAttemptPrefix_cache_le key message cache result hr))
            have hgrowth := signAttempt_cachedMessageEntryCount_le key message result.1 cache result.2
              (signDigestAttemptPrefix_support_attempt key message cache result hr)
            calc
              _ ≤ (cachedMessageEntryCount cache key.parameter key.root message + 1) + (attempts : ENNReal) :=
                add_le_add hgrowth le_rfl
              _ = cachedMessageEntryCount cache key.parameter key.root message + ((attempts + 1 : Nat) : ENNReal) := by
                push_cast; ring
              _ ≤ _ := hbudget
          · simp only [if_neg hnone, mul_zero, zero_mul, le_refl]
        · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul, le_refl]

noncomputable def messageDigestFreshRate (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  (1 - (cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal)) *
    ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹

noncomputable def messageDigestReuseWeight (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ / messageDigestFreshRate key message cache

theorem messageDigestFreshRate_ge_budget (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hcache : QueryCache.enncard cache ≤ q) :
    (1 - ((q + digestAttemptLimit : Nat) : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≤ messageDigestFreshRate key message cache := by
  unfold messageDigestFreshRate
  rw [Nat.cast_add]
  exact mul_le_mul' (tsub_le_tsub_left (mul_le_mul' (add_le_add
    ((cachedMessageEntryCount_le_enncard cache key.parameter key.root message).trans hcache) le_rfl) le_rfl) _) le_rfl

theorem messageDigestFreshRate_ne_zero (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 128) (hcache : QueryCache.enncard cache ≤ q) :
    messageDigestFreshRate key message cache ≠ 0 := by
  apply ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr ?_) (messageDigestFreshRate_ge_budget key message cache q hcache))
  apply digestRaceSuccessRate_ne_zero_of_budget_lt
  norm_num [digestAttemptLimit, randomnessBits] at *
  omega

theorem messageDigestFreshRate_ne_top (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    messageDigestFreshRate key message cache ≠ ⊤ := by
  unfold messageDigestFreshRate
  finiteness

theorem messageDigestReuseWeight_le (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hcache : QueryCache.enncard cache ≤ q) :
    messageDigestReuseWeight key message cache ≤ digestReuseWeight q :=
  ENNReal.div_le_div_left (messageDigestFreshRate_ge_budget key message cache q hcache) _

theorem messageDigestReuseWeight_ne_top (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 128) (hcache : QueryCache.enncard cache ≤ q) :
    messageDigestReuseWeight key message cache ≠ ⊤ :=
  ne_top_of_le_ne_top (digestReuseWeight_ne_top q hq) (messageDigestReuseWeight_le key message cache q hcache)

theorem exactDigestReuseWeight_le_fresh_mul_messageReuseWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 128) (hcache : QueryCache.enncard cache ≤ q) :
    exactDigestReuseWeight key message cache ≤ freshDigestSelectionProbability key message cache * messageDigestReuseWeight key message cache := by
  have hcancel : messageDigestFreshRate key message cache * messageDigestReuseWeight key message cache =
      ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
    unfold messageDigestReuseWeight
    rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel
      (messageDigestFreshRate_ne_zero key message cache q hq hcache) (messageDigestFreshRate_ne_top key message cache), mul_one]
  have h := mul_le_mul' (digestAttemptExpectation_mul_message_rate_le_freshSelection digestAttemptLimit key message cache cache le_rfl
    (cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal))
    (messageDigestFreshRate key message cache) le_rfl le_rfl) (le_refl (messageDigestReuseWeight key message cache))
  rw [mul_assoc, hcancel] at h
  exact h

end SphincsSecurity.Concrete
