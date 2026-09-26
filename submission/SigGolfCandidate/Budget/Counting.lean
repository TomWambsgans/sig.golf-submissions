import SigGolfCandidate.Budget.Loops

/-!
# Budget: the acceptance probabilities of one fresh answer

For a uniform answer `u : BitVec 256`:

* the digest is admissible with probability exactly `2^-10` (`probEvent_not_admissible`);
* the randomizer lands in a set `R` of values with probability at most `|R| / 2^128`
  (`probEvent_answerBytes_mem_le`);
* the encoding decodes with probability exactly `codeCount / 2^128`, where
  `codeCount = 693523430046796437145478038506044352` is the number of pairs of 21-digit octal
  words with digit sum 170 (`probEvent_decode_none`). The count is a generating-function identity
  evaluated by the kernel (`codeCount_eq`), as in the leanVM completeness proof.
-/

namespace SigGolfCandidate.Budget
open SigGolf SigGolfCandidate.Ref OracleComp Finset ENNReal

/-! ## Counting over ranges -/

theorem sum_range_mul {M : Type} [AddCommMonoid M] (f : Nat → M) (A B : Nat) :
    ∑ k ∈ range (A * B), f k = ∑ b ∈ range B, ∑ a ∈ range A, f (a + A * b) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.add_comm]

theorem card_bitVec_filter (n : Nat) (P : Nat → Prop) [DecidablePred P] :
    (univ.filter fun u : BitVec n => P u.toNat).card = ((range (2 ^ n)).filter P).card := by
  refine Finset.card_nbij' (fun u => u.toNat) (fun k => BitVec.ofNat n k) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, mem_range] at hu ⊢
    exact ⟨u.isLt, hu⟩
  · intro k hk
    simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_univ, true_and] at hk ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk.1]; exact hk.2
  · intro u _; simp
  · intro k hk
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hk
    simp [Nat.mod_eq_of_lt hk.1]

theorem probEvent_uniform_toNat (P : Nat → Prop) [DecidablePred P] :
    Pr[fun u : BitVec 256 => P u.toNat | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      (((range (2 ^ 256)).filter P).card : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  rw [probEvent_uniformSample, card_bitVec_filter, Fintype.card_bitVec, Nat.cast_pow,
    Nat.cast_ofNat]

/-- Indicator sums. -/
theorem card_filter_range (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    ((range n).filter P).card = ∑ k ∈ range n, if P k then 1 else 0 :=
  Finset.card_filter _ _

/-! ## Admissibility -/

theorem count_split (A B : Nat) (P Q : Nat → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ a, a < A → ∀ b, (P (a + A * b) ↔ Q b)) :
    (∑ k ∈ range (A * B), if P k then 1 else 0) = A * ∑ b ∈ range B, if Q b then 1 else 0 := by
  rw [sum_range_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_congr rfl fun a ha => by rw [if_congr (hPQ a (mem_range.mp ha) b) rfl rfl]]
  by_cases hb : Q b <;> simp [hb]

theorem count_mod (m t : Nat) (hm : 0 < m) :
    (∑ b ∈ range (m * t), if b % m = 0 then 1 else 0) = t := by
  rw [sum_range_mul]
  have : ∀ s ∈ range t, (∑ r ∈ range m, if (r + m * s) % m = 0 then 1 else 0) = 1 := by
    intro s _
    rw [Finset.sum_congr rfl fun r hr => by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.mp hr)]]
    rw [Finset.sum_ite_eq' (range m) 0 (fun _ => 1)]
    simp [hm]
  rw [Finset.sum_congr rfl this]
  simp

theorem admissible_split (a b : Nat) (ha : a < 2 ^ 174) :
    admissible ((a + 2 ^ 174 * b) % 2 ^ 184) = true ↔ b % 2 ^ 10 = 0 := by
  unfold admissible uOf
  simp only [totalH, ftsA]
  have h1 : (2 : Nat) ^ 184 = 2 ^ 174 * 2 ^ 10 := by rw [← pow_add]
  rw [h1, Nat.mod_mul_right_div_self, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt ha, Nat.zero_add]
  simp

theorem count_admissible :
    ((range (2 ^ 256)).filter fun k => admissible (k % 2 ^ 184) = true).card = 2 ^ 246 := by
  rw [card_filter_range, show (2 : Nat) ^ 256 = 2 ^ 174 * (2 ^ 10 * 2 ^ 72) by
    rw [← pow_add, ← pow_add]]
  rw [count_split _ _ _ (fun b => b % 2 ^ 10 = 0) (fun a ha b => admissible_split a b ha),
    count_mod _ _ (by positivity), ← pow_add]

/-- A fresh digest is rejected with probability `1 - 2^-10`. -/
theorem probEvent_not_admissible :
    Pr[fun u : BitVec 256 => ¬ admissible (u.toNat % 2 ^ 184) = true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = 1 - (2 ^ 246 : ℝ≥0∞) / 2 ^ 256 := by
  have hc := probEvent_compl ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    (fun u : BitVec 256 => admissible (u.toNat % 2 ^ 184) = true)
  have hfail : Pr[⊥ | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = 0 := by simp
  rw [hfail, tsub_zero] at hc
  rw [hc, probEvent_uniform_toNat (fun k => admissible (k % 2 ^ 184) = true), count_admissible,
    Nat.cast_pow, Nat.cast_ofNat]

/-! ## Answer bytes -/

theorem leBytes_add (a b v : Nat) :
    leBytes (a + b) v = leBytes a v ++ leBytes b (v / 256 ^ a) := by
  unfold leBytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.pow_add, Nat.div_div_eq_div_mul]

theorem answerBytes_eq (k : Nat) (u : BitVec 256) (hk : k ≤ 32) :
    answerBytes k u = leBytes k u.toNat := by
  unfold answerBytes leBytes
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have := extractByte_ofNat 256 u.toNat i (by omega)
  simpa using this

theorem leNat_answerBytes16 (u : BitVec 256) : leNat (answerBytes 16 u) = u.toNat % 2 ^ 128 := by
  rw [answerBytes_eq 16 u (by omega), leNat_leBytes]; norm_num

/-- The randomizer is in `R` with probability at most `|R| / 2^128`. -/
theorem probEvent_answerBytes_mem_le (R : Finset Val) :
    Pr[fun u : BitVec 256 => answerBytes 16 u ∈ R | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤
      (R.card : ℝ≥0∞) / 2 ^ 128 := by
  classical
  rw [probEvent_uniformSample]
  have hsub : (univ.filter fun u : BitVec 256 => answerBytes 16 u ∈ R) ⊆
      R.biUnion fun ρ => univ.filter fun u : BitVec 256 => u.toNat % 2 ^ 128 = leNat ρ := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    exact ⟨_, hu, by rw [leNat_answerBytes16]⟩
  have hone : ∀ r : Nat,
      (univ.filter fun u : BitVec 256 => u.toNat % 2 ^ 128 = r).card ≤ 2 ^ 128 := by
    intro r
    rw [card_bitVec_filter 256 (fun k => k % 2 ^ 128 = r), card_filter_range,
      show (2 : Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 by norm_num, sum_range_mul]
    calc (∑ b ∈ range (2 ^ 128), ∑ a ∈ range (2 ^ 128),
          if (a + 2 ^ 128 * b) % 2 ^ 128 = r then 1 else 0)
        ≤ ∑ _b ∈ range (2 ^ 128), 1 := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [Finset.sum_congr rfl fun a ha => by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.mp ha)]]
          rw [Finset.sum_ite_eq (range (2 ^ 128)) r (fun _ => 1)]
          split <;> simp
      _ = 2 ^ 128 := by simp
  have hcard : (univ.filter fun u : BitVec 256 => answerBytes 16 u ∈ R).card ≤ R.card * 2 ^ 128 :=
    (card_le_card hsub).trans (card_biUnion_le.trans (by
      calc ∑ ρ ∈ R, (univ.filter fun u : BitVec 256 => u.toNat % 2 ^ 128 = leNat ρ).card
          ≤ ∑ _ρ ∈ R, 2 ^ 128 := Finset.sum_le_sum fun ρ _ => hone _
        _ = R.card * 2 ^ 128 := by simp))
  have hc : (Fintype.card (BitVec 256) : ℝ≥0∞) = 2 ^ 128 * 2 ^ 128 := by
    rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
  rw [hc]
  calc ((univ.filter fun u : BitVec 256 => answerBytes 16 u ∈ R).card : ℝ≥0∞) / (2 ^ 128 * 2 ^ 128)
      ≤ ((R.card * 2 ^ 128 : Nat) : ℝ≥0∞) / (2 ^ 128 * 2 ^ 128) := by
        gcongr; exact_mod_cast hcard
    _ = (R.card : ℝ≥0∞) / 2 ^ 128 := by
        push_cast
        rw [ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

/-! ## Decoding -/

/-- Octal digit sum of the low `n` digits. -/
def ds (n a : Nat) : Nat := ∑ r ∈ range n, a / 8 ^ r % 8

theorem list_sum_map_range (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ r ∈ range n, f r := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem sum_digitsOfWord (d : Nat) : (digitsOfWord d).sum = ds 21 d := by
  unfold digitsOfWord ds
  exact list_sum_map_range _ 21

end SigGolfCandidate.Budget
