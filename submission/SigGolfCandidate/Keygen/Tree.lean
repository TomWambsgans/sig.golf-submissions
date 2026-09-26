import SigGolfCandidate.Keygen.Chain

/-!
# `keygen`: the tree levels (in place in the tree array)
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

/-- Node-loop context of level `lam = k + 1` (`n` nodes): nodes `0 .. j-1` done, inputs
`L[2j ..]` still in place. -/
structure NCtx (W : List Word) (k n : Nat) (L : List Val) (j : Nat) (acc : List Val)
    (t : MachineState) : Prop where
  base : Base W t
  r15 : t.getReg .x15 = BitVec.ofNat 64 (k + 1)
  r17 : t.getReg .x17 = BitVec.ofNat 64 n
  r16 : t.getReg .x16 = BitVec.ofNat 64 j
  w448 : t.getMem (BitVec.ofNat 64 448) = BitVec.ofNat 64 (769 + 2 ^ 32 * (k + 1))
  w456 : (t.getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = 0
  alen : acc.length = j
  av : Vals t TA acc
  llen : L.length = 2 * n
  l16 : ∀ v ∈ L, v.length = 16
  lv : ∀ i, 2 * j ≤ i → i < 2 * n → ValAt t (TA + 16 * i) (L.getD i [])

theorem getD_len {L : List Val} (h : ∀ v ∈ L, v.length = 16) (i : Nat) (hi : i < L.length) :
    (L.getD i []).length = 16 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact h _ (List.getElem_mem hi)

/-- One node. -/
theorem node_xsim (W : List Word) (k n : Nat) (hk : k < 5) (hn : n ≤ 16) (L : List Val) (j : Nat)
    (hj : j < n) (acc : List Val) (t : MachineState) (h : NCtx W k n L j acc t)
    (hpc : t.pc = pcOf 73) :
    XSim image t 18 25 1 1
      (do let v ← Ref.hash16 (nodeInput 0 0 (k + 1) j (L.getD (2 * j) []) (L.getD (2 * j + 1) []))
          pure (acc ++ [v]))
      (fun acc' u => NCtx W k n L (j + 1) acc' u ∧ u.pc = if j + 1 < n then pcOf 73 else pcOf 91) := by
  obtain ⟨u, hst, upc, u10, u11, u12, uun, u456, u480, u488, u496, u504, ufr⟩ :=
    spec_73 t hpc j (by omega) h.r16 h.base.r19 h.w456
  have ux : ∀ r, r ≠ .x1 ∧ r ≠ .x3 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 → u.getReg r = t.getReg r :=
    fun r hr => uun r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2
  have hl := h.lv (2 * j) (by omega) (by omega)
  have hr := h.lv (2 * j + 1) (by omega) (by omega)
  have hll := getD_len h.l16 (2 * j) (by rw [h.llen]; omega)
  have hrl := getD_len h.l16 (2 * j + 1) (by rw [h.llen]; omega)
  have hq : hashInput u = pad64 (nodeInput 0 0 (k + 1) j (L.getD (2 * j) []) (L.getD (2 * j + 1) [])) := by
    have hx : (nodeInput 0 0 (k + 1) j (L.getD (2 * j) []) (L.getD (2 * j + 1) [])).length = 64 := by
      simp only [nodeInput, thInput, List.length_append, length_tweak, length_P, hll, hrl]
    refine hashInput_eq_pad64 u 0 448 _ (by rw [u11]) (by norm_num) u10
      (by norm_num) (by norm_num) (by omega) (by omega) ?_
    rw [readWords8]
    simp only [Nat.reduceAdd, wordsToNat]
    rw [getMem_frame (A := 448) ufr (by norm_num) (by simp),
      getMem_frame (A := 464) ufr (by norm_num) (by simp),
      getMem_frame (A := 472) ufr (by norm_num) (by simp), u456, u480, u488, u496, u504, h.w448,
      h.base.zero 464 (by simp [zeroKeys]), h.base.zero 472 (by simp [zeroKeys])]
    obtain ⟨hl1, hl2⟩ := hl
    obtain ⟨hr1, hr2⟩ := hr
    simp only [TA] at hl1 hl2 hr1 hr2
    rw [show 213248 + 32 * j = 213248 + 16 * (2 * j) by ring, hl1,
      show 213248 + 16 * (2 * j) + 8 = 213248 + 16 * (2 * j) + 8 from rfl, hl2,
      show 213248 + 16 * (2 * j) + 16 = 213248 + 16 * (2 * j + 1) by ring, hr1,
      show 213248 + 16 * (2 * j) + 24 = 213248 + 16 * (2 * j + 1) + 8 by ring, hr2]
    simp only [nodeInput, thInput, leNat_append, List.length_append, length_tweak,
      P, leNat_zeros, length_zeros, leNat_tweak0 3 0 _ _ (by norm_num) (by norm_num), hll,
      leNat_val _ hll, leNat_val _ hrl]
    simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl, Nat.reducePow, Nat.reduceMul,
      Nat.reduceAdd]
    rw [Nat.mod_eq_of_lt (a := 769 + 4294967296 * (k + 1)) (by omega),
      Nat.mod_eq_of_lt (a := 4294967296 * j) (by omega), Nat.mod_eq_of_lt (a := k + 1) (by omega),
      Nat.mod_eq_of_lt (a := j) (by omega)]
    ring
  sorry

end SigGolfCandidate.Keygen
