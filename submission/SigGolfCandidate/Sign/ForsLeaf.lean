import SigGolfCandidate.Sign.Blocks
import SigGolfCandidate.Sign.Inv

/-!
# `sign`, FORS leaves (`fors_leaf_loop`, instructions 120 .. 139)

`forsLeaves_sim` : from `fors_leaf_loop` with `J = 0`, the machine refines
`buildFtsLeaves S k idx 10 u`: leaf `j` is stored at `FA + 16 j`, the secret of leaf `u` at
`SIGL + 16`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref


/-- The (fixed) facts at the start of the leaf loop of tree `k`. -/
structure LeafCtx (S : List Byte) (k idx u : Nat) (t0 : MachineState) : Prop where
  pb0 : t0.getMem (BitVec.ofNat 64 0x6A0) = twWord0 8 k idx 0
  pb8 : lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) = BitVec.ofNat 32 idx
  pbP : t0.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : t0.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cb0 : t0.getMem (BitVec.ofNat 64 0xC0) = twWord0 9 k idx 0
  cb8 : lo32 (t0.getMem (BitVec.ofNat 64 0xC8)) = BitVec.ofNat 32 idx
  cbP : t0.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0]
  x5 : t0.getReg .x5 = 0
  x13 : t0.getReg .x13 = BitVec.ofNat 64 u
  x18 : t0.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k)
  x19 : t0.getReg .x19 = BitVec.ofNat 64 0x30000

/-- Addresses written by the leaf loop of tree `k`. -/
def leafW (k : Nat) (a : Nat) : Prop :=
  a = 0x6A8 ∨ a = 0xC8 ∨ (0xE0 ≤ a ∧ a < 0x100) ∨ (0x30000 ≤ a ∧ a < 0x30000 + 16 * 1025) ∨
    a = 0x2650 + 176 * k + 16 ∨ a = 0x2650 + 176 * k + 24

def leafRegs : List Reg := [.x1, .x2, .x3, .x9, .x10, .x11, .x12]

/-- Invariant after `j` leaves. -/
def LeafInv (k u : Nat) (t0 : MachineState) (j : Nat) (st : List Val × Val) (t : MachineState) : Prop :=
  j ≤ 1024 ∧ st.1.length = j ∧ (∀ v ∈ st.1, v.length = 16) ∧ Slots t 0x30000 st.1 ∧
  (u < j → st.2.length = 16 ∧ t.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf st.2) ∧
  t.pc = (if j < 1024 then pcOf 120 else pcOf 140) ∧ t.getReg .x9 = BitVec.ofNat 64 j ∧
  RegsEq t0 t leafRegs ∧ Frame t0 t (leafW k) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8))

theorem forsLeaf_body (S : List Byte) (hS : S.length = 32) (k idx u : Nat) (hk : k < 14)
    (hidx : idx < 2 ^ 34) (hu : u < 1024) (t0 : MachineState) (ctx : LeafCtx S k idx u t0)
    (j : Nat) (hj : j < 1024) (st : List Val × Val) (t : MachineState)
    (hinv : LeafInv k u t0 j st t) :
    Sim image t 34 (do
        let s ← hash16 (ftsPrfInput S k idx j)
        let leaf ← hash16 (ftsLeafInput k idx j s)
        pure (st.1 ++ [leaf], if j = u then s else st.2))
      (LeafInv k u t0 (j + 1)) := by
  obtain ⟨-, hlen, hvals, hslots, hcap, tpc, t9, tregs, tframe, tlo1, tlo2⟩ := hinv
  have tpc' : t.pc = pcOf 120 := by rw [tpc, if_pos hj]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by simp [leafRegs]), ctx.x5]
  have tx13 : t.getReg .x13 = BitVec.ofNat 64 u := by rw [tregs.get .x13 (by simp [leafRegs]), ctx.x13]
  have tx18 : t.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) := by
    rw [tregs.get .x18 (by simp [leafRegs]), ctx.x18]
  have tx19 : t.getReg .x19 = BitVec.ofNat 64 0x30000 := by rw [tregs.get .x19 (by simp [leafRegs]), ctx.x19]
  -- block 120: prf input
  have hs1 := symRun_sound blk120 codeAt_120 t tpc' (by simp only [blk120.res, rv_simp])
  have hc1 : blk120.res.cycles = 4 := rfl
  rw [hc1] at hs1
  set t1 := blk120.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x6A8) := by
    apply frame_toState; intro x hx hW
    simp only [blk120.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x10, .x11, .x12] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | rfl | simp_all [blk120.res, rv_simp]
  have e1 := symRun_ecall blk120 codeAt_120 t (by simp only [blk120.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x6A0 := by simp only [ht1, blk120.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht1, blk120.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0xE0 := by simp only [ht1, blk120.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have pc1 : t1.pc = pcOf 124 := by simp only [ht1, blk120.res, rv_simp]
  have m6A8 : t1.getMem (BitVec.ofNat 64 0x6A8) =
      BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32)) := by
    rvs [ht1, blk120.res, t9]
    exact word_of_halves _ idx j (by rw [lo32_replace1, tlo1, ctx.pb8]) (by rw [hi32_replace1])
  have hq1 : hashInput t1 = pad64 (ftsPrfInput S k idx j) := by
    obtain ⟨hn, hw⟩ := words_ftsPrfInput S hS k idx j
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, m6A8, f1.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [leafW]; omega), ctx.pb0,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega), ctx.pbP, ctx.pbS]
    simp [twWords_eq]
  have hb1 : (pad64 (ftsPrfInput S k idx j)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_ftsPrfInput S hS k idx j).1]
  sorry

end SigGolfCandidate.Sign
