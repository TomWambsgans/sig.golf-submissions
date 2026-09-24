import SigGolfCandidate.SphincsVerifierLeaf0

/-!
# Verifier FORS selector code

The first 24 selector blocks have the same eleven-instruction shape. The
instruction words are checked against the submitted verifier image.
-/

namespace SigGolfCandidate.SphincsVerifierLeafCode
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.Hypertree.Signing
set_option maxRecDepth 16384

private theorem getByte_setPC (s : MachineState) (pc a : Word) :
    (s.setPC pc).getByte a = s.getByte a := by
  simp [MachineState.getByte]

def leafInstructions (tree : Fin 24) : List Instr := [
  .LUI .x6 0x42,
  .ADDI .x6 .x6 0,
  .LBU .x10 .x6 (4 + tree.val),
  .LBU .x11 .x6 (5 + tree.val),
  .SRLI .x10 .x10 2,
  .SLLI .x11 .x11 6,
  .ADD .x10 .x10 .x11,
  .ANDI .x10 .x10 255,
  .LUI .x7 0x45,
  .ADDI .x7 .x7 (-2048 + tree.val),
  .SB .x7 .x10 0]

theorem leafInstructions_length (tree : Fin 24) :
    (leafInstructions tree).length = 11 := by rfl

set_option maxHeartbeats 0 in
theorem leaf_code (tree : Fin 24) (offset : Fin 11) :
    (SphincsImages.verify.code[180 + 11 * tree.val + offset.val]?).bind
      decodeInstruction =
      some (.base ((leafInstructions tree)[offset.val]'(by
        rw [leafInstructions_length]; exact offset.isLt))) := by
  fin_cases tree <;> fin_cases offset <;> decide

theorem leaf_fetch (tree : Fin 24) (offset : Fin 11)
    (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val + offset.val))) :
    fetch SphincsImages.verify state =
      some (.base ((leafInstructions tree)[offset.val]'(by
        rw [leafInstructions_length]; exact offset.isLt))) := by
  rw [fetch_index SphincsImages.verify state _ (by
    have bound := tree.isLt
    have step := offset.isLt
    omega) pc]
  exact leaf_code tree offset

def leafState (tree : Fin 24) (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x42)
  let state := execInstrBr state (.ADDI .x6 .x6 0)
  let state := execInstrBr state (.LBU .x10 .x6 (4 + tree.val))
  let state := execInstrBr state (.LBU .x11 .x6 (5 + tree.val))
  let state := execInstrBr state (.SRLI .x10 .x10 2)
  let state := execInstrBr state (.SLLI .x11 .x11 6)
  let state := execInstrBr state (.ADD .x10 .x10 .x11)
  let state := execInstrBr state (.ANDI .x10 .x10 255)
  let state := execInstrBr state (.LUI .x7 0x45)
  let state := execInstrBr state (.ADDI .x7 .x7 (-2048 + tree.val))
  execInstrBr state (.SB .x7 .x10 0)

theorem leafState_pc (tree : Fin 24) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val))) :
    (leafState tree state).pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val + 11)) := by
  simp [leafState, execInstrBr, pc, BitVec.ofNat_add_ofNat]
  congr 1

set_option maxHeartbeats 0 in
theorem leaf_block (tree : Fin 24) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val))) :
    OrdinarySteps SphincsImages.verify state 11 (leafState tree state) := by
  let s1 := execInstrBr state (.LUI .x6 0x42)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LBU .x10 .x6 (4 + tree.val))
  let s4 := execInstrBr s3 (.LBU .x11 .x6 (5 + tree.val))
  let s5 := execInstrBr s4 (.SRLI .x10 .x10 2)
  let s6 := execInstrBr s5 (.SLLI .x11 .x11 6)
  let s7 := execInstrBr s6 (.ADD .x10 .x10 .x11)
  let s8 := execInstrBr s7 (.ANDI .x10 .x10 255)
  let s9 := execInstrBr s8 (.LUI .x7 0x45)
  let s10 := execInstrBr s9 (.ADDI .x7 .x7 (-2048 + tree.val))
  let s11 := execInstrBr s10 (.SB .x7 .x10 0)
  have p1 : s1.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val + 1)) := by
    simp [s1, execInstrBr, pc, BitVec.ofNat_add_ofNat]
    congr 1
  have p2 : s2.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val + 2)) := by
    simp [s2, execInstrBr, p1, BitVec.ofNat_add_ofNat]
    congr 1
  have p3 : s3.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val + 3)) := by
    simp [s3, execInstrBr, p2, BitVec.ofNat_add_ofNat]
    congr 1
  have p4 : s4.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val + 4)) := by
    simp [s4, execInstrBr, p3, BitVec.ofNat_add_ofNat]
    congr 1
  have p5 : s5.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val + 5)) := by
    simp [s5, execInstrBr, p4, BitVec.ofNat_add_ofNat]
    congr 1
  have p6 : s6.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val + 6)) := by
    simp [s6, execInstrBr, p5, BitVec.ofNat_add_ofNat]
    congr 1
  have p7 : s7.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val + 7)) := by
    simp [s7, execInstrBr, p6, BitVec.ofNat_add_ofNat]
    congr 1
  have p8 : s8.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val + 8)) := by
    simp [s8, execInstrBr, p7, BitVec.ofNat_add_ofNat]
    congr 1
  have p9 : s9.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val + 9)) := by
    simp [s9, execInstrBr, p8, BitVec.ofNat_add_ofNat]
    congr 1
  have p10 : s10.pc = BitVec.ofNat 64
      (0x1000 + 4 * (180 + 11 * tree.val + 10)) := by
    simp [s10, execInstrBr, p9, BitVec.ofNat_add_ofNat]
    congr 1
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x42)) 10
  · simpa [leafInstructions] using leaf_fetch tree 0 state pc
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 9
  · simpa [leafInstructions] using leaf_fetch tree 1 s1 p1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LBU .x10 .x6 (4 + tree.val))) 8
  · simpa [leafInstructions] using leaf_fetch tree 2 s2 p2
  · fin_cases tree <;>
      simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid,
        execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LBU .x11 .x6 (5 + tree.val))) 7
  · simpa [leafInstructions] using leaf_fetch tree 3 s3 p3
  · fin_cases tree <;>
      simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid,
        execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SRLI .x10 .x10 2)) 6
  · simpa [leafInstructions] using leaf_fetch tree 4 s4 p4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SLLI .x11 .x11 6)) 5
  · simpa [leafInstructions] using leaf_fetch tree 5 s5 p5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x10 .x10 .x11)) 4
  · simpa [leafInstructions] using leaf_fetch tree 6 s6 p6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ANDI .x10 .x10 255)) 3
  · simpa [leafInstructions] using leaf_fetch tree 7 s7 p7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x7 0x45)) 2
  · simpa [leafInstructions] using leaf_fetch tree 8 s8 p8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x7 .x7 (-2048 + tree.val))) 1
  · simpa [leafInstructions] using leaf_fetch tree 9 s9 p9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.SB .x7 .x10 0)) 0
  · simpa [leafInstructions] using leaf_fetch tree 10 s10 p10
  · fin_cases tree <;>
      simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11,
        ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
        accessValid, rangeValid, MEMORY_BYTES,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem leaf_byte (tree : Fin 24) (state : MachineState) :
    (leafState tree state).getByte
      (BitVec.ofNat 64 (0x44800 + tree.val)) =
      (((((state.getByte (BitVec.ofNat 64 (0x42004 + tree.val))).zeroExtend 64) >>> 2) +
        (((state.getByte (BitVec.ofNat 64 (0x42005 + tree.val))).zeroExtend 64) <<< 6)) &&&
          255#64).truncate 8 := by
  fin_cases tree <;>
    simp [leafState, execInstrBr, signExtend12, getByte_setByte,
      Memory.getByte_setReg, getByte_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem selector_byte_nat (a b : BitVec 8) :
    (((((a.zeroExtend 64) >>> 2) + ((b.zeroExtend 64) <<< 6)) &&&
      255#64).truncate 8).toNat = (a.toNat / 4 + b.toNat * 64) % 256 := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_and,
    BitVec.toNat_add, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [show (255#64).toNat = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  norm_num
  omega

theorem leaf_byte_nat (tree : Fin 24) (state : MachineState) :
    ((leafState tree state).getByte
      (BitVec.ofNat 64 (0x44800 + tree.val))).toNat =
      (((state.getByte (BitVec.ofNat 64 (0x42004 + tree.val))).toNat / 4 +
        (state.getByte (BitVec.ofNat 64 (0x42005 + tree.val))).toNat * 64) % 256) := by
  rw [leaf_byte]
  exact selector_byte_nat _ _

/-- info: 'SigGolfCandidate.SphincsVerifierLeafCode.leaf_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leaf_code

/-- info: 'SigGolfCandidate.SphincsVerifierLeafCode.leaf_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leaf_block

/-- info: 'SigGolfCandidate.SphincsVerifierLeafCode.leaf_byte_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leaf_byte_nat

end SigGolfCandidate.SphincsVerifierLeafCode
