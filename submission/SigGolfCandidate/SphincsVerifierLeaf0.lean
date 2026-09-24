import SigGolfCandidate.SphincsVerifierIndexStore
import RiscvZkvm.Rv64.Logic.MemRegionWrite

/-!
# First FORS leaf-selection instruction block

The verifier decodes the first eight-bit leaf selector from overlapping
message-digest bytes and stores it for the forest verification loop.
-/

namespace SigGolfCandidate.SphincsVerifierLeaf0
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierDigestDecode
open SigGolfCandidate.SphincsVerifierMessageHash

private theorem getByte_setPC (s : MachineState) (pc a : Word) :
    (s.setPC pc).getByte a = s.getByte a := by
  simp [MachineState.getByte]

@[simp] private theorem mem_setMem (s : MachineState) (a v b : Word) :
    (s.setMem a v).getMem b = if b = a then v else s.getMem b := by
  simp [MachineState.setMem, MachineState.getMem]

private theorem getByte_setByte (s : MachineState) (address : Word)
    (b : Byte) (a : Word) :
    (s.setByte address b).getByte a =
      if a = address then b else s.getByte a := by
  by_cases same : a = address
  · subst a
    simp only [MachineState.getByte, MachineState.setByte, mem_setMem, if_pos rfl]
    exact extractByte_replaceByte_same _ ⟨byteOffset address, byteOffset_lt_8⟩ b
  · rw [if_neg same]
    simp only [MachineState.getByte, MachineState.setByte, mem_setMem]
    by_cases aligned : alignToDword a = alignToDword address
    · rw [if_pos aligned]
      have offset : byteOffset a ≠ byteOffset address := by
        intro eq
        apply same
        rw [← alignToDword_add_byteOffset a,
          ← alignToDword_add_byteOffset address, aligned, eq]
      rw [extractByte_replaceByte_diff _ _ (byteOffset_lt_8)
        (byteOffset_lt_8) offset, aligned]
    · rw [if_neg aligned]

def leaf0State (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x42)
  let state := execInstrBr state (.ADDI .x6 .x6 0)
  let state := execInstrBr state (.LBU .x10 .x6 4)
  let state := execInstrBr state (.LBU .x11 .x6 5)
  let state := execInstrBr state (.SRLI .x10 .x10 2)
  let state := execInstrBr state (.SLLI .x11 .x11 6)
  let state := execInstrBr state (.ADD .x10 .x10 .x11)
  let state := execInstrBr state (.ANDI .x10 .x10 255)
  let state := execInstrBr state (.LUI .x7 0x45)
  let state := execInstrBr state (.ADDI .x7 .x7 (-2048))
  execInstrBr state (.SB .x7 .x10 0)

theorem leaf0_block (state : MachineState) (pc : state.pc = 0x12d0) :
    OrdinarySteps SphincsImages.verify state 11 (leaf0State state) := by
  let s1 := execInstrBr state (.LUI .x6 0x42)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LBU .x10 .x6 4)
  let s4 := execInstrBr s3 (.LBU .x11 .x6 5)
  let s5 := execInstrBr s4 (.SRLI .x10 .x10 2)
  let s6 := execInstrBr s5 (.SLLI .x11 .x11 6)
  let s7 := execInstrBr s6 (.ADD .x10 .x10 .x11)
  let s8 := execInstrBr s7 (.ANDI .x10 .x10 255)
  let s9 := execInstrBr s8 (.LUI .x7 0x45)
  let s10 := execInstrBr s9 (.ADDI .x7 .x7 (-2048))
  let s11 := execInstrBr s10 (.SB .x7 .x10 0)
  have p1 : s1.pc = 0x12d4 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x12d8 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x12dc := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x12e0 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x12e4 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x12e8 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x12ec := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x12f0 := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x12f4 := by simp [s9, execInstrBr, p8]
  have p10 : s10.pc = 0x12f8 := by simp [s10, execInstrBr, p9]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x42)) 10
  · rw [fetch_index SphincsImages.verify state 180 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 9
  · rw [fetch_index SphincsImages.verify s1 181 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LBU .x10 .x6 4)) 8
  · rw [fetch_index SphincsImages.verify s2 182 (by decide) (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LBU .x11 .x6 5)) 7
  · rw [fetch_index SphincsImages.verify s3 183 (by decide) (by simpa using p3)]
    decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SRLI .x10 .x10 2)) 6
  · rw [fetch_index SphincsImages.verify s4 184 (by decide) (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SLLI .x11 .x11 6)) 5
  · rw [fetch_index SphincsImages.verify s5 185 (by decide) (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x10 .x10 .x11)) 4
  · rw [fetch_index SphincsImages.verify s6 186 (by decide) (by simpa using p6)]
    decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ANDI .x10 .x10 255)) 3
  · rw [fetch_index SphincsImages.verify s7 187 (by decide) (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x7 0x45)) 2
  · rw [fetch_index SphincsImages.verify s8 188 (by decide) (by simpa using p8)]
    decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x7 .x7 (-2048))) 1
  · rw [fetch_index SphincsImages.verify s9 189 (by decide) (by simpa using p9)]
    decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.SB .x7 .x10 0)) 0
  · rw [fetch_index SphincsImages.verify s10 190 (by decide) (by simpa using p10)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11,
      ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem leaf0_byte (state : MachineState) :
    (leaf0State state).getByte 0x44800 =
      (((((state.getByte 0x42004).zeroExtend 64) >>> 2) +
        (((state.getByte 0x42005).zeroExtend 64) <<< 6)) &&& 255#64).truncate 8 := by
  simp [leaf0State, execInstrBr, signExtend12, getByte_setByte,
    Memory.getByte_setReg, getByte_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem indexStored_answer_byte4 (state : MachineState) :
    (indexStoredState state).getByte 0x42004 = state.getByte 0x42004 := by
  simp [indexStoredState, execInstrBr, signExtend12,
    MachineState.getByte, MachineState.getMem_setPC,
    MachineState.getMem_setReg, MachineState.getMem_setMem_ne,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    show alignToDword 270340#64 ≠ 274552#64 by decide,
    show alignToDword 270340#64 ≠ 274456#64 by decide]

theorem indexStored_answer_byte5 (state : MachineState) :
    (indexStoredState state).getByte 0x42005 = state.getByte 0x42005 := by
  simp [indexStoredState, execInstrBr, signExtend12,
    MachineState.getByte, MachineState.getMem_setPC,
    MachineState.getMem_setReg, MachineState.getMem_setMem_ne,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    show alignToDword 270341#64 ≠ 274552#64 by decide,
    show alignToDword 270341#64 ≠ 274456#64 by decide]

theorem indexValue_answer_byte (state : MachineState) (address : Word) :
    (indexValueState state).getByte address = state.getByte address := by
  simp [indexValueState, execInstrBr, Memory.getByte_setReg, getByte_setPC]

theorem leaf0_byte_nat (state : MachineState) :
    ((leaf0State state).getByte 0x44800).toNat =
      (((state.getByte 0x42004).toNat / 4 +
        (state.getByte 0x42005).toNat * 64) % 256) := by
  rw [leaf0_byte]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_and,
    BitVec.toNat_add, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [show (255#64).toNat = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  norm_num
  omega

theorem messageReady_leaf0 (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256) :
    let final := leaf0State (indexStoredState
      (indexValueState (writeHash state answer)))
    OrdinarySteps SphincsImages.verify (writeHash state answer) 22 final ∧
      (final.getByte 0x44800).toNat =
        (SphincsSecurity.Concrete.digestLeaves
          (SphincsSecurity.truncateMessageDigest answer)
          ⟨0, by simp [SphincsSecurity.ftsTrees]⟩).val := by
  obtain ⟨front, storedPc, _, _⟩ :=
    messageReady_indexStored state pk message randomness ready pc answer
  have suffix := leaf0_block _ storedPc
  have select := leaf0_byte_nat
    (indexStoredState (indexValueState (writeHash state answer)))
  rw [indexStored_answer_byte4, indexStored_answer_byte5,
    indexValue_answer_byte, indexValue_answer_byte] at select
  have decoded := messageReady_leaf_decode state pk message randomness
    ready answer ⟨0, by simp [SphincsSecurity.ftsTrees]⟩
  exact ⟨by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    front.append suffix,
    by simpa using select.trans (by simpa using decoded)⟩

/-- info: 'SigGolfCandidate.SphincsVerifierLeaf0.leaf0_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leaf0_block

/-- info: 'SigGolfCandidate.SphincsVerifierLeaf0.messageReady_leaf0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms messageReady_leaf0

end SigGolfCandidate.SphincsVerifierLeaf0
