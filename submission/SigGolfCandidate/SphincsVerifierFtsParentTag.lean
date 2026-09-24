import SigGolfCandidate.SphincsVerifierFtsLevelPosition

/-! Write the domain tag for the first FORS parent hash. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentTag
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierCopyMemory
set_option maxRecDepth 16384

@[simp] private theorem getWord32_setPC (state : MachineState) (pc address : Word) :
    (state.setPC pc).getWord32 address = state.getWord32 address := rfl

def parentTagBeforeStore (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x1)
  let state := execInstrBr state (.ADDI .x6 .x6 (-1535))
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 0)
  let state := execInstrBr state (.LD .x7 .x28 0)
  let state := execInstrBr state (.SLLI .x7 .x7 16)
  let state := execInstrBr state (.ADD .x6 .x6 .x7)
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 0)

def parentTagState (state : MachineState) : MachineState :=
  execInstrBr (parentTagBeforeStore state) (.SW .x7 .x6 0)

theorem parentTag_pc (state : MachineState)
    (pc : state.pc = 0x1a70) :
    (parentTagState state).pc = 0x1a98 := by
  simp [parentTagState, parentTagBeforeStore, execInstrBr, pc]

theorem parentTag_hash_pointer (state : MachineState) :
    (parentTagState state).getReg .x7 = 0x40000 := by
  simp [parentTagState, parentTagBeforeStore, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem parentTag_value (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0) :
    (parentTagState state).getWord32 0x40000 = 0xa01 := by
  simp [parentTagState, parentTagBeforeStore, execInstrBr,
    signExtend12, getWord32_setWord32_same,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  have zero : state.getMem (274432#64) = 0 := by
    have address : (274432#64) = (0x43000 : Word) := by decide
    rw [address]
    exact layerZero
  rw [zero]
  decide

theorem parentTag_mem_frame (state : MachineState) (address : Word)
    (outside : address ≠ alignToDword (0x40000#64)) :
    (parentTagState state).getMem address = state.getMem address := by
  simp [parentTagState, parentTagBeforeStore, execInstrBr,
    signExtend12, setWord32_eq, outside,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem parentTag_word_frame (state : MachineState) (address : Word)
    (outside : alignToDword address ≠ alignToDword (0x40000#64)) :
    (parentTagState state).getWord32 address =
      state.getWord32 address := by
  simp only [MachineState.getWord32]
  rw [parentTag_mem_frame state (alignToDword address) outside]

theorem parentTag_pair_data (state : MachineState) (index : Fin 5) :
    (parentTagState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x40028 + 4 * index.val)) ∧
    (parentTagState state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x4003c + 4 * index.val)) := by
  constructor <;> apply parentTag_word_frame <;>
    fin_cases index <;> decide

theorem parentTag_block (state : MachineState)
    (pc : state.pc = 0x1a70) :
    OrdinarySteps SphincsImages.verify state 10
      (parentTagState state) := by
  let s1 := execInstrBr state (.LUI .x6 0x1)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-1535))
  let s3 := execInstrBr s2 (.LUI .x28 0x43)
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 0)
  let s5 := execInstrBr s4 (.LD .x7 .x28 0)
  let s6 := execInstrBr s5 (.SLLI .x7 .x7 16)
  let s7 := execInstrBr s6 (.ADD .x6 .x6 .x7)
  let s8 := execInstrBr s7 (.LUI .x7 0x40)
  let s9 := execInstrBr s8 (.ADDI .x7 .x7 0)
  let s10 := execInstrBr s9 (.SW .x7 .x6 0)
  have p1 : s1.pc = 0x1a74 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1a78 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1a7c := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1a80 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1a84 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1a88 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x1a8c := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x1a90 := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x1a94 := by simp [s9, execInstrBr, p8]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x1)) 9
  · rw [fetch_index SphincsImages.verify state 668 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-1535))) 8
  · rw [fetch_index SphincsImages.verify s1 669 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x28 0x43)) 7
  · rw [fetch_index SphincsImages.verify s2 670 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x28 0)) 6
  · rw [fetch_index SphincsImages.verify s3 671 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x7 .x28 0)) 5
  · rw [fetch_index SphincsImages.verify s4 672 (by decide)
      (by simpa using p4)]
    decide
  · have pointer : s4.getReg .x28 = 0x43000 := by
      simp [s4, s3, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s5, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s5 s6 _ (.base (.SLLI .x7 .x7 16)) 4
  · rw [fetch_index SphincsImages.verify s5 673 (by decide)
      (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x6 .x6 .x7)) 3
  · rw [fetch_index SphincsImages.verify s6 674 (by decide)
      (by simpa using p6)]
    decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x7 0x40)) 2
  · rw [fetch_index SphincsImages.verify s7 675 (by decide)
      (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x7 .x7 0)) 1
  · rw [fetch_index SphincsImages.verify s8 676 (by decide)
      (by simpa using p8)]
    decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.SW .x7 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s9 677 (by decide)
      (by simpa using p9)]
    decide
  · have pointer : s9.getReg .x7 = 0x40000 := by
      simp [s9, s8, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s10, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem parentPosition_block (state : MachineState)
    (pc : state.pc = 0x1a98)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.positionState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 16)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SW .x7 .x6 4)
  have p1 : s1.pc = 0x1a9c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1aa0 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1aa4 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 678 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 16)) 2
  · rw [fetch_index SphincsImages.verify s1 679 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 680 (by decide)
      (by simpa using p2)]
    decide
  · have pointer : s2.getReg .x28 = 0x43010 := by
      simp [s2, s1, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SW .x7 .x6 4)) 0
  · rw [fetch_index SphincsImages.verify s3 681 (by decide)
      (by simpa using p3)]
    decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr, destination,
        MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem parentPosition_pc (state : MachineState)
    (pc : state.pc = 0x1a98) :
    (SphincsVerifierHeader.positionState state).pc = 0x1aa8 := by
  simp [SphincsVerifierHeader.positionState,
    SphincsVerifierHeader.positionBeforeStore, execInstrBr, pc]

theorem parentPosition_value (state : MachineState)
    (destination : state.getReg .x7 = 0x40000)
    (position : state.getMem 0x43010 = 1) :
    (SphincsVerifierHeader.positionState state).getWord32 0x40004 = 1 := by
  change state.getMem (274448#64) = 1 at position
  simp [SphincsVerifierHeader.positionState,
    SphincsVerifierHeader.positionBeforeStore, execInstrBr,
    signExtend12, getWord32_setWord32_same, destination,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, position]

theorem parentPosition_mem_frame (state : MachineState)
    (destination : state.getReg .x7 = 0x40000)
    (address : Word)
    (outside : address ≠ alignToDword (0x40004#64)) :
    (SphincsVerifierHeader.positionState state).getMem address =
      state.getMem address := by
  simp [SphincsVerifierHeader.positionState,
    SphincsVerifierHeader.positionBeforeStore, execInstrBr,
    signExtend12, setWord32_eq, destination, outside,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem parentPosition_preserve_tag (state : MachineState)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.positionState state).getWord32 0x40000 =
      state.getWord32 0x40000 := by
  simp only [SphincsVerifierHeader.positionState, execInstrBr,
    getWord32_setPC]
  rw [SphincsVerifierHeader.positionBeforeStore_pointer, destination]
  simp only [signExtend12]
  rw [show (0x40000 : Word) + BitVec.signExtend 64 4 = 0x40004 by decide]
  rw [getWord32_setWord32_other _ 0x40004 0x40000 _ (Or.inr (by decide))]
  simp only [MachineState.getWord32]
  rw [SphincsVerifierHeader.positionBeforeStore_memory]

theorem parentPosition_pair_data (state : MachineState)
    (destination : state.getReg .x7 = 0x40000) (index : Fin 5) :
    (SphincsVerifierHeader.positionState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x40028 + 4 * index.val)) ∧
    (SphincsVerifierHeader.positionState state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x4003c + 4 * index.val)) := by
  constructor <;> simp only [MachineState.getWord32] <;>
    rw [parentPosition_mem_frame state destination _ (by fin_cases index <;> decide)]

def parentPrefixState (state : MachineState) : MachineState :=
  SphincsVerifierHeader.positionState (parentTagState state)

theorem parentPrefix_values (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0)
    (positionOne : state.getMem 0x43010 = 1) :
    (parentPrefixState state).getWord32 0x40000 = 0xa01 ∧
      (parentPrefixState state).getWord32 0x40004 = 1 := by
  constructor
  · rw [parentPrefixState,
      parentPosition_preserve_tag _ (parentTag_hash_pointer state),
      parentTag_value state layerZero]
  · apply parentPosition_value _ (parentTag_hash_pointer state)
    rw [parentTag_mem_frame state 0x43010 (by decide)]
    exact positionOne

theorem parentPrefix_pair_data (state : MachineState) (index : Fin 5) :
    (parentPrefixState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x40028 + 4 * index.val)) ∧
    (parentPrefixState state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x4003c + 4 * index.val)) := by
  have h := parentPosition_pair_data (parentTagState state)
    (parentTag_hash_pointer state) index
  have t := parentTag_pair_data state index
  exact ⟨h.1.trans t.1, h.2.trans t.2⟩

theorem parentPrefix_block (state : MachineState)
    (pc : state.pc = 0x1a70) :
    OrdinarySteps SphincsImages.verify state 14
      (parentPrefixState state) ∧
      (parentPrefixState state).pc = 0x1aa8 := by
  let tagged := parentTagState state
  have tagTrace := parentTag_block state pc
  have tagPc := parentTag_pc state pc
  have positionTrace := parentPosition_block tagged tagPc
    (parentTag_hash_pointer state)
  exact ⟨tagTrace.append positionTrace,
    parentPosition_pc tagged tagPc⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentTag.parentPrefix_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentPrefix_block

end SigGolfCandidate.SphincsVerifierFtsParentTag
