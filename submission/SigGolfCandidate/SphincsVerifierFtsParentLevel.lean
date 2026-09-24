import SigGolfCandidate.SphincsVerifierFtsParentResult

/-! Increment the FORS authentication level after the first parent HASH. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentLevel
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
set_option maxRecDepth 16384

def advanceLevelState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 72)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.ADDI .x6 .x6 1)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 72)
  execInstrBr state (.SD .x28 .x6 0)

theorem advanceLevel_pc (state : MachineState)
    (pc : state.pc = 0x1b54) :
    (advanceLevelState state).pc = 0x1b70 := by
  simp [advanceLevelState, execInstrBr, pc]

theorem advanceLevel_cell (state : MachineState) :
    (advanceLevelState state).getMem 0x43048 =
      state.getMem 0x43048 + 1 := by
  simp [advanceLevelState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem advanceLevel_mem_frame (state : MachineState) (address : Word)
    (outside : address ≠ 0x43048) :
    (advanceLevelState state).getMem address =
      state.getMem address := by
  change address ≠ (274504#64) at outside
  simp [advanceLevelState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne, outside,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem advanceLevel_word_frame (state : MachineState) (address : Word)
    (outside : alignToDword address ≠ 0x43048) :
    (advanceLevelState state).getWord32 address =
      state.getWord32 address := by
  simp only [MachineState.getWord32]
  rw [advanceLevel_mem_frame state (alignToDword address) outside]

theorem advanceLevel_pair_data (state : MachineState) (index : Fin 5) :
    (advanceLevelState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x40028 + 4 * index.val)) ∧
    (advanceLevelState state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x4003c + 4 * index.val)) := by
  constructor <;> apply advanceLevel_word_frame <;>
    fin_cases index <;> decide

theorem advanceLevel_block (state : MachineState)
    (pc : state.pc = 0x1b54) :
    OrdinarySteps SphincsImages.verify state 7
      (advanceLevelState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 72)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1)
  let s5 := execInstrBr s4 (.LUI .x28 0x43)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 72)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x1b58 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1b5c := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1b60 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1b64 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1b68 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1b6c := by simp [s6, execInstrBr, p5]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 6
  · rw [fetch_index SphincsImages.verify state 725 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 72)) 5
  · rw [fetch_index SphincsImages.verify s1 726 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 4
  · rw [fetch_index SphincsImages.verify s2 727 (by decide)
      (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1)) 3
  · rw [fetch_index SphincsImages.verify s3 728 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s4 729 (by decide)
      (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 72)) 1
  · rw [fetch_index SphincsImages.verify s5 730 (by decide)
      (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s6 731 (by decide)
      (by simpa using p6)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep,
      memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentLevel.advanceLevel_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms advanceLevel_block

end SigGolfCandidate.SphincsVerifierFtsParentLevel
