import SigGolfCandidate.SphincsVerifierFtsLevelShift

/-! Record the current FORS authentication-path level as the parent-hash position. -/

namespace SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
set_option maxRecDepth 16384

def levelPositionState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 72)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 16)
  execInstrBr state (.SD .x28 .x6 0)

theorem levelPosition_pc (state : MachineState)
    (pc : state.pc = 0x1a58) :
    (levelPositionState state).pc = 0x1a70 := by
  simp [levelPositionState, execInstrBr, pc]

theorem levelPosition_cell (state : MachineState) :
    (levelPositionState state).getMem 0x43010 =
      state.getMem 0x43048 := by
  simp [levelPositionState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem levelPosition_mem_frame (state : MachineState) (address : Word)
    (outside : address ≠ 0x43010) :
    (levelPositionState state).getMem address = state.getMem address := by
  change address ≠ (274448#64) at outside
  simp [levelPositionState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne, outside,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem levelPosition_word_frame (state : MachineState) (address : Word)
    (outside : alignToDword address ≠ 0x43010) :
    (levelPositionState state).getWord32 address =
      state.getWord32 address := by
  simp only [MachineState.getWord32]
  rw [levelPosition_mem_frame state (alignToDword address) outside]

theorem levelPosition_pair_data (state : MachineState) (index : Fin 5) :
    (levelPositionState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x40028 + 4 * index.val)) ∧
    (levelPositionState state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x4003c + 4 * index.val)) := by
  constructor <;> apply levelPosition_word_frame <;>
    fin_cases index <;> decide

theorem levelPosition_block (state : MachineState)
    (pc : state.pc = 0x1a58) :
    OrdinarySteps SphincsImages.verify state 6
      (levelPositionState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 72)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x43)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 16)
  let s6 := execInstrBr s5 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x1a5c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1a60 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1a64 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1a68 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1a6c := by simp [s5, execInstrBr, p4]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 5
  · rw [fetch_index SphincsImages.verify state 662 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 72)) 4
  · rw [fetch_index SphincsImages.verify s1 663 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 3
  · rw [fetch_index SphincsImages.verify s2 664 (by decide)
      (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s3 665 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 16)) 1
  · rw [fetch_index SphincsImages.verify s4 666 (by decide)
      (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s5 667 (by decide)
      (by simpa using p5)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep,
      memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem firstLevelPosition (start : MachineState)
    (pc : start.pc = 0x1914)
    (pointer : start.getMem 0x43028 = 0x22cf0)
    (level : start.getMem 0x43048 = 1) :
    let pair := pairState start
    let advanced := advancePointerState pair
    let shifted := shiftIndexState advanced
    let positioned := levelPositionState shifted
    OrdinarySteps SphincsImages.verify pair 23 positioned ∧
      positioned.pc = 0x1a70 ∧
      positioned.getMem 0x43028 = 0x22d04 ∧
      positioned.getMem 0x43010 = 1 ∧
      positioned.getMem 0x43070 = start.getMem 0x43070 >>> 1 ∧
      positioned.getMem 0x43018 = start.getMem 0x43070 >>> 1 := by
  let pair := pairState start
  let advanced := advancePointerState pair
  let shifted := shiftIndexState advanced
  have front := pair_shift_index start pc pointer
  have back := levelPosition_block shifted front.2.1
  have shiftedLevel : shifted.getMem 0x43048 = 1 := by
    rw [shiftIndex_mem_frame _ 0x43048 (by decide) (by decide),
      advancePointer_mem_frame _ 0x43048 (by decide),
      pair_level_frame]
    exact level
  have shiftedBit : shifted.getMem 0x43070 =
      start.getMem 0x43070 >>> 1 := by
    rw [front.2.2.2.1,
      advancePointer_mem_frame _ 0x43070 (by decide),
      pair_selector_frame]
  have shiftedIndex : shifted.getMem 0x43018 =
      start.getMem 0x43070 >>> 1 := by
    rw [front.2.2.2.2,
      advancePointer_mem_frame _ 0x43070 (by decide),
      pair_selector_frame]
  exact ⟨front.1.append back,
    levelPosition_pc shifted front.2.1,
    by rw [levelPosition_mem_frame _ 0x43028 (by decide)];
       exact front.2.2.1,
    by rw [levelPosition_cell]; exact shiftedLevel,
    by rw [levelPosition_mem_frame _ 0x43070 (by decide)];
       exact shiftedBit,
    by rw [levelPosition_mem_frame _ 0x43018 (by decide)];
       exact shiftedIndex⟩

end SigGolfCandidate.SphincsVerifierFtsLevelPosition
