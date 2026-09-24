import SigGolfCandidate.SphincsVerifierFtsPairAdvance

/-! Shift the first FORS selector and store the parent-node index. -/

namespace SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsPair
set_option maxRecDepth 16384

def shiftIndexState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 112)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.SRLI .x6 .x6 1)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 112)
  let state := execInstrBr state (.SD .x28 .x6 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 24)
  execInstrBr state (.SD .x28 .x6 0)

theorem shiftIndex_pc (state : MachineState)
    (pc : state.pc = 0x1a30) :
    (shiftIndexState state).pc = 0x1a58 := by
  simp [shiftIndexState, execInstrBr, pc]

theorem shiftIndex_cells (state : MachineState) :
    (shiftIndexState state).getMem 0x43070 =
      state.getMem 0x43070 >>> 1 ∧
    (shiftIndexState state).getMem 0x43018 =
      state.getMem 0x43070 >>> 1 := by
  constructor <;>
    simp [shiftIndexState, execInstrBr, signExtend12,
      MachineState.getMem_setMem_ne,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem shiftIndex_mem_frame (state : MachineState) (address : Word)
    (notBit : address ≠ 0x43070) (notIndex : address ≠ 0x43018) :
    (shiftIndexState state).getMem address = state.getMem address := by
  change address ≠ (274544#64) at notBit
  change address ≠ (274456#64) at notIndex
  simp [shiftIndexState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne, notBit, notIndex,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem shiftIndex_word_frame (state : MachineState) (address : Word)
    (notBit : alignToDword address ≠ 0x43070)
    (notIndex : alignToDword address ≠ 0x43018) :
    (shiftIndexState state).getWord32 address =
      state.getWord32 address := by
  simp only [MachineState.getWord32]
  rw [shiftIndex_mem_frame state (alignToDword address) notBit notIndex]

theorem shiftIndex_pair_data (state : MachineState) (index : Fin 5) :
    (shiftIndexState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x40028 + 4 * index.val)) ∧
    (shiftIndexState state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x4003c + 4 * index.val)) := by
  constructor <;> apply shiftIndex_word_frame <;>
    fin_cases index <;> decide

theorem shiftIndex_block (state : MachineState)
    (pc : state.pc = 0x1a30) :
    OrdinarySteps SphincsImages.verify state 10
      (shiftIndexState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 112)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SRLI .x6 .x6 1)
  let s5 := execInstrBr s4 (.LUI .x28 0x43)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 112)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.LUI .x28 0x43)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 24)
  let s10 := execInstrBr s9 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x1a34 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1a38 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1a3c := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1a40 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1a44 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1a48 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x1a4c := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x1a50 := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x1a54 := by simp [s9, execInstrBr, p8]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 9
  · rw [fetch_index SphincsImages.verify state 652 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 112)) 8
  · rw [fetch_index SphincsImages.verify s1 653 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 7
  · rw [fetch_index SphincsImages.verify s2 654 (by decide)
      (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SRLI .x6 .x6 1)) 6
  · rw [fetch_index SphincsImages.verify s3 655 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x43)) 5
  · rw [fetch_index SphincsImages.verify s4 656 (by decide)
      (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 112)) 4
  · rw [fetch_index SphincsImages.verify s5 657 (by decide)
      (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 3
  · rw [fetch_index SphincsImages.verify s6 658 (by decide)
      (by simpa using p6)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep,
      memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s7 659 (by decide)
      (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 24)) 1
  · rw [fetch_index SphincsImages.verify s8 660 (by decide)
      (by simpa using p8)]
    decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s9 661 (by decide)
      (by simpa using p9)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
      ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem pair_shift_index (start : MachineState)
    (pc : start.pc = 0x1914)
    (pointer : start.getMem 0x43028 = 0x22cf0) :
    let pair := pairState start
    let advanced := advancePointerState pair
    let shifted := shiftIndexState advanced
    OrdinarySteps SphincsImages.verify pair 17 shifted ∧
      shifted.pc = 0x1a58 ∧
      shifted.getMem 0x43028 = 0x22d04 ∧
      shifted.getMem 0x43070 = advanced.getMem 0x43070 >>> 1 ∧
      shifted.getMem 0x43018 = advanced.getMem 0x43070 >>> 1 := by
  let pair := pairState start
  let advanced := advancePointerState pair
  have front := pair_advance_pointer start pc pointer
  have back := shiftIndex_block advanced front.2.1
  have cells := shiftIndex_cells advanced
  exact ⟨front.1.append back,
    shiftIndex_pc advanced front.2.1,
    by rw [shiftIndex_mem_frame _ 0x43028 (by decide) (by decide)];
       exact front.2.2,
    cells.1, cells.2⟩

end SigGolfCandidate.SphincsVerifierFtsLevelShift
