import SigGolfCandidate.SphincsVerifierFtsPair

/-! Advance the FORS witness pointer after assembling the first parent pair. -/

namespace SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsPair
set_option maxRecDepth 16384

def advancePointerState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.ADDI .x6 .x6 20)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  execInstrBr state (.SD .x28 .x6 0)

theorem advancePointer_pc (state : MachineState)
    (pc : state.pc = 0x1a14) :
    (advancePointerState state).pc = 0x1a30 := by
  simp [advancePointerState, execInstrBr, pc]

theorem advancePointer_cell (state : MachineState) :
    (advancePointerState state).getMem 0x43028 =
      state.getMem 0x43028 + 20 := by
  simp [advancePointerState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem advancePointer_mem_frame (state : MachineState) (address : Word)
    (outside : address ≠ 0x43028) :
    (advancePointerState state).getMem address =
      state.getMem address := by
  change address ≠ (274472#64) at outside
  simp [advancePointerState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne, outside,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem advancePointer_word_frame (state : MachineState) (address : Word)
    (outside : alignToDword address ≠ 0x43028) :
    (advancePointerState state).getWord32 address =
      state.getWord32 address := by
  simp only [MachineState.getWord32]
  rw [advancePointer_mem_frame state (alignToDword address) outside]

theorem advancePointer_pair_data (state : MachineState) (index : Fin 5) :
    (advancePointerState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x40028 + 4 * index.val)) ∧
    (advancePointerState state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x4003c + 4 * index.val)) := by
  constructor <;> apply advancePointer_word_frame <;>
    fin_cases index <;> decide

theorem advancePointer_block (state : MachineState)
    (pc : state.pc = 0x1a14) :
    OrdinarySteps SphincsImages.verify state 7
      (advancePointerState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 40)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 20)
  let s5 := execInstrBr s4 (.LUI .x28 0x43)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 40)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x1a18 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1a1c := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1a20 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1a24 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1a28 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1a2c := by simp [s6, execInstrBr, p5]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 6
  · rw [fetch_index SphincsImages.verify state 645 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 40)) 5
  · rw [fetch_index SphincsImages.verify s1 646 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 4
  · rw [fetch_index SphincsImages.verify s2 647 (by decide)
      (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 20)) 3
  · rw [fetch_index SphincsImages.verify s3 648 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s4 649 (by decide)
      (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 40)) 1
  · rw [fetch_index SphincsImages.verify s5 650 (by decide)
      (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s6 651 (by decide)
      (by simpa using p6)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep,
      memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem pair_advance_pointer (start : MachineState)
    (pc : start.pc = 0x1914)
    (pointer : start.getMem 0x43028 = 0x22cf0) :
    let pair := pairState start
    let advanced := advancePointerState pair
    OrdinarySteps SphincsImages.verify pair 7 advanced ∧
      advanced.pc = 0x1a30 ∧
      advanced.getMem 0x43028 = 0x22d04 := by
  have pair := pair_from_level_start start pc pointer
  have pointerAtPair : (pairState start).getMem 0x43028 = 0x22cf0 := by
    rw [pair_pointer_frame]
    exact pointer
  exact ⟨advancePointer_block _ pair.2,
    advancePointer_pc _ pair.2,
    by rw [advancePointer_cell, pointerAtPair]; decide⟩

end SigGolfCandidate.SphincsVerifierFtsPairAdvance
