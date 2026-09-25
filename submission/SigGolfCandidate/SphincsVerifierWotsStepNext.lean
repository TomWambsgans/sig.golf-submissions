import SigGolfCandidate.SphincsVerifierWotsStepHash

namespace SigGolfCandidate.SphincsVerifierWotsStepNext
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def stepAnswerPointersState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x42)
  let state := execInstrBr state (.ADDI .x6 .x6 0)
  let state := execInstrBr state (.LUI .x7 0x45)
  execInstrBr state (.ADDI .x7 .x7 (-1280))

theorem stepAnswerPointers_block (state : MachineState)
    (pc : state.pc = 0x2894) :
    OrdinarySteps SphincsImages.verify state 4
      (stepAnswerPointersState state) ∧
    (stepAnswerPointersState state).pc = 0x28a4 ∧
    (stepAnswerPointersState state).getReg .x6 = 0x42000 ∧
    (stepAnswerPointersState state).getReg .x7 = 0x44b00 := by
  let s1 := execInstrBr state (.LUI .x6 0x42)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LUI .x7 0x45)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 (-1280))
  have p1 : s1.pc = 0x2898 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x289c := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x28a0 := by simp [s3, execInstrBr, p2]
  have trace : OrdinarySteps SphincsImages.verify state 4 s4 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x42)) 3
    · rw [fetch_index SphincsImages.verify state 1573 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 2
    · rw [fetch_index SphincsImages.verify s1 1574 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x45)) 1
    · rw [fetch_index SphincsImages.verify s2 1575 (by decide)
        (by simpa using p2)]
      decide
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 (-1280))) 0
    · rw [fetch_index SphincsImages.verify s3 1576 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [stepAnswerPointersState] using trace, ?_, ?_, ?_⟩
  · simp [stepAnswerPointersState, execInstrBr, pc]
  · simp [stepAnswerPointersState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  · simp [stepAnswerPointersState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]

theorem step_answer_copy_code : Copy20Code SphincsImages.verify 1577 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

def stepAnswerCopyState (state : MachineState) : MachineState :=
  copyRootState (stepAnswerPointersState state)

theorem stepAnswerCopy_block (state : MachineState)
    (pc : state.pc = 0x2894) :
    OrdinarySteps SphincsImages.verify state 14
      (stepAnswerCopyState state) ∧
    (stepAnswerCopyState state).pc = 0x28cc := by
  obtain ⟨pointers, pointerPc, source, destination⟩ :=
    stepAnswerPointers_block state pc
  have copy := copy20_block_general SphincsImages.verify 1577
    step_answer_copy_code (stepAnswerPointersState state)
    0x42000 0x44b00 (by simpa using pointerPc)
    source destination (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine ⟨by simpa only [stepAnswerCopyState] using pointers.append copy,
    ?_⟩
  exact copy20_final_pc (stepAnswerPointersState state) 1577
    (by simpa using pointerPc)

def stepAdvanceState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 88)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.ADDI .x6 .x6 1)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 88)
  execInstrBr state (.SD .x28 .x6 0)

theorem stepAdvance_block (state : MachineState)
    (pc : state.pc = 0x28cc) :
    OrdinarySteps SphincsImages.verify state 7
      (stepAdvanceState state) ∧
    (stepAdvanceState state).pc = 0x28e8 := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 88)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1)
  let s5 := execInstrBr s4 (.LUI .x28 0x43)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 88)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x28d0 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x28d4 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x28d8 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x28dc := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x28e0 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x28e4 := by simp [s6, execInstrBr, p5]
  have trace : OrdinarySteps SphincsImages.verify state 7 s7 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 6
    · rw [fetch_index SphincsImages.verify state 1587 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 88)) 5
    · rw [fetch_index SphincsImages.verify s1 1588 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 4
    · rw [fetch_index SphincsImages.verify s2 1589 (by decide)
        (by simpa using p2)]
      decide
    · simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s2, s1,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1)) 3
    · rw [fetch_index SphincsImages.verify s3 1590 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x43)) 2
    · rw [fetch_index SphincsImages.verify s4 1591 (by decide)
        (by simpa using p4)]
      decide
    · rfl
    apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 88)) 1
    · rw [fetch_index SphincsImages.verify s5 1592 (by decide)
        (by simpa using p5)]
      decide
    · rfl
    apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 0
    · rw [fetch_index SphincsImages.verify s6 1593 (by decide)
        (by simpa using p6)]
      decide
    · simp [s7, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s6, s5,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    exact OrdinarySteps.refl _
  exact ⟨by simpa only [stepAdvanceState] using trace,
    by simpa only [stepAdvanceState] using
      (show s7.pc = 0x28e8 by simp [s7, execInstrBr, p6])⟩

theorem stepAdvance_cell (state : MachineState) :
    (stepAdvanceState state).getMem 0x43058 =
      state.getMem 0x43058 + 1 := by
  simp [stepAdvanceState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def stepReturnState (state : MachineState) : MachineState :=
  execInstrBr (stepAdvanceState state) (.JAL .x0 (-372))

theorem stepReturn_block (state : MachineState)
    (pc : state.pc = 0x28cc) :
    OrdinarySteps SphincsImages.verify state 8
      (stepReturnState state) ∧
    (stepReturnState state).pc = 0x2774 := by
  have advance := stepAdvance_block state pc
  have jump : OrdinarySteps SphincsImages.verify
      (stepAdvanceState state) 1 (stepReturnState state) := by
    apply OrdinarySteps.step (stepAdvanceState state)
      (stepReturnState state) _ (.base (.JAL .x0 (-372))) 0
    · rw [fetch_index SphincsImages.verify (stepAdvanceState state)
        1594 (by decide) (by simpa using advance.2)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  exact ⟨by simpa only [stepReturnState] using advance.1.append jump,
    by simp [stepReturnState, execInstrBr, advance.2, signExtend21]⟩

theorem stepReturn_cell (state : MachineState) :
    (stepReturnState state).getMem 0x43058 =
      state.getMem 0x43058 + 1 := by
  simpa [stepReturnState, execInstrBr] using stepAdvance_cell state

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepNext.stepAnswerCopy_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepAnswerCopy_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepNext.stepReturn_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepReturn_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepNext.stepReturn_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepReturn_cell

end SigGolfCandidate.SphincsVerifierWotsStepNext
