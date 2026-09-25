import SigGolfCandidate.SphincsVerifierWotsStepCheck
import SigGolfCandidate.SphincsVerifierFtsCopyAccess

namespace SigGolfCandidate.SphincsVerifierWotsStepBody
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def stepValuePointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x45)
  let state := execInstrBr state (.ADDI .x6 .x6 (-1280))
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 40)

theorem stepValuePointers_block (state : MachineState)
    (pc : state.pc = 0x2788) :
    OrdinarySteps SphincsImages.verify state 4
      (stepValuePointers state) ∧
    (stepValuePointers state).pc = 0x2798 ∧
    (stepValuePointers state).getReg .x6 = 0x44b00 ∧
    (stepValuePointers state).getReg .x7 = 0x40028 := by
  let s1 := execInstrBr state (.LUI .x6 0x45)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-1280))
  let s3 := execInstrBr s2 (.LUI .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 40)
  have p1 : s1.pc = 0x278c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x2790 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x2794 := by simp [s3, execInstrBr, p2]
  have trace : OrdinarySteps SphincsImages.verify state 4 s4 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x45)) 3
    · rw [fetch_index SphincsImages.verify state 1506 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-1280))) 2
    · rw [fetch_index SphincsImages.verify s1 1507 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x40)) 1
    · rw [fetch_index SphincsImages.verify s2 1508 (by decide)
        (by simpa using p2)]
      decide
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 40)) 0
    · rw [fetch_index SphincsImages.verify s3 1509 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [stepValuePointers] using trace, ?_, ?_, ?_⟩
  · simp [stepValuePointers, execInstrBr, pc]
  · simp [stepValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  · simp [stepValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]

theorem step_value_copy_code : Copy20Code SphincsImages.verify 1510 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

def stepValueCopied (state : MachineState) : MachineState :=
  copyRootState (stepValuePointers state)

theorem stepValueCopied_block (state : MachineState)
    (pc : state.pc = 0x2788) :
    OrdinarySteps SphincsImages.verify state 14
      (stepValueCopied state) ∧
    (stepValueCopied state).pc = 0x27c0 := by
  obtain ⟨pre, prePc, source, destination⟩ :=
    stepValuePointers_block state pc
  have copy := copy20_block_general SphincsImages.verify 1510
    step_value_copy_code (stepValuePointers state)
    0x44b00 0x40028 (by simpa using prePc)
    source destination (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine ⟨by simpa only [stepValueCopied] using pre.append copy, ?_⟩
  exact copy20_final_pc (stepValuePointers state) 1510
    (by simpa using prePc)

def stepPositionState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 80)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.SLLI .x6 .x6 3)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 88)
  let state := execInstrBr state (.LD .x7 .x28 0)
  let state := execInstrBr state (.ADD .x6 .x6 .x7)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 16)
  execInstrBr state (.SD .x28 .x6 0)

theorem stepPosition_block (state : MachineState)
    (pc : state.pc = 0x27c0) :
    OrdinarySteps SphincsImages.verify state 11
      (stepPositionState state) ∧
    (stepPositionState state).pc = 0x27ec := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 80)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x6 .x6 3)
  let s5 := execInstrBr s4 (.LUI .x28 0x43)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 88)
  let s7 := execInstrBr s6 (.LD .x7 .x28 0)
  let s8 := execInstrBr s7 (.ADD .x6 .x6 .x7)
  let s9 := execInstrBr s8 (.LUI .x28 0x43)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 16)
  let s11 := execInstrBr s10 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x27c4 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x27c8 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x27cc := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x27d0 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x27d4 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x27d8 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x27dc := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x27e0 := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x27e4 := by simp [s9, execInstrBr, p8]
  have p10 : s10.pc = 0x27e8 := by simp [s10, execInstrBr, p9]
  have p11 : s11.pc = 0x27ec := by simp [s11, execInstrBr, p10]
  have trace : OrdinarySteps SphincsImages.verify state 11 s11 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 10
    · rw [fetch_index SphincsImages.verify state 1520 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 80)) 9
    · rw [fetch_index SphincsImages.verify s1 1521 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 8
    · rw [fetch_index SphincsImages.verify s2 1522 (by decide)
        (by simpa using p2)]
      decide
    · simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s2, s1,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x6 .x6 3)) 7
    · rw [fetch_index SphincsImages.verify s3 1523 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x43)) 6
    · rw [fetch_index SphincsImages.verify s4 1524 (by decide)
        (by simpa using p4)]
      decide
    · rfl
    apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 88)) 5
    · rw [fetch_index SphincsImages.verify s5 1525 (by decide)
        (by simpa using p5)]
      decide
    · rfl
    apply OrdinarySteps.step s6 s7 _ (.base (.LD .x7 .x28 0)) 4
    · rw [fetch_index SphincsImages.verify s6 1526 (by decide)
        (by simpa using p6)]
      decide
    · simp [s7, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s6, s5,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    apply OrdinarySteps.step s7 s8 _ (.base (.ADD .x6 .x6 .x7)) 3
    · rw [fetch_index SphincsImages.verify s7 1527 (by decide)
        (by simpa using p7)]
      decide
    · rfl
    apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 0x43)) 2
    · rw [fetch_index SphincsImages.verify s8 1528 (by decide)
        (by simpa using p8)]
      decide
    · rfl
    apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 16)) 1
    · rw [fetch_index SphincsImages.verify s9 1529 (by decide)
        (by simpa using p9)]
      decide
    · rfl
    apply OrdinarySteps.step s10 s11 _ (.base (.SD .x28 .x6 0)) 0
    · rw [fetch_index SphincsImages.verify s10 1530 (by decide)
        (by simpa using p10)]
      decide
    · simp [s11, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s10, s9,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    exact OrdinarySteps.refl _
  exact ⟨by simpa only [stepPositionState] using trace,
    by simpa only [stepPositionState] using p11⟩

def stepHashPrefixState (state : MachineState) : MachineState :=
  stepPositionState (stepValueCopied state)

theorem stepHashPrefix_block (state : MachineState)
    (pc : state.pc = 0x2788) :
    OrdinarySteps SphincsImages.verify state 25
      (stepHashPrefixState state) ∧
    (stepHashPrefixState state).pc = 0x27ec := by
  have copied := stepValueCopied_block state pc
  have position := stepPosition_block (stepValueCopied state) copied.2
  refine ⟨?_, position.2⟩
  simpa [stepHashPrefixState] using copied.1.append position.1

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepBody.stepValueCopied_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepValueCopied_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepBody.stepPosition_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepPosition_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepBody.stepHashPrefix_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepHashPrefix_block

end SigGolfCandidate.SphincsVerifierWotsStepBody
