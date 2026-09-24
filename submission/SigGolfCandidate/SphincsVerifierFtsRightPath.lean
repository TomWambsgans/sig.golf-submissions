import SigGolfCandidate.SphincsVerifierFtsLevelBranch

/-! Start the right-oriented first FORS authentication-path level. -/

namespace SigGolfCandidate.SphincsVerifierFtsRightPath
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopy20DataGeneral
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
set_option maxRecDepth 16384

def rightPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 40)

theorem rightPointers_pc (state : MachineState)
    (pc : state.pc = 0x1928) :
    (rightPointers state).pc = 0x193c := by
  simp [rightPointers, execInstrBr, pc]

theorem rightPointers_regs (state : MachineState) :
    (rightPointers state).getReg .x6 = state.getMem 0x43028 ∧
      (rightPointers state).getReg .x7 = 0x40028 := by
  constructor <;>
    simp [rightPointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem rightPointers_mem (state : MachineState) (address : Word) :
    (rightPointers state).getMem address = state.getMem address := by
  simp [rightPointers, execInstrBr]

theorem rightPointers_block (state : MachineState)
    (pc : state.pc = 0x1928) :
    OrdinarySteps SphincsImages.verify state 5 (rightPointers state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 40)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x7 0x40)
  let s5 := execInstrBr s4 (.ADDI .x7 .x7 40)
  have p1 : s1.pc = 0x192c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1930 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1934 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1938 := by simp [s4, execInstrBr, p3]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 4
  · rw [fetch_index SphincsImages.verify state 586 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 40)) 3
  · rw [fetch_index SphincsImages.verify s1 587 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 2
  · rw [fetch_index SphincsImages.verify s2 588 (by decide)
      (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x7 0x40)) 1
  · rw [fetch_index SphincsImages.verify s3 589 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x7 .x7 40)) 0
  · rw [fetch_index SphincsImages.verify s4 590 (by decide)
      (by simpa using p4)]
    decide
  · rfl
  exact OrdinarySteps.refl _

set_option maxHeartbeats 0 in
theorem rightCopy_code : Copy20Code SphincsImages.verify 591 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

theorem rightCopy_block (state : MachineState)
    (pc : state.pc = 0x193c)
    (source : state.getReg .x6 = 0x22cf0)
    (destination : state.getReg .x7 = 0x40028) :
    OrdinarySteps SphincsImages.verify state 10
      (copyRootState state) := by
  apply copy20_block_general SphincsImages.verify 591 rightCopy_code state
    0x22cf0 0x40028 (by simpa using pc) source destination
  all_goals decide

theorem rightCopy_pc (state : MachineState) (pc : state.pc = 0x193c) :
    (copyRootState state).pc = 0x1964 := by
  simpa using copy20_final_pc state 591 (by simpa using pc)

theorem rightPath_from_parity (start : MachineState)
    (pc : (parityState start).pc = 0x1924)
    (odd : (parityState start).getReg .x6 ≠ 0)
    (pointer : start.getMem 0x43028 = 0x22cf0) :
    let parity := parityState start
    let branched := branchState parity
    let pointers := rightPointers branched
    let copied := copyRootState pointers
    OrdinarySteps SphincsImages.verify parity 16 copied ∧
      copied.pc = 0x1964 := by
  let parity := parityState start
  let branched := branchState parity
  let pointers := rightPointers branched
  have branchTrace := branch_block parity pc
  have branchPc := branch_pc_odd parity pc odd
  have pointerAtBranch : branched.getMem 0x43028 = 0x22cf0 := by
    rw [branch_mem, parity_mem]
    exact pointer
  have source : pointers.getReg .x6 = 0x22cf0 := by
    rw [(rightPointers_regs branched).1]
    exact pointerAtBranch
  have destination : pointers.getReg .x7 = 0x40028 :=
    (rightPointers_regs branched).2
  have pointerTrace := rightPointers_block branched branchPc
  have pointersPc := rightPointers_pc branched branchPc
  have copyTrace := rightCopy_block pointers pointersPc source destination
  exact ⟨(branchTrace.append pointerTrace).append copyTrace,
    rightCopy_pc pointers pointersPc⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRightPath.rightCopy_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rightCopy_block

end SigGolfCandidate.SphincsVerifierFtsRightPath
