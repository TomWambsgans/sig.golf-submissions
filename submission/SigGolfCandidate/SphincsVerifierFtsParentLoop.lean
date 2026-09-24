import SigGolfCandidate.SphincsVerifierFtsParentLevel

/-! Check whether the FORS authentication path has completed eight parent levels. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsParentLevel
set_option maxRecDepth 16384

def levelCheckState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 72)
  let state := execInstrBr state (.LD .x6 .x28 0)
  execInstrBr state (.ADDI .x7 .x0 9)

theorem levelCheck_pc (state : MachineState) (pc : state.pc = 0x1b70) :
    (levelCheckState state).pc = 0x1b80 := by
  simp [levelCheckState, execInstrBr, pc]

theorem levelCheck_values (state : MachineState) :
    (levelCheckState state).getReg .x6 = state.getMem 0x43048 ∧
      (levelCheckState state).getReg .x7 = 9 := by
  simp [levelCheckState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem levelCheck_mem (state : MachineState) (address : Word) :
    (levelCheckState state).getMem address = state.getMem address := by
  simp [levelCheckState, execInstrBr]

theorem levelCheck_block (state : MachineState) (pc : state.pc = 0x1b70) :
    OrdinarySteps SphincsImages.verify state 4 (levelCheckState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 72)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 9)
  have p1 : s1.pc = 0x1b74 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1b78 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1b7c := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 732 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 72)) 2
  · rw [fetch_index SphincsImages.verify s1 733 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 734 (by decide)
      (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x0 9)) 0
  · rw [fetch_index SphincsImages.verify s3 735 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

def levelBranchState (state : MachineState) : MachineState :=
  execInstrBr state (.BNE .x6 .x7 (-620))

theorem levelBranch_mem (state : MachineState) (address : Word) :
    (levelBranchState state).getMem address = state.getMem address := by
  simp [levelBranchState, execInstrBr]

theorem levelBranch_block (state : MachineState) (pc : state.pc = 0x1b80) :
    OrdinarySteps SphincsImages.verify state 1 (levelBranchState state) := by
  apply OrdinarySteps.step state _ _ (.base (.BNE .x6 .x7 (-620))) 0
  · rw [fetch_index SphincsImages.verify state 736 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem levelBranch_pc_repeat (state : MachineState)
    (pc : state.pc = 0x1b80)
    (repeats : state.getReg .x6 ≠ state.getReg .x7) :
    (levelBranchState state).pc = 0x1914 := by
  simp [levelBranchState, execInstrBr, pc, repeats, signExtend13]

theorem levelBranch_pc_done (state : MachineState)
    (pc : state.pc = 0x1b80)
    (done : state.getReg .x6 = state.getReg .x7) :
    (levelBranchState state).pc = 0x1b84 := by
  simp [levelBranchState, execInstrBr, pc, done, signExtend13]

theorem firstParent_loopBack (state : MachineState)
    (pc : state.pc = 0x1b54)
    (level : state.getMem 0x43048 = 1) :
    let advanced := advanceLevelState state
    let checked := levelCheckState advanced
    let branched := levelBranchState checked
    OrdinarySteps SphincsImages.verify state 12 branched ∧
      branched.pc = 0x1914 ∧
      branched.getMem 0x43048 = 2 := by
  let advanced := advanceLevelState state
  let checked := levelCheckState advanced
  let branched := levelBranchState checked
  have first := advanceLevel_block state pc
  have nextPc := advanceLevel_pc state pc
  have second := levelCheck_block advanced nextPc
  have checkedPc := levelCheck_pc advanced nextPc
  have values := levelCheck_values advanced
  have advancedLevel : advanced.getMem 0x43048 = 2 := by
    rw [advanceLevel_cell, level]
    decide
  have unequal : checked.getReg .x6 ≠ checked.getReg .x7 := by
    rw [values.1, values.2, advancedLevel]
    decide
  have third := levelBranch_block checked checkedPc
  exact ⟨(first.append second).append third,
    levelBranch_pc_repeat checked checkedPc unequal,
    by rw [levelBranch_mem, levelCheck_mem]; exact advancedLevel⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentLoop.firstParent_loopBack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstParent_loopBack

end SigGolfCandidate.SphincsVerifierFtsParentLoop
