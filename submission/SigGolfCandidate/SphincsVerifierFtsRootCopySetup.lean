import SigGolfCandidate.SphincsVerifierFtsRootCopyBytes

namespace SigGolfCandidate.SphincsVerifierFtsRootCopySetup
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def zeroLayer (state : MachineState) : MachineState :=
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  execInstrBr s3 (.SD .x28 .x6 0)

private theorem zeroLayer_block (state : MachineState)
    (pc : state.pc = 0x1c08) :
    OrdinarySteps SphincsImages.verify state 4 (zeroLayer state) := by
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  have p1 : s1.pc = 0x1c0c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1c10 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1c14 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · rw [fetch_index SphincsImages.verify state 770 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s1 771 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 772 (by decide) (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 (zeroLayer state) _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s3 773 (by decide) (by simpa using p3)]
    decide
  · simp [zeroLayer, s1, s2, s3, ordinaryStep, memoryArgumentsValid,
      accessValid, rangeValid, execInstrBr, signExtend12, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

def zeroTree (state : MachineState) : MachineState :=
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 8)
  execInstrBr s3 (.SD .x28 .x6 0)

private theorem zeroTree_block (state : MachineState)
    (pc : state.pc = 0x1c18) :
    OrdinarySteps SphincsImages.verify state 4 (zeroTree state) := by
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 8)
  have p1 : s1.pc = 0x1c1c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1c20 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1c24 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · rw [fetch_index SphincsImages.verify state 774 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s1 775 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 8)) 1
  · rw [fetch_index SphincsImages.verify s2 776 (by decide) (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 (zeroTree state) _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s3 777 (by decide) (by simpa using p3)]
    decide
  · simp [zeroTree, s1, s2, s3, ordinaryStep, memoryArgumentsValid,
      accessValid, rangeValid, execInstrBr, signExtend12, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _


def zeroPosition (state : MachineState) : MachineState :=
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 16)
  execInstrBr s3 (.SD .x28 .x6 0)

private theorem zeroPosition_block (state : MachineState)
    (pc : state.pc = 0x1c28) :
    OrdinarySteps SphincsImages.verify state 4 (zeroPosition state) := by
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 16)
  have p1 : s1.pc = 0x1c2c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1c30 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1c34 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · rw [fetch_index SphincsImages.verify state 778 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s1 779 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 16)) 1
  · rw [fetch_index SphincsImages.verify s2 780 (by decide) (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 (zeroPosition state) _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s3 781 (by decide) (by simpa using p3)]
    decide
  · simp [zeroPosition, s1, s2, s3, ordinaryStep, memoryArgumentsValid,
      accessValid, rangeValid, execInstrBr, signExtend12, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _


def zeroIndex (state : MachineState) : MachineState :=
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 24)
  execInstrBr s3 (.SD .x28 .x6 0)

private theorem zeroIndex_block (state : MachineState)
    (pc : state.pc = 0x1c38) :
    OrdinarySteps SphincsImages.verify state 4 (zeroIndex state) := by
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 24)
  have p1 : s1.pc = 0x1c3c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1c40 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1c44 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · rw [fetch_index SphincsImages.verify state 782 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s1 783 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 24)) 1
  · rw [fetch_index SphincsImages.verify s2 784 (by decide) (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 (zeroIndex state) _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s3 785 (by decide) (by simpa using p3)]
    decide
  · simp [zeroIndex, s1, s2, s3, ordinaryStep, memoryArgumentsValid,
      accessValid, rangeValid, execInstrBr, signExtend12, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

def clearHeaderState (state : MachineState) : MachineState :=
  zeroIndex (zeroPosition (zeroTree (zeroLayer state)))

private theorem clearHeader_block (state : MachineState)
    (pc : state.pc = 0x1c08) :
    OrdinarySteps SphincsImages.verify state 16 (clearHeaderState state) := by
  let s1 := zeroLayer state
  let s2 := zeroTree s1
  let s3 := zeroPosition s2
  have p1 : s1.pc = 0x1c18 := by simp [s1, zeroLayer, execInstrBr, pc]
  have p2 : s2.pc = 0x1c28 := by simp [s2, zeroTree, execInstrBr, p1]
  have p3 : s3.pc = 0x1c38 := by simp [s3, zeroPosition, execInstrBr, p2]
  have a := zeroLayer_block state pc
  have b := zeroTree_block s1 p1
  have c := zeroPosition_block s2 p2
  have d := zeroIndex_block s3 p3
  simpa only [clearHeaderState] using ((a.append b).append c).append d

private theorem clearHeader_pc (state : MachineState) :
    (clearHeaderState state).pc = state.pc + 64 := by
  simp [clearHeaderState, zeroIndex, zeroPosition, zeroTree, zeroLayer,
    execInstrBr, BitVec.add_assoc]


def copySetupState (state : MachineState) : MachineState :=
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 120)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x43)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 8)
  let s6 := execInstrBr s5 (.SD .x28 .x6 0)
  let s7 := execInstrBr s6 (.LUI .x6 0x44)
  let s8 := execInstrBr s7 (.ADDI .x6 .x6 256)
  let s9 := execInstrBr s8 (.LUI .x7 0x40)
  let s10 := execInstrBr s9 (.ADDI .x7 .x7 40)
  execInstrBr s10 (.ADDI .x10 .x0 60)

private theorem copySetup_block (state : MachineState)
    (pc : state.pc = 0x1c48) :
    OrdinarySteps SphincsImages.verify state 11 (copySetupState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 120)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x43)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 8)
  let s6 := execInstrBr s5 (.SD .x28 .x6 0)
  let s7 := execInstrBr s6 (.LUI .x6 0x44)
  let s8 := execInstrBr s7 (.ADDI .x6 .x6 256)
  let s9 := execInstrBr s8 (.LUI .x7 0x40)
  let s10 := execInstrBr s9 (.ADDI .x7 .x7 40)
  let s11 := execInstrBr s10 (.ADDI .x10 .x0 60)
  have p1 : s1.pc = 0x1c4c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1c50 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1c54 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1c58 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1c5c := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1c60 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x1c64 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x1c68 := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x1c6c := by simp [s9, execInstrBr, p8]
  have p10 : s10.pc = 0x1c70 := by simp [s10, execInstrBr, p9]
  have p11 : s11.pc = 0x1c74 := by simp [s11, execInstrBr, p10]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 10
  · rw [fetch_index SphincsImages.verify state 786 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 120)) 9
  · rw [fetch_index SphincsImages.verify s1 787 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 8
  · rw [fetch_index SphincsImages.verify s2 788 (by decide) (by simpa using p2)]
    decide
  · simp [copySetupState, s1, s2, s3, ordinaryStep, memoryArgumentsValid,
      accessValid, rangeValid, execInstrBr, signExtend12, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x43)) 7
  · rw [fetch_index SphincsImages.verify s3 789 (by decide) (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 8)) 6
  · rw [fetch_index SphincsImages.verify s4 790 (by decide) (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SD .x28 .x6 0)) 5
  · rw [fetch_index SphincsImages.verify s5 791 (by decide) (by simpa using p5)]
    decide
  · simp [copySetupState, s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid,
      accessValid, rangeValid, execInstrBr, signExtend12, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x6 0x44)) 4
  · rw [fetch_index SphincsImages.verify s6 792 (by decide) (by simpa using p6)]
    decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x6 .x6 256)) 3
  · rw [fetch_index SphincsImages.verify s7 793 (by decide) (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x7 0x40)) 2
  · rw [fetch_index SphincsImages.verify s8 794 (by decide) (by simpa using p8)]
    decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x7 .x7 40)) 1
  · rw [fetch_index SphincsImages.verify s9 795 (by decide) (by simpa using p9)]
    decide
  · rfl
  apply OrdinarySteps.step s10 (copySetupState state) _ (.base (.ADDI .x10 .x0 60)) 0
  · rw [fetch_index SphincsImages.verify s10 796 (by decide) (by simpa using p10)]
    decide
  · rfl
  exact OrdinarySteps.refl _

def rootCopyEntryState (state : MachineState) : MachineState :=
  copySetupState (clearHeaderState state)

theorem rootCopyEntry_header_cells (state : MachineState) :
    (rootCopyEntryState state).getMem 0x43000 = 0 ∧
    (rootCopyEntryState state).getMem 0x43010 = 0 ∧
    (rootCopyEntryState state).getMem 0x43018 = 0 ∧
    (rootCopyEntryState state).getMem 0x43008 =
      state.getMem 0x43078 := by
  simp [rootCopyEntryState, copySetupState, clearHeaderState,
    zeroLayer, zeroTree, zeroPosition, zeroIndex, execInstrBr,
    signExtend12, MachineState.getMem_setMem_eq,
    MachineState.getMem_setMem_ne, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootCopySetup.rootCopyEntry_header_cells' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rootCopyEntry_header_cells

/-- From the final FORS root store to the first copy-loop instruction. -/
theorem rootCopyEntry (state : MachineState)
    (pc : state.pc = 0x1c08) :
    OrdinarySteps SphincsImages.verify state 27 (rootCopyEntryState state) ∧
      (rootCopyEntryState state).pc = 0x1c74 ∧
      (rootCopyEntryState state).getReg .x6 = 0x44100 ∧
      (rootCopyEntryState state).getReg .x7 = 0x40028 ∧
      (rootCopyEntryState state).getReg .x10 = 60 := by
  have first := clearHeader_block state pc
  have middlePc : (clearHeaderState state).pc = 0x1c48 := by
    rw [clearHeader_pc, pc]
    decide
  have second := copySetup_block (clearHeaderState state) middlePc
  refine ⟨by simpa only [rootCopyEntryState] using first.append second,
    ?_, ?_, ?_, ?_⟩
  · simp [rootCopyEntryState, copySetupState, execInstrBr, middlePc]
  · simp [rootCopyEntryState, copySetupState, execInstrBr,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    decide
  · simp [rootCopyEntryState, copySetupState, execInstrBr,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    decide
  · simp [rootCopyEntryState, copySetupState, execInstrBr,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    decide

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootCopySetup.rootCopyEntry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootCopyEntry

end SigGolfCandidate.SphincsVerifierFtsRootCopySetup
