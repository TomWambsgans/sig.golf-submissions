import SigGolfCandidate.SphincsVerifierFtsRootStoreData

/-! Increment the FORS tree counter and branch to the next tree. -/

namespace SigGolfCandidate.SphincsVerifierFtsTreeAdvance
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierMessageCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def treeAdvanceState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 64)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.ADDI .x6 .x6 1)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 64)
  let state := execInstrBr state (.SD .x28 .x6 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 64)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.ADDI .x7 .x0 24)
  execInstrBr state (.BNE .x6 .x7 (-1224))

theorem treeAdvance_block (state : MachineState)
    (pc : state.pc = 0x1bd8) :
    OrdinarySteps SphincsImages.verify state 12 (treeAdvanceState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 64)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1)
  let s5 := execInstrBr s4 (.LUI .x28 0x43)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 64)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.LUI .x28 0x43)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 64)
  let s10 := execInstrBr s9 (.LD .x6 .x28 0)
  let s11 := execInstrBr s10 (.ADDI .x7 .x0 24)
  let s12 := execInstrBr s11 (.BNE .x6 .x7 (-1224))
  have p1 : s1.pc = 0x1bdc := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1be0 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1be4 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1be8 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1bec := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1bf0 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x1bf4 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x1bf8 := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x1bfc := by simp [s9, execInstrBr, p8]
  have p10 : s10.pc = 0x1c00 := by simp [s10, execInstrBr, p9]
  have p11 : s11.pc = 0x1c04 := by simp [s11, execInstrBr, p10]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 11
  · rw [fetch_index SphincsImages.verify state 758 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 64)) 10
  · rw [fetch_index SphincsImages.verify s1 759 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 9
  · rw [fetch_index SphincsImages.verify s2 760 (by decide)
      (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1)) 8
  · rw [fetch_index SphincsImages.verify s3 761 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x43)) 7
  · rw [fetch_index SphincsImages.verify s4 762 (by decide)
      (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 64)) 6
  · rw [fetch_index SphincsImages.verify s5 763 (by decide)
      (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 5
  · rw [fetch_index SphincsImages.verify s6 764 (by decide)
      (by simpa using p6)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep,
      memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x43)) 4
  · rw [fetch_index SphincsImages.verify s7 765 (by decide)
      (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 64)) 3
  · rw [fetch_index SphincsImages.verify s8 766 (by decide)
      (by simpa using p8)]
    decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x6 .x28 0)) 2
  · rw [fetch_index SphincsImages.verify s9 767 (by decide)
      (by simpa using p9)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
      ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x7 .x0 24)) 1
  · rw [fetch_index SphincsImages.verify s10 768 (by decide)
      (by simpa using p10)]
    decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.BNE .x6 .x7 (-1224))) 0
  · rw [fetch_index SphincsImages.verify s11 769 (by decide)
      (by simpa using p11)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem treeAdvance_counter (state : MachineState) :
    (treeAdvanceState state).getMem 0x43040 =
      state.getMem 0x43040 + 1 := by
  simp [treeAdvanceState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_eq,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem treeAdvance_mem_frame (state : MachineState) (address : Word)
    (outside : address ≠ 0x43040) :
    (treeAdvanceState state).getMem address = state.getMem address := by
  change address ≠ (274496#64) at outside
  simp [treeAdvanceState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne, outside,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem treeAdvance_pc_next (state : MachineState) (tree : FtsTree)
    (pc : state.pc = 0x1bd8)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (next : tree.val + 1 < ftsTrees - 1) :
    (treeAdvanceState state).pc = 0x173c := by
  change state.getMem (274496#64) = BitVec.ofNat 64 tree.val at counter
  have notLast : tree.val ≠ 23 := by
    dsimp [ftsTrees] at next
    omega
  fin_cases tree <;>
    simp_all [ftsTrees, treeAdvanceState, execInstrBr,
      signExtend12, signExtend13,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      MachineState.getMem_setReg, MachineState.getMem_setPC]

theorem treeAdvance_pc_done (state : MachineState)
    (pc : state.pc = 0x1bd8)
    (counter : state.getMem 0x43040 = 23) :
    (treeAdvanceState state).pc = 0x1c08 := by
  change state.getMem (274496#64) = 23 at counter
  simp [treeAdvanceState, execInstrBr, pc, counter,
    signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setReg, MachineState.getMem_setPC]

end SigGolfCandidate.SphincsVerifierFtsTreeAdvance

/-! Axiom guards for the exact instruction block and its state effects. -/

/-- info: 'SigGolfCandidate.SphincsVerifierFtsTreeAdvance.treeAdvance_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SigGolfCandidate.SphincsVerifierFtsTreeAdvance.treeAdvance_block

/-- info: 'SigGolfCandidate.SphincsVerifierFtsTreeAdvance.treeAdvance_counter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SigGolfCandidate.SphincsVerifierFtsTreeAdvance.treeAdvance_counter

/-- info: 'SigGolfCandidate.SphincsVerifierFtsTreeAdvance.treeAdvance_mem_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SigGolfCandidate.SphincsVerifierFtsTreeAdvance.treeAdvance_mem_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsTreeAdvance.treeAdvance_pc_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SigGolfCandidate.SphincsVerifierFtsTreeAdvance.treeAdvance_pc_next

/-- info: 'SigGolfCandidate.SphincsVerifierFtsTreeAdvance.treeAdvance_pc_done' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SigGolfCandidate.SphincsVerifierFtsTreeAdvance.treeAdvance_pc_done
