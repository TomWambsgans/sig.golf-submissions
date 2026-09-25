import SigGolfCandidate.SphincsVerifierFtsLoadedFirstTree
import SigGolfCandidate.SphincsVerifierFtsCopyAccess

/-! Compute the destination of one FORS root and certify its copy opcode block. -/

namespace SigGolfCandidate.SphincsVerifierFtsRootStore
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def rootStoreSetupState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x44)
  let state := execInstrBr state (.ADDI .x6 .x6 256)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 64)
  let state := execInstrBr state (.LD .x7 .x28 0)
  let state := execInstrBr state (.SLLI .x10 .x7 2)
  let state := execInstrBr state (.SLLI .x11 .x7 4)
  let state := execInstrBr state (.ADD .x10 .x10 .x11)
  let state := execInstrBr state (.ADD .x7 .x6 .x10)
  let state := execInstrBr state (.LUI .x6 0x45)
  execInstrBr state (.ADDI .x6 .x6 (-1536))

theorem rootStoreSetup_block (state : MachineState)
    (pc : state.pc = 0x1b84) :
    OrdinarySteps SphincsImages.verify state 11 (rootStoreSetupState state) := by
  let s1 := execInstrBr state (.LUI .x6 0x44)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 256)
  let s3 := execInstrBr s2 (.LUI .x28 0x43)
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 64)
  let s5 := execInstrBr s4 (.LD .x7 .x28 0)
  let s6 := execInstrBr s5 (.SLLI .x10 .x7 2)
  let s7 := execInstrBr s6 (.SLLI .x11 .x7 4)
  let s8 := execInstrBr s7 (.ADD .x10 .x10 .x11)
  let s9 := execInstrBr s8 (.ADD .x7 .x6 .x10)
  let s10 := execInstrBr s9 (.LUI .x6 0x45)
  let s11 := execInstrBr s10 (.ADDI .x6 .x6 (-1536))
  have p1 : s1.pc = 0x1b88 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1b8c := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1b90 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1b94 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1b98 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1b9c := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x1ba0 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x1ba4 := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x1ba8 := by simp [s9, execInstrBr, p8]
  have p10 : s10.pc = 0x1bac := by simp [s10, execInstrBr, p9]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x44)) 10
  · rw [fetch_index SphincsImages.verify state 737 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 256)) 9
  · rw [fetch_index SphincsImages.verify s1 738 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x28 0x43)) 8
  · rw [fetch_index SphincsImages.verify s2 739 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x28 64)) 7
  · rw [fetch_index SphincsImages.verify s3 740 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x7 .x28 0)) 6
  · rw [fetch_index SphincsImages.verify s4 741 (by decide)
      (by simpa using p4)]
    decide
  · simp [s1, s2, s3, s4, s5, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s5 s6 _ (.base (.SLLI .x10 .x7 2)) 5
  · rw [fetch_index SphincsImages.verify s5 742 (by decide)
      (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SLLI .x11 .x7 4)) 4
  · rw [fetch_index SphincsImages.verify s6 743 (by decide)
      (by simpa using p6)]
    decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADD .x10 .x10 .x11)) 3
  · rw [fetch_index SphincsImages.verify s7 744 (by decide)
      (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADD .x7 .x6 .x10)) 2
  · rw [fetch_index SphincsImages.verify s8 745 (by decide)
      (by simpa using p8)]
    decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x6 0x45)) 1
  · rw [fetch_index SphincsImages.verify s9 746 (by decide)
      (by simpa using p9)]
    decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x6 .x6 (-1536))) 0
  · rw [fetch_index SphincsImages.verify s10 747 (by decide)
      (by simpa using p10)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem rootStoreSetup_pc (state : MachineState)
    (pc : state.pc = 0x1b84) :
    (rootStoreSetupState state).pc = 0x1bb0 := by
  simp [rootStoreSetupState, execInstrBr, pc]

theorem rootStoreSetup_source (state : MachineState) :
    (rootStoreSetupState state).getReg .x6 = 0x44a00 := by
  simp [rootStoreSetupState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem rootStoreSetup_mem (state : MachineState) (address : Word) :
    (rootStoreSetupState state).getMem address = state.getMem address := by
  simp [rootStoreSetupState, execInstrBr]

theorem rootStoreSetup_destination (state : MachineState)
    (tree : FtsTree)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val) :
    (rootStoreSetupState state).getReg .x7 =
      BitVec.ofNat 64 (0x44100 + 20 * tree.val) := by
  change state.getMem (274496#64) = BitVec.ofNat 64 tree.val at counter
  fin_cases tree <;>
    simp [rootStoreSetupState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      MachineState.getMem_setReg, MachineState.getMem_setPC, counter]

theorem rootStore_copy_code : Copy20Code SphincsImages.verify 748 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

theorem rootStore_block (state : MachineState) (tree : FtsTree)
    (pc : state.pc = 0x1b84)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val) :
    OrdinarySteps SphincsImages.verify state 21
      (copyRootState (rootStoreSetupState state)) ∧
    (copyRootState (rootStoreSetupState state)).pc = 0x1bd8 := by
  let setup := rootStoreSetupState state
  have setupPc : setup.pc = BitVec.ofNat 64 (0x1000 + 4 * 748) := by
    simpa [setup] using rootStoreSetup_pc state pc
  have copied := copy20_block_general SphincsImages.verify 748
    rootStore_copy_code setup 0x44a00 (0x44100 + 20 * tree.val)
    setupPc (rootStoreSetup_source state)
    (rootStoreSetup_destination state tree counter)
    (by decide) (by decide) (by omega) (by
      have h := tree.isLt
      dsimp [ftsTrees] at h
      dsimp [MEMORY_BYTES]
      omega) (by decide)
  exact ⟨(rootStoreSetup_block state pc).append copied,
    by simpa [setup] using copy20_final_pc setup 748 setupPc⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootStore.rootStoreSetup_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootStoreSetup_block

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootStore.rootStoreSetup_destination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootStoreSetup_destination

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootStore.rootStore_copy_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootStore_copy_code

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootStore.rootStore_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootStore_block

end SigGolfCandidate.SphincsVerifierFtsRootStore
