import SigGolfCandidate.SphincsVerifierFtsPostForestCopy

namespace SigGolfCandidate.SphincsVerifierFtsForestHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def forestTagBeforeStore (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x1)
  let state := execInstrBr state (.ADDI .x6 .x6 (-1279))
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 0)
  let state := execInstrBr state (.LD .x7 .x28 0)
  let state := execInstrBr state (.SLLI .x7 .x7 16)
  let state := execInstrBr state (.ADD .x6 .x6 .x7)
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 0)

def forestTagState (state : MachineState) : MachineState :=
  execInstrBr (forestTagBeforeStore state) (.SW .x7 .x6 0)

theorem forestTag_pc (state : MachineState)
    (pc : state.pc = 0x1c8c) :
    (forestTagState state).pc = 0x1cb4 := by
  simp [forestTagState, forestTagBeforeStore, execInstrBr, pc]

theorem forestTag_hash_pointer (state : MachineState) :
    (forestTagState state).getReg .x7 = 0x40000 := by
  simp [forestTagState, forestTagBeforeStore, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem forestTag_block (state : MachineState)
    (pc : state.pc = 0x1c8c) :
    OrdinarySteps SphincsImages.verify state 10
      (forestTagState state) := by
  let s1 := execInstrBr state (.LUI .x6 0x1)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-1279))
  let s3 := execInstrBr s2 (.LUI .x28 0x43)
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 0)
  let s5 := execInstrBr s4 (.LD .x7 .x28 0)
  let s6 := execInstrBr s5 (.SLLI .x7 .x7 16)
  let s7 := execInstrBr s6 (.ADD .x6 .x6 .x7)
  let s8 := execInstrBr s7 (.LUI .x7 0x40)
  let s9 := execInstrBr s8 (.ADDI .x7 .x7 0)
  let s10 := execInstrBr s9 (.SW .x7 .x6 0)
  have p1 : s1.pc = 0x1c90 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1c94 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1c98 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1c9c := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1ca0 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1ca4 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x1ca8 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x1cac := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x1cb0 := by simp [s9, execInstrBr, p8]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x1)) 9
  · rw [fetch_index SphincsImages.verify state 803 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-1279))) 8
  · rw [fetch_index SphincsImages.verify s1 804 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x28 0x43)) 7
  · rw [fetch_index SphincsImages.verify s2 805 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x28 0)) 6
  · rw [fetch_index SphincsImages.verify s3 806 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x7 .x28 0)) 5
  · rw [fetch_index SphincsImages.verify s4 807 (by decide)
      (by simpa using p4)]
    decide
  · have pointer : s4.getReg .x28 = 0x43000 := by
      simp [s4, s3, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s5, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s5 s6 _ (.base (.SLLI .x7 .x7 16)) 4
  · rw [fetch_index SphincsImages.verify s5 808 (by decide)
      (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x6 .x6 .x7)) 3
  · rw [fetch_index SphincsImages.verify s6 809 (by decide)
      (by simpa using p6)]
    decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x7 0x40)) 2
  · rw [fetch_index SphincsImages.verify s7 810 (by decide)
      (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x7 .x7 0)) 1
  · rw [fetch_index SphincsImages.verify s8 811 (by decide)
      (by simpa using p8)]
    decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.SW .x7 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s9 812 (by decide)
      (by simpa using p9)]
    decide
  · have pointer : s9.getReg .x7 = 0x40000 := by
      simp [s9, s8, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s10, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem forestPosition_block (state : MachineState)
    (pc : state.pc = 0x1cb4)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.positionState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 16)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SW .x7 .x6 4)
  have p1 : s1.pc = 0x1cb8 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1cbc := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1cc0 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 813 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 16)) 2
  · rw [fetch_index SphincsImages.verify s1 814 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 815 (by decide)
      (by simpa using p2)]
    decide
  · have pointer : s2.getReg .x28 = 0x43010 := by
      simp [s2, s1, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SW .x7 .x6 4)) 0
  · rw [fetch_index SphincsImages.verify s3 816 (by decide)
      (by simpa using p3)]
    decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr, destination,
        MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem forestPosition_pc (state : MachineState)
    (pc : state.pc = 0x1cb4) :
    (SphincsVerifierHeader.positionState state).pc = 0x1cc4 := by
  simp [SphincsVerifierHeader.positionState,
    SphincsVerifierHeader.positionBeforeStore, execInstrBr, pc]
theorem forestTree_block (state : MachineState) (pc : state.pc = 0x1cc4)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.treeState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SD .x7 .x6 8)
  have p1 : s1.pc = 0x1cc8 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1ccc := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1cd0 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 817 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 2
  · rw [fetch_index SphincsImages.verify s1 818 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 819 (by decide)
      (by simpa using p2)]
    decide
  · have pointer : s2.getReg .x28 = 0x43008 := by
      simp [s2, s1, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x7 .x6 8)) 0
  · rw [fetch_index SphincsImages.verify s3 820 (by decide)
      (by simpa using p3)]
    decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr,
        MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem forestTree_next_pc (state : MachineState) (pc : state.pc = 0x1cc4) :
    (SphincsVerifierHeader.treeState state).pc = 0x1cd4 := by
  simp [SphincsVerifierHeader.treeState,
    SphincsVerifierHeader.treeBeforeStore, execInstrBr, pc]

theorem forestIndex_block (state : MachineState) (pc : state.pc = 0x1cd4)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.indexState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 24)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SW .x7 .x6 16)
  have p1 : s1.pc = 0x1cd8 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1cdc := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1ce0 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 821 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 24)) 2
  · rw [fetch_index SphincsImages.verify s1 822 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 823 (by decide)
      (by simpa using p2)]
    decide
  · have pointer : s2.getReg .x28 = 0x43018 := by
      simp [s2, s1, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SW .x7 .x6 16)) 0
  · rw [fetch_index SphincsImages.verify s3 824 (by decide)
      (by simpa using p3)]
    decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr,
        MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem forestIndex_next_pc (state : MachineState) (pc : state.pc = 0x1cd4) :
    (SphincsVerifierHeader.indexState state).pc = 0x1ce4 := by
  simp [SphincsVerifierHeader.indexState,
    SphincsVerifierHeader.indexBeforeStore, execInstrBr, pc]

def forestHeaderState (state : MachineState) : MachineState :=
  SphincsVerifierHeader.indexState
    (SphincsVerifierHeader.treeState
      (SphincsVerifierHeader.positionState (forestTagState state)))

theorem forestHeader_block (state : MachineState) (pc : state.pc = 0x1c8c) :
    OrdinarySteps SphincsImages.verify state 22 (forestHeaderState state) ∧
      (forestHeaderState state).pc = 0x1ce4 := by
  let tagged := forestTagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have first := forestTag_block state pc
  have tagPc := forestTag_pc state pc
  have second := forestPosition_block tagged tagPc (forestTag_hash_pointer state)
  have positionPc := forestPosition_pc tagged tagPc
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans
      (forestTag_hash_pointer state)
  have third := forestTree_block positioned positionPc positionPointer
  have treePc := forestTree_next_pc positioned positionPc
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  have fourth := forestIndex_block treed treePc treePointer
  exact ⟨by simpa only [forestHeaderState] using
    ((first.append second).append third).append fourth,
    by simpa only [forestHeaderState] using forestIndex_next_pc treed treePc⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestHeader.forestHeader_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestHeader_block

end SigGolfCandidate.SphincsVerifierFtsForestHeader
