import SigGolfCandidate.SphincsVerifierFtsParentTag

/-! Complete the first FORS parent HASH header with its tree and index. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsParentTag
set_option maxRecDepth 16384

theorem parentTree_block (state : MachineState) (pc : state.pc = 0x1aa8)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.treeState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SD .x7 .x6 8)
  have p1 : s1.pc = 0x1aac := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1ab0 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1ab4 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 682 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 2
  · rw [fetch_index SphincsImages.verify s1 683 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 684 (by decide)
      (by simpa using p2)]
    decide
  · have pointer : s2.getReg .x28 = 0x43008 := by
      simp [s2, s1, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x7 .x6 8)) 0
  · rw [fetch_index SphincsImages.verify s3 685 (by decide)
      (by simpa using p3)]
    decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr,
        MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem parentTree_next_pc (state : MachineState) (pc : state.pc = 0x1aa8) :
    (SphincsVerifierHeader.treeState state).pc = 0x1ab8 := by
  simp [SphincsVerifierHeader.treeState,
    SphincsVerifierHeader.treeBeforeStore, execInstrBr, pc]

theorem parentIndex_block (state : MachineState) (pc : state.pc = 0x1ab8)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.indexState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 24)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SW .x7 .x6 16)
  have p1 : s1.pc = 0x1abc := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1ac0 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1ac4 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 686 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 24)) 2
  · rw [fetch_index SphincsImages.verify s1 687 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 688 (by decide)
      (by simpa using p2)]
    decide
  · have pointer : s2.getReg .x28 = 0x43018 := by
      simp [s2, s1, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SW .x7 .x6 16)) 0
  · rw [fetch_index SphincsImages.verify s3 689 (by decide)
      (by simpa using p3)]
    decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr,
        MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem parentIndex_next_pc (state : MachineState) (pc : state.pc = 0x1ab8) :
    (SphincsVerifierHeader.indexState state).pc = 0x1ac8 := by
  simp [SphincsVerifierHeader.indexState,
    SphincsVerifierHeader.indexBeforeStore, execInstrBr, pc]


def parentHeaderState (state : MachineState) : MachineState :=
  SphincsVerifierHeader.indexState
    (SphincsVerifierHeader.treeState (parentPrefixState state))

theorem parentHeader_block (state : MachineState) (pc : state.pc = 0x1a70) :
    OrdinarySteps SphincsImages.verify state 22 (parentHeaderState state) ∧
      (parentHeaderState state).pc = 0x1ac8 := by
  let prefixed := parentPrefixState state
  let treed := SphincsVerifierHeader.treeState prefixed
  have first := (parentPrefix_block state pc).1
  have prefixPc := (parentPrefix_block state pc).2
  have prefixPointer : prefixed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer (parentTagState state)).trans
      (parentTag_hash_pointer state)
  have second := parentTree_block prefixed prefixPc prefixPointer
  have treePc := parentTree_next_pc prefixed prefixPc
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer prefixed).trans prefixPointer
  have third := parentIndex_block treed treePc treePointer
  exact ⟨(first.append second).append third,
    parentIndex_next_pc treed treePc⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentHeader.parentHeader_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentHeader_block

end SigGolfCandidate.SphincsVerifierFtsParentHeader
