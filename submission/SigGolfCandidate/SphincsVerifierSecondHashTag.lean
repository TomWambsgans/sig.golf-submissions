import SigGolfCandidate.SphincsVerifierWitnessAtHash

/-!
# Message-index HASH domain tag

The second HASH header starts at PC `0x11f8`. Its first ten instructions write
the message-index tag to the beginning of the 112-byte input buffer.
-/

namespace SigGolfCandidate.SphincsVerifierSecondHashTag
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopyMemory

def tagBeforeStore (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x1)
  let state := execInstrBr state (.ADDI .x6 .x6 (-1023))
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 0)
  let state := execInstrBr state (.LD .x7 .x28 0)
  let state := execInstrBr state (.SLLI .x7 .x7 16)
  let state := execInstrBr state (.ADD .x6 .x6 .x7)
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 0)

def tagState (state : MachineState) : MachineState :=
  execInstrBr (tagBeforeStore state) (.SW .x7 .x6 0)

theorem tag_block (state : MachineState) (pc : state.pc = 0x11f8) :
    OrdinarySteps SphincsImages.verify state 10 (tagState state) := by
  let s1 := execInstrBr state (.LUI .x6 0x1)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-1023))
  let s3 := execInstrBr s2 (.LUI .x28 0x43)
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 0)
  let s5 := execInstrBr s4 (.LD .x7 .x28 0)
  let s6 := execInstrBr s5 (.SLLI .x7 .x7 16)
  let s7 := execInstrBr s6 (.ADD .x6 .x6 .x7)
  let s8 := execInstrBr s7 (.LUI .x7 0x40)
  let s9 := execInstrBr s8 (.ADDI .x7 .x7 0)
  let s10 := execInstrBr s9 (.SW .x7 .x6 0)
  have p1 : s1.pc = 0x11fc := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1200 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1204 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1208 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x120c := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1210 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x1214 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x1218 := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x121c := by simp [s9, execInstrBr, p8]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x1)) 9
  · rw [fetch_index SphincsImages.verify state 126 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-1023))) 8
  · rw [fetch_index SphincsImages.verify s1 127 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x28 0x43)) 7
  · rw [fetch_index SphincsImages.verify s2 128 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x28 0)) 6
  · rw [fetch_index SphincsImages.verify s3 129 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x7 .x28 0)) 5
  · rw [fetch_index SphincsImages.verify s4 130 (by decide)
      (by simpa using p4)]
    decide
  · have pointer : s4.getReg .x28 = 0x43000 := by
      simp [s4, s3, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s5, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s5 s6 _ (.base (.SLLI .x7 .x7 16)) 4
  · rw [fetch_index SphincsImages.verify s5 131 (by decide)
      (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x6 .x6 .x7)) 3
  · rw [fetch_index SphincsImages.verify s6 132 (by decide)
      (by simpa using p6)]
    decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x7 0x40)) 2
  · rw [fetch_index SphincsImages.verify s7 133 (by decide)
      (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x7 .x7 0)) 1
  · rw [fetch_index SphincsImages.verify s8 134 (by decide)
      (by simpa using p8)]
    decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.SW .x7 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s9 135 (by decide)
      (by simpa using p9)]
    decide
  · have pointer : s9.getReg .x7 = 0x40000 := by
      simp [s9, s8, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s10, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem tag_next_pc (state : MachineState) (pc : state.pc = 0x11f8) :
    (tagState state).pc = 0x1220 := by
  simp [tagState, tagBeforeStore, execInstrBr, pc]

theorem tag_value (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0) :
    (tagState state).getWord32 0x40000 = 0xc01 := by
  simp [tagState, tagBeforeStore, execInstrBr, signExtend12,
    getWord32_setWord32_same, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  have zero : state.getMem (274432#64) = 0 := by
    have address : (274432#64) = (0x43000 : Word) := by decide
    rw [address]
    exact layerZero
  rw [zero]
  decide

theorem position_block (state : MachineState) (pc : state.pc = 0x1220)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.positionState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 16)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SW .x7 .x6 4)
  have p1 : s1.pc = 0x1224 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1228 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x122c := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 136 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 16)) 2
  · rw [fetch_index SphincsImages.verify s1 137 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 138 (by decide)
      (by simpa using p2)]
    decide
  · have pointer : s2.getReg .x28 = 0x43010 := by
      simp [s2, s1, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SW .x7 .x6 4)) 0
  · rw [fetch_index SphincsImages.verify s3 139 (by decide)
      (by simpa using p3)]
    decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr,
        MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem position_next_pc (state : MachineState) (pc : state.pc = 0x1220) :
    (SphincsVerifierHeader.positionState state).pc = 0x1230 := by
  simp [SphincsVerifierHeader.positionState,
    SphincsVerifierHeader.positionBeforeStore, execInstrBr, pc]

theorem tree_block (state : MachineState) (pc : state.pc = 0x1230)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.treeState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SD .x7 .x6 8)
  have p1 : s1.pc = 0x1234 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1238 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x123c := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 140 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 2
  · rw [fetch_index SphincsImages.verify s1 141 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 142 (by decide)
      (by simpa using p2)]
    decide
  · have pointer : s2.getReg .x28 = 0x43008 := by
      simp [s2, s1, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x7 .x6 8)) 0
  · rw [fetch_index SphincsImages.verify s3 143 (by decide)
      (by simpa using p3)]
    decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr,
        MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem tree_next_pc (state : MachineState) (pc : state.pc = 0x1230) :
    (SphincsVerifierHeader.treeState state).pc = 0x1240 := by
  simp [SphincsVerifierHeader.treeState,
    SphincsVerifierHeader.treeBeforeStore, execInstrBr, pc]

theorem index_block (state : MachineState) (pc : state.pc = 0x1240)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.indexState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 24)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SW .x7 .x6 16)
  have p1 : s1.pc = 0x1244 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1248 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x124c := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 144 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 24)) 2
  · rw [fetch_index SphincsImages.verify s1 145 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 146 (by decide)
      (by simpa using p2)]
    decide
  · have pointer : s2.getReg .x28 = 0x43018 := by
      simp [s2, s1, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SW .x7 .x6 16)) 0
  · rw [fetch_index SphincsImages.verify s3 147 (by decide)
      (by simpa using p3)]
    decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr,
        MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem index_next_pc (state : MachineState) (pc : state.pc = 0x1240) :
    (SphincsVerifierHeader.indexState state).pc = 0x1250 := by
  simp [SphincsVerifierHeader.indexState,
    SphincsVerifierHeader.indexBeforeStore, execInstrBr, pc]

theorem tag_hash_pointer (state : MachineState) :
    (tagState state).getReg .x7 = 0x40000 := by
  simp [tagState, tagBeforeStore, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def headerState (state : MachineState) : MachineState :=
  SphincsVerifierHeader.indexState
    (SphincsVerifierHeader.treeState
      (SphincsVerifierHeader.positionState (tagState state)))

theorem header_block (state : MachineState) (pc : state.pc = 0x11f8) :
    OrdinarySteps SphincsImages.verify state 22 (headerState state) := by
  let tagged := tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have first := tag_block state pc
  have taggedPc := tag_next_pc state pc
  have second := position_block tagged taggedPc (tag_hash_pointer state)
  have positionedPc := position_next_pc tagged taggedPc
  have positionedPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans
      (tag_hash_pointer state)
  have third := tree_block positioned positionedPc positionedPointer
  have treedPc := tree_next_pc positioned positionedPc
  have treedPointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans
      positionedPointer
  have fourth := index_block treed treedPc treedPointer
  simpa [headerState, tagged, positioned, treed] using
    ((first.append second).append third).append fourth

theorem header_next_pc (state : MachineState) (pc : state.pc = 0x11f8) :
    (headerState state).pc = 0x1250 :=
  index_next_pc _ (tree_next_pc _
    (position_next_pc _ (tag_next_pc state pc)))

/-- info: 'SigGolfCandidate.SphincsVerifierSecondHashTag.tag_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tag_block

/-- info: 'SigGolfCandidate.SphincsVerifierSecondHashTag.header_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms header_block

end SigGolfCandidate.SphincsVerifierSecondHashTag
