import SigGolfCandidate.SphincsVerifierFtsAdvance
import SigGolfCandidate.SphincsVerifierWitnessAtHash

/-!
# First FORS leaf HASH domain header

The first FORS HASH header starts at PC `0x1820` and writes domain tag 9.
-/

namespace SigGolfCandidate.SphincsVerifierFtsHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierFtsAdvance
open SigGolfCandidate.SphincsVerifierFtsLeafCopy
open SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsEntry
open SigGolfCandidate.SphincsVerifierLastLeaf
open SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierMessageHash
set_option maxRecDepth 16384

def tagBeforeStore (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x1)
  let state := execInstrBr state (.ADDI .x6 .x6 (-1791))
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 0)
  let state := execInstrBr state (.LD .x7 .x28 0)
  let state := execInstrBr state (.SLLI .x7 .x7 16)
  let state := execInstrBr state (.ADD .x6 .x6 .x7)
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 0)

def tagState (state : MachineState) : MachineState :=
  execInstrBr (tagBeforeStore state) (.SW .x7 .x6 0)

theorem tag_block (state : MachineState) (pc : state.pc = 0x1820) :
    OrdinarySteps SphincsImages.verify state 10 (tagState state) := by
  let s1 := execInstrBr state (.LUI .x6 0x1)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-1791))
  let s3 := execInstrBr s2 (.LUI .x28 0x43)
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 0)
  let s5 := execInstrBr s4 (.LD .x7 .x28 0)
  let s6 := execInstrBr s5 (.SLLI .x7 .x7 16)
  let s7 := execInstrBr s6 (.ADD .x6 .x6 .x7)
  let s8 := execInstrBr s7 (.LUI .x7 0x40)
  let s9 := execInstrBr s8 (.ADDI .x7 .x7 0)
  let s10 := execInstrBr s9 (.SW .x7 .x6 0)
  have p1 : s1.pc = 0x1824 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1828 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x182c := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1830 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1834 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1838 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x183c := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x1840 := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x1844 := by simp [s9, execInstrBr, p8]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x1)) 9
  · rw [fetch_index SphincsImages.verify state 520 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-1791))) 8
  · rw [fetch_index SphincsImages.verify s1 521 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x28 0x43)) 7
  · rw [fetch_index SphincsImages.verify s2 522 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x28 0)) 6
  · rw [fetch_index SphincsImages.verify s3 523 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x7 .x28 0)) 5
  · rw [fetch_index SphincsImages.verify s4 524 (by decide)
      (by simpa using p4)]
    decide
  · have pointer : s4.getReg .x28 = 0x43000 := by
      simp [s4, s3, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s5, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s5 s6 _ (.base (.SLLI .x7 .x7 16)) 4
  · rw [fetch_index SphincsImages.verify s5 525 (by decide)
      (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x6 .x6 .x7)) 3
  · rw [fetch_index SphincsImages.verify s6 526 (by decide)
      (by simpa using p6)]
    decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x7 0x40)) 2
  · rw [fetch_index SphincsImages.verify s7 527 (by decide)
      (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x7 .x7 0)) 1
  · rw [fetch_index SphincsImages.verify s8 528 (by decide)
      (by simpa using p8)]
    decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.SW .x7 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s9 529 (by decide)
      (by simpa using p9)]
    decide
  · have pointer : s9.getReg .x7 = 0x40000 := by
      simp [s9, s8, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s10, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem tag_next_pc (state : MachineState) (pc : state.pc = 0x1820) :
    (tagState state).pc = 0x1848 := by
  simp [tagState, tagBeforeStore, execInstrBr, pc]

theorem tag_value (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0) :
    (tagState state).getWord32 0x40000 = 0x901 := by
  simp [tagState, tagBeforeStore, execInstrBr, signExtend12,
    getWord32_setWord32_same, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  have zero : state.getMem (274432#64) = 0 := by
    have address : (274432#64) = (0x43000 : Word) := by decide
    rw [address]
    exact layerZero
  rw [zero]
  decide

theorem position_block (state : MachineState) (pc : state.pc = 0x1848)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.positionState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 16)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SW .x7 .x6 4)
  have p1 : s1.pc = 0x184c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1850 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1854 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 530 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 16)) 2
  · rw [fetch_index SphincsImages.verify s1 531 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 532 (by decide)
      (by simpa using p2)]
    decide
  · have pointer : s2.getReg .x28 = 0x43010 := by
      simp [s2, s1, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SW .x7 .x6 4)) 0
  · rw [fetch_index SphincsImages.verify s3 533 (by decide)
      (by simpa using p3)]
    decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr,
        MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem position_next_pc (state : MachineState) (pc : state.pc = 0x1848) :
    (SphincsVerifierHeader.positionState state).pc = 0x1858 := by
  simp [SphincsVerifierHeader.positionState,
    SphincsVerifierHeader.positionBeforeStore, execInstrBr, pc]

theorem tree_block (state : MachineState) (pc : state.pc = 0x1858)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.treeState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SD .x7 .x6 8)
  have p1 : s1.pc = 0x185c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1860 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1864 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 534 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 2
  · rw [fetch_index SphincsImages.verify s1 535 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 536 (by decide)
      (by simpa using p2)]
    decide
  · have pointer : s2.getReg .x28 = 0x43008 := by
      simp [s2, s1, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x7 .x6 8)) 0
  · rw [fetch_index SphincsImages.verify s3 537 (by decide)
      (by simpa using p3)]
    decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr,
        MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem tree_next_pc (state : MachineState) (pc : state.pc = 0x1858) :
    (SphincsVerifierHeader.treeState state).pc = 0x1868 := by
  simp [SphincsVerifierHeader.treeState,
    SphincsVerifierHeader.treeBeforeStore, execInstrBr, pc]

theorem index_block (state : MachineState) (pc : state.pc = 0x1868)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.indexState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 24)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SW .x7 .x6 16)
  have p1 : s1.pc = 0x186c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1870 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1874 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 538 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 24)) 2
  · rw [fetch_index SphincsImages.verify s1 539 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 540 (by decide)
      (by simpa using p2)]
    decide
  · have pointer : s2.getReg .x28 = 0x43018 := by
      simp [s2, s1, execInstrBr, signExtend12,
        MachineState.getReg_setReg_eq]
    simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SW .x7 .x6 16)) 0
  · rw [fetch_index SphincsImages.verify s3 541 (by decide)
      (by simpa using p3)]
    decide
  · have pointer : s3.getReg .x7 = 0x40000 := by
      simp [s3, s2, s1, execInstrBr,
        MachineState.getReg_setReg_ne, destination]
    simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, signExtend12, pointer, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem index_next_pc (state : MachineState) (pc : state.pc = 0x1868) :
    (SphincsVerifierHeader.indexState state).pc = 0x1878 := by
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

theorem header_block (state : MachineState) (pc : state.pc = 0x1820) :
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

theorem header_next_pc (state : MachineState) (pc : state.pc = 0x1820) :
    (headerState state).pc = 0x1878 :=
  index_next_pc _ (tree_next_pc _
    (position_next_pc _ (tag_next_pc state pc)))

theorem messageReady_admissible_ftsHeader (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer)) :
    let initial := indexStoredState (indexValueState (writeHash state answer))
    let selected := leafStates initial 24 (by decide)
    let accepted := lastAcceptState selected
    let entered := ftsEntryState accepted
    let firstHeader := ftsTreeHeaderState entered
    let selection := ftsSelectState firstHeader
    let pointers := ftsCopyPointers selection
    let copied := SphincsVerifierCopy.copyRootState pointers
    let advanced := ftsAdvanceState copied
    let final := headerState advanced
    OrdinarySteps SphincsImages.verify (writeHash state answer) 372 final ∧
      final.pc = 0x1878 := by
  obtain ⟨front, advancedPc, _, _, _⟩ :=
    messageReady_admissible_ftsAdvance state pk message randomness
      ready pc answer admissible
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selected := leafStates initial 24 (by decide)
  let accepted := lastAcceptState selected
  let entered := ftsEntryState accepted
  let firstHeader := ftsTreeHeaderState entered
  let selection := ftsSelectState firstHeader
  let pointers := ftsCopyPointers selection
  let copied := SphincsVerifierCopy.copyRootState pointers
  let advanced := ftsAdvanceState copied
  have back := header_block advanced advancedPc
  exact ⟨by simpa [initial, selected, accepted, entered, firstHeader, selection,
      pointers, copied, advanced] using front.append back,
    header_next_pc advanced advancedPc⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsHeader.tag_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tag_block

/-- info: 'SigGolfCandidate.SphincsVerifierFtsHeader.header_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms header_block

/-- info: 'SigGolfCandidate.SphincsVerifierFtsHeader.messageReady_admissible_ftsHeader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_admissible_ftsHeader

end SigGolfCandidate.SphincsVerifierFtsHeader
