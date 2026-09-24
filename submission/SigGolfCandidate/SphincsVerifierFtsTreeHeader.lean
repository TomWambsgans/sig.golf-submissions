import SigGolfCandidate.SphincsVerifierFtsEntry

/-! First FORS tree loop: load the tree counter and digest index into header cells. -/

namespace SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsEntry
open SigGolfCandidate.SphincsVerifierLastLeaf
open SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierMessageHash
set_option maxRecDepth 16384

def ftsTreeHeaderState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 64)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 0)
  let state := execInstrBr state (.SD .x28 .x6 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 120)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 8)
  execInstrBr state (.SD .x28 .x6 0)

theorem ftsTreeHeader_block (state : MachineState) (pc : state.pc = 0x173c) :
    OrdinarySteps SphincsImages.verify state 12 (ftsTreeHeaderState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 64)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x43)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0)
  let s6 := execInstrBr s5 (.SD .x28 .x6 0)
  let s7 := execInstrBr s6 (.LUI .x28 0x43)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 120)
  let s9 := execInstrBr s8 (.LD .x6 .x28 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x43)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 8)
  let s12 := execInstrBr s11 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x1740 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1744 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1748 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x174c := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1750 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1754 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x1758 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x175c := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x1760 := by simp [s9, execInstrBr, p8]
  have p10 : s10.pc = 0x1764 := by simp [s10, execInstrBr, p9]
  have p11 : s11.pc = 0x1768 := by simp [s11, execInstrBr, p10]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 11
  · rw [fetch_index SphincsImages.verify state 463 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 64)) 10
  · rw [fetch_index SphincsImages.verify s1 464 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 9
  · rw [fetch_index SphincsImages.verify s2 465 (by decide) (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x43)) 8
  · rw [fetch_index SphincsImages.verify s3 466 (by decide) (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0)) 7
  · rw [fetch_index SphincsImages.verify s4 467 (by decide) (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SD .x28 .x6 0)) 6
  · rw [fetch_index SphincsImages.verify s5 468 (by decide) (by simpa using p5)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x43)) 5
  · rw [fetch_index SphincsImages.verify s6 469 (by decide) (by simpa using p6)]
    decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 120)) 4
  · rw [fetch_index SphincsImages.verify s7 470 (by decide) (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x6 .x28 0)) 3
  · rw [fetch_index SphincsImages.verify s8 471 (by decide) (by simpa using p8)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s9 472 (by decide) (by simpa using p9)]
    decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 8)) 1
  · rw [fetch_index SphincsImages.verify s10 473 (by decide) (by simpa using p10)]
    decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s11 474 (by decide) (by simpa using p11)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem ftsTreeHeader_pc (state : MachineState) (pc : state.pc = 0x173c) :
    (ftsTreeHeaderState state).pc = 0x176c := by
  simp [ftsTreeHeaderState, execInstrBr, pc]

theorem ftsTreeHeader_cells (state : MachineState) :
    (ftsTreeHeaderState state).getMem 0x43000 = state.getMem 0x43040 ∧
      (ftsTreeHeaderState state).getMem 0x43008 = state.getMem 0x43078 := by
  constructor <;>
    simp [ftsTreeHeaderState, execInstrBr, signExtend12,
      MachineState.getMem_setMem_ne,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem ftsTreeHeader_mem_frame (state : MachineState) (address : Word)
    (notLayer : address ≠ 0x43000) (notTree : address ≠ 0x43008) :
    (ftsTreeHeaderState state).getMem address = state.getMem address := by
  change address ≠ (274432#64) at notLayer
  change address ≠ (274440#64) at notTree
  simp [ftsTreeHeaderState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne, notLayer, notTree,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

set_option maxHeartbeats 0 in
theorem ftsTreeHeader_selector_byte (state : MachineState)
    (tree : Fin 24) :
    (ftsTreeHeaderState state).getByte
      (BitVec.ofNat 64 (0x44800 + tree.val)) =
      state.getByte (BitVec.ofNat 64 (0x44800 + tree.val)) := by
  fin_cases tree <;>
    simp [ftsTreeHeaderState, execInstrBr, signExtend12,
      MachineState.getByte, MachineState.getMem_setPC,
      MachineState.getMem_setReg, MachineState.getMem_setMem_ne,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      alignToDword]

theorem messageReady_admissible_treeHeader (state : MachineState)
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
    let final := ftsTreeHeaderState entered
    OrdinarySteps SphincsImages.verify (writeHash state answer) 305 final ∧
      final.pc = 0x176c ∧
      final.getMem 0x43000 = 0 ∧
      final.getMem 0x43008 =
        BitVec.ofNat 64 (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest answer)).val ∧
      final.getMem 0x43028 = 0x22cdc ∧
      ∀ tree : Fin 24,
        (final.getByte (BitVec.ofNat 64 (0x44800 + tree.val))).toNat =
          abstractLeaf answer tree := by
  obtain ⟨front, enteredPc, treeZero, pointer, selectors⟩ :=
    messageReady_admissible_ftsEntry state pk message randomness
      ready pc answer admissible
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selectedState := leafStates initial 24 (by decide)
  let acceptedState := lastAcceptState selectedState
  let enteredState := ftsEntryState acceptedState
  have index := messageReady_ftsEntry_msgIndex state pk message randomness
    ready pc answer
  have back := ftsTreeHeader_block enteredState enteredPc
  have finalPc := ftsTreeHeader_pc enteredState enteredPc
  have fields := ftsTreeHeader_cells enteredState
  exact ⟨by simpa [initial, selectedState, acceptedState, enteredState] using
      front.append back,
    finalPc,
    by rw [fields.1]; exact treeZero,
    by rw [fields.2]; exact index,
    by rw [ftsTreeHeader_mem_frame _ 0x43028 (by decide) (by decide)];
       exact pointer,
    by intro tree
       rw [ftsTreeHeader_selector_byte]
       exact selectors tree⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsTreeHeader.messageReady_admissible_treeHeader' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_admissible_treeHeader

end SigGolfCandidate.SphincsVerifierFtsTreeHeader
