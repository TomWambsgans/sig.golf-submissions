import SigGolfCandidate.SphincsVerifierLastLeaf

/-! First verifier instructions after digest admission: initialize the FORS loop. -/

namespace SigGolfCandidate.SphincsVerifierFtsEntry
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierLastLeaf
open SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierMessageHash

def ftsEntryState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.ADDI .x6 .x0 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 64)
  let state := execInstrBr state (.SD .x28 .x6 0)
  let state := execInstrBr state (.LUI .x6 0x23)
  let state := execInstrBr state (.ADDI .x6 .x6 (-804))
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  execInstrBr state (.SD .x28 .x6 0)

set_option maxRecDepth 16384 in
theorem ftsEntry_block (state : MachineState) (pc : state.pc = 0x1718) :
    OrdinarySteps SphincsImages.verify state 9 (ftsEntryState state) := by
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 64)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.LUI .x6 0x23)
  let s6 := execInstrBr s5 (.ADDI .x6 .x6 (-804))
  let s7 := execInstrBr s6 (.LUI .x28 0x43)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 40)
  let s9 := execInstrBr s8 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x171c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1720 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1724 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1728 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x172c := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1730 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x1734 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x1738 := by simp [s8, execInstrBr, p7]
  apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 0)) 8
  · rw [fetch_index SphincsImages.verify state 454 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x43)) 7
  · rw [fetch_index SphincsImages.verify s1 455 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 64)) 6
  · rw [fetch_index SphincsImages.verify s2 456 (by decide) (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 5
  · rw [fetch_index SphincsImages.verify s3 457 (by decide) (by simpa using p3)]
    decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x6 0x23)) 4
  · rw [fetch_index SphincsImages.verify s4 458 (by decide) (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x6 .x6 (-804))) 3
  · rw [fetch_index SphincsImages.verify s5 459 (by decide) (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s6 460 (by decide) (by simpa using p6)]
    decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 40)) 1
  · rw [fetch_index SphincsImages.verify s7 461 (by decide) (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s8 462 (by decide) (by simpa using p8)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9,
      ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem ftsEntry_pc (state : MachineState) (pc : state.pc = 0x1718) :
    (ftsEntryState state).pc = 0x173c := by
  simp [ftsEntryState, execInstrBr, pc]

theorem ftsEntry_cells (state : MachineState) :
    (ftsEntryState state).getMem 0x43040 = 0 ∧
      (ftsEntryState state).getMem 0x43028 = 0x22cdc := by
  constructor <;>
    simp [ftsEntryState, execInstrBr, signExtend12,
      MachineState.getMem_setMem_ne,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem ftsEntry_mem_frame (state : MachineState) (address : Word)
    (notTree : address ≠ 0x43040) (notPointer : address ≠ 0x43028) :
    (ftsEntryState state).getMem address = state.getMem address := by
  change address ≠ (274496#64) at notTree
  change address ≠ (274472#64) at notPointer
  simp [ftsEntryState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne, notTree, notPointer,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

set_option maxHeartbeats 0 in
theorem ftsEntry_answer_byte (state : MachineState) (index : Fin 30) :
    (ftsEntryState state).getByte
      (BitVec.ofNat 64 (0x42000 + index.val)) =
      state.getByte (BitVec.ofNat 64 (0x42000 + index.val)) := by
  fin_cases index <;>
    simp [ftsEntryState, execInstrBr, signExtend12,
      MachineState.getByte, MachineState.getMem_setPC,
      MachineState.getMem_setReg, MachineState.getMem_setMem_ne,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      alignToDword]

set_option maxHeartbeats 0 in
theorem ftsEntry_selector_byte (state : MachineState) (tree : Fin 24) :
    (ftsEntryState state).getByte
      (BitVec.ofNat 64 (0x44800 + tree.val)) =
      state.getByte (BitVec.ofNat 64 (0x44800 + tree.val)) := by
  fin_cases tree <;>
    simp [ftsEntryState, execInstrBr, signExtend12,
      MachineState.getByte, MachineState.getMem_setPC,
      MachineState.getMem_setReg, MachineState.getMem_setMem_ne,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      alignToDword]

theorem messageReady_admissible_ftsEntry (state : MachineState)
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
    let final := ftsEntryState accepted
    OrdinarySteps SphincsImages.verify (writeHash state answer) 293 final ∧
      final.pc = 0x173c ∧
      final.getMem 0x43040 = 0 ∧
      final.getMem 0x43028 = 0x22cdc ∧
      ∀ tree : Fin 24,
        (final.getByte (BitVec.ofNat 64 (0x44800 + tree.val))).toNat =
          abstractLeaf answer tree := by
  obtain ⟨front, acceptedPc, selected⟩ :=
    messageReady_admissible_leaves state pk message randomness ready
      pc answer admissible
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selectedState := leafStates initial 24 (by decide)
  let acceptedState := lastAcceptState selectedState
  have back := ftsEntry_block acceptedState acceptedPc
  have finalPc := ftsEntry_pc acceptedState acceptedPc
  have cells := ftsEntry_cells acceptedState
  exact ⟨by simpa [initial, selectedState, acceptedState] using front.append back,
    finalPc, cells.1, cells.2,
    by intro tree
       rw [ftsEntry_selector_byte]
       exact selected tree⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsEntry.messageReady_admissible_ftsEntry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_admissible_ftsEntry

end SigGolfCandidate.SphincsVerifierFtsEntry
