import SigGolfCandidate.SphincsVerifierFtsLeafCopy

/-! Advance to the first FORS authentication path and record its selected leaf index. -/

namespace SigGolfCandidate.SphincsVerifierFtsAdvance
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
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

def ftsAdvanceState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.ADDI .x6 .x6 20)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  let state := execInstrBr state (.SD .x28 .x6 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 32)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 24)
  execInstrBr state (.SD .x28 .x6 0)

theorem ftsAdvance_block (state : MachineState)
    (pc : state.pc = 0x17ec) :
    OrdinarySteps SphincsImages.verify state 13 (ftsAdvanceState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 40)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 20)
  let s5 := execInstrBr s4 (.LUI .x28 0x43)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 40)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.LUI .x28 0x43)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 32)
  let s10 := execInstrBr s9 (.LD .x6 .x28 0)
  let s11 := execInstrBr s10 (.LUI .x28 0x43)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 24)
  let s13 := execInstrBr s12 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x17f0 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x17f4 := by simp [s1, s2, execInstrBr, pc]
  have p3 : s3.pc = 0x17f8 := by simp [s1, s2, s3, execInstrBr, pc]
  have p4 : s4.pc = 0x17fc := by simp [s1, s2, s3, s4, execInstrBr, pc]
  have p5 : s5.pc = 0x1800 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
  have p6 : s6.pc = 0x1804 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
  have p7 : s7.pc = 0x1808 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
  have p8 : s8.pc = 0x180c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc]
  have p9 : s9.pc = 0x1810 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc]
  have p10 : s10.pc = 0x1814 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc]
  have p11 : s11.pc = 0x1818 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc]
  have p12 : s12.pc = 0x181c := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 12
  · rw [fetch_index SphincsImages.verify state 507 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 40)) 11
  · rw [fetch_index SphincsImages.verify s1 508 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 10
  · rw [fetch_index SphincsImages.verify s2 509 (by decide) (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 20)) 9
  · rw [fetch_index SphincsImages.verify s3 510 (by decide) (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x43)) 8
  · rw [fetch_index SphincsImages.verify s4 511 (by decide) (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 40)) 7
  · rw [fetch_index SphincsImages.verify s5 512 (by decide) (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 6
  · rw [fetch_index SphincsImages.verify s6 513 (by decide) (by simpa using p6)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x43)) 5
  · rw [fetch_index SphincsImages.verify s7 514 (by decide) (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 32)) 4
  · rw [fetch_index SphincsImages.verify s8 515 (by decide) (by simpa using p8)]
    decide
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x6 .x28 0)) 3
  · rw [fetch_index SphincsImages.verify s9 516 (by decide) (by simpa using p9)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, ordinaryStep,
      memoryArgumentsValid, execInstrBr, signExtend12, accessValid,
      rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s10 517 (by decide) (by simpa using p10)]
    decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 24)) 1
  · rw [fetch_index SphincsImages.verify s11 518 (by decide) (by simpa using p11)]
    decide
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s12 519 (by decide) (by simpa using p12)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13,
      ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem ftsAdvance_pc (state : MachineState) (pc : state.pc = 0x17ec) :
    (ftsAdvanceState state).pc = 0x1820 := by
  simp [ftsAdvanceState, execInstrBr, pc]

theorem ftsAdvance_cells (state : MachineState) :
    (ftsAdvanceState state).getMem 0x43028 = state.getMem 0x43028 + 20 ∧
    (ftsAdvanceState state).getMem 0x43018 = state.getMem 0x43020 := by
  constructor <;>
    simp [ftsAdvanceState, execInstrBr, signExtend12,
      MachineState.getMem_setMem_ne,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem ftsAdvance_mem_frame (state : MachineState) (address : Word)
    (notPointer : address ≠ 0x43028) (notIndex : address ≠ 0x43018) :
    (ftsAdvanceState state).getMem address = state.getMem address := by
  change address ≠ (274472#64) at notPointer
  change address ≠ (274456#64) at notIndex
  simp [ftsAdvanceState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne, notPointer, notIndex,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem messageReady_admissible_ftsAdvance (state : MachineState)
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
    let header := ftsTreeHeaderState entered
    let selection := ftsSelectState header
    let pointers := ftsCopyPointers selection
    let copied := SphincsVerifierCopy.copyRootState pointers
    let final := ftsAdvanceState copied
    OrdinarySteps SphincsImages.verify (writeHash state answer) 350 final ∧
      final.pc = 0x1820 ∧
      final.getMem 0x43028 = 0x22cf0 ∧
      (final.getMem 0x43018).toNat = abstractLeaf answer (0 : Fin 24) ∧
      final.getMem 0x43008 =
        BitVec.ofNat 64 (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest answer)).val := by
  obtain ⟨front, copiedPc, treeIndex, leaf, pointer, _⟩ :=
    messageReady_admissible_ftsLeafCopy state pk message randomness
      ready pc answer admissible
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selected := leafStates initial 24 (by decide)
  let accepted := lastAcceptState selected
  let entered := ftsEntryState accepted
  let header := ftsTreeHeaderState entered
  let selection := ftsSelectState header
  let pointers := ftsCopyPointers selection
  let copied := SphincsVerifierCopy.copyRootState pointers
  have back := ftsAdvance_block copied copiedPc
  have finalPc := ftsAdvance_pc copied copiedPc
  have cells := ftsAdvance_cells copied
  exact ⟨by simpa [initial, selected, accepted, entered, header, selection,
      pointers, copied] using front.append back,
    finalPc,
    by rw [cells.1, pointer]; decide,
    by rw [cells.2]; exact leaf,
    by rw [ftsAdvance_mem_frame _ 0x43008 (by decide) (by decide)];
       exact treeIndex⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsAdvance.messageReady_admissible_ftsAdvance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_admissible_ftsAdvance

end SigGolfCandidate.SphincsVerifierFtsAdvance
