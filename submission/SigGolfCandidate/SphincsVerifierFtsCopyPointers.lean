import SigGolfCandidate.SphincsVerifierFtsSelect

/-! The first FORS witness copy reads its source pointer and sets its hash-buffer destination. -/

namespace SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsEntry
open SigGolfCandidate.SphincsVerifierLastLeaf
open SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierMessageHash
set_option maxRecDepth 16384

def ftsCopyPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 40)

theorem ftsCopyPointers_block (state : MachineState)
    (pc : state.pc = 0x17b0) :
    OrdinarySteps SphincsImages.verify state 5 (ftsCopyPointers state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 40)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x7 0x40)
  let s5 := execInstrBr s4 (.ADDI .x7 .x7 40)
  have p1 : s1.pc = 0x17b4 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x17b8 := by simp [s1, s2, execInstrBr, pc]
  have p3 : s3.pc = 0x17bc := by simp [s1, s2, s3, execInstrBr, pc]
  have p4 : s4.pc = 0x17c0 := by simp [s1, s2, s3, s4, execInstrBr, pc]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 4
  · rw [fetch_index SphincsImages.verify state 492 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 40)) 3
  · rw [fetch_index SphincsImages.verify s1 493 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 2
  · rw [fetch_index SphincsImages.verify s2 494 (by decide) (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x7 0x40)) 1
  · rw [fetch_index SphincsImages.verify s3 495 (by decide) (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x7 .x7 40)) 0
  · rw [fetch_index SphincsImages.verify s4 496 (by decide) (by simpa using p4)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem ftsCopyPointers_pc (state : MachineState) (pc : state.pc = 0x17b0) :
    (ftsCopyPointers state).pc = 0x17c4 := by
  simp [ftsCopyPointers, execInstrBr, pc]

theorem ftsCopyPointers_regs (state : MachineState) :
    (ftsCopyPointers state).getReg .x6 = state.getMem 0x43028 ∧
      (ftsCopyPointers state).getReg .x7 = 0x40028 := by
  constructor <;>
    simp [ftsCopyPointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem ftsCopyPointers_mem (state : MachineState) (address : Word) :
    (ftsCopyPointers state).getMem address = state.getMem address := by
  simp [ftsCopyPointers, execInstrBr]

theorem messageReady_admissible_ftsCopyPointers (state : MachineState)
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
    let final := ftsCopyPointers selection
    OrdinarySteps SphincsImages.verify (writeHash state answer) 327 final ∧
      final.pc = 0x17c4 ∧
      final.getReg .x6 = 0x22cdc ∧
      final.getReg .x7 = 0x40028 ∧
      final.getMem 0x43008 =
        BitVec.ofNat 64 (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest answer)).val ∧
      (final.getMem 0x43020).toNat = abstractLeaf answer (0 : Fin 24) := by
  obtain ⟨front, selectionPc, _, treeIndex, pointer, _, _, leaf, _⟩ :=
    messageReady_admissible_ftsSelect state pk message randomness
      ready pc answer admissible
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selected := leafStates initial 24 (by decide)
  let accepted := lastAcceptState selected
  let entered := ftsEntryState accepted
  let header := ftsTreeHeaderState entered
  let selection := ftsSelectState header
  have back := ftsCopyPointers_block selection selectionPc
  have finalPc := ftsCopyPointers_pc selection selectionPc
  have regs := ftsCopyPointers_regs selection
  exact ⟨by simpa [initial, selected, accepted, entered, header, selection] using
      front.append back,
    finalPc,
    by rw [regs.1]; exact pointer,
    regs.2,
    by rw [ftsCopyPointers_mem]; exact treeIndex,
    by rw [ftsCopyPointers_mem]; exact leaf⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsCopyPointers.messageReady_admissible_ftsCopyPointers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_admissible_ftsCopyPointers

end SigGolfCandidate.SphincsVerifierFtsCopyPointers
