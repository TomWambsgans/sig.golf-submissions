import SigGolfCandidate.SphincsVerifierFtsParameter

/-!
# First FORS leaf HASH setup

The verifier selects the 60-byte input at `0x40000`, the output at `0x42000`,
and the HASH service. The next instruction is ECALL at PC `0x18c8`.
-/

namespace SigGolfCandidate.SphincsVerifierFtsSetup
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsParameter
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

def hashRegistersState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x10 0x40)
  let state := execInstrBr state (.ADDI .x10 .x10 0)
  let state := execInstrBr state (.ADDI .x11 .x0 480)
  let state := execInstrBr state (.LUI .x12 0x42)
  let state := execInstrBr state (.ADDI .x12 .x12 0)
  execInstrBr state (.ADDI .x5 .x0 1)

theorem hashRegisters_block (state : MachineState) (pc : state.pc = 0x18b0) :
    OrdinarySteps SphincsImages.verify state 6 (hashRegistersState state) := by
  let s1 := execInstrBr state (.LUI .x10 0x40)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 480)
  let s4 := execInstrBr s3 (.LUI .x12 0x42)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 0)
  let s6 := execInstrBr s5 (.ADDI .x5 .x0 1)
  have p1 : s1.pc = 0x18b4 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x18b8 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x18bc := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x18c0 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x18c4 := by simp [s5, execInstrBr, p4]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x10 0x40)) 5
  · rw [fetch_index SphincsImages.verify state 556 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 4
  · rw [fetch_index SphincsImages.verify s1 557 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 480)) 3
  · rw [fetch_index SphincsImages.verify s2 558 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x42)) 2
  · rw [fetch_index SphincsImages.verify s3 559 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 0)) 1
  · rw [fetch_index SphincsImages.verify s4 560 (by decide)
      (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x5 .x0 1)) 0
  · rw [fetch_index SphincsImages.verify s5 561 (by decide)
      (by simpa using p5)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem hashRegisters_pc (state : MachineState) (pc : state.pc = 0x18b0) :
    (hashRegistersState state).pc = 0x18c8 := by
  simp [hashRegistersState, execInstrBr, pc]

theorem hashRegisters_ready (state : MachineState) :
    (hashRegistersState state).getReg .x10 = 0x40000 ∧
    (hashRegistersState state).getReg .x11 = 480 ∧
    (hashRegistersState state).getReg .x12 = 0x42000 ∧
    (hashRegistersState state).getReg .x5 = 1 := by
  simp [hashRegistersState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def ftsHashReadyState (state : MachineState) : MachineState :=
  hashRegistersState (headerAndParameterState state)

theorem ftsHashReady_block (state : MachineState) (pc : state.pc = 0x1820) :
    OrdinarySteps SphincsImages.verify state 42 (ftsHashReadyState state) := by
  have first := headerAndParameter_block state pc
  have headerPc := SphincsVerifierFtsHeader.header_next_pc state pc
  have parameterPc := parameter_next_pc
    (SphincsVerifierFtsHeader.headerState state) headerPc
  have second := hashRegisters_block (headerAndParameterState state)
    (by simpa [headerAndParameterState] using parameterPc)
  simpa [ftsHashReadyState] using first.append second

theorem ftsHashReady_pc (state : MachineState) (pc : state.pc = 0x1820) :
    (ftsHashReadyState state).pc = 0x18c8 := by
  have headerPc := SphincsVerifierFtsHeader.header_next_pc state pc
  have parameterPc := parameter_next_pc
    (SphincsVerifierFtsHeader.headerState state) headerPc
  exact hashRegisters_pc (headerAndParameterState state)
    (by simpa [headerAndParameterState] using parameterPc)

theorem ftsHashReady_regs (state : MachineState) :
    (ftsHashReadyState state).getReg .x10 = 0x40000 ∧
    (ftsHashReadyState state).getReg .x11 = 480 ∧
    (ftsHashReadyState state).getReg .x12 = 0x42000 ∧
    (ftsHashReadyState state).getReg .x5 = 1 :=
  hashRegisters_ready _

theorem messageReady_admissible_ftsHashReady (state : MachineState)
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
    let final := ftsHashReadyState advanced
    OrdinarySteps SphincsImages.verify (writeHash state answer) 392 final ∧
      final.pc = 0x18c8 ∧
      final.getReg .x10 = 0x40000 ∧
      final.getReg .x11 = 480 ∧
      final.getReg .x12 = 0x42000 ∧
      final.getReg .x5 = 1 := by
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
  have back := ftsHashReady_block advanced advancedPc
  have registers := ftsHashReady_regs advanced
  exact ⟨by simpa [initial, selected, accepted, entered, firstHeader,
      selection, pointers, copied, advanced] using front.append back,
    ftsHashReady_pc advanced advancedPc,
    registers.1, registers.2.1, registers.2.2.1, registers.2.2.2⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsSetup.messageReady_admissible_ftsHashReady' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_admissible_ftsHashReady

/-- info: 'SigGolfCandidate.SphincsVerifierFtsSetup.ftsHashReady_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ftsHashReady_block

end SigGolfCandidate.SphincsVerifierFtsSetup
