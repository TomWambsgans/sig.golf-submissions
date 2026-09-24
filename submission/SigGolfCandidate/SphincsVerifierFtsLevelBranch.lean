import SigGolfCandidate.SphincsVerifierFtsLevelInit

/-! Read the first FORS authentication-path selector and isolate its low bit. -/

namespace SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierFtsResult
set_option maxRecDepth 16384

def parityState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 112)
  let state := execInstrBr state (.LD .x6 .x28 0)
  execInstrBr state (.ANDI .x6 .x6 1)

theorem parity_pc (state : MachineState) (pc : state.pc = 0x1914) :
    (parityState state).pc = 0x1924 := by
  simp [parityState, execInstrBr, pc]

theorem parity_block (state : MachineState) (pc : state.pc = 0x1914) :
    OrdinarySteps SphincsImages.verify state 4 (parityState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 112)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ANDI .x6 .x6 1)
  have p1 : s1.pc = 0x1918 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x191c := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1920 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 581 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 112)) 2
  · rw [fetch_index SphincsImages.verify s1 582 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 583 (by decide)
      (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ANDI .x6 .x6 1)) 0
  · rw [fetch_index SphincsImages.verify s3 584 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem parity_reg (state : MachineState) :
    (parityState state).getReg .x6 = state.getMem 0x43070 &&& 1 := by
  simp [parityState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem parity_mem (state : MachineState) (address : Word) :
    (parityState state).getMem address = state.getMem address := by
  simp [parityState, execInstrBr]

theorem selection_scratch_after_advance (selection : MachineState) :
    let pointers := SphincsVerifierFtsCopyPointers.ftsCopyPointers selection
    let copied := SphincsVerifierCopy.copyRootState pointers
    let advanced := SphincsVerifierFtsAdvance.ftsAdvanceState copied
    advanced.getMem 0x43070 = selection.getMem 0x43070 ∧
      advanced.getMem 0x43040 = selection.getMem 0x43040 := by
  let pointers := SphincsVerifierFtsCopyPointers.ftsCopyPointers selection
  let copied := SphincsVerifierCopy.copyRootState pointers
  have frame (address : Word) (notPointer : address ≠ 0x43028)
      (notIndex : address ≠ 0x43018)
      (notCopy : ∀ offset : Fin 5,
        address ≠ alignToDword
          (0x40028 + signExtend12
            (4#12 * BitVec.ofNat 12 offset.val))) :
      (SphincsVerifierFtsAdvance.ftsAdvanceState copied).getMem address =
        selection.getMem address := by
    rw [SphincsVerifierFtsAdvance.ftsAdvance_mem_frame _ address
      notPointer notIndex]
    change (SphincsVerifierCopy.copyRootState pointers).getMem address = _
    rw [SphincsVerifierCopyMemory.copyRoot_mem_frame]
    · exact SphincsVerifierFtsCopyPointers.ftsCopyPointers_mem selection address
    · intro offset
      rw [(SphincsVerifierFtsCopyPointers.ftsCopyPointers_regs selection).2]
      exact notCopy offset
  constructor
  · apply frame
    all_goals try { intro offset; fin_cases offset <;> decide }
    all_goals decide
  · apply frame
    all_goals try { intro offset; fin_cases offset <;> decide }
    all_goals decide

theorem selection_firstPath_parity (selection : MachineState)
    (answer : BitVec 256) :
    let pointers := SphincsVerifierFtsCopyPointers.ftsCopyPointers selection
    let copied := SphincsVerifierCopy.copyRootState pointers
    let advanced := SphincsVerifierFtsAdvance.ftsAdvanceState copied
    let ready := SphincsVerifierFtsSetup.ftsHashReadyState advanced
    let start := levelInitState (resultState (writeHash ready answer))
    (parityState start).getReg .x6 = selection.getMem 0x43070 &&& 1 ∧
      start.getMem 0x43040 = selection.getMem 0x43040 := by
  let pointers := SphincsVerifierFtsCopyPointers.ftsCopyPointers selection
  let copied := SphincsVerifierCopy.copyRootState pointers
  let advanced := SphincsVerifierFtsAdvance.ftsAdvanceState copied
  let ready := SphincsVerifierFtsSetup.ftsHashReadyState advanced
  let start := levelInitState (resultState (writeHash ready answer))
  have scratch := firstFts_levelStart_scratch advanced answer
  have selected := selection_scratch_after_advance selection
  exact ⟨by rw [parity_reg, scratch.2.1, selected.1],
    by rw [scratch.2.2, selected.2]⟩
theorem parity_preserve_witness (state : MachineState)
    (signature : SphincsSecurity.Signature)
    (witness : SphincsVerifierFtsEarlyFrame.FtsWitness state signature) :
    SphincsVerifierFtsEarlyFrame.FtsWitness (parityState state)
      signature := by
  apply SphincsVerifierFtsEarlyFrame.FtsWitness.transport
    state _ signature witness
  intro i hi
  simp only [MachineState.getByte]
  rw [parity_mem]

set_option maxHeartbeats 0 in
theorem firstFtsLevelParity (state : MachineState)
    (signature : SphincsSecurity.Signature) (answer : BitVec 256)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (witness : SphincsVerifierFtsEarlyFrame.FtsWitness state signature) :
    let hashed := writeHash state answer
    let start := levelInitState (resultState hashed)
    let parity := parityState start
    OrdinarySteps SphincsImages.verify hashed 22 parity ∧
      parity.pc = 0x1924 ∧
      parity.getReg .x6 = start.getMem 0x43070 &&& 1 ∧
      SphincsVerifierFtsEarlyFrame.FtsWitness parity signature := by
  let hashed := writeHash state answer
  let start := levelInitState (resultState hashed)
  obtain ⟨trace, startPc, _, preserved, _⟩ :=
    firstFtsLevelStart state signature answer pc source bits destination witness
  exact ⟨trace.append (parity_block start startPc),
    parity_pc start startPc, parity_reg start,
    parity_preserve_witness start signature preserved⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLevelBranch.parity_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parity_block

end SigGolfCandidate.SphincsVerifierFtsLevelBranch
