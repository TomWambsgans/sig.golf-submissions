import SigGolfCandidate.SphincsVerifierWotsOuterLoop

namespace SigGolfCandidate.SphincsVerifierWotsChainRound
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierWotsChainEntry
open SigGolfCandidate.SphincsVerifierWotsChainEnd
open SigGolfCandidate.SphincsVerifierWotsOuterFrame
open SigGolfCandidate.SphincsVerifierWotsOuterLoop
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem chainEntry_controlFrame (state : MachineState)
    (address : Word) (control : Control address) :
    (chainEntryState state).getMem address =
      state.getMem address := by
  have destination : (chainValuePointers state).getReg .x7 =
      0x44b00 := by
    simp [chainValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have copyFrame := copyRoot_mem_frame (chainValuePointers state) address
    (by intro offset; rw [destination]; rcases control with rfl | rfl <;>
      fin_cases offset <;> decide)
  have pointerFrame : (chainValuePointers state).getMem address =
      state.getMem address := by
    simp [chainValuePointers, execInstrBr]
  have digitFrame : (chainDigitState (chainValueCopied state)).getMem
      address = (chainValueCopied state).getMem address := by
    rcases control with rfl | rfl <;>
      simp [chainDigitState, execInstrBr, signExtend12,
        MachineState.getMem_setMem_ne,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact digitFrame.trans (copyFrame.trans pointerFrame)

theorem chainRound (hash : Hash) (state : MachineState)
    (chain : Fin 52) (digit : Fin 8)
    (pc : state.pc = 0x2710)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val))
    (decoded : state.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
      BitVec.ofNat 8 digit.val) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc =
        (if chain.val + 1 = 52 then 0x298c else 0x2710) ∧
      final.getMem 0x43050 = BitVec.ofNat 64 (chain.val + 1) ∧
      final.getMem 0x43028 =
        BitVec.ofNat 64 (0x2547c + 20 * (chain.val + 1)) ∧
      steps ≤ 94 * (7 - digit.val) + 70 ∧
      cycles ≤ 101 * (7 - digit.val) + 70 ∧
      calls ≤ 7 - digit.val ∧
      blocks ≤ 7 - digit.val ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  obtain ⟨entry, entryPc⟩ := chainEntry_block state chain pc pointer counter
  have entryCell : (chainEntryState state).getMem 0x43058 =
      BitVec.ofNat 64 digit.val := by
    rw [chainEntry_step state chain counter, decoded]
    fin_cases digit <;> decide
  obtain ⟨middle, middleSteps, middleCycles, middleCalls, middleBlocks,
      middlePc, middleFrame, middleStepBound, middleCycleBound,
      middleCallBound, middleBlockBound, middleRun⟩ :=
    stepLoop_to_chain_end_frame hash digit (chainEntryState state)
      entryPc entryCell
  have middleCounter : middle.getMem 0x43050 =
      BitVec.ofNat 64 chain.val := by
    rw [middleFrame 0x43050 (Or.inl rfl),
      chainEntry_controlFrame state 0x43050 (Or.inl rfl), counter]
  have middlePointer : middle.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val) := by
    rw [middleFrame 0x43028 (Or.inr rfl),
      chainEntry_controlFrame state 0x43028 (Or.inr rfl), pointer]
  obtain ⟨endTrace, endPc, endCounter⟩ :=
    chainEnd_block middle chain middlePc middleCounter
  have endPointer := chainEnd_pointer middle chain
    middleCounter middlePointer
  refine ⟨chainEndState middle, middleSteps + 65,
    middleCycles + 65, middleCalls, middleBlocks,
    endPc, endCounter, endPointer,
    by omega, by omega, middleCallBound, middleBlockBound, ?_⟩
  intro tailSteps result tail
  have endRun := endTrace.then_executes tail
  have middleRun' := middleRun (tailSteps + 40)
    (result.charge 40 0 0) endRun
  have entryRun := entry.then_executes middleRun'
  simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using entryRun

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainRound.chainRound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chainRound

end SigGolfCandidate.SphincsVerifierWotsChainRound
