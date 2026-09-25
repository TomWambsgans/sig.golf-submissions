import SigGolfCandidate.SphincsVerifierWotsFullChain

namespace SigGolfCandidate.SphincsVerifierWotsChainPreserved
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsChainEntry
open SigGolfCandidate.SphincsVerifierWotsChainEnd
open SigGolfCandidate.SphincsVerifierWotsDigitFrame
open SigGolfCandidate.SphincsVerifierWotsFullChain
open SigGolfCandidate.SphincsVerifierWotsChainRound
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem chainRound_preserved (hash : Hash) (state : MachineState)
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
      (∀ address, DigitAddr address →
        final.getMem address = state.getMem address) ∧
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
    stepLoop_to_chain_end_preserved hash digit (chainEntryState state)
      entryPc entryCell
  have middleCounter : middle.getMem 0x43050 =
      BitVec.ofNat 64 chain.val := by
    rw [middleFrame 0x43050 (Or.inl (Or.inl rfl)),
      chainEntry_controlFrame state 0x43050 (Or.inl rfl), counter]
  have middlePointer : middle.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val) := by
    rw [middleFrame 0x43028 (Or.inl (Or.inr rfl)),
      chainEntry_controlFrame state 0x43028 (Or.inr rfl), pointer]
  obtain ⟨endTrace, endPc, endCounter⟩ :=
    chainEnd_block middle chain middlePc middleCounter
  have endPointer := chainEnd_pointer middle chain
    middleCounter middlePointer
  refine ⟨chainEndState middle, middleSteps + 65,
    middleCycles + 65, middleCalls, middleBlocks,
    endPc, endCounter, endPointer, ?_,
    by omega, by omega, middleCallBound, middleBlockBound, ?_⟩
  · intro address digitAddr
    exact (chainEnd_digitFrame middle chain middleCounter address
      digitAddr).trans ((middleFrame address (Or.inr digitAddr)).trans
        (chainEntry_digitFrame state address digitAddr))
  · intro tailSteps result tail
    have endRun := endTrace.then_executes tail
    have middleRun' := middleRun (tailSteps + 40)
      (result.charge 40 0 0) endRun
    have entryRun := entry.then_executes middleRun'
    simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using entryRun

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainPreserved.chainRound_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainRound_preserved

end SigGolfCandidate.SphincsVerifierWotsChainPreserved

namespace SigGolfCandidate.SphincsVerifierWotsChainPreservedGeneral
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsChainEntryGeneral
open SigGolfCandidate.SphincsVerifierWotsChainEndGeneral
open SigGolfCandidate.SphincsVerifierWotsDigitFrame
open SigGolfCandidate.SphincsVerifierWotsChainRoundGeneral
open SigGolfCandidate.SphincsVerifierWotsChainRound
open SigGolfCandidate.SphincsVerifierWotsChainEntry
open SigGolfCandidate.SphincsVerifierWotsChainEnd
open SigGolfCandidate.SphincsVerifierWotsFullChain
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem chainRound_preserved_general (hash : Hash) (state : MachineState)
    (sourceBase : Nat)
    (baseBound : sourceBase + 20 * 52 ≤ 0x40000)
    (baseAligned : sourceBase % 4 = 0)
    (chain : Fin 52) (digit : Fin 8)
    (pc : state.pc = 0x2710)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (sourceBase + 20 * chain.val))
    (decoded : state.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
      BitVec.ofNat 8 digit.val) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc =
        (if chain.val + 1 = 52 then 0x298c else 0x2710) ∧
      final.getMem 0x43050 = BitVec.ofNat 64 (chain.val + 1) ∧
      final.getMem 0x43028 =
        BitVec.ofNat 64 (sourceBase + 20 * (chain.val + 1)) ∧
      (∀ address, DigitAddr address →
        final.getMem address = state.getMem address) ∧
      steps ≤ 94 * (7 - digit.val) + 70 ∧
      cycles ≤ 101 * (7 - digit.val) + 70 ∧
      calls ≤ 7 - digit.val ∧
      blocks ≤ 7 - digit.val ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  obtain ⟨entry, entryPc⟩ := chainEntry_block_general state chain
    (sourceBase + 20 * chain.val)
    (by have := chain.isLt; omega) (by omega) pc pointer counter
  have entryCell : (chainEntryState state).getMem 0x43058 =
      BitVec.ofNat 64 digit.val := by
    rw [chainEntry_step state chain counter, decoded]
    fin_cases digit <;> decide
  obtain ⟨middle, middleSteps, middleCycles, middleCalls, middleBlocks,
      middlePc, middleFrame, middleStepBound, middleCycleBound,
      middleCallBound, middleBlockBound, middleRun⟩ :=
    stepLoop_to_chain_end_preserved hash digit (chainEntryState state)
      entryPc entryCell
  have middleCounter : middle.getMem 0x43050 =
      BitVec.ofNat 64 chain.val := by
    rw [middleFrame 0x43050 (Or.inl (Or.inl rfl)),
      chainEntry_controlFrame state 0x43050 (Or.inl rfl), counter]
  have middlePointer : middle.getMem 0x43028 =
      BitVec.ofNat 64 (sourceBase + 20 * chain.val) := by
    rw [middleFrame 0x43028 (Or.inl (Or.inr rfl)),
      chainEntry_controlFrame state 0x43028 (Or.inr rfl), pointer]
  obtain ⟨endTrace, endPc, endCounter⟩ :=
    chainEnd_block middle chain middlePc middleCounter
  have endPointer := chainEnd_pointer_general middle chain sourceBase
    middleCounter middlePointer
  refine ⟨chainEndState middle, middleSteps + 65,
    middleCycles + 65, middleCalls, middleBlocks,
    endPc, endCounter, endPointer, ?_,
    by omega, by omega, middleCallBound, middleBlockBound, ?_⟩
  · intro address digitAddr
    exact (chainEnd_digitFrame middle chain middleCounter address
      digitAddr).trans ((middleFrame address (Or.inr digitAddr)).trans
        (chainEntry_digitFrame state address digitAddr))
  · intro tailSteps result tail
    have endRun := endTrace.then_executes tail
    have middleRun' := middleRun (tailSteps + 40)
      (result.charge 40 0 0) endRun
    have entryRun := entry.then_executes middleRun'
    simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using entryRun

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainPreservedGeneral.chainRound_preserved_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainRound_preserved_general

end SigGolfCandidate.SphincsVerifierWotsChainPreservedGeneral
