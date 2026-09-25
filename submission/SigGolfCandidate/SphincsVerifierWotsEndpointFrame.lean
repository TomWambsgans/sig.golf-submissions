import SigGolfCandidate.SphincsVerifierWotsEndpointCopy

namespace SigGolfCandidate.SphincsVerifierWotsEndpointFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierWotsStepBody
open SigGolfCandidate.SphincsVerifierWotsStepCheck
open SigGolfCandidate.SphincsVerifierWotsStepHashReady
open SigGolfCandidate.SphincsVerifierWotsStepNext
open SigGolfCandidate.SphincsVerifierWotsStepIteration
open SigGolfCandidate.SphincsVerifierWotsChainEntry
open SigGolfCandidate.SphincsVerifierWotsChainEnd
open SigGolfCandidate.SphincsVerifierWotsOuterFrame
open SigGolfCandidate.SphincsVerifierWotsLoop
open SigGolfCandidate.SphincsVerifierWotsEndpointCopy
open SigGolfCandidate.SphincsVerifierWotsDigitFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def ScratchAddr (address : Word) : Prop :=
  0x44000 ≤ address.toNat ∧ address.toNat < 0x44800

theorem scratch_ne (address : Word) (inside : ScratchAddr address)
    (written : Word)
    (outside : written.toNat < 0x44000 ∨ 0x44800 ≤ written.toNat) :
    address ≠ written := by
  intro equal
  have same := congrArg BitVec.toNat equal
  dsimp [ScratchAddr] at inside
  rcases outside with low | high <;> omega

theorem valueCopy_frame (state : MachineState) (address : Word)
    (inside : ScratchAddr address) :
    (stepValueCopied state).getMem address = state.getMem address := by
  have destination : (stepValuePointers state).getReg .x7 = 0x40028 := by
    simp [stepValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (stepValuePointers state) address
    (by
      intro offset
      rw [destination]
      apply scratch_ne address inside
      left
      fin_cases offset <;> decide)
  have pointerFrame : (stepValuePointers state).getMem address =
      state.getMem address := by
    simp [stepValuePointers, execInstrBr]
  exact frame.trans pointerFrame

theorem position_frame (state : MachineState) (address : Word)
    (inside : ScratchAddr address) :
    (stepPositionState state).getMem address = state.getMem address := by
  have different : address ≠ 0x43010 :=
    scratch_ne address inside _ (Or.inl (by decide))
  simp [stepPositionState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  intro equal
  exact (different equal).elim

theorem prefix_frame (state : MachineState) (address : Word)
    (inside : ScratchAddr address) :
    (stepHashPrefixState state).getMem address =
      state.getMem address :=
  (position_frame _ address inside).trans (valueCopy_frame _ address inside)

theorem tag_frame (state : MachineState) (address : Word)
    (inside : ScratchAddr address) :
    (stepTagState state).getMem address = state.getMem address := by
  simp [stepTagState, execInstrBr, signExtend12, setWord32_eq,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    scratch_ne address inside (alignToDword (0x40000#64))
      (Or.inl (by decide))]

theorem header_frame (state : MachineState) (address : Word)
    (inside : ScratchAddr address) :
    (stepHeaderState state).getMem address = state.getMem address := by
  let tagged := stepTagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagDst : tagged.getReg .x7 = 0x40000 := by
    simp [tagged, stepTagState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have positionDst : positioned.getReg .x7 = 0x40000 := by
    rw [SphincsVerifierHeader.position_hash_pointer]; exact tagDst
  have treeDst : treed.getReg .x7 = 0x40000 := by
    rw [SphincsVerifierHeader.tree_hash_pointer]; exact positionDst
  have positionCell : positioned.getMem address = tagged.getMem address := by
    simp only [positioned, SphincsVerifierHeader.positionState,
      execInstrBr, MachineState.getMem_setPC]
    rw [SphincsVerifierHeader.positionBeforeStore_pointer, tagDst]
    rw [setWord32_eq]
    simp [signExtend12, alignToDword]
    split_ifs with equal
    · exact (scratch_ne address inside 0x40000
        (Or.inl (by decide)) equal).elim
    · exact SphincsVerifierHeader.positionBeforeStore_memory tagged _
  have treeCell : treed.getMem address = positioned.getMem address := by
    simp only [treed, SphincsVerifierHeader.treeState,
      execInstrBr, MachineState.getMem_setPC]
    rw [SphincsVerifierHeader.treeBeforeStore_pointer, positionDst]
    simp [signExtend12]
    split_ifs with equal
    · exact (scratch_ne address inside 0x40008
        (Or.inl (by decide)) equal).elim
    · exact SphincsVerifierHeader.treeBeforeStore_memory positioned _
  have indexCell : (SphincsVerifierHeader.indexState treed).getMem
      address = treed.getMem address := by
    simp only [SphincsVerifierHeader.indexState,
      execInstrBr, MachineState.getMem_setPC]
    rw [SphincsVerifierHeader.indexBeforeStore_pointer, treeDst]
    rw [setWord32_eq]
    simp [signExtend12, alignToDword]
    split_ifs with equal
    · exact (scratch_ne address inside 0x40010
        (Or.inl (by decide)) equal).elim
    · exact SphincsVerifierHeader.indexBeforeStore_memory treed _
  exact indexCell.trans (treeCell.trans
    (positionCell.trans (tag_frame state address inside)))

theorem parameter_frame (state : MachineState) (address : Word)
    (inside : ScratchAddr address) :
    (stepParameterState state).getMem address =
      state.getMem address := by
  have destination : (stepParameterPointers state).getReg .x7 =
      0x40014 := by
    simp [stepParameterPointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (stepParameterPointers state) address
    (by
      intro offset
      rw [destination]
      apply scratch_ne address inside
      left
      fin_cases offset <;> decide)
  have pointerFrame : (stepParameterPointers state).getMem address =
      state.getMem address := by
    simp [stepParameterPointers, execInstrBr]
  exact frame.trans pointerFrame

theorem ready_frame (state : MachineState) (address : Word)
    (inside : ScratchAddr address) :
    (stepReady state).getMem address = state.getMem address := by
  have registers (pre : MachineState) :
      (stepHashRegistersState pre).getMem address =
        pre.getMem address := by
    simp [stepHashRegistersState, execInstrBr]
  exact (registers _).trans
    ((parameter_frame _ address inside).trans
      ((header_frame _ address inside).trans
        (prefix_frame state address inside)))

theorem afterHash_frame (hash : Hash) (state : MachineState)
    (address : Word) (inside : ScratchAddr address) :
    (stepAfterHash hash state).getMem address =
      state.getMem address := by
  have destination : (stepReady state).getReg .x12 = 0x42000 := by
    simp [stepReady, stepHashReadyState, stepHashRegistersState,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  have outside : address ≠ 0x42000 ∧ address ≠ 0x42008 ∧
      address ≠ 0x42010 ∧ address ≠ 0x42018 := by
    exact ⟨scratch_ne address inside _ (Or.inl (by decide)),
      scratch_ne address inside _ (Or.inl (by decide)),
      scratch_ne address inside _ (Or.inl (by decide)),
      scratch_ne address inside _ (Or.inl (by decide))⟩
  have frame := SphincsVerifierFtsLevelInit.writeHash_mem_frame
    (stepReady state) (hash (hashInput (stepReady state))) destination
    address outside.1 outside.2.1 outside.2.2.1 outside.2.2.2
  exact frame.trans (ready_frame state address inside)

theorem answerCopy_frame (state : MachineState) (address : Word)
    (inside : ScratchAddr address) :
    (stepAnswerCopyState state).getMem address =
      state.getMem address := by
  have destination : (stepAnswerPointersState state).getReg .x7 =
      0x44b00 := by
    simp [stepAnswerPointersState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (stepAnswerPointersState state) address
    (by
      intro offset
      rw [destination]
      apply scratch_ne address inside
      right
      fin_cases offset <;> decide)
  have pointerFrame : (stepAnswerPointersState state).getMem address =
      state.getMem address := by
    simp [stepAnswerPointersState, execInstrBr]
  exact frame.trans pointerFrame

theorem return_frame (state : MachineState) (address : Word)
    (inside : ScratchAddr address) :
    (stepReturnState state).getMem address =
      state.getMem address := by
  have different : address ≠ 0x43058 :=
    scratch_ne address inside _ (Or.inl (by decide))
  simp [stepReturnState, stepAdvanceState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  intro equal
  exact (different equal).elim

theorem stepNext_scratchFrame (hash : Hash) (state : MachineState)
    (address : Word) (inside : ScratchAddr address) :
    (stepNext hash state).getMem address =
      state.getMem address :=
  (return_frame _ address inside).trans
    ((answerCopy_frame _ address inside).trans
      (afterHash_frame hash state address inside))

theorem stepRound_scratchFrame (hash : Hash) (state : MachineState)
    (address : Word) (inside : ScratchAddr address) :
    (stepRound hash state).getMem address =
      state.getMem address := by
  rw [stepRound, stepNext_scratchFrame hash (stepCheckState state)
    address inside]
  simp [stepCheckState, execInstrBr]

theorem chainEntry_scratchFrame (state : MachineState)
    (address : Word) (inside : ScratchAddr address) :
    (chainEntryState state).getMem address = state.getMem address := by
  have destination : (chainValuePointers state).getReg .x7 = 0x44b00 := by
    simp [chainValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have copyFrame := copyRoot_mem_frame (chainValuePointers state) address
    (by
      intro offset
      rw [destination]
      apply scratch_ne address inside
      right
      fin_cases offset <;> decide)
  have pointerFrame : (chainValuePointers state).getMem address =
      state.getMem address := by
    simp [chainValuePointers, execInstrBr]
  have scratchFrame : (chainDigitState (chainValueCopied state)).getMem
      address = (chainValueCopied state).getMem address := by
    have different : address ≠ 0x43058 :=
      scratch_ne address inside _ (Or.inl (by decide))
    simp [chainDigitState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    intro equal
    exact (different equal).elim
  exact scratchFrame.trans (copyFrame.trans pointerFrame)


def Preserved (address : Word) : Prop :=
  Control address ∨ ScratchAddr address

theorem preserved_round_frame (hash : Hash) (state : MachineState)
    (address : Word) (preserved : Preserved address) :
    (stepRound hash state).getMem address = state.getMem address := by
  rcases preserved with control | digit
  · exact stepRound_controlFrame hash state address control
  · exact stepRound_scratchFrame hash state address digit

theorem stepLoop_to_chain_end_scratch (hash : Hash) (start : Fin 8)
    (state : MachineState)
    (pc : state.pc = 0x2774)
    (cell : state.getMem 0x43058 = BitVec.ofNat 64 start.val) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc = 0x28ec ∧
      (∀ address, Preserved address →
        final.getMem address = state.getMem address) ∧
      steps ≤ 94 * (7 - start.val) + 5 ∧
      cycles ≤ 101 * (7 - start.val) + 5 ∧
      calls ≤ 7 - start.val ∧
      blocks ≤ 7 - start.val ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  let Inv : Nat → MachineState → Prop := fun i current =>
    current.pc = 0x2774 ∧
    current.getMem 0x43058 = BitVec.ofNat 64 (start.val + i) ∧
    ∀ address, Preserved address →
      current.getMem address = state.getMem address
  have next (i : Nat) (current : MachineState)
      (bound : i < 7 - start.val) (inv : Inv i current) :
      ∃ (following : MachineState) (steps cycles calls blocks : Nat),
        Inv (i + 1) following ∧
        steps ≤ 94 ∧ cycles ≤ 101 ∧ calls ≤ 1 ∧ blocks ≤ 1 ∧
        ∀ (tailSteps : Nat) (result : Execution),
          Executes hash SphincsImages.verify following tailSteps result →
          Executes hash SphincsImages.verify current (tailSteps + steps)
            (result.charge cycles calls blocks) := by
    let digit : Fin 8 := ⟨start.val + i, by have := start.isLt; omega⟩
    have small : digit.val < 7 := by dsimp [digit]; omega
    have currentCell : current.getMem 0x43058 =
        BitVec.ofNat 64 digit.val := inv.2.1
    refine ⟨stepRound hash current, 94, 101, 1, 1, ?_, by decide,
      by decide, by decide, by decide, ?_⟩
    · refine ⟨stepRound_pc hash current digit inv.1 currentCell small,
        ?_, ?_⟩
      · rw [stepRound_cell, currentCell]
        change BitVec.ofNat 64 (start.val + i) +
          BitVec.ofNat 64 1 =
          BitVec.ofNat 64 (start.val + (i + 1))
        rw [← BitVec.ofNat_add]
        congr 1
      · intro address control
        exact (preserved_round_frame hash current address control).trans
          (inv.2.2 address control)
    · intro tailSteps result tail
      exact stepRound_exec hash current digit inv.1 currentCell small
        tailSteps result tail
  obtain ⟨seven, steps, cycles, calls, blocks, finalInv,
      stepBound, cycleBound, callBound, blockBound, run⟩ :=
    bounded_loop hash SphincsImages.verify Inv (7 - start.val)
      94 101 1 1 next 0 (7 - start.val) state
      (by omega) ⟨pc, by simpa [Inv] using cell,
        by intro address _; rfl⟩
  have sevenCell : seven.getMem 0x43058 = 7 := by
    have sum : start.val + (7 - start.val) = 7 := by
      have := start.isLt
      omega
    simpa [Inv, sum] using finalInv.2.1
  have checked := stepCheck_block seven (⟨7, by decide⟩ : Fin 8)
    finalInv.1 (by simpa using sevenCell)
  refine ⟨stepCheckState seven, steps + 5, cycles + 5,
    calls, blocks, by simpa using checked.2, ?_,
    by omega, by omega, by simpa using callBound,
    by simpa using blockBound, ?_⟩
  · intro address control
    have frame : (stepCheckState seven).getMem address =
        seven.getMem address := by
      simp [stepCheckState, execInstrBr]
    exact frame.trans (finalInv.2.2 address control)
  · intro tailSteps result tail
    have after := checked.1.then_executes tail
    have before := run (tailSteps + 5) (result.charge 5 0 0) after
    simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using before

theorem endpoint_address (chain : Fin 52) (index : Fin 5) :
    ScratchAddr (alignToDword
      (word (0x44300 + 20 * chain.val) index)) := by
  unfold ScratchAddr
  fin_cases chain <;> fin_cases index <;> decide

theorem chainRound_otherWord (hash : Hash) (state : MachineState)
    (chain : Fin 52) (digit : Fin 8)
    (pc : state.pc = 0x2710)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val))
    (decoded : state.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
      BitVec.ofNat 8 digit.val) :
    ∃ (final middle : MachineState) (steps cycles calls blocks : Nat),
      final.pc =
        (if chain.val + 1 = 52 then 0x298c else 0x2710) ∧
      middle.pc = 0x28ec ∧
      final.getMem 0x43050 = BitVec.ofNat 64 (chain.val + 1) ∧
      final.getMem 0x43028 =
        BitVec.ofNat 64 (0x2547c + 20 * (chain.val + 1)) ∧
      (∀ index : Fin 5,
        final.getWord32 (word (0x44300 + 20 * chain.val) index) =
          middle.getWord32 (word 0x44b00 index)) ∧
      (∀ (other : Fin 52) (index : Fin 5), chain ≠ other →
        final.getWord32 (word (0x44300 + 20 * other.val) index) =
          state.getWord32 (word (0x44300 + 20 * other.val) index)) ∧
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
  obtain ⟨entry, entryPc⟩ :=
    chainEntry_block state chain pc pointer counter
  have entryCell : (chainEntryState state).getMem 0x43058 =
      BitVec.ofNat 64 digit.val := by
    rw [chainEntry_step state chain counter, decoded]
    fin_cases digit <;> decide
  obtain ⟨middle, middleSteps, middleCycles, middleCalls,
      middleBlocks, middlePc, middleFrame, middleStepBound,
      middleCycleBound, middleCallBound, middleBlockBound,
      middleRun⟩ :=
    stepLoop_to_chain_end_scratch hash digit (chainEntryState state)
      entryPc entryCell
  have middleCounter : middle.getMem 0x43050 =
      BitVec.ofNat 64 chain.val := by
    rw [middleFrame 0x43050 (Or.inl (Or.inl rfl)),
      SphincsVerifierWotsChainRound.chainEntry_controlFrame state
        0x43050 (Or.inl rfl), counter]
  have middlePointer : middle.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val) := by
    rw [middleFrame 0x43028 (Or.inl (Or.inr rfl)),
      SphincsVerifierWotsChainRound.chainEntry_controlFrame state
        0x43028 (Or.inr rfl), pointer]
  obtain ⟨endTrace, endPc, endCounter⟩ :=
    chainEnd_block middle chain middlePc middleCounter
  have endPointer := chainEnd_pointer middle chain
    middleCounter middlePointer
  have readFrame : ∀ (other : Fin 52) (index : Fin 5),
      chain ≠ other →
      (chainEndState middle).getWord32
        (word (0x44300 + 20 * other.val) index) =
        state.getWord32 (word (0x44300 + 20 * other.val) index) := by
    intro other index different
    rw [chainEnd_otherWord middle chain other different middleCounter index]
    unfold MachineState.getWord32
    rw [middleFrame _ (Or.inr (endpoint_address other index)),
      chainEntry_scratchFrame state _ (endpoint_address other index)]
  have digitFrame : ∀ address, DigitAddr address →
      (chainEndState middle).getMem address =
        state.getMem address := by
    intro address digitAddr
    have scratch : ScratchAddr address := by
      dsimp [ScratchAddr, DigitAddr] at *
      omega
    exact (chainEnd_digitFrame middle chain middleCounter address
      digitAddr).trans ((middleFrame address (Or.inr scratch)).trans
        (chainEntry_scratchFrame state address scratch))
  have currentValue : ∀ index : Fin 5,
      (chainEndState middle).getWord32
        (word (0x44300 + 20 * chain.val) index) =
          middle.getWord32 (word 0x44b00 index) := by
    intro index
    exact chainEnd_word middle chain middleCounter index
  refine ⟨chainEndState middle, middle, middleSteps + 65,
    middleCycles + 65, middleCalls, middleBlocks,
    endPc, middlePc, endCounter, endPointer, currentValue,
    readFrame, digitFrame,
    by omega, by omega, middleCallBound, middleBlockBound, ?_⟩
  intro tailSteps result tail
  have endRun := endTrace.then_executes tail
  have middleRun' := middleRun (tailSteps + 40)
    (result.charge 40 0 0) endRun
  have entryRun := entry.then_executes middleRun'
  simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using entryRun

/-- info: 'SigGolfCandidate.SphincsVerifierWotsEndpointFrame.stepRound_scratchFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepRound_scratchFrame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsEndpointFrame.stepLoop_to_chain_end_scratch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepLoop_to_chain_end_scratch

/-- info: 'SigGolfCandidate.SphincsVerifierWotsEndpointFrame.chainRound_otherWord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainRound_otherWord

end SigGolfCandidate.SphincsVerifierWotsEndpointFrame
