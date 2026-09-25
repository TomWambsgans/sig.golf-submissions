import SigGolfCandidate.SphincsVerifierWotsChainRound

namespace SigGolfCandidate.SphincsVerifierWotsDigitFrame
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
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def DigitAddr (address : Word) : Prop :=
  0x44000 ≤ address.toNat ∧ address.toNat < 0x44040

theorem digit_ne (address : Word) (inside : DigitAddr address)
    (written : Word)
    (outside : written.toNat < 0x44000 ∨ 0x44040 ≤ written.toNat) :
    address ≠ written := by
  intro equal
  have same := congrArg BitVec.toNat equal
  dsimp [DigitAddr] at inside
  rcases outside with low | high <;> omega

theorem valueCopy_frame (state : MachineState) (address : Word)
    (inside : DigitAddr address) :
    (stepValueCopied state).getMem address = state.getMem address := by
  have destination : (stepValuePointers state).getReg .x7 = 0x40028 := by
    simp [stepValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (stepValuePointers state) address
    (by
      intro offset
      rw [destination]
      apply digit_ne address inside
      left
      fin_cases offset <;> decide)
  have pointerFrame : (stepValuePointers state).getMem address =
      state.getMem address := by
    simp [stepValuePointers, execInstrBr]
  exact frame.trans pointerFrame

theorem position_frame (state : MachineState) (address : Word)
    (inside : DigitAddr address) :
    (stepPositionState state).getMem address = state.getMem address := by
  have different : address ≠ 0x43010 :=
    digit_ne address inside _ (Or.inl (by decide))
  simp [stepPositionState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  intro equal
  exact (different equal).elim

theorem prefix_frame (state : MachineState) (address : Word)
    (inside : DigitAddr address) :
    (stepHashPrefixState state).getMem address =
      state.getMem address :=
  (position_frame _ address inside).trans (valueCopy_frame _ address inside)

theorem tag_frame (state : MachineState) (address : Word)
    (inside : DigitAddr address) :
    (stepTagState state).getMem address = state.getMem address := by
  simp [stepTagState, execInstrBr, signExtend12, setWord32_eq,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    digit_ne address inside (alignToDword (0x40000#64))
      (Or.inl (by decide))]

theorem header_frame (state : MachineState) (address : Word)
    (inside : DigitAddr address) :
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
    · exact (digit_ne address inside 0x40000
        (Or.inl (by decide)) equal).elim
    · exact SphincsVerifierHeader.positionBeforeStore_memory tagged _
  have treeCell : treed.getMem address = positioned.getMem address := by
    simp only [treed, SphincsVerifierHeader.treeState,
      execInstrBr, MachineState.getMem_setPC]
    rw [SphincsVerifierHeader.treeBeforeStore_pointer, positionDst]
    simp [signExtend12]
    split_ifs with equal
    · exact (digit_ne address inside 0x40008
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
    · exact (digit_ne address inside 0x40010
        (Or.inl (by decide)) equal).elim
    · exact SphincsVerifierHeader.indexBeforeStore_memory treed _
  exact indexCell.trans (treeCell.trans
    (positionCell.trans (tag_frame state address inside)))

theorem parameter_frame (state : MachineState) (address : Word)
    (inside : DigitAddr address) :
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
      apply digit_ne address inside
      left
      fin_cases offset <;> decide)
  have pointerFrame : (stepParameterPointers state).getMem address =
      state.getMem address := by
    simp [stepParameterPointers, execInstrBr]
  exact frame.trans pointerFrame

theorem ready_frame (state : MachineState) (address : Word)
    (inside : DigitAddr address) :
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
    (address : Word) (inside : DigitAddr address) :
    (stepAfterHash hash state).getMem address =
      state.getMem address := by
  have destination : (stepReady state).getReg .x12 = 0x42000 := by
    simp [stepReady, stepHashReadyState, stepHashRegistersState,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  have outside : address ≠ 0x42000 ∧ address ≠ 0x42008 ∧
      address ≠ 0x42010 ∧ address ≠ 0x42018 := by
    exact ⟨digit_ne address inside _ (Or.inl (by decide)),
      digit_ne address inside _ (Or.inl (by decide)),
      digit_ne address inside _ (Or.inl (by decide)),
      digit_ne address inside _ (Or.inl (by decide))⟩
  have frame := SphincsVerifierFtsLevelInit.writeHash_mem_frame
    (stepReady state) (hash (hashInput (stepReady state))) destination
    address outside.1 outside.2.1 outside.2.2.1 outside.2.2.2
  exact frame.trans (ready_frame state address inside)

theorem answerCopy_frame (state : MachineState) (address : Word)
    (inside : DigitAddr address) :
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
      apply digit_ne address inside
      right
      fin_cases offset <;> decide)
  have pointerFrame : (stepAnswerPointersState state).getMem address =
      state.getMem address := by
    simp [stepAnswerPointersState, execInstrBr]
  exact frame.trans pointerFrame

theorem return_frame (state : MachineState) (address : Word)
    (inside : DigitAddr address) :
    (stepReturnState state).getMem address =
      state.getMem address := by
  have different : address ≠ 0x43058 :=
    digit_ne address inside _ (Or.inl (by decide))
  simp [stepReturnState, stepAdvanceState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  intro equal
  exact (different equal).elim

theorem stepNext_digitFrame (hash : Hash) (state : MachineState)
    (address : Word) (inside : DigitAddr address) :
    (stepNext hash state).getMem address =
      state.getMem address :=
  (return_frame _ address inside).trans
    ((answerCopy_frame _ address inside).trans
      (afterHash_frame hash state address inside))

theorem digit_address (j : Fin 52) :
    DigitAddr (alignToDword (BitVec.ofNat 64 (0x44000 + j.val))) := by
  have aligned : alignToDword (BitVec.ofNat 64 (0x44000 + j.val)) =
      BitVec.ofNat 64 (0x44000 + 8 * (j.val / 8)) := by
    have ha : ((BitVec.ofNat 64 0x44000).toNat % 8 = 0) := by decide
    have hover : (BitVec.ofNat 64 0x44000).toNat + j.val < 2 ^ 64 := by
      have := j.isLt
      simpa using (show 0x44000 + j.val < 2 ^ 64 by omega)
    simpa only [BitVec.ofNat_add] using
      (alignToDword_add_ofNat_of_aligned ha hover)
  rw [aligned]
  simp only [DigitAddr, BitVec.toNat_ofNat]
  have small : 0x44000 + 8 * (j.val / 8) < 2 ^ 64 := by
    have := j.isLt
    omega
  rw [Nat.mod_eq_of_lt small]
  have := j.isLt
  constructor <;> omega

theorem stepRound_digitFrame (hash : Hash) (state : MachineState)
    (address : Word) (inside : DigitAddr address) :
    (stepRound hash state).getMem address =
      state.getMem address := by
  rw [stepRound, stepNext_digitFrame hash (stepCheckState state)
    address inside]
  simp [stepCheckState, execInstrBr]

theorem chainEntry_digitFrame (state : MachineState)
    (address : Word) (inside : DigitAddr address) :
    (chainEntryState state).getMem address = state.getMem address := by
  have destination : (chainValuePointers state).getReg .x7 = 0x44b00 := by
    simp [chainValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have copyFrame := copyRoot_mem_frame (chainValuePointers state) address
    (by
      intro offset
      rw [destination]
      apply digit_ne address inside
      right
      fin_cases offset <;> decide)
  have pointerFrame : (chainValuePointers state).getMem address =
      state.getMem address := by
    simp [chainValuePointers, execInstrBr]
  have digitFrame : (chainDigitState (chainValueCopied state)).getMem
      address = (chainValueCopied state).getMem address := by
    have different : address ≠ 0x43058 :=
      digit_ne address inside _ (Or.inl (by decide))
    simp [chainDigitState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    intro equal
    exact (different equal).elim
  exact digitFrame.trans (copyFrame.trans pointerFrame)

theorem chainEnd_digitFrame (state : MachineState) (chain : Fin 52)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (address : Word) (inside : DigitAddr address) :
    (chainEndState state).getMem address = state.getMem address := by
  let pointers := endpointSourceState (endpointPointersState state)
  have destination : pointers.getReg .x7 =
      BitVec.ofNat 64 (0x44300 + 20 * chain.val) := by
    simpa [pointers, endpointSourceState, execInstrBr,
      MachineState.getReg_setReg_ne] using
      endpointPointers_regs state chain counter
  have copyFrame := copyRoot_mem_frame pointers address (by
    intro offset
    rw [destination]
    apply digit_ne address inside
    right
    fin_cases chain <;> fin_cases offset <;> decide)
  have pointerFrame : pointers.getMem address = state.getMem address := by
    simp [pointers, endpointSourceState, endpointPointersState, execInstrBr]
  have advanceFrame :
      (chainBranchState (chainAdvanceState
        (pointerAdvanceState (copyRootState pointers)))).getMem address =
        (copyRootState pointers).getMem address := by
    have pointerDifferent : address ≠ 0x43028 :=
      digit_ne address inside _ (Or.inl (by decide))
    have chainDifferent : address ≠ 0x43050 :=
      digit_ne address inside _ (Or.inl (by decide))
    simp [chainBranchState, chainAdvanceState, pointerAdvanceState,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    split_ifs with equal1 equal2
    · exact (chainDifferent equal1).elim
    · exact (pointerDifferent equal2).elim
    · rfl
  exact advanceFrame.trans (copyFrame.trans pointerFrame)

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDigitFrame.stepNext_digitFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepNext_digitFrame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDigitFrame.stepRound_digitFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepRound_digitFrame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDigitFrame.chainEnd_digitFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainEnd_digitFrame

end SigGolfCandidate.SphincsVerifierWotsDigitFrame
