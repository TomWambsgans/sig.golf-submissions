import SigGolfCandidate.SphincsVerifierWotsValue

namespace SigGolfCandidate.SphincsVerifierWotsSemanticFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierWotsStepBody
open SigGolfCandidate.SphincsVerifierWotsStepCheck
open SigGolfCandidate.SphincsVerifierWotsStepHashReady
open SigGolfCandidate.SphincsVerifierWotsStepNext
open SigGolfCandidate.SphincsVerifierWotsStepIteration
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def SafeAddr (address : Word) : Prop :=
  address.toNat < 0x40000 ∨
    (0x43000 ≤ address.toNat ∧ address.toNat < 0x44000 ∧
      address ≠ 0x43010 ∧ address ≠ 0x43058)

theorem safe_ne (address : Word) (inside : SafeAddr address)
    (written : Word)
    (outside : (0x40000 ≤ written.toNat ∧ written.toNat < 0x43000) ∨
      0x44000 ≤ written.toNat ∨ written = 0x43010 ∨ written = 0x43058) :
    address ≠ written := by
  intro equal
  rcases inside with low | ⟨lower, upper, noPosition, noStep⟩
  · rcases outside with ⟨lo, _⟩ | high | pos | step
    · have := congrArg BitVec.toNat equal; omega
    · have := congrArg BitVec.toNat equal; omega
    · have := congrArg BitVec.toNat equal; simp [pos] at this; omega
    · have := congrArg BitVec.toNat equal; simp [step] at this; omega
  · rcases outside with ⟨_, high⟩ | high | pos | step
    · have := congrArg BitVec.toNat equal; omega
    · have := congrArg BitVec.toNat equal; omega
    · exact noPosition (equal.trans pos)
    · exact noStep (equal.trans step)

theorem valueCopy_frame (state : MachineState) (address : Word)
    (inside : SafeAddr address) :
    (stepValueCopied state).getMem address = state.getMem address := by
  have destination : (stepValuePointers state).getReg .x7 = 0x40028 := by
    simp [stepValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (stepValuePointers state) address
    (by
      intro offset
      rw [destination]
      apply safe_ne address inside
      left
      fin_cases offset <;> decide)
  have pointerFrame : (stepValuePointers state).getMem address =
      state.getMem address := by
    simp [stepValuePointers, execInstrBr]
  exact frame.trans pointerFrame

theorem position_frame (state : MachineState) (address : Word)
    (inside : SafeAddr address) :
    (stepPositionState state).getMem address = state.getMem address := by
  have different : address ≠ 0x43010 :=
    safe_ne address inside _ (Or.inr (Or.inr (Or.inl rfl)))
  simp [stepPositionState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  intro equal
  exact (different equal).elim

theorem prefix_frame (state : MachineState) (address : Word)
    (inside : SafeAddr address) :
    (stepHashPrefixState state).getMem address =
      state.getMem address :=
  (position_frame _ address inside).trans (valueCopy_frame _ address inside)

theorem tag_frame (state : MachineState) (address : Word)
    (inside : SafeAddr address) :
    (stepTagState state).getMem address = state.getMem address := by
  simp [stepTagState, execInstrBr, signExtend12, setWord32_eq,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    safe_ne address inside (alignToDword (0x40000#64))
      (Or.inl (by decide))]

theorem header_frame (state : MachineState) (address : Word)
    (inside : SafeAddr address) :
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
    · exact (safe_ne address inside 0x40000
        (Or.inl (by decide)) equal).elim
    · exact SphincsVerifierHeader.positionBeforeStore_memory tagged _
  have treeCell : treed.getMem address = positioned.getMem address := by
    simp only [treed, SphincsVerifierHeader.treeState,
      execInstrBr, MachineState.getMem_setPC]
    rw [SphincsVerifierHeader.treeBeforeStore_pointer, positionDst]
    simp [signExtend12]
    split_ifs with equal
    · exact (safe_ne address inside 0x40008
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
    · exact (safe_ne address inside 0x40010
        (Or.inl (by decide)) equal).elim
    · exact SphincsVerifierHeader.indexBeforeStore_memory treed _
  exact indexCell.trans (treeCell.trans
    (positionCell.trans (tag_frame state address inside)))

theorem parameter_frame (state : MachineState) (address : Word)
    (inside : SafeAddr address) :
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
      apply safe_ne address inside
      left
      fin_cases offset <;> decide)
  have pointerFrame : (stepParameterPointers state).getMem address =
      state.getMem address := by
    simp [stepParameterPointers, execInstrBr]
  exact frame.trans pointerFrame

theorem ready_frame (state : MachineState) (address : Word)
    (inside : SafeAddr address) :
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
    (address : Word) (inside : SafeAddr address) :
    (stepAfterHash hash state).getMem address =
      state.getMem address := by
  have destination : (stepReady state).getReg .x12 = 0x42000 := by
    simp [stepReady, stepHashReadyState, stepHashRegistersState,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  have outside : address ≠ 0x42000 ∧ address ≠ 0x42008 ∧
      address ≠ 0x42010 ∧ address ≠ 0x42018 := by
    exact ⟨safe_ne address inside _ (Or.inl (by decide)),
      safe_ne address inside _ (Or.inl (by decide)),
      safe_ne address inside _ (Or.inl (by decide)),
      safe_ne address inside _ (Or.inl (by decide))⟩
  have frame := SphincsVerifierFtsLevelInit.writeHash_mem_frame
    (stepReady state) (hash (hashInput (stepReady state))) destination
    address outside.1 outside.2.1 outside.2.2.1 outside.2.2.2
  exact frame.trans (ready_frame state address inside)

theorem answerCopy_frame (state : MachineState) (address : Word)
    (inside : SafeAddr address) :
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
      apply safe_ne address inside
      right
      left
      fin_cases offset <;> decide)
  have pointerFrame : (stepAnswerPointersState state).getMem address =
      state.getMem address := by
    simp [stepAnswerPointersState, execInstrBr]
  exact frame.trans pointerFrame

theorem return_frame (state : MachineState) (address : Word)
    (inside : SafeAddr address) :
    (stepReturnState state).getMem address =
      state.getMem address := by
  have different : address ≠ 0x43058 :=
    safe_ne address inside _ (Or.inr (Or.inr (Or.inr rfl)))
  simp [stepReturnState, stepAdvanceState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  intro equal
  exact (different equal).elim

theorem stepNext_safeFrame (hash : Hash) (state : MachineState)
    (address : Word) (inside : SafeAddr address) :
    (stepNext hash state).getMem address =
      state.getMem address :=
  (return_frame _ address inside).trans
    ((answerCopy_frame _ address inside).trans
      (afterHash_frame hash state address inside))



#print axioms stepNext_safeFrame

end SigGolfCandidate.SphincsVerifierWotsSemanticFrame
