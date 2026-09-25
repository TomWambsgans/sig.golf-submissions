import SigGolfCandidate.SphincsVerifierWotsChainEnd

namespace SigGolfCandidate.SphincsVerifierWotsOuterFrame
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

def Control (address : Word) : Prop :=
  address = 0x43050 ∨ address = 0x43028

private theorem control_ne (address : Word) (control : Control address)
    (written : Word)
    (low : written.toNat < 0x43028) : address ≠ written := by
  rcases control with rfl | rfl
  · intro eq
    subst written
    simp [BitVec.toNat_ofNat] at low
  · intro eq
    subst written
    simp [BitVec.toNat_ofNat] at low

theorem valueCopy_frame (state : MachineState) (address : Word)
    (control : Control address) :
    (stepValueCopied state).getMem address = state.getMem address := by
  have destination : (stepValuePointers state).getReg .x7 = 0x40028 := by
    simp [stepValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (stepValuePointers state) address
    (by intro offset; rw [destination]; rcases control with rfl | rfl <;>
      fin_cases offset <;> decide)
  have pointerFrame : (stepValuePointers state).getMem address =
      state.getMem address := by
    simp [stepValuePointers, execInstrBr]
  exact frame.trans pointerFrame

theorem position_frame (state : MachineState) (address : Word)
    (control : Control address) :
    (stepPositionState state).getMem address = state.getMem address := by
  rcases control with rfl | rfl <;>
    simp [stepPositionState, execInstrBr, signExtend12,
      MachineState.getMem_setMem_ne,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem prefix_frame (state : MachineState) (address : Word)
    (control : Control address) :
    (stepHashPrefixState state).getMem address =
      state.getMem address :=
  (position_frame _ address control).trans (valueCopy_frame _ address control)

theorem tag_frame (state : MachineState) (address : Word)
    (control : Control address) :
    (stepTagState state).getMem address = state.getMem address := by
  rcases control with rfl | rfl
  · simp [stepTagState, execInstrBr, signExtend12, setWord32_eq,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      show (274512#64) ≠ alignToDword (262144#64) by decide]
  · simp [stepTagState, execInstrBr, signExtend12, setWord32_eq,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      show (274472#64) ≠ alignToDword (262144#64) by decide]

theorem header_frame (state : MachineState) (address : Word)
    (control : Control address) :
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
    rw [MachineState.getMem_setMem_ne (control_ne address control _ (by decide))]
    exact SphincsVerifierHeader.positionBeforeStore_memory tagged _
  have treeCell : treed.getMem address = positioned.getMem address := by
    simp only [treed, SphincsVerifierHeader.treeState,
      execInstrBr, MachineState.getMem_setPC]
    rw [SphincsVerifierHeader.treeBeforeStore_pointer, positionDst]
    rw [MachineState.getMem_setMem_ne (control_ne address control _ (by decide))]
    exact SphincsVerifierHeader.treeBeforeStore_memory positioned _
  have indexCell : (SphincsVerifierHeader.indexState treed).getMem
      address = treed.getMem address := by
    simp only [SphincsVerifierHeader.indexState,
      execInstrBr, MachineState.getMem_setPC]
    rw [SphincsVerifierHeader.indexBeforeStore_pointer, treeDst]
    rw [setWord32_eq]
    rw [MachineState.getMem_setMem_ne (control_ne address control _ (by decide))]
    exact SphincsVerifierHeader.indexBeforeStore_memory treed _
  exact indexCell.trans (treeCell.trans
    (positionCell.trans (tag_frame state address control)))

theorem parameter_frame (state : MachineState) (address : Word)
    (control : Control address) :
    (stepParameterState state).getMem address =
      state.getMem address := by
  have destination : (stepParameterPointers state).getReg .x7 =
      0x40014 := by
    simp [stepParameterPointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (stepParameterPointers state) address
    (by intro offset; rw [destination]; rcases control with rfl | rfl <;>
      fin_cases offset <;> decide)
  have pointerFrame : (stepParameterPointers state).getMem address =
      state.getMem address := by
    simp [stepParameterPointers, execInstrBr]
  exact frame.trans pointerFrame

theorem ready_frame (state : MachineState) (address : Word)
    (control : Control address) :
    (stepReady state).getMem address = state.getMem address := by
  have registers (pre : MachineState) :
      (stepHashRegistersState pre).getMem address =
        pre.getMem address := by
    simp [stepHashRegistersState, execInstrBr]
  exact (registers _).trans
    ((parameter_frame _ address control).trans
      ((header_frame _ address control).trans
        (prefix_frame state address control)))

theorem afterHash_frame (hash : Hash) (state : MachineState)
    (address : Word) (control : Control address) :
    (stepAfterHash hash state).getMem address =
      state.getMem address := by
  have destination : (stepReady state).getReg .x12 = 0x42000 := by
    simp [stepReady, stepHashReadyState, stepHashRegistersState,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  have outside : address ≠ 0x42000 ∧ address ≠ 0x42008 ∧
      address ≠ 0x42010 ∧ address ≠ 0x42018 := by
    rcases control with rfl | rfl <;> decide
  have frame := SphincsVerifierFtsLevelInit.writeHash_mem_frame
    (stepReady state) (hash (hashInput (stepReady state))) destination
    address outside.1 outside.2.1 outside.2.2.1 outside.2.2.2
  exact frame.trans (ready_frame state address control)

theorem answerCopy_frame (state : MachineState) (address : Word)
    (control : Control address) :
    (stepAnswerCopyState state).getMem address =
      state.getMem address := by
  have destination : (stepAnswerPointersState state).getReg .x7 =
      0x44b00 := by
    simp [stepAnswerPointersState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (stepAnswerPointersState state) address
    (by intro offset; rw [destination]; rcases control with rfl | rfl <;>
      fin_cases offset <;> decide)
  have pointerFrame : (stepAnswerPointersState state).getMem address =
      state.getMem address := by
    simp [stepAnswerPointersState, execInstrBr]
  exact frame.trans pointerFrame

theorem return_frame (state : MachineState) (address : Word)
    (control : Control address) :
    (stepReturnState state).getMem address =
      state.getMem address := by
  rcases control with rfl | rfl <;>
    simp [stepReturnState, stepAdvanceState, execInstrBr, signExtend12,
      MachineState.getMem_setMem_ne,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem stepNext_controlFrame (hash : Hash) (state : MachineState)
    (address : Word) (control : Control address) :
    (stepNext hash state).getMem address =
      state.getMem address :=
  (return_frame _ address control).trans
    ((answerCopy_frame _ address control).trans
      (afterHash_frame hash state address control))

theorem stepRound_controlFrame (hash : Hash) (state : MachineState)
    (address : Word) (control : Control address) :
    (stepRound hash state).getMem address =
      state.getMem address := by
  rw [stepRound, stepNext_controlFrame hash (stepCheckState state)
    address control]
  simp [stepCheckState, execInstrBr]

/-- info: 'SigGolfCandidate.SphincsVerifierWotsOuterFrame.stepNext_controlFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepNext_controlFrame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsOuterFrame.stepRound_controlFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepRound_controlFrame

end SigGolfCandidate.SphincsVerifierWotsOuterFrame
