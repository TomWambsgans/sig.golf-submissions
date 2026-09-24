import SigGolfCandidate.SphincsVerifierSecondHashParameterData
import SigGolfCandidate.SphincsVerifierHashMemory

/-!
# Second HASH public-parameter bytes

The message-index header cannot alter the witness's public parameter. The
following five-word copy therefore moves that parameter into the HASH input.
-/

namespace SigGolfCandidate.SphincsVerifierSecondHashFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierSecondHashTag
open SigGolfCandidate.SphincsVerifierSecondHashParameter
open SigGolfCandidate.SphincsVerifierSecondHashParameterData
open SigGolfCandidate.SphincsVerifierSecondHashSetup
open SigGolfCandidate.SphincsVerifierHashMemory

theorem tagBeforeStore_memory (state : MachineState) (address : Word) :
    (tagBeforeStore state).getMem address = state.getMem address := by
  simp [tagBeforeStore, execInstrBr]

theorem tagBeforeStore_pointer (state : MachineState) :
    (tagBeforeStore state).getReg .x7 = 0x40000 := by
  simp [tagBeforeStore, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem tag_word_frame (state : MachineState) (read : Word)
    (other : alignToDword (0x40000 : Word) ≠ alignToDword read ∨
      byteOffset (0x40000 : Word) / 4 ≠ byteOffset read / 4) :
    (tagState state).getWord32 read = state.getWord32 read := by
  simp only [tagState, execInstrBr, MachineState.getWord32]
  rw [tagBeforeStore_pointer]
  have frame := getWord32_setWord32_other
    (tagBeforeStore state) 0x40000 read
    (BitVec.setWidth 32 ((tagBeforeStore state).getReg .x6)) other
  simpa [MachineState.getWord32, signExtend12,
    tagBeforeStore_memory] using frame

theorem header_word_frame (state : MachineState) (read : Word)
    (tagOther : alignToDword (0x40000 : Word) ≠ alignToDword read ∨
      byteOffset (0x40000 : Word) / 4 ≠ byteOffset read / 4)
    (positionOther : alignToDword (0x40004 : Word) ≠ alignToDword read ∨
      byteOffset (0x40004 : Word) / 4 ≠ byteOffset read / 4)
    (treeOther : alignToDword read ≠ (0x40008 : Word))
    (indexOther : alignToDword (0x40010 : Word) ≠ alignToDword read ∨
      byteOffset (0x40010 : Word) / 4 ≠ byteOffset read / 4) :
    (headerState state).getWord32 read = state.getWord32 read := by
  let tagged := tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 read =
    state.getWord32 read
  rw [SphincsVerifierHashMemory.index_word_frame treed read treePointer indexOther,
    SphincsVerifierHashMemory.tree_word_frame positioned read positionPointer treeOther,
    SphincsVerifierHashMemory.position_word_frame tagged read tagPointer positionOther,
    tag_word_frame state read tagOther]

theorem header_parameter_source (state : MachineState) (index : Fin 5) :
    (headerState state).getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  apply header_word_frame <;>
    fin_cases index <;> decide

theorem headerAndParameter_data (state : MachineState) (index : Fin 5) :
    (headerAndParameterState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  rw [headerAndParameterState, parameterState_data, header_parameter_source]

theorem secondHashReady_data (state : MachineState) (index : Fin 5) :
    (secondHashReadyState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  simp only [secondHashReadyState, MachineState.getWord32]
  rw [show (hashRegistersState (headerAndParameterState state)).getMem
      (alignToDword (BitVec.ofNat 64 (0x40014 + 4 * index.val))) =
      (headerAndParameterState state).getMem
        (alignToDword (BitVec.ofNat 64 (0x40014 + 4 * index.val))) by
        simp [hashRegistersState, execInstrBr]]
  exact headerAndParameter_data state index

/-- info: 'SigGolfCandidate.SphincsVerifierSecondHashFrame.secondHashReady_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms secondHashReady_data

end SigGolfCandidate.SphincsVerifierSecondHashFrame
