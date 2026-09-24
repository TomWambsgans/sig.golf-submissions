import SigGolfCandidate.SphincsVerifierSecondHashParameterData
import SigGolfCandidate.SphincsVerifierHashMemory

/-!
# Second HASH public-parameter bytes

The message-index header cannot alter the witness's public parameter. The
following five-word copy therefore moves that parameter into the HASH input.
-/

namespace SigGolfCandidate.SphincsVerifierSecondHashFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierSecondHashTag
open SigGolfCandidate.SphincsVerifierSecondHashParameter
open SigGolfCandidate.SphincsVerifierSecondHashParameterData
open SigGolfCandidate.SphincsVerifierSecondHashSetup
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierMessageFields

theorem parameterPointers_memory (state : MachineState) (address : Word) :
    (parameterPointers state).getMem address = state.getMem address := by
  simp [parameterPointers, execInstrBr]

theorem hashRegisters_memory (state : MachineState) (address : Word) :
    (hashRegistersState state).getMem address = state.getMem address := by
  simp [hashRegistersState, execInstrBr]

theorem tagBeforeStore_memory (state : MachineState) (address : Word) :
    (tagBeforeStore state).getMem address = state.getMem address := by
  simp [tagBeforeStore, execInstrBr]

theorem tagBeforeStore_pointer (state : MachineState) :
    (tagBeforeStore state).getReg .x7 = 0x40000 := by
  simp [tagBeforeStore, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem header_mem_frame (state : MachineState) (read : Word)
    (first : read ≠ 0x40000) (second : read ≠ 0x40008)
    (third : read ≠ 0x40010) :
    (headerState state).getMem read = state.getMem read := by
  let tagged := tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getMem read = state.getMem read
  simp only [SphincsVerifierHeader.indexState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.indexBeforeStore_pointer, treePointer,
    setWord32_eq]
  have indexAddress : (0x40000 : Word) + signExtend12 (16 : BitVec 12) =
      0x40010 := by decide
  rw [indexAddress,
    show alignToDword (0x40010 : Word) = 0x40010 by decide,
    MachineState.getMem_setMem_ne third,
    SphincsVerifierHeader.indexBeforeStore_memory]
  change (SphincsVerifierHeader.treeState positioned).getMem read =
    state.getMem read
  simp only [SphincsVerifierHeader.treeState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.treeBeforeStore_pointer, positionPointer]
  have treeAddress : (0x40000 : Word) + signExtend12 (8 : BitVec 12) =
      0x40008 := by decide
  rw [treeAddress, MachineState.getMem_setMem_ne second,
    SphincsVerifierHeader.treeBeforeStore_memory]
  change (SphincsVerifierHeader.positionState tagged).getMem read =
    state.getMem read
  simp only [SphincsVerifierHeader.positionState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.positionBeforeStore_pointer, tagPointer,
    setWord32_eq]
  have positionAddress : (0x40000 : Word) + signExtend12 (4 : BitVec 12) =
      0x40004 := by decide
  rw [positionAddress]
  have positionDword : alignToDword (0x40004 : Word) = 0x40000 := by decide
  rw [positionDword, MachineState.getMem_setMem_ne first,
    SphincsVerifierHeader.positionBeforeStore_memory]
  change (tagState state).getMem read = state.getMem read
  simp only [tagState, execInstrBr, MachineState.getMem_setPC]
  rw [tagBeforeStore_pointer, setWord32_eq,
    show (0x40000 : Word) + signExtend12 (0 : BitVec 12) = 0x40000 by decide,
    show alignToDword (0x40000 : Word) = 0x40000 by decide,
    MachineState.getMem_setMem_ne first,
    tagBeforeStore_memory]

theorem secondHashReady_mem_frame (state : MachineState) (read : Word)
    (first : read ≠ 0x40000) (second : read ≠ 0x40008)
    (third : read ≠ 0x40010)
    (parameter : ∀ offset : Fin 5,
      read ≠ alignToDword (0x40014 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val))) :
    (secondHashReadyState state).getMem read = state.getMem read := by
  change (hashRegistersState
    (copyRootState (parameterPointers (headerState state)))).getMem read =
      state.getMem read
  rw [hashRegisters_memory]
  have destination := (parameterPointers_regs (headerState state)).2
  rw [copyRoot_mem_frame (parameterPointers (headerState state)) read (by
    intro offset
    rw [destination]
    exact parameter offset)]
  rw [parameterPointers_memory, header_mem_frame state read first second third]

theorem secondHashReady_field_frame (state : MachineState)
    (pair : CopyPair) (index : Fin 5) :
    (secondHashReadyState state).getWord32 (destinationWord pair index) =
      state.getWord32 (destinationWord pair index) := by
  simp only [MachineState.getWord32]
  apply congrArg (fun word : Word =>
    extractWord32 word (byteOffset (destinationWord pair index) / 4))
  apply secondHashReady_mem_frame
  · cases pair <;> fin_cases index <;> decide
  · cases pair <;> fin_cases index <;> decide
  · cases pair <;> fin_cases index <;> decide
  · intro offset
    cases pair <;> fin_cases index <;> fin_cases offset <;>
      decide

theorem secondHashReady_message_frame (state : MachineState)
    (index : Fin 4) :
    (secondHashReadyState state).getMem
      (BitVec.ofNat 64 (0x40050 + 8 * index.val)) =
      state.getMem (BitVec.ofNat 64 (0x40050 + 8 * index.val)) := by
  apply secondHashReady_mem_frame
  · fin_cases index <;> decide
  · fin_cases index <;> decide
  · fin_cases index <;> decide
  · intro offset
    fin_cases index <;> fin_cases offset <;>
      decide

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
