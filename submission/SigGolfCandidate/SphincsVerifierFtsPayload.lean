import SigGolfCandidate.SphincsVerifierFtsHeaderFields
import SigGolfCandidate.SphincsVerifierSecondHashParameterData

/-! Public-parameter and opened-secret words in the first FORS HASH input. -/

namespace SigGolfCandidate.SphincsVerifierFtsPayload
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierFtsParameter
open SigGolfCandidate.SphincsVerifierFtsHeader
open SigGolfCandidate.SphincsVerifierFtsSetup
open SigGolfCandidate.SphincsVerifierFtsAdvance
open SigGolfCandidate.SphincsVerifierSecondHashParameterData
open SigGolfCandidate.SphincsVerifierCopy20DataGeneral
set_option maxRecDepth 16384

theorem parameterState_data (state : MachineState) (index : Fin 5) :
    (parameterState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  change (copyRootState (parameterPointers state)).getWord32 _ = _
  rw [copySecondParameter_data _ (parameterPointers_regs state).1
    (parameterPointers_regs state).2]
  simp [parameterPointers, execInstrBr]

theorem readyParameter_data (state : MachineState) (index : Fin 5) :
    (ftsHashReadyState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      (headerState state).getWord32
        (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  change (hashRegistersState (parameterState (headerState state))).getWord32 _ = _
  have registers (s : MachineState) (address : Word) :
      (hashRegistersState s).getWord32 address = s.getWord32 address := by
    simp [MachineState.getWord32, hashRegistersState, execInstrBr]
  rw [registers]
  exact parameterState_data (headerState state) index

private theorem tag_witness_word (state : MachineState) (index : Fin 5) :
    (tagState state).getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  let read := BitVec.ofNat 64 (0x22cb4 + 4 * index.val)
  have pointer : (tagBeforeStore state).getReg .x7 = 0x40000 := by
    simp [tagBeforeStore, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  have frame := getWord32_setWord32_other
    (tagBeforeStore state) 0x40000 read
    (BitVec.setWidth 32 ((tagBeforeStore state).getReg .x6))
    (by fin_cases index <;> decide)
  simp only [tagState, execInstrBr, MachineState.getWord32]
  rw [pointer]
  simpa [MachineState.getWord32, signExtend12, tagBeforeStore,
    execInstrBr] using frame

private theorem tag_word_frame (state : MachineState) (read : Word)
    (other : alignToDword (0x40000 : Word) ≠ alignToDword read ∨
      byteOffset (0x40000 : Word) / 4 ≠ byteOffset read / 4) :
    (tagState state).getWord32 read = state.getWord32 read := by
  have pointer : (tagBeforeStore state).getReg .x7 = 0x40000 := by
    simp [tagBeforeStore, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  have frame := getWord32_setWord32_other
    (tagBeforeStore state) 0x40000 read
    (BitVec.setWidth 32 ((tagBeforeStore state).getReg .x6)) other
  simp only [tagState, execInstrBr, MachineState.getWord32]
  rw [pointer]
  simpa [MachineState.getWord32, signExtend12, tagBeforeStore,
    execInstrBr] using frame

theorem header_witness_word (state : MachineState) (index : Fin 5) :
    (headerState state).getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  let read := BitVec.ofNat 64 (0x22cb4 + 4 * index.val)
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
  rw [index_word_frame treed read treePointer
      (by fin_cases index <;> decide),
    tree_word_frame positioned read positionPointer
      (by fin_cases index <;> decide),
    position_word_frame tagged read tagPointer
      (by fin_cases index <;> decide)]
  exact tag_witness_word state index

theorem header_secret_word_frame (state : MachineState) (index : Fin 5) :
    (headerState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  let read := BitVec.ofNat 64 (0x40028 + 4 * index.val)
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
  rw [index_word_frame treed read treePointer
      (by fin_cases index <;> decide),
    tree_word_frame positioned read positionPointer
      (by fin_cases index <;> decide),
    position_word_frame tagged read tagPointer
      (by fin_cases index <;> decide)]
  exact tag_word_frame state read (by fin_cases index <;> decide)

theorem ready_secret_word_frame (state : MachineState) (index : Fin 5) :
    (ftsHashReadyState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  let read := BitVec.ofNat 64 (0x40028 + 4 * index.val)
  change (hashRegistersState
    (copyRootState (parameterPointers (headerState state)))).getWord32 read =
      state.getWord32 read
  have registers (s : MachineState) (address : Word) :
      (hashRegistersState s).getWord32 address = s.getWord32 address := by
    simp [MachineState.getWord32, hashRegistersState, execInstrBr]
  rw [registers]
  have destination := (parameterPointers_regs (headerState state)).2
  rw [copyRoot_getWord32_frame
    (parameterPointers (headerState state)) read (by
      intro offset
      rw [destination]
      fin_cases offset <;> fin_cases index <;> decide)]
  have pointers : (parameterPointers (headerState state)).getWord32 read =
      (headerState state).getWord32 read := by
    simp [MachineState.getWord32, parameterPointers, execInstrBr]
  rw [pointers]
  exact header_secret_word_frame state index

theorem advanced_secret_word_frame (state : MachineState) (index : Fin 5) :
    (ftsAdvanceState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  fin_cases index <;>
    (simp only [MachineState.getWord32]
     rw [ftsAdvance_mem_frame state _ (by decide) (by decide)])

theorem readyParameter_witness_word (state : MachineState) (index : Fin 5) :
    (ftsHashReadyState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) :=
  (readyParameter_data state index).trans (header_witness_word state index)

theorem readySecret_data (pointers : MachineState)
    (source : pointers.getReg .x6 = 0x22cdc)
    (destination : pointers.getReg .x7 = 0x40028)
    (index : Fin 5) :
    (ftsHashReadyState (ftsAdvanceState (copyRootState pointers))).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      pointers.getWord32
        (BitVec.ofNat 64 (0x22cdc + 4 * index.val)) := by
  rw [ready_secret_word_frame, advanced_secret_word_frame]
  exact firstFtsCopy_data pointers source destination index

theorem advanced_witness_word_frame (state : MachineState) (index : Fin 5) :
    (ftsAdvanceState state).getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
      state.getWord32
        (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  fin_cases index <;>
    (simp only [MachineState.getWord32]
     rw [ftsAdvance_mem_frame state _ (by decide) (by decide)])

theorem copied_witness_word_frame (pointers : MachineState)
    (destination : pointers.getReg .x7 = 0x40028)
    (index : Fin 5) :
    (copyRootState pointers).getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
      pointers.getWord32
        (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  apply copyRoot_getWord32_frame
  intro offset
  rw [destination]
  fin_cases offset <;> fin_cases index <;> decide

theorem readyParameter_from_pointers (pointers : MachineState)
    (destination : pointers.getReg .x7 = 0x40028)
    (index : Fin 5) :
    (ftsHashReadyState (ftsAdvanceState (copyRootState pointers))).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      pointers.getWord32
        (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  rw [readyParameter_witness_word, advanced_witness_word_frame]
  exact copied_witness_word_frame pointers destination index

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPayload.parameterState_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parameterState_data

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPayload.readySecret_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms readySecret_data

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPayload.readyParameter_from_pointers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms readyParameter_from_pointers

end SigGolfCandidate.SphincsVerifierFtsPayload
