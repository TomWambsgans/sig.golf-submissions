import SigGolfCandidate.SphincsVerifierFtsForestPayloadFrame
import SigGolfCandidate.SphincsVerifierFtsParentFields

namespace SigGolfCandidate.SphincsVerifierFtsForestHeaderFields
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierFtsForestHeader
open SigGolfCandidate.SphincsVerifierFtsForestHashReady
open SigGolfCandidate.SphincsVerifierFtsParentTag
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem header_tag_position (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0)
    (positionZero : state.getMem 0x43010 = 0) :
    (forestHeaderState state).getWord32 0x40000 = 0xb01 ∧
      (forestHeaderState state).getWord32 0x40004 = 0 := by
  let prefixed := forestPrefixState state
  let treed := SphincsVerifierHeader.treeState prefixed
  have prefixPointer : prefixed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer (forestTagState state)).trans
      (forestTag_hash_pointer state)
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer prefixed).trans prefixPointer
  have values := forestPrefix_values state layerZero positionZero
  constructor
  · change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
    rw [index_word_frame treed _ treePointer (by decide),
      tree_word_frame prefixed _ prefixPointer (by decide)]
    exact values.1
  · change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
    rw [index_word_frame treed _ treePointer (by decide),
      tree_word_frame prefixed _ prefixPointer (by decide)]
    exact values.2

private theorem tag_scratch (state : MachineState) (slot : Fin 4) :
    (forestTagState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  simp only [forestTagState, execInstrBr, MachineState.getMem_setPC]
  have pointer : (forestTagBeforeStore state).getReg .x7 = 0x40000 := by
    simp [forestTagBeforeStore, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  rw [pointer, setWord32_eq]
  rw [MachineState.getMem_setMem_ne (by fin_cases slot <;> decide)]
  simp [forestTagBeforeStore, execInstrBr]

private theorem tree_copy (state : MachineState)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.treeState state).getMem 0x40008 =
      state.getMem 0x43008 := by
  simp [SphincsVerifierHeader.treeState,
    SphincsVerifierHeader.treeBeforeStore, execInstrBr, signExtend12,
    destination, MachineState.getMem_setMem_eq,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

private theorem index_copy (state : MachineState)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.indexState state).getWord32 0x40010 =
      (state.getMem 0x43018).truncate 32 := by
  simp [SphincsVerifierHeader.indexState,
    SphincsVerifierHeader.indexBeforeStore, execInstrBr, signExtend12,
    getWord32_setWord32_same, destination,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

private theorem position_scratch (state : MachineState) (slot : Fin 4)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.positionState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  simp only [SphincsVerifierHeader.positionState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.positionBeforeStore_pointer, destination]
  rw [setWord32_eq]
  rw [MachineState.getMem_setMem_ne (by fin_cases slot <;> decide)]
  exact SphincsVerifierHeader.positionBeforeStore_memory state _

private theorem tree_scratch (state : MachineState) (slot : Fin 4)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.treeState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  simp only [SphincsVerifierHeader.treeState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.treeBeforeStore_pointer, destination]
  rw [MachineState.getMem_setMem_ne (by fin_cases slot <;> decide)]
  exact SphincsVerifierHeader.treeBeforeStore_memory state _

theorem forestHeader_tree (state : MachineState) :
    (forestHeaderState state).getMem 0x40008 = state.getMem 0x43008 := by
  let tagged := forestTagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := forestTag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  change (SphincsVerifierHeader.indexState treed).getMem 0x40008 =
    state.getMem 0x43008
  simp only [SphincsVerifierHeader.indexState, execInstrBr,
    MachineState.getMem_setPC]
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  rw [SphincsVerifierHeader.indexBeforeStore_pointer, treePointer,
    setWord32_eq]
  rw [MachineState.getMem_setMem_ne (by decide),
    SphincsVerifierHeader.indexBeforeStore_memory]
  rw [tree_copy positioned positionPointer]
  have cell1 : positioned.getMem (0x43008#64) = tagged.getMem (0x43008#64) := by
    simpa [positioned] using position_scratch tagged 1 tagPointer
  have cell0 : tagged.getMem (0x43008#64) = state.getMem (0x43008#64) := by
    simpa [tagged] using tag_scratch state 1
  simpa using cell1.trans cell0

theorem forestHeader_index (state : MachineState) :
    (forestHeaderState state).getWord32 0x40010 =
      (state.getMem 0x43018).truncate 32 := by
  let tagged := forestTagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := forestTag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 0x40010 =
    (state.getMem 0x43018).truncate 32
  rw [index_copy treed treePointer]
  have cell2 : treed.getMem (0x43018#64) = positioned.getMem (0x43018#64) := by
    simpa [treed] using tree_scratch positioned 3 positionPointer
  have cell1 : positioned.getMem (0x43018#64) = tagged.getMem (0x43018#64) := by
    simpa [positioned] using position_scratch tagged 3 tagPointer
  have cell0 : tagged.getMem (0x43018#64) = state.getMem (0x43018#64) := by
    simpa [tagged] using tag_scratch state 3
  simpa using congrArg (fun value : Word => value.truncate 32)
    ((cell2.trans cell1).trans cell0)

private theorem ready_word_frame (state : MachineState) (read : Word)
    (outside : ∀ offset : Fin 5,
      alignToDword (0x40014 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) ≠ alignToDword read ∨
      byteOffset (0x40014 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) / 4 ≠
          byteOffset read / 4) :
    (forestHashReadyState state).getWord32 read =
      (forestHeaderState state).getWord32 read := by
  let headed := forestHeaderState state
  let pointers := forestParameterPointers headed
  change (forestHashRegistersState (copyRootState pointers)).getWord32 read =
    headed.getWord32 read
  have registers (s : MachineState) (address : Word) :
      (forestHashRegistersState s).getWord32 address = s.getWord32 address := by
    simp [MachineState.getWord32, forestHashRegistersState, execInstrBr]
  rw [registers]
  rw [copyRoot_getWord32_frame pointers read outside]
  simp [pointers, forestParameterPointers, execInstrBr, MachineState.getWord32]

theorem ready_tag_position (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0)
    (positionZero : state.getMem 0x43010 = 0) :
    (forestHashReadyState state).getWord32 0x40000 = 0xb01 ∧
      (forestHashReadyState state).getWord32 0x40004 = 0 := by
  have values := header_tag_position state layerZero positionZero
  constructor
  · rw [ready_word_frame state 0x40000 (by intro offset; fin_cases offset <;> decide)]
    exact values.1
  · rw [ready_word_frame state 0x40004 (by intro offset; fin_cases offset <;> decide)]
    exact values.2

theorem ready_tree (state : MachineState) :
    (forestHashReadyState state).getMem 0x40008 =
      state.getMem 0x43008 := by
  let headed := forestHeaderState state
  let pointers := forestParameterPointers headed
  have destination := (forestParameterPointers_regs headed).2
  change (forestHashRegistersState (copyRootState pointers)).getMem 0x40008 =
    state.getMem 0x43008
  have registers (s : MachineState) (address : Word) :
      (forestHashRegistersState s).getMem address = s.getMem address := by
    simp [forestHashRegistersState, execInstrBr]
  rw [registers]
  rw [copyRoot_mem_frame pointers 0x40008 (by
    intro offset
    rw [destination]
    fin_cases offset <;> decide)]
  have unchanged : pointers.getMem 0x40008 = headed.getMem 0x40008 := by
    simp [pointers, forestParameterPointers, execInstrBr]
  rw [unchanged]
  exact forestHeader_tree state

theorem ready_index (state : MachineState) :
    (forestHashReadyState state).getWord32 0x40010 =
      (state.getMem 0x43018).truncate 32 := by
  rw [ready_word_frame state 0x40010 (by intro offset; fin_cases offset <;> decide)]
  exact forestHeader_index state


/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestHeaderFields.ready_tag_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ready_tag_position

end SigGolfCandidate.SphincsVerifierFtsForestHeaderFields
