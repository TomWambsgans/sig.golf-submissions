import SigGolfCandidate.SphincsVerifierFtsHash
import SigGolfCandidate.SphincsVerifierSecondHashHeader

/-! Values of the first FORS HASH header, as written by the exact verifier. -/

namespace SigGolfCandidate.SphincsVerifierFtsHeaderFields
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierFtsHeader
open SigGolfCandidate.SphincsVerifierFtsParameter
open SigGolfCandidate.SphincsVerifierFtsSetup
open SigGolfCandidate.SphincsVerifierFtsAdvance
open SigGolfCandidate.SphincsVerifierFtsLeafCopy
open SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsEntry
open SigGolfCandidate.SphincsVerifierLastLeaf
open SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierMessageHash
set_option maxRecDepth 16384

theorem header_tag (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0) :
    (headerState state).getWord32 0x40000 = 0x901 := by
  let tagged := tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 0x40000 = 0x901
  rw [SphincsVerifierHashMemory.index_word_frame treed 0x40000 treePointer
      (by decide),
    SphincsVerifierHashMemory.tree_word_frame positioned 0x40000
      positionPointer (by decide),
    SphincsVerifierHashMemory.position_word_frame tagged 0x40000
      tagPointer (by decide)]
  exact tag_value state layerZero

private theorem tag_scratch (state : MachineState) (slot : Fin 4) :
    (tagState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  simp only [tagState, execInstrBr, MachineState.getMem_setPC]
  have pointer : (tagBeforeStore state).getReg .x7 = 0x40000 := by
    simp [tagBeforeStore, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  rw [pointer, setWord32_eq]
  rw [MachineState.getMem_setMem_ne (by fin_cases slot <;> decide)]
  simp [tagBeforeStore, execInstrBr]

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

theorem header_position (state : MachineState)
    (positionZero : state.getMem 0x43010 = 0) :
    (headerState state).getWord32 0x40004 = 0 := by
  let tagged := tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 0x40004 = 0
  rw [SphincsVerifierHashMemory.index_word_frame treed 0x40004 treePointer
      (by decide),
    SphincsVerifierHashMemory.tree_word_frame positioned 0x40004
      positionPointer (by decide)]
  apply SphincsVerifierHeader.position_value tagged tagPointer
  have cell : tagged.getMem (0x43010#64) = state.getMem (0x43010#64) := by
    simpa [tagged] using tag_scratch state 2
  rw [cell]
  exact positionZero

theorem header_tree (state : MachineState) :
    (headerState state).getMem 0x40008 = state.getMem 0x43008 := by
  let tagged := tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_hash_pointer state
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

theorem header_index (state : MachineState) :
    (headerState state).getWord32 0x40010 =
      (state.getMem 0x43018).truncate 32 := by
  let tagged := tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_hash_pointer state
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

theorem ready_header_word_frame (state : MachineState) (read : Word)
    (outside : ∀ offset : Fin 5,
      alignToDword (0x40014 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) ≠ alignToDword read ∨
      byteOffset (0x40014 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) / 4 ≠
          byteOffset read / 4) :
    (ftsHashReadyState state).getWord32 read =
      (headerState state).getWord32 read := by
  change (hashRegistersState
    (copyRootState (parameterPointers (headerState state)))).getWord32 read =
      (headerState state).getWord32 read
  have registers : (hashRegistersState
      (copyRootState (parameterPointers (headerState state)))).getWord32 read =
      (copyRootState (parameterPointers (headerState state))).getWord32 read := by
    simp [MachineState.getWord32, hashRegistersState, execInstrBr]
  rw [registers]
  have destination := (parameterPointers_regs (headerState state)).2
  rw [copyRoot_getWord32_frame
    (parameterPointers (headerState state)) read (by
      intro offset
      rw [destination]
      exact outside offset)]
  simp [MachineState.getWord32, parameterPointers, execInstrBr]

theorem ready_tag (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0) :
    (ftsHashReadyState state).getWord32 0x40000 = 0x901 := by
  rw [ready_header_word_frame state 0x40000
      (by intro offset; fin_cases offset <;> decide)]
  exact header_tag state layerZero

theorem ready_position (state : MachineState)
    (positionZero : state.getMem 0x43010 = 0) :
    (ftsHashReadyState state).getWord32 0x40004 = 0 := by
  rw [ready_header_word_frame state 0x40004
      (by intro offset; fin_cases offset <;> decide)]
  exact header_position state positionZero

theorem ready_tree (state : MachineState) :
    (ftsHashReadyState state).getMem 0x40008 = state.getMem 0x43008 := by
  change (hashRegistersState
    (copyRootState (parameterPointers (headerState state)))).getMem 0x40008 =
    state.getMem 0x43008
  have registers : (hashRegistersState
      (copyRootState (parameterPointers (headerState state)))).getMem 0x40008 =
      (copyRootState (parameterPointers (headerState state))).getMem 0x40008 := by
    simp [hashRegistersState, execInstrBr]
  rw [registers]
  have destination := (parameterPointers_regs (headerState state)).2
  rw [copyRoot_mem_frame (parameterPointers (headerState state)) 0x40008
      (by intro offset; rw [destination]; fin_cases offset <;> decide)]
  have pointers : (parameterPointers (headerState state)).getMem 0x40008 =
      (headerState state).getMem 0x40008 := by
    simp [parameterPointers, execInstrBr]
  rw [pointers]
  exact header_tree state

theorem ready_index (state : MachineState) :
    (ftsHashReadyState state).getWord32 0x40010 =
      (state.getMem 0x43018).truncate 32 := by
  rw [ready_header_word_frame state 0x40010
      (by intro offset; fin_cases offset <;> decide)]
  exact header_index state

theorem advance_mem_frame (selection : MachineState) (address : Word)
    (notPointer : address ≠ 0x43028)
    (notIndex : address ≠ 0x43018)
    (outside : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x40028 + signExtend12 (4#12 * BitVec.ofNat 12 offset.val))) :
    (ftsAdvanceState (copyRootState (ftsCopyPointers selection))).getMem address =
      selection.getMem address := by
  let pointers := ftsCopyPointers selection
  let copied := copyRootState pointers
  have destination := (ftsCopyPointers_regs selection).2
  rw [ftsAdvance_mem_frame copied address notPointer notIndex,
    ftsLeafCopy_mem_frame pointers destination address outside,
    ftsCopyPointers_mem]

theorem messageReady_firstFts_layerZero (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer)) :
    let initial := indexStoredState (indexValueState (writeHash state answer))
    let selected := leafStates initial 24 (by decide)
    let accepted := lastAcceptState selected
    let entered := ftsEntryState accepted
    let firstHeader := ftsTreeHeaderState entered
    let selection := ftsSelectState firstHeader
    let pointers := ftsCopyPointers selection
    let copied := copyRootState pointers
    let advanced := ftsAdvanceState copied
    advanced.getMem 0x43000 = 0 := by
  obtain ⟨_, _, layer, _, _, _, _, _, _⟩ :=
    messageReady_admissible_ftsSelect state pk message randomness
      ready pc answer admissible
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selected := leafStates initial 24 (by decide)
  let accepted := lastAcceptState selected
  let entered := ftsEntryState accepted
  let firstHeader := ftsTreeHeaderState entered
  let selection := ftsSelectState firstHeader
  change (ftsAdvanceState (copyRootState
    (ftsCopyPointers selection))).getMem 0x43000 = 0
  rw [advance_mem_frame selection 0x43000 (by decide) (by decide)
    (by intro offset; fin_cases offset <;> decide)]
  exact layer

theorem messageReady_firstFts_positionZero (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256) :
    let initial := indexStoredState (indexValueState (writeHash state answer))
    let selected := leafStates initial 24 (by decide)
    let accepted := lastAcceptState selected
    let entered := ftsEntryState accepted
    let firstHeader := ftsTreeHeaderState entered
    let selection := ftsSelectState firstHeader
    let pointers := ftsCopyPointers selection
    let copied := copyRootState pointers
    let advanced := ftsAdvanceState copied
    advanced.getMem 0x43010 = 0 := by
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selected := leafStates initial 24 (by decide)
  let accepted := lastAcceptState selected
  let entered := ftsEntryState accepted
  let firstHeader := ftsTreeHeaderState entered
  let selection := ftsSelectState firstHeader
  change (ftsAdvanceState (copyRootState
    (ftsCopyPointers selection))).getMem 0x43010 = 0
  rw [advance_mem_frame selection 0x43010 (by decide) (by decide)
    (by intro offset; fin_cases offset <;> decide)]
  exact ftsSelect_position firstHeader

theorem messageReady_firstFts_tag (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer)) :
    let initial := indexStoredState (indexValueState (writeHash state answer))
    let selected := leafStates initial 24 (by decide)
    let accepted := lastAcceptState selected
    let entered := ftsEntryState accepted
    let firstHeader := ftsTreeHeaderState entered
    let selection := ftsSelectState firstHeader
    let pointers := ftsCopyPointers selection
    let copied := copyRootState pointers
    let advanced := ftsAdvanceState copied
    (ftsHashReadyState advanced).getWord32 0x40000 = 0x901 := by
  exact ready_tag _ (messageReady_firstFts_layerZero state pk message
    randomness ready pc answer admissible)

theorem messageReady_firstFts_position (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256) :
    let initial := indexStoredState (indexValueState (writeHash state answer))
    let selected := leafStates initial 24 (by decide)
    let accepted := lastAcceptState selected
    let entered := ftsEntryState accepted
    let firstHeader := ftsTreeHeaderState entered
    let selection := ftsSelectState firstHeader
    let pointers := ftsCopyPointers selection
    let copied := copyRootState pointers
    let advanced := ftsAdvanceState copied
    (ftsHashReadyState advanced).getWord32 0x40004 = 0 := by
  exact ready_position _ (messageReady_firstFts_positionZero state pk
    message randomness ready pc answer)

theorem messageReady_firstFts_tree (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer)) :
    let initial := indexStoredState (indexValueState (writeHash state answer))
    let selected := leafStates initial 24 (by decide)
    let accepted := lastAcceptState selected
    let entered := ftsEntryState accepted
    let firstHeader := ftsTreeHeaderState entered
    let selection := ftsSelectState firstHeader
    let pointers := ftsCopyPointers selection
    let copied := copyRootState pointers
    let advanced := ftsAdvanceState copied
    (ftsHashReadyState advanced).getMem 0x40008 =
      BitVec.ofNat 64 (SphincsSecurity.Concrete.digestIndex
        (SphincsSecurity.truncateMessageDigest answer)).val := by
  obtain ⟨_, _, _, _, treeIndex⟩ :=
    messageReady_admissible_ftsAdvance state pk message randomness
      ready pc answer admissible
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selected := leafStates initial 24 (by decide)
  let accepted := lastAcceptState selected
  let entered := ftsEntryState accepted
  let firstHeader := ftsTreeHeaderState entered
  let selection := ftsSelectState firstHeader
  let pointers := ftsCopyPointers selection
  let copied := copyRootState pointers
  let advanced := ftsAdvanceState copied
  change (ftsHashReadyState advanced).getMem 0x40008 = _
  rw [ready_tree advanced]
  exact treeIndex

theorem messageReady_firstFts_index (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer)) :
    let initial := indexStoredState (indexValueState (writeHash state answer))
    let selected := leafStates initial 24 (by decide)
    let accepted := lastAcceptState selected
    let entered := ftsEntryState accepted
    let firstHeader := ftsTreeHeaderState entered
    let selection := ftsSelectState firstHeader
    let pointers := ftsCopyPointers selection
    let copied := copyRootState pointers
    let advanced := ftsAdvanceState copied
    ((ftsHashReadyState advanced).getWord32 0x40010).toNat =
      abstractLeaf answer (0 : Fin 24) := by
  obtain ⟨_, _, _, leaf, _⟩ :=
    messageReady_admissible_ftsAdvance state pk message randomness
      ready pc answer admissible
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selected := leafStates initial 24 (by decide)
  let accepted := lastAcceptState selected
  let entered := ftsEntryState accepted
  let firstHeader := ftsTreeHeaderState entered
  let selection := ftsSelectState firstHeader
  let pointers := ftsCopyPointers selection
  let copied := copyRootState pointers
  let advanced := ftsAdvanceState copied
  change ((ftsHashReadyState advanced).getWord32 0x40010).toNat = _
  rw [ready_index advanced]
  simp only [BitVec.toNat_setWidth]
  rw [leaf]
  have small : abstractLeaf answer (0 : Fin 24) < 2 ^ 32 := by
    unfold abstractLeaf
    exact (SphincsSecurity.Concrete.digestLeaves
      (SphincsSecurity.truncateMessageDigest answer)
      ⟨0, by decide⟩).isLt.trans (by decide)
  exact Nat.mod_eq_of_lt small

/-- info: 'SigGolfCandidate.SphincsVerifierFtsHeaderFields.ready_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ready_tag

/-- info: 'SigGolfCandidate.SphincsVerifierFtsHeaderFields.messageReady_firstFts_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_firstFts_tag

/-- info: 'SigGolfCandidate.SphincsVerifierFtsHeaderFields.messageReady_firstFts_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_firstFts_index

end SigGolfCandidate.SphincsVerifierFtsHeaderFields
