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
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierSecondHashBytes
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

theorem readyParameter_bytes (pointers : MachineState)
    (destination : pointers.getReg .x7 = 0x40028)
    (pk : SphincsSecurity.PublicKey)
    (encoded : WitnessPrefix pointers pk)
    (i : Nat) (hi : i < 20) :
    (ftsHashReadyState (ftsAdvanceState (copyRootState pointers))).getByte
      (BitVec.ofNat 64 (0x40014 + i)) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  exact parameter_bytes_of_words _ pointers pk
    (readyParameter_from_pointers pointers destination) encoded i hi

private theorem secretSource_word32_byte (state : MachineState)
    (index : Fin 5) (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64 (0x22cdc + 4 * index.val + byte.val)) =
      (state.getWord32 (BitVec.ofNat 64 (0x22cdc + 4 * index.val))).extractLsb'
        (8 * byte.val) 8 := by
  have split := SphincsVerifierSecondHashHeader.extractByte_from_word32
    (state.getMem (alignToDword
      (BitVec.ofNat 64 (0x22cdc + 4 * index.val + byte.val))))
    ⟨(0x22cdc + 4 * index.val + byte.val) % 8,
      Nat.mod_lt _ (by decide)⟩
  fin_cases index <;> fin_cases byte <;>
    simpa [MachineState.getByte, MachineState.getWord32,
      alignToDword, byteOffset] using split

theorem readySecret_bytes (pointers : MachineState)
    (source : pointers.getReg .x6 = 0x22cdc)
    (destination : pointers.getReg .x7 = 0x40028)
    (secret : SphincsSecurity.Digest)
    (encoded : ∀ i, (hi : i < 20) →
      pointers.getByte (BitVec.ofNat 64 (0x22cdc + i)) =
        secret.extractLsb' (8 * i) 8)
    (i : Nat) (hi : i < 20) :
    (ftsHashReadyState (ftsAdvanceState (copyRootState pointers))).getByte
      (BitVec.ofNat 64 (0x40028 + i)) =
      secret.extractLsb' (8 * i) 8 := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  calc
    (ftsHashReadyState (ftsAdvanceState (copyRootState pointers))).getByte
        (BitVec.ofNat 64 (0x40028 + i)) =
      (ftsHashReadyState (ftsAdvanceState (copyRootState pointers))).getByte
        (BitVec.ofNat 64 (0x40028 + 4 * index.val + byte.val)) := by
          simpa only [Nat.add_assoc, split]
    _ = ((ftsHashReadyState (ftsAdvanceState (copyRootState pointers))).getWord32
          (BitVec.ofNat 64 (0x40028 + 4 * index.val))).extractLsb'
            (8 * byte.val) 8 :=
      word32_byte _ 0x40028 (Or.inr (Or.inl rfl)) index byte
    _ = (pointers.getWord32
          (BitVec.ofNat 64 (0x22cdc + 4 * index.val))).extractLsb'
            (8 * byte.val) 8 := by
      rw [readySecret_data pointers source destination index]
    _ = pointers.getByte
          (BitVec.ofNat 64 (0x22cdc + 4 * index.val + byte.val)) :=
      (secretSource_word32_byte pointers index byte).symm
    _ = secret.extractLsb' (8 * i) 8 := by
      simpa only [Nat.add_assoc, split] using encoded i hi

private theorem header_word32_byte (state : MachineState) (base : Nat)
    (supported : base = 0x40000 ∨ base = 0x40004 ∨ base = 0x40010)
    (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64 (base + byte.val)) =
      (state.getWord32 (BitVec.ofNat 64 base)).extractLsb'
        (8 * byte.val) 8 := by
  have split := SphincsVerifierSecondHashHeader.extractByte_from_word32
    (state.getMem (alignToDword (BitVec.ofNat 64 (base + byte.val))))
    ⟨(base + byte.val) % 8, Nat.mod_lt _ (by decide)⟩
  rcases supported with h | h | h <;> subst base <;> fin_cases byte <;>
    simpa [MachineState.getByte, MachineState.getWord32,
      alignToDword, byteOffset] using split

theorem readyHeader_tagByte (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0) (byte : Fin 4) :
    (ftsHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      (0x901#32).extractLsb' (8 * byte.val) 8 := by
  rw [header_word32_byte _ 0x40000 (Or.inl rfl) byte]
  simpa using congrArg (fun value : BitVec 32 => value.extractLsb' (8 * byte.val) 8)
    (SigGolfCandidate.SphincsVerifierFtsHeaderFields.ready_tag state layerZero)

theorem readyHeader_positionByte (state : MachineState)
    (positionZero : state.getMem 0x43010 = 0) (byte : Fin 4) :
    (ftsHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40004 + byte.val)) = 0 := by
  rw [header_word32_byte _ 0x40004 (Or.inr (Or.inl rfl)) byte]
  have address : BitVec.ofNat 64 0x40004 = (0x40004 : Word) := by decide
  rw [address]
  rw [SigGolfCandidate.SphincsVerifierFtsHeaderFields.ready_position state positionZero]
  simp

theorem readyHeader_treeByte (state : MachineState)
    (index : SphincsSecurity.Index)
    (treeIndex : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (byte : Fin 8) :
    (ftsHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40008 + byte.val)) =
      (BitVec.ofNat 64 index.val).extractLsb' (8 * byte.val) 8 := by
  have word : (ftsHashReadyState state).getMem 0x40008 =
      BitVec.ofNat 64 index.val := by
    rw [SigGolfCandidate.SphincsVerifierFtsHeaderFields.ready_tree, treeIndex]
  have word' : (ftsHashReadyState state).getMem (262152#64) =
      BitVec.ofNat 64 index.val := by simpa using word
  fin_cases byte <;>
    simp [MachineState.getByte, alignToDword, byteOffset, word', extractByte,
      BitVec.setWidth_ushiftRight_eq_extractLsb]
  have small : index.val < 2 ^ 64 := by
    have h := index.isLt
    simp only [SphincsSecurity.Index, SphincsSecurity.totalHeight] at h
    omega
  simp [BitVec.extractLsb']
  rw [Nat.mod_eq_of_lt (by simpa using small)]

theorem readyHeader_indexByte (state : MachineState)
    (leaf : SphincsSecurity.FtsLeaf)
    (leafIndex : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (byte : Fin 4) :
    (ftsHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40010 + byte.val)) =
      (BitVec.ofNat 32 leaf.val).extractLsb' (8 * byte.val) 8 := by
  rw [header_word32_byte _ 0x40010 (Or.inr (Or.inr rfl)) byte]
  have address : BitVec.ofNat 64 0x40010 = (0x40010 : Word) := by decide
  rw [address]
  rw [SigGolfCandidate.SphincsVerifierFtsHeaderFields.ready_index,
    leafIndex]
  simp

set_option maxHeartbeats 0 in
theorem readyHeader_bytes (state : MachineState)
    (index : SphincsSecurity.Index) (leaf : SphincsSecurity.FtsLeaf)
    (layerZero : state.getMem 0x43000 = 0)
    (positionZero : state.getMem 0x43010 = 0)
    (treeIndex : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (leafIndex : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (byte : Fin 20) :
    (ftsHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      ((SphincsSecurity.fieldBytes
        (SphincsSecurity.tweakFields 9 0 index.val 0 leaf.val)).map
        UInt8.toBitVec)[byte.val]'(by
          simp [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
            SphincsSecurity.bytesLE]) := by
  fin_cases byte <;>
    first
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_tagByte state layerZero 0
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_tagByte state layerZero 1
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_tagByte state layerZero 2
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_tagByte state layerZero 3
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_positionByte state positionZero 0
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_positionByte state positionZero 1
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_positionByte state positionZero 2
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_positionByte state positionZero 3
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_treeByte state index treeIndex 0
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_treeByte state index treeIndex 1
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_treeByte state index treeIndex 2
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_treeByte state index treeIndex 3
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_treeByte state index treeIndex 4
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_treeByte state index treeIndex 5
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_treeByte state index treeIndex 6
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_treeByte state index treeIndex 7
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_indexByte state leaf leafIndex 0
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_indexByte state leaf leafIndex 1
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_indexByte state leaf leafIndex 2
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        readyHeader_indexByte state leaf leafIndex 3

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
