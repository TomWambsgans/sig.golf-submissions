import SigGolfCandidate.SphincsVerifierFtsGenericFirstQuery

/-! FORS parent HASH header at an arbitrary level, retaining the same fixed domain. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsParentTag
open SigGolfCandidate.SphincsVerifierFtsParentHeader
open SigGolfCandidate.SphincsVerifierFtsParentFields
open SigGolfCandidate.SphincsVerifierFtsParentHeaderBytes
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
set_option maxRecDepth 16384

theorem parentPosition_value_generic (state : MachineState)
    (destination : state.getReg .x7 = 0x40000)
    (position : Word)
    (positionValue : state.getMem 0x43010 = position) :
    (SphincsVerifierHeader.positionState state).getWord32 0x40004 =
      position.truncate 32 := by
  change state.getMem (274448#64) = position at positionValue
  simp [SphincsVerifierHeader.positionState,
    SphincsVerifierHeader.positionBeforeStore, execInstrBr,
    signExtend12, getWord32_setWord32_same, destination,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, positionValue]

theorem parentPrefix_values_generic (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0)
    (position : Word)
    (positionValue : state.getMem 0x43010 = position) :
    (parentPrefixState state).getWord32 0x40000 = 0xa01 ∧
      (parentPrefixState state).getWord32 0x40004 =
        position.truncate 32 := by
  constructor
  · rw [parentPrefixState,
      parentPosition_preserve_tag _ (parentTag_hash_pointer state),
      parentTag_value state layerZero]
  · apply parentPosition_value_generic _ (parentTag_hash_pointer state)
      position
    rw [parentTag_mem_frame state 0x43010 (by decide)]
    exact positionValue

theorem header_tag_position_generic (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0)
    (position : Word)
    (positionValue : state.getMem 0x43010 = position) :
    (parentHeaderState state).getWord32 0x40000 = 0xa01 ∧
      (parentHeaderState state).getWord32 0x40004 =
        position.truncate 32 := by
  let prefixed := parentPrefixState state
  let treed := SphincsVerifierHeader.treeState prefixed
  have prefixPointer : prefixed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer (parentTagState state)).trans
      (parentTag_hash_pointer state)
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer prefixed).trans prefixPointer
  have values := parentPrefix_values_generic state layerZero position
    positionValue
  constructor
  · change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
    rw [index_word_frame treed _ treePointer (by decide),
      tree_word_frame prefixed _ prefixPointer (by decide)]
    exact values.1
  · change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
    rw [index_word_frame treed _ treePointer (by decide),
      tree_word_frame prefixed _ prefixPointer (by decide)]
    exact values.2

theorem ready_tag_position_generic (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0)
    (position : Word)
    (positionValue : state.getMem 0x43010 = position) :
    (parentHashReadyState state).getWord32 0x40000 = 0xa01 ∧
      (parentHashReadyState state).getWord32 0x40004 =
        position.truncate 32 := by
  have values := header_tag_position_generic state layerZero position
    positionValue
  have frame (read : Word)
      (outside : ∀ offset : Fin 5,
        alignToDword (0x40014 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)) ≠ alignToDword read ∨
        byteOffset (0x40014 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)) / 4 ≠
            byteOffset read / 4) :
      (parentHashReadyState state).getWord32 read =
        (parentHeaderState state).getWord32 read := by
    let headed := parentHeaderState state
    let pointers := parameterPointers headed
    change (hashRegistersState (copyRootState pointers)).getWord32 read =
      headed.getWord32 read
    have registers (s : MachineState) (address : Word) :
        (hashRegistersState s).getWord32 address = s.getWord32 address := by
      simp [MachineState.getWord32, hashRegistersState, execInstrBr]
    rw [registers]
    rw [copyRoot_getWord32_frame pointers read outside]
    simp [pointers, parameterPointers, execInstrBr, MachineState.getWord32]
  constructor
  · rw [frame 0x40000
      (by intro offset; fin_cases offset <;> decide)]
    exact values.1
  · rw [frame 0x40004
      (by intro offset; fin_cases offset <;> decide)]
    exact values.2

theorem ready_tag_byte_generic (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0)
    (position : Word)
    (positionValue : state.getMem 0x43010 = position)
    (byte : Fin 4) :
    (parentHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
        (0xa01#32).extractLsb' (8 * byte.val) 8 := by
  have split := variableWord_byte (parentHashReadyState state) 0x40000
    (by decide) (by decide) 0 byte
  have value := (ready_tag_position_generic state layerZero position
    positionValue).1
  simpa using
    split.trans (congrArg (fun result : BitVec 32 =>
      result.extractLsb' (8 * byte.val) 8) value)

theorem ready_position_byte_generic (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0)
    (position : Word)
    (positionValue : state.getMem 0x43010 = position)
    (byte : Fin 4) :
    (parentHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40004 + byte.val)) =
        (position.truncate 32).extractLsb' (8 * byte.val) 8 := by
  have split := variableWord_byte (parentHashReadyState state) 0x40004
    (by decide) (by decide) 0 byte
  have value := (ready_tag_position_generic state layerZero position
    positionValue).2
  simpa using
    split.trans (congrArg (fun result : BitVec 32 =>
      result.extractLsb' (8 * byte.val) 8) value)

set_option maxHeartbeats 0 in
theorem parentHeader_bytes_generic (state : MachineState)
    (index : Index) (nodeIdx : FtsLeaf) (level : Nat)
    (layerZero : state.getMem 0x43000 = 0)
    (positionValue : state.getMem 0x43010 = BitVec.ofNat 64 level)
    (treeIndex : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (leafIndex : state.getMem 0x43018 = BitVec.ofNat 64 nodeIdx.val)
    (byte : Fin 20) :
    (parentHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      ((fieldBytes (tweakFields 10 0 index.val level nodeIdx.val)).map
        UInt8.toBitVec)[byte.val]'(by
          simp [fieldBytes, tweakFields, bytesLE]) := by
  fin_cases byte <;>
    first
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_tag_byte_generic state layerZero _ positionValue 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_tag_byte_generic state layerZero _ positionValue 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_tag_byte_generic state layerZero _ positionValue 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_tag_byte_generic state layerZero _ positionValue 3
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_position_byte_generic state layerZero _ positionValue 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_position_byte_generic state layerZero _ positionValue 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_position_byte_generic state layerZero _ positionValue 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_position_byte_generic state layerZero _ positionValue 3
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        parentHeader_treeByte state index treeIndex 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        parentHeader_treeByte state index treeIndex 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        parentHeader_treeByte state index treeIndex 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        parentHeader_treeByte state index treeIndex 3
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        parentHeader_treeByte state index treeIndex 4
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        parentHeader_treeByte state index treeIndex 5
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        parentHeader_treeByte state index treeIndex 6
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        parentHeader_treeByte state index treeIndex 7
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        parentHeader_indexByte state nodeIdx leafIndex 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        parentHeader_indexByte state nodeIdx leafIndex 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        parentHeader_indexByte state nodeIdx leafIndex 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        parentHeader_indexByte state nodeIdx leafIndex 3

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericHeader.ready_tag_position_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ready_tag_position_generic

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericHeader.parentHeader_bytes_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentHeader_bytes_generic

end SigGolfCandidate.SphincsVerifierFtsGenericHeader
