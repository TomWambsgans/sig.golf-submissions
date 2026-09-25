import SigGolfCandidate.SphincsVerifierFtsGenericReadyTrace

/-! The FORS tree identifier in the parent HASH tag for every forest tree. -/

namespace SigGolfCandidate.SphincsVerifierFtsTreeTag
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsParentTag
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierFtsParentHeader
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierFtsGenericHeader
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
open SigGolfCandidate.SphincsVerifierFtsParentHeaderBytes
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem parentTag_value_tree (state : MachineState) (tree : FtsTree)
    (treeValue : state.getMem 0x43000 = BitVec.ofNat 64 tree.val) :
    (parentTagState state).getWord32 0x40000 =
      BitVec.ofNat 32 (0xa01 + 0x10000 * tree.val) := by
  simp [parentTagState, parentTagBeforeStore, execInstrBr,
    signExtend12, getWord32_setWord32_same,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  have value : state.getMem (274432#64) = BitVec.ofNat 64 tree.val := by
    have address : (274432#64) = (0x43000 : Word) := by decide
    rw [address]
    exact treeValue
  rw [value]
  fin_cases tree <;> decide

theorem parentPrefix_values_tree (state : MachineState) (tree : FtsTree)
    (treeValue : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (position : Word)
    (positionValue : state.getMem 0x43010 = position) :
    (parentPrefixState state).getWord32 0x40000 =
        BitVec.ofNat 32 (0xa01 + 0x10000 * tree.val) ∧
      (parentPrefixState state).getWord32 0x40004 =
        position.truncate 32 := by
  constructor
  · rw [parentPrefixState,
      parentPosition_preserve_tag _ (parentTag_hash_pointer state),
      parentTag_value_tree state tree treeValue]
  · apply parentPosition_value_generic _ (parentTag_hash_pointer state)
      position
    rw [parentTag_mem_frame state 0x43010 (by decide)]
    exact positionValue

theorem header_tag_position_tree (state : MachineState) (tree : FtsTree)
    (treeValue : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (position : Word)
    (positionValue : state.getMem 0x43010 = position) :
    (parentHeaderState state).getWord32 0x40000 =
        BitVec.ofNat 32 (0xa01 + 0x10000 * tree.val) ∧
      (parentHeaderState state).getWord32 0x40004 =
        position.truncate 32 := by
  let prefixed := parentPrefixState state
  let treed := SphincsVerifierHeader.treeState prefixed
  have prefixPointer : prefixed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer (parentTagState state)).trans
      (parentTag_hash_pointer state)
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer prefixed).trans prefixPointer
  have values := parentPrefix_values_tree state tree treeValue position
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

theorem ready_tag_position_tree (state : MachineState) (tree : FtsTree)
    (treeValue : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (position : Word)
    (positionValue : state.getMem 0x43010 = position) :
    (parentHashReadyState state).getWord32 0x40000 =
        BitVec.ofNat 32 (0xa01 + 0x10000 * tree.val) ∧
      (parentHashReadyState state).getWord32 0x40004 =
        position.truncate 32 := by
  have values := header_tag_position_tree state tree treeValue position
    positionValue
  constructor
  · rw [ready_header_word_frame state 0x40000
      (by intro offset; fin_cases offset <;> decide)]
    exact values.1
  · rw [ready_header_word_frame state 0x40004
      (by intro offset; fin_cases offset <;> decide)]
    exact values.2

theorem ready_tag_byte_tree (state : MachineState) (tree : FtsTree)
    (treeValue : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (position : Word)
    (positionValue : state.getMem 0x43010 = position)
    (byte : Fin 4) :
    (parentHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
        (BitVec.ofNat 32 (0xa01 + 0x10000 * tree.val)).extractLsb'
          (8 * byte.val) 8 := by
  have split := variableWord_byte (parentHashReadyState state) 0x40000
    (by decide) (by decide) 0 byte
  have value := (ready_tag_position_tree state tree treeValue position
    positionValue).1
  simpa using
    split.trans (congrArg (fun result : BitVec 32 =>
      result.extractLsb' (8 * byte.val) 8) value)

theorem ready_position_byte_tree (state : MachineState) (tree : FtsTree)
    (treeValue : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (position : Word)
    (positionValue : state.getMem 0x43010 = position)
    (byte : Fin 4) :
    (parentHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40004 + byte.val)) =
        (position.truncate 32).extractLsb' (8 * byte.val) 8 := by
  have split := variableWord_byte (parentHashReadyState state) 0x40004
    (by decide) (by decide) 0 byte
  have value := (ready_tag_position_tree state tree treeValue position
    positionValue).2
  simpa using
    split.trans (congrArg (fun result : BitVec 32 =>
      result.extractLsb' (8 * byte.val) 8) value)

theorem tagByte_tree_expected (tree : FtsTree) (index : Index)
    (nodeIdx : FtsLeaf) (level : Nat) (byte : Fin 4) :
    (BitVec.ofNat 32 (0xa01 + 0x10000 * tree.val)).extractLsb'
      (8 * byte.val) 8 =
      ((fieldBytes (tweakFields 10 tree.val index.val level nodeIdx.val)).map
        UInt8.toBitVec)[byte.val]'(by
          have h := byte.isLt
          simp [fieldBytes, tweakFields, bytesLE]
          omega) := by
  fin_cases tree <;> fin_cases byte <;>
    simp [fieldBytes, tweakFields, protocolDomainSep, bytesLE] <;> decide

set_option maxHeartbeats 0 in
theorem parentHeader_bytes_tree (state : MachineState)
    (tree : FtsTree) (index : Index) (nodeIdx : FtsLeaf) (level : Nat)
    (treeValue : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (positionValue : state.getMem 0x43010 = BitVec.ofNat 64 level)
    (treeIndex : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (leafIndex : state.getMem 0x43018 = BitVec.ofNat 64 nodeIdx.val)
    (byte : Fin 20) :
    (parentHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      ((fieldBytes (tweakFields 10 tree.val index.val level nodeIdx.val)).map
        UInt8.toBitVec)[byte.val]'(by
          simp [fieldBytes, tweakFields, bytesLE]) := by
  fin_cases byte <;>
    first
    | exact (ready_tag_byte_tree state tree treeValue _ positionValue 0).trans
        (tagByte_tree_expected tree index nodeIdx level 0)
    | exact (ready_tag_byte_tree state tree treeValue _ positionValue 1).trans
        (tagByte_tree_expected tree index nodeIdx level 1)
    | exact (ready_tag_byte_tree state tree treeValue _ positionValue 2).trans
        (tagByte_tree_expected tree index nodeIdx level 2)
    | exact (ready_tag_byte_tree state tree treeValue _ positionValue 3).trans
        (tagByte_tree_expected tree index nodeIdx level 3)
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_position_byte_tree state tree treeValue _ positionValue 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_position_byte_tree state tree treeValue _ positionValue 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_position_byte_tree state tree treeValue _ positionValue 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_position_byte_tree state tree treeValue _ positionValue 3
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

/-- info: 'SigGolfCandidate.SphincsVerifierFtsTreeTag.parentTag_value_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentTag_value_tree

/-- info: 'SigGolfCandidate.SphincsVerifierFtsTreeTag.ready_tag_position_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ready_tag_position_tree

/-- info: 'SigGolfCandidate.SphincsVerifierFtsTreeTag.parentHeader_bytes_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentHeader_bytes_tree

end SigGolfCandidate.SphincsVerifierFtsTreeTag
