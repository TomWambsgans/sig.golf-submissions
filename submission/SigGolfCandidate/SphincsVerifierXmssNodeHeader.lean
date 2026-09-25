import SigGolfCandidate.SphincsVerifierXmssNodeValue
import SigGolfCandidate.SphincsVerifierFtsGenericQuery
import SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame

namespace SigGolfCandidate.SphincsVerifierXmssNodeHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssNodeReady
open SigGolfCandidate.SphincsVerifierXmssNodeValue
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierSecondHashBytes
open SigGolfCandidate.SphincsVerifierFtsParentPayload
open SigGolfCandidate.SphincsVerifierFtsGenericQuery
open SigGolfCandidate.SphincsVerifierLoader
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierFtsGenericHeader
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierFtsParentTag
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def nodeInput (pk : SphincsSecurity.PublicKey) (lay : Layer)
    (tree : TreeIndex) (level nodeIdx : Nat) (left right : Digest) : HashInput :=
  tweakableHashInput pk.parameter (.node lay tree level nodeIdx)
    (SphincsSecurity.Concrete.nodePayload left right)

theorem nodeInput_eq (pk : SphincsSecurity.PublicKey) (lay : Layer)
    (tree : TreeIndex) (level nodeIdx : Nat) (left right : Digest) :
    nodeInput pk lay tree level nodeIdx left right =
      fieldBytes (tweakFields 3 lay.val tree.val level nodeIdx) ++
        bytesLE 20 pk.parameter ++ bytesLE 20 left ++ bytesLE 20 right := by
  rfl

theorem nodeInput_length (pk : SphincsSecurity.PublicKey) (lay : Layer)
    (tree : TreeIndex) (level nodeIdx : Nat) (left right : Digest) :
    (nodeInput pk lay tree level nodeIdx left right).length = 80 := by
  simp [nodeInput, tweakableHashInput, tweakBytes,
    hashDomainFields, fieldBytes, SphincsSecurity.Concrete.nodePayload, bytesLE]

theorem nodeInput_header (pk : SphincsSecurity.PublicKey) (lay : Layer)
    (tree : TreeIndex) (level nodeIdx : Nat) (left right : Digest)
    (i : Nat) (hi : i < 20) :
    ((nodeInput pk lay tree level nodeIdx left right).map UInt8.toBitVec)[i]'(by
      rw [List.length_map, nodeInput_length]; omega) =
      ((fieldBytes (tweakFields 3 lay.val tree.val level nodeIdx)).map UInt8.toBitVec)[i]'(by simp [fieldBytes,bytesLE]; omega) := by
  simp only [nodeInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega)]

theorem nodeInput_parameter (pk : SphincsSecurity.PublicKey) (lay : Layer)
    (tree : TreeIndex) (level nodeIdx : Nat) (left right : Digest)
    (i : Nat) (hi : i < 20) :
    ((nodeInput pk lay tree level nodeIdx left right).map UInt8.toBitVec)[20 + i]'(by
      rw [List.length_map, nodeInput_length]; omega) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  simp only [nodeInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [fieldBytes, bytesLE]
  rfl

theorem nodeInput_left (pk : SphincsSecurity.PublicKey) (lay : Layer)
    (tree : TreeIndex) (level nodeIdx : Nat) (left right : Digest)
    (i : Nat) (hi : i < 20) :
    ((nodeInput pk lay tree level nodeIdx left right).map UInt8.toBitVec)[40 + i]'(by
      rw [List.length_map, nodeInput_length]; omega) =
      left.extractLsb' (8 * i) 8 := by
  simp only [nodeInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [fieldBytes, bytesLE]
  rfl

theorem nodeInput_right (pk : SphincsSecurity.PublicKey) (lay : Layer)
    (tree : TreeIndex) (level nodeIdx : Nat) (left right : Digest)
    (i : Nat) (hi : i < 20) :
    ((nodeInput pk lay tree level nodeIdx left right).map UInt8.toBitVec)[60 + i]'(by
      rw [List.length_map, nodeInput_length]; omega) =
      right.extractLsb' (8 * i) 8 := by
  simp only [nodeInput_eq, List.map_append]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [fieldBytes, bytesLE]
  rfl


theorem ready_pair_bytes_node (s : MachineState) (i : Nat) (hi : i < 20) :
    (nodeReadyState s).getByte (BitVec.ofNat 64 (0x40028 + i)) =
      s.getByte (BitVec.ofNat 64 (0x40028 + i)) ∧
    (nodeReadyState s).getByte (BitVec.ofNat 64 (0x4003c + i)) =
      s.getByte (BitVec.ofNat 64 (0x4003c + i)) := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  have words := ready_pair_words s index
  constructor
  · have ready := word32_byte (nodeReadyState s) 0x40028
      (Or.inr (Or.inl rfl)) index byte
    have original := word32_byte s 0x40028
      (Or.inr (Or.inl rfl)) index byte
    simpa only [Nat.add_assoc, split] using
      ready.trans ((congrArg (fun value : BitVec 32 =>
        value.extractLsb' (8 * byte.val) 8) words.1).trans original.symm)
  · have ready := word32_byte (nodeReadyState s) 0x4003c
      (Or.inr (Or.inr (Or.inl rfl))) index byte
    have original := word32_byte s 0x4003c
      (Or.inr (Or.inr (Or.inl rfl))) index byte
    simpa only [Nat.add_assoc, split] using
      ready.trans ((congrArg (fun value : BitVec 32 =>
        value.extractLsb' (8 * byte.val) 8) words.2).trans original.symm)

theorem ready_parameter_words_node (s : MachineState) (index : Fin 5) :
    (nodeReadyState s).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
        s.getWord32
          (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  let headed := nodeHeaderState (nodeTagState s)
  let pointers := parameterPointers headed
  change (hashRegistersState (copyRootState pointers)).getWord32 _ = _
  have registers (t : MachineState) (address : Word) :
      (hashRegistersState t).getWord32 address = t.getWord32 address := by
    simp [MachineState.getWord32, hashRegistersState, execInstrBr]
  rw [registers]
  have copied := SphincsVerifierFtsPayload.parameterState_data headed index
  change (SphincsVerifierFtsParameter.parameterState headed).getWord32 _ = _
  rw [copied]
  let read := BitVec.ofNat 64 (0x22cb4 + 4 * index.val)
  let tagged := nodeTagState s
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_pointer s
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 read =
    s.getWord32 read
  rw [index_word_frame treed read treePointer
      (by fin_cases index <;> decide),
    tree_word_frame positioned read positionPointer
      (by fin_cases index <;> decide),
    position_word_frame tagged read tagPointer
      (by fin_cases index <;> decide)]
  have outside : alignToDword read ≠ alignToDword (0x40000#64) := by
    fin_cases index <;> decide
  change (nodeTagState s).getWord32 read = s.getWord32 read
  exact SphincsVerifierXmssNodeValue.tag_word_frame s read outside

theorem ready_position_word_node (s : MachineState) (level : Nat)
    (levelCell : s.getMem 0x43010 = BitVec.ofNat 64 level) :
    (nodeReadyState s).getWord32 0x40004 =
      (BitVec.ofNat 64 level).truncate 32 := by
  let tagged := nodeTagState s
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_pointer s
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  rw [SphincsVerifierXmssNodeValue.ready_header_word_frame s 0x40004
    (by intro offset; fin_cases offset <;> decide)]
  change (SphincsVerifierHeader.indexState treed).getWord32 0x40004 = _
  rw [index_word_frame treed _ treePointer (by decide),
    tree_word_frame positioned _ positionPointer (by decide)]
  apply parentPosition_value_generic tagged tagPointer _
  rw [SphincsVerifierXmssNodeValue.tag_mem_frame s 0x43010 (by decide)]
  exact levelCell

theorem header_tree_word_node (s : MachineState) :
    (nodeHeaderState (nodeTagState s)).getMem 0x40008 =
      s.getMem 0x43008 := by
  let tagged := nodeTagState s
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_pointer s
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getMem 0x40008 = _
  simp only [SphincsVerifierHeader.indexState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.indexBeforeStore_pointer, treePointer,
    setWord32_eq]
  rw [MachineState.getMem_setMem_ne (by decide),
    SphincsVerifierHeader.indexBeforeStore_memory]
  have treeCopy : treed.getMem 0x40008 = positioned.getMem 0x43008 := by
    simp [treed, SphincsVerifierHeader.treeState,
      SphincsVerifierHeader.treeBeforeStore, execInstrBr, signExtend12,
      positionPointer, MachineState.getMem_setMem_eq,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  rw [treeCopy]
  rw [parentPosition_mem_frame tagged tagPointer 0x43008 (by decide)]
  exact tag_mem_frame s 0x43008 (by decide)

theorem header_index_word_node (s : MachineState) :
    (nodeHeaderState (nodeTagState s)).getWord32 0x40010 =
      (s.getMem 0x43018).truncate 32 := by
  let tagged := nodeTagState s
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_pointer s
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 0x40010 = _
  have copied : (SphincsVerifierHeader.indexState treed).getWord32 0x40010 =
      (treed.getMem 0x43018).truncate 32 := by
    simp [SphincsVerifierHeader.indexState,
      SphincsVerifierHeader.indexBeforeStore, execInstrBr, signExtend12,
      getWord32_setWord32_same, treePointer,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  rw [copied,
    parentTree_mem_frame positioned 0x43018 (by right; decide) positionPointer,
    parentPosition_mem_frame tagged tagPointer 0x43018 (by decide),
    tag_mem_frame s 0x43018 (by decide)]

theorem ready_tree_word_node (s : MachineState) :
    (nodeReadyState s).getMem 0x40008 = s.getMem 0x43008 := by
  let headed := nodeHeaderState (nodeTagState s)
  let pointers := parameterPointers headed
  have destination := (parameterPointers_regs headed).2
  change (hashRegistersState (copyRootState pointers)).getMem 0x40008 = _
  have registers (t : MachineState) (address : Word) :
      (hashRegistersState t).getMem address = t.getMem address := by
    simp [hashRegistersState, execInstrBr]
  rw [registers]
  rw [copyRoot_mem_frame pointers 0x40008 (by
    intro offset
    rw [destination]
    fin_cases offset <;> decide)]
  have unchanged : pointers.getMem 0x40008 = headed.getMem 0x40008 := by
    simp [pointers, parameterPointers, execInstrBr]
  rw [unchanged]
  exact header_tree_word_node s

theorem ready_index_word_node (s : MachineState) :
    (nodeReadyState s).getWord32 0x40010 =
      (s.getMem 0x43018).truncate 32 := by
  rw [SphincsVerifierXmssNodeValue.ready_header_word_frame s 0x40010
    (by intro offset; fin_cases offset <;> decide)]
  exact header_index_word_node s

theorem ready_tag_byte_node (s : MachineState) (lay : Layer)
    (layerCell : s.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (byte : Fin 4) :
    (nodeReadyState s).getByte (BitVec.ofNat 64 (0x40000 + byte.val)) =
      (BitVec.ofNat 32 (0x301 + 0x10000 * lay.val)).extractLsb'
        (8 * byte.val) 8 := by
  have split := variableWord_byte (nodeReadyState s) 0x40000
    (by decide) (by decide) 0 byte
  have value := ready_tag_word lay s layerCell
  simpa using split.trans (congrArg (fun result : BitVec 32 =>
    result.extractLsb' (8 * byte.val) 8) value)

theorem ready_position_byte_node (s : MachineState) (level : Nat)
    (levelCell : s.getMem 0x43010 = BitVec.ofNat 64 level)
    (byte : Fin 4) :
    (nodeReadyState s).getByte (BitVec.ofNat 64 (0x40004 + byte.val)) =
      (BitVec.ofNat 32 level).extractLsb' (8 * byte.val) 8 := by
  have split := variableWord_byte (nodeReadyState s) 0x40004
    (by decide) (by decide) 0 byte
  have value := ready_position_word_node s level levelCell
  simpa using split.trans (congrArg (fun result : BitVec 32 =>
    result.extractLsb' (8 * byte.val) 8) value)

theorem ready_tree_byte_node (s : MachineState) (tree : TreeIndex)
    (treeCell : s.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (byte : Fin 8) :
    (nodeReadyState s).getByte (BitVec.ofNat 64 (0x40008 + byte.val)) =
      (BitVec.ofNat 64 tree.val).extractLsb' (8 * byte.val) 8 := by
  have word : (nodeReadyState s).getMem (262152#64) =
      BitVec.ofNat 64 tree.val := by
    simpa using (ready_tree_word_node s).trans treeCell
  fin_cases byte <;>
    simp [MachineState.getByte, alignToDword, byteOffset, word, extractByte,
      BitVec.setWidth_ushiftRight_eq_extractLsb]
  have small : tree.val < 2 ^ 64 := by
    have h := tree.isLt
    simp only [SphincsSecurity.totalHeight] at h
    omega
  simp [BitVec.extractLsb']
  rw [Nat.mod_eq_of_lt (by simpa using small)]

theorem ready_index_byte_node (s : MachineState) (nodeIdx : Nat)
    (indexCell : s.getMem 0x43018 = BitVec.ofNat 64 nodeIdx)
    (byte : Fin 4) :
    (nodeReadyState s).getByte (BitVec.ofNat 64 (0x40010 + byte.val)) =
      (BitVec.ofNat 32 nodeIdx).extractLsb' (8 * byte.val) 8 := by
  have split := variableWord_byte (nodeReadyState s) 0x40010
    (by decide) (by decide) 0 byte
  have value := ready_index_word_node s
  rw [indexCell] at value
  simpa using split.trans (congrArg (fun result : BitVec 32 =>
    result.extractLsb' (8 * byte.val) 8) value)


theorem node_tag_field_byte (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) (byte : Fin 4) :
    ((fieldBytes (tweakFields 3 lay.val tree.val level nodeIdx)).map
      UInt8.toBitVec)[byte.val]'(by
        simp [fieldBytes, tweakFields, bytesLE]; omega) =
      (BitVec.ofNat 32 (0x301 + 0x10000 * lay.val)).extractLsb'
        (8 * byte.val) 8 := by
  fin_cases lay <;> fin_cases byte <;>
    simp [fieldBytes, tweakFields, protocolDomainSep, bytesLE]

set_option maxHeartbeats 0 in
theorem ready_header_bytes_node (s : MachineState)
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (layerCell : s.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (levelCell : s.getMem 0x43010 = BitVec.ofNat 64 level)
    (treeCell : s.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (indexCell : s.getMem 0x43018 = BitVec.ofNat 64 nodeIdx)
    (byte : Fin 20) :
    (nodeReadyState s).getByte (BitVec.ofNat 64 (0x40000 + byte.val)) =
      ((fieldBytes (tweakFields 3 lay.val tree.val level nodeIdx)).map
        UInt8.toBitVec)[byte.val]'(by
          simp [fieldBytes, tweakFields, bytesLE]) := by
  fin_cases byte <;>
    first
    | simpa using (ready_tag_byte_node s lay layerCell 0).trans
        (node_tag_field_byte lay tree level nodeIdx 0).symm
    | simpa using (ready_tag_byte_node s lay layerCell 1).trans
        (node_tag_field_byte lay tree level nodeIdx 1).symm
    | simpa using (ready_tag_byte_node s lay layerCell 2).trans
        (node_tag_field_byte lay tree level nodeIdx 2).symm
    | simpa using (ready_tag_byte_node s lay layerCell 3).trans
        (node_tag_field_byte lay tree level nodeIdx 3).symm
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_position_byte_node s level levelCell 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_position_byte_node s level levelCell 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_position_byte_node s level levelCell 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_position_byte_node s level levelCell 3
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_tree_byte_node s tree treeCell 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_tree_byte_node s tree treeCell 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_tree_byte_node s tree treeCell 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_tree_byte_node s tree treeCell 3
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_tree_byte_node s tree treeCell 4
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_tree_byte_node s tree treeCell 5
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_tree_byte_node s tree treeCell 6
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_tree_byte_node s tree treeCell 7
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_index_byte_node s nodeIdx indexCell 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_index_byte_node s nodeIdx indexCell 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_index_byte_node s nodeIdx indexCell 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        ready_index_byte_node s nodeIdx indexCell 3

theorem ready_hashInput_node (s : MachineState)
    (pk : SphincsSecurity.PublicKey) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) (left right : Digest)
    (layerCell : s.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (levelCell : s.getMem 0x43010 = BitVec.ofNat 64 level)
    (treeCell : s.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (indexCell : s.getMem 0x43018 = BitVec.ofNat 64 nodeIdx)
    (parameterEncoded : WitnessPrefix s pk)
    (leftEncoded : ∀ i, (hi : i < 20) →
      s.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        left.extractLsb' (8 * i) 8)
    (rightEncoded : ∀ i, (hi : i < 20) →
      s.getByte (BitVec.ofNat 64 (0x4003c + i)) =
        right.extractLsb' (8 * i) 8) :
    hashInput (nodeReadyState s) =
      toQuery (nodeInput pk lay tree level nodeIdx left right) := by
  let ready := nodeReadyState s
  have regs := hashRegisters_ready
    (copyRootState (parameterPointers (nodeHeaderState (nodeTagState s))))
  apply Serialization.hashInput_of_list ready 0x40000
    ((nodeInput pk lay tree level nodeIdx left right).map UInt8.toBitVec)
  · exact regs.1
  · change ((hashRegistersState
      (copyRootState (parameterPointers (nodeHeaderState (nodeTagState s))))).getReg .x11).toNat = _
    rw [regs.2.1, List.length_map, nodeInput_length]
    rfl
  · intro i hi
    have hi80 : i < 80 := by
      simpa [nodeInput_length] using hi
    by_cases header : i < 20
    · let byte : Fin 20 := ⟨i, header⟩
      have actual := ready_header_bytes_node s lay tree level nodeIdx
        layerCell levelCell treeCell indexCell byte
      have expected := nodeInput_header pk lay tree level nodeIdx
        left right i header
      simpa [ready, byte] using actual.trans expected.symm
    · by_cases parameter : i < 40
      · have smaller : i - 20 < 20 := by omega
        have split : 20 + (i - 20) = i := by omega
        have actual := parameter_bytes_of_words ready s pk
          (ready_parameter_words_node s) parameterEncoded
          (i - 20) smaller
        have expected := nodeInput_parameter pk lay tree level nodeIdx
          left right (i - 20) smaller
        have joined := actual.trans expected.symm
        simp only [split] at joined
        have address : 0x40014 + (i - 20) = 0x40000 + i := by omega
        rw [address] at joined
        simpa only [ready] using joined
      · by_cases leftPart : i < 60
        · have smaller : i - 40 < 20 := by omega
          have split : 40 + (i - 40) = i := by omega
          have actual := (ready_pair_bytes_node s (i - 40) smaller).1.trans
            (leftEncoded (i - 40) smaller)
          have expected := nodeInput_left pk lay tree level nodeIdx
            left right (i - 40) smaller
          have joined := actual.trans expected.symm
          simp only [split] at joined
          have address : 0x40028 + (i - 40) = 0x40000 + i := by omega
          rw [address] at joined
          simpa only [ready] using joined
        · have smaller : i - 60 < 20 := by omega
          have split : 60 + (i - 60) = i := by omega
          have actual := (ready_pair_bytes_node s (i - 60) smaller).2.trans
            (rightEncoded (i - 60) smaller)
          have expected := nodeInput_right pk lay tree level nodeIdx
            left right (i - 60) smaller
          have joined := actual.trans expected.symm
          simp only [split] at joined
          have address : 0x4003c + (i - 60) = 0x40000 + i := by omega
          rw [address] at joined
          simpa only [ready] using joined

#print axioms ready_pair_bytes_node
#print axioms ready_parameter_words_node
#print axioms ready_position_word_node
#print axioms header_tree_word_node
#print axioms header_index_word_node
#print axioms ready_tree_word_node
#print axioms ready_index_word_node
#print axioms ready_header_bytes_node
/-- info: 'SigGolfCandidate.SphincsVerifierXmssNodeHeader.ready_hashInput_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ready_hashInput_node

end SigGolfCandidate.SphincsVerifierXmssNodeHeader
