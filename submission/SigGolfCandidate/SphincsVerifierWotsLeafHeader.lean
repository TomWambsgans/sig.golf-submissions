import SigGolfCandidate.SphincsVerifierWotsLeafParameter
import SigGolfCandidate.SphincsVerifierWotsLeafQuery

namespace SigGolfCandidate.SphincsVerifierWotsLeafHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierWotsLeafHashReady
open SigGolfCandidate.SphincsVerifierWotsLeafParameter
open SigGolfCandidate.SphincsVerifierWotsLeafQuery
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384
set_option maxHeartbeats 0

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

theorem leafHeader_tagByte (state : MachineState) (lay : Layer)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (byte : Fin 4) :
    (leafHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      ((1 : UInt8).toBitVec :: [2#8, BitVec.ofNat 8 lay.val, 0#8])[byte.val]'(by
        simp) := by
  rw [header_word32_byte _ 0x40000 (Or.inl rfl) byte]
  have tag : (leafHashReadyState state).getWord32 (262144#64) =
      ((513#64) + (state.getMem 0x43000 <<< 16)).truncate 32 := by
    simpa using (leafHashReady_tag_position state).1
  rw [tag, layerCell]
  fin_cases lay <;> fin_cases byte <;>
    decide

theorem leafHeader_positionByte (state : MachineState)
    (positionZero : state.getMem 0x43010 = 0) (byte : Fin 4) :
    (leafHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40004 + byte.val)) = 0 := by
  rw [header_word32_byte _ 0x40004 (Or.inr (Or.inl rfl)) byte]
  have cell : state.getMem (274448#64) = 0 := by simpa using positionZero
  have position : (leafHashReadyState state).getWord32 (262148#64) = 0 := by
    simpa [cell] using (leafHashReady_tag_position state).2
  rw [position]
  fin_cases byte <;> decide

theorem leafHeader_treeByte (state : MachineState) (tree : TreeIndex)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (byte : Fin 8) :
    (leafHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40008 + byte.val)) =
      (BitVec.ofNat 64 tree.val).extractLsb' (8 * byte.val) 8 := by
  have word : (leafHashReadyState state).getMem (262152#64) =
      BitVec.ofNat 64 tree.val := by
    have cell : state.getMem (274440#64) = BitVec.ofNat 64 tree.val := by
      simpa using treeCell
    simpa [cell] using leafHashReady_tree state
  fin_cases byte <;>
    simp [MachineState.getByte, alignToDword, byteOffset, word,
      extractByte, BitVec.setWidth_ushiftRight_eq_extractLsb]
  have small : tree.val < 2 ^ 64 := by
    have h := tree.isLt
    simp only [totalHeight] at h
    omega
  simp [BitVec.extractLsb']
  rw [Nat.mod_eq_of_lt (by simpa using small)]

theorem leafHeader_indexByte (state : MachineState) (leaf : LeafIndex)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (byte : Fin 4) :
    (leafHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40010 + byte.val)) =
      (BitVec.ofNat 32 leaf.val).extractLsb' (8 * byte.val) 8 := by
  rw [header_word32_byte _ 0x40010 (Or.inr (Or.inr rfl)) byte]
  have cell : state.getMem (274456#64) = BitVec.ofNat 64 leaf.val := by
    simpa using leafCell
  have index : (leafHashReadyState state).getWord32 (262160#64) =
      BitVec.ofNat 32 leaf.val := by
    simpa [cell] using leafHashReady_index state
  rw [index]

theorem leafHeader_bytes (state : MachineState) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (positionZero : state.getMem 0x43010 = 0)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (byte : Fin 20) :
    (leafHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      ((fieldBytes (tweakFields 2 lay.val tree.val 0 leaf.val)).map
        UInt8.toBitVec)[byte.val]'(by
          simp [fieldBytes, tweakFields, bytesLE]) := by
  fin_cases byte <;>
    first
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_tagByte state lay layerCell 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_tagByte state lay layerCell 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_tagByte state lay layerCell 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_tagByte state lay layerCell 3
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_positionByte state positionZero 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_positionByte state positionZero 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_positionByte state positionZero 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_positionByte state positionZero 3
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_treeByte state tree treeCell 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_treeByte state tree treeCell 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_treeByte state tree treeCell 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_treeByte state tree treeCell 3
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_treeByte state tree treeCell 4
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_treeByte state tree treeCell 5
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_treeByte state tree treeCell 6
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_treeByte state tree treeCell 7
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_indexByte state leaf leafCell 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_indexByte state leaf leafCell 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_indexByte state leaf leafCell 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        leafHeader_indexByte state leaf leafCell 3

theorem leafInput_header (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (endpoints : ChainIndex → Digest)
    (i : Nat) (hi : i < 20) :
    ((leafInput parameter lay tree leaf endpoints).map UInt8.toBitVec)[i]'(by
      rw [List.length_map, leafInput_length]; omega) =
      ((fieldBytes (tweakFields 2 lay.val tree.val 0 leaf.val)).map
        UInt8.toBitVec)[i]'(by simp [fieldBytes, bytesLE]; omega) := by
  simp only [leafInput, tweakableHashInput, tweakBytes, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega)]
  rfl

theorem leafInput_parameter (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (endpoints : ChainIndex → Digest)
    (i : Nat) (hi : i < 20) :
    ((leafInput parameter lay tree leaf endpoints).map UInt8.toBitVec)[20 + i]'(by
      rw [List.length_map, leafInput_length]; omega) =
      parameter.extractLsb' (8 * i) 8 := by
  simp only [leafInput, tweakableHashInput, tweakBytes, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [fieldBytes, bytesLE]
  rfl

theorem leafReady_fullQuery (state : MachineState) (pk : SphincsSecurity.PublicKey)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (positionZero : state.getMem 0x43010 = 0)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (parameterEncoded : WitnessPrefix state pk)
    (payload : ∀ i, (hi : i < 1040) →
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        ((Concrete.leafPayload endpoints).map UInt8.toBitVec)[i]'(by
          rw [List.length_map, SphincsVerifierWotsSemanticLeaf.leafPayload_length]; exact hi)) :
    hashInput (leafHashReadyState state) =
      toQuery (leafInput pk.parameter lay tree leaf endpoints) := by
  apply readyLeaf_hashInput state pk.parameter lay tree leaf endpoints ?_ payload
  intro i hi
  by_cases header : i < 20
  · let byte : Fin 20 := ⟨i, header⟩
    have actual := leafHeader_bytes state lay tree leaf layerCell positionZero
      treeCell leafCell byte
    have expected := leafInput_header pk.parameter lay tree leaf endpoints i header
    simpa [byte] using actual.trans expected.symm
  · have parameter : i - 20 < 20 := by omega
    have actual := leafReady_parameter_byte state pk parameterEncoded (i - 20) parameter
    have expected := leafInput_parameter pk.parameter lay tree leaf endpoints
      (i - 20) parameter
    have shift : 20 + (i - 20) = i := by omega
    have address : 0x40014 + (i - 20) = 0x40000 + i := by omega
    simpa only [shift, address] using actual.trans expected.symm

#print axioms leafHeader_bytes
#print axioms leafReady_fullQuery

#print axioms leafHeader_tagByte
#print axioms leafHeader_treeByte
#print axioms leafHeader_indexByte

end SigGolfCandidate.SphincsVerifierWotsLeafHeader
