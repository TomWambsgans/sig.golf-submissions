import SigGolfCandidate.SphincsVerifierFtsForestHeaderFields

/-! Decode the exact 20-byte domain header of the first FORS parent HASH call. -/

namespace SigGolfCandidate.SphincsVerifierFtsForestHeaderBytes
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsForestHeaderFields
open SigGolfCandidate.SphincsVerifierFtsForestHashReady
set_option maxRecDepth 16384

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

theorem forestHeader_tagByte (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0)
    (positionZero : state.getMem 0x43010 = 0) (byte : Fin 4) :
    (forestHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      (0xb01#32).extractLsb' (8 * byte.val) 8 := by
  rw [header_word32_byte _ 0x40000 (Or.inl rfl) byte]
  simpa using congrArg (fun value : BitVec 32 => value.extractLsb' (8 * byte.val) 8)
    (SphincsVerifierFtsForestHeaderFields.ready_tag_position state layerZero positionZero).1

theorem forestHeader_positionByte (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0)
    (positionZero : state.getMem 0x43010 = 0) (byte : Fin 4) :
    (forestHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40004 + byte.val)) = (0#32).extractLsb' (8 * byte.val) 8 := by
  rw [header_word32_byte _ 0x40004 (Or.inr (Or.inl rfl)) byte]
  have address : BitVec.ofNat 64 0x40004 = (0x40004 : Word) := by decide
  rw [address]
  rw [(SphincsVerifierFtsForestHeaderFields.ready_tag_position state layerZero positionZero).2]
  simp

theorem forestHeader_treeByte (state : MachineState)
    (index : SphincsSecurity.Index)
    (treeIndex : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (byte : Fin 8) :
    (forestHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40008 + byte.val)) =
      (BitVec.ofNat 64 index.val).extractLsb' (8 * byte.val) 8 := by
  have word : (forestHashReadyState state).getMem 0x40008 =
      BitVec.ofNat 64 index.val := by
    rw [SigGolfCandidate.SphincsVerifierFtsForestHeaderFields.ready_tree, treeIndex]
  have word' : (forestHashReadyState state).getMem (262152#64) =
      BitVec.ofNat 64 index.val := by simpa using word
  fin_cases byte <;>
    simp [MachineState.getByte, alignToDword, byteOffset, word', extractByte,
      BitVec.setWidth_ushiftRight_eq_extractLsb]
  have small : index.val < 2 ^ 64 := by
    have h := index.isLt
    simp only [SphincsSecurity.totalHeight] at h
    omega
  simp [BitVec.extractLsb']
  rw [Nat.mod_eq_of_lt (by simpa using small)]

theorem forestHeader_indexByte (state : MachineState)
    (nodeIdx : SphincsSecurity.FtsLeaf)
    (leafIndex : state.getMem 0x43018 = BitVec.ofNat 64 nodeIdx.val)
    (byte : Fin 4) :
    (forestHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40010 + byte.val)) =
      (BitVec.ofNat 32 nodeIdx.val).extractLsb' (8 * byte.val) 8 := by
  rw [header_word32_byte _ 0x40010 (Or.inr (Or.inr rfl)) byte]
  have address : BitVec.ofNat 64 0x40010 = (0x40010 : Word) := by decide
  rw [address]
  rw [SigGolfCandidate.SphincsVerifierFtsForestHeaderFields.ready_index,
    leafIndex]
  simp

set_option maxHeartbeats 0 in
theorem forestHeader_bytes (state : MachineState)
    (index : SphincsSecurity.Index) (nodeIdx : SphincsSecurity.FtsLeaf)
    (layerZero : state.getMem 0x43000 = 0)
    (positionZero : state.getMem 0x43010 = 0)
    (treeIndex : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (leafIndex : state.getMem 0x43018 = BitVec.ofNat 64 nodeIdx.val)
    (byte : Fin 20) :
    (forestHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      ((SphincsSecurity.fieldBytes
        (SphincsSecurity.tweakFields 11 0 index.val 0 nodeIdx.val)).map
        UInt8.toBitVec)[byte.val]'(by
          simp [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
            SphincsSecurity.bytesLE]) := by
  fin_cases byte <;>
    first
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_tagByte state layerZero positionZero 0
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_tagByte state layerZero positionZero 1
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_tagByte state layerZero positionZero 2
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_tagByte state layerZero positionZero 3
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_positionByte state layerZero positionZero 0
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_positionByte state layerZero positionZero 1
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_positionByte state layerZero positionZero 2
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_positionByte state layerZero positionZero 3
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_treeByte state index treeIndex 0
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_treeByte state index treeIndex 1
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_treeByte state index treeIndex 2
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_treeByte state index treeIndex 3
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_treeByte state index treeIndex 4
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_treeByte state index treeIndex 5
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_treeByte state index treeIndex 6
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_treeByte state index treeIndex 7
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_indexByte state nodeIdx leafIndex 0
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_indexByte state nodeIdx leafIndex 1
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_indexByte state nodeIdx leafIndex 2
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        forestHeader_indexByte state nodeIdx leafIndex 3

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestHeaderBytes.forestHeader_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestHeader_bytes

end SigGolfCandidate.SphincsVerifierFtsForestHeaderBytes
