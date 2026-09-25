import SigGolfCandidate.SphincsVerifierFtsGenericHeader

/-! Identify the FORS parent HASH query for any level and bounded path pointer. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericQuery
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierFtsParentPayload
open SigGolfCandidate.SphincsVerifierFtsGenericHeader
open SigGolfCandidate.SphincsVerifierSecondHashBytes
open SigGolfCandidate.SphincsVerifierLoader
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierHashBytes
set_option maxRecDepth 16384

def parentInput (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (level : Nat) (left right : Digest) : HashInput :=
  tweakableHashInput pk.parameter (.ftsNode index ⟨0, by decide⟩ level nodeIdx.val)
    (SphincsSecurity.Concrete.nodePayload left right)

theorem parentInput_eq (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (level : Nat) (left right : Digest) :
    parentInput pk index nodeIdx level left right =
      fieldBytes (tweakFields 10 0 index.val level nodeIdx.val) ++
        bytesLE 20 pk.parameter ++ bytesLE 20 left ++ bytesLE 20 right := by
  rfl

theorem parentInput_length (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (level : Nat) (left right : Digest) :
    (parentInput pk index nodeIdx level left right).length = 80 := by
  simp [parentInput, tweakableHashInput, tweakBytes,
    hashDomainFields, fieldBytes, SphincsSecurity.Concrete.nodePayload, bytesLE]

theorem parentInput_header (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (level : Nat) (left right : Digest)
    (i : Nat) (hi : i < 20) :
    ((parentInput pk index nodeIdx level left right).map UInt8.toBitVec)[i]'(by
      rw [List.length_map, parentInput_length]; omega) =
      ((fieldBytes (tweakFields 10 0 index.val level nodeIdx.val)).map
        UInt8.toBitVec)[i]'(by simp [fieldBytes, bytesLE]; omega) := by
  simp only [parentInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega)]

theorem parentInput_parameter (pk : SphincsSecurity.PublicKey)
    (index : Index) (nodeIdx : FtsLeaf) (level : Nat)
    (left right : Digest) (i : Nat) (hi : i < 20) :
    ((parentInput pk index nodeIdx level left right).map UInt8.toBitVec)[20 + i]'(by
      rw [List.length_map, parentInput_length]; omega) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  simp only [parentInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [List.length_map, fieldBytes, bytesLE]
  rfl

theorem parentInput_left (pk : SphincsSecurity.PublicKey)
    (index : Index) (nodeIdx : FtsLeaf) (level : Nat)
    (left right : Digest) (i : Nat) (hi : i < 20) :
    ((parentInput pk index nodeIdx level left right).map UInt8.toBitVec)[40 + i]'(by
      rw [List.length_map, parentInput_length]; omega) =
      left.extractLsb' (8 * i) 8 := by
  simp only [parentInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [List.length_map, fieldBytes, bytesLE]
  rfl

theorem parentInput_right (pk : SphincsSecurity.PublicKey)
    (index : Index) (nodeIdx : FtsLeaf) (level : Nat)
    (left right : Digest) (i : Nat) (hi : i < 20) :
    ((parentInput pk index nodeIdx level left right).map UInt8.toBitVec)[60 + i]'(by
      rw [List.length_map, parentInput_length]; omega) =
      right.extractLsb' (8 * i) 8 := by
  simp only [parentInput_eq, List.map_append]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [List.length_map, fieldBytes, bytesLE]
  rfl

theorem readyParent_hashInput_generic (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (level : Nat) (left right : Digest)
    (layerZero : state.getMem 0x43000 = 0)
    (positionValue : state.getMem 0x43010 = BitVec.ofNat 64 level)
    (treeIndex : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (nodeIndex : state.getMem 0x43018 = BitVec.ofNat 64 nodeIdx.val)
    (parameterEncoded : WitnessPrefix state pk)
    (leftEncoded : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        left.extractLsb' (8 * i) 8)
    (rightEncoded : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x4003c + i)) =
        right.extractLsb' (8 * i) 8) :
    hashInput (parentHashReadyState state) =
      toQuery (parentInput pk index nodeIdx level left right) := by
  let ready := parentHashReadyState state
  have regs := hashRegisters_ready (parentReadyState state)
  apply Serialization.hashInput_of_list ready 0x40000
    ((parentInput pk index nodeIdx level left right).map UInt8.toBitVec)
  · exact regs.1
  · change ((hashRegistersState (parentReadyState state)).getReg .x11).toNat = _
    rw [regs.2.1, List.length_map, parentInput_length]
    rfl
  · intro i hi
    have hi80 : i < 80 := by
      simpa [parentInput_length] using hi
    by_cases header : i < 20
    · let byte : Fin 20 := ⟨i, header⟩
      have actual := parentHeader_bytes_generic state index nodeIdx level
        layerZero positionValue treeIndex nodeIndex byte
      have expected := parentInput_header pk index nodeIdx level
        left right i header
      simpa [ready, byte] using actual.trans expected.symm
    · by_cases parameter : i < 40
      · have smaller : i - 20 < 20 := by omega
        have split : 20 + (i - 20) = i := by omega
        have actual := parameter_bytes_of_words ready state pk
          (ready_parameter_data state) parameterEncoded (i - 20) smaller
        have expected := parentInput_parameter pk index nodeIdx level
          left right (i - 20) smaller
        have joined := actual.trans expected.symm
        simp only [split] at joined
        have address : 0x40014 + (i - 20) = 0x40000 + i := by omega
        rw [address] at joined
        simpa only [ready] using joined
      · by_cases leftPart : i < 60
        · have smaller : i - 40 < 20 := by omega
          have split : 40 + (i - 40) = i := by omega
          have actual := (ready_pair_bytes state (i - 40) smaller).1.trans
            (leftEncoded (i - 40) smaller)
          have expected := parentInput_left pk index nodeIdx level
            left right (i - 40) smaller
          have joined := actual.trans expected.symm
          simp only [split] at joined
          have address : 0x40028 + (i - 40) = 0x40000 + i := by omega
          rw [address] at joined
          simpa only [ready] using joined
        · have smaller : i - 60 < 20 := by omega
          have split : 60 + (i - 60) = i := by omega
          have actual := (ready_pair_bytes state (i - 60) smaller).2.trans
            (rightEncoded (i - 60) smaller)
          have expected := parentInput_right pk index nodeIdx level
            left right (i - 60) smaller
          have joined := actual.trans expected.symm
          simp only [split] at joined
          have address : 0x4003c + (i - 60) = 0x40000 + i := by omega
          rw [address] at joined
          simpa only [ready] using joined

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericQuery.readyParent_hashInput_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms readyParent_hashInput_generic

end SigGolfCandidate.SphincsVerifierFtsGenericQuery
