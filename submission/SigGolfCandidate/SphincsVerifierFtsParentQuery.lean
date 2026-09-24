import SigGolfCandidate.SphincsVerifierFtsParentHeaderBytes
import SigGolfCandidate.SphincsVerifierFtsQuery

/-! Identify the first FORS parent HASH call with the abstract scheme's oracle query. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentQuery
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierFtsParentPayload
open SigGolfCandidate.SphincsVerifierFtsParentHeaderBytes
open SigGolfCandidate.SphincsVerifierSecondHashBytes
open SigGolfCandidate.SphincsVerifierLoader
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierHashBytes
set_option maxRecDepth 16384

def firstParentInput (pk : SphincsSecurity.PublicKey) (index : Index) (nodeIdx : FtsLeaf)
    (left right : Digest) : HashInput :=
  tweakableHashInput pk.parameter (.ftsNode index ⟨0, by decide⟩ 1 nodeIdx.val)
    (SphincsSecurity.Concrete.nodePayload left right)

theorem firstParentInput_eq (pk : SphincsSecurity.PublicKey) (index : Index) (nodeIdx : FtsLeaf)
    (left right : Digest) :
    firstParentInput pk index nodeIdx left right =
      fieldBytes (tweakFields 10 0 index.val 1 nodeIdx.val) ++
        bytesLE 20 pk.parameter ++ bytesLE 20 left ++ bytesLE 20 right := by
  rfl

theorem firstParentInput_length (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (left right : Digest) :
    (firstParentInput pk index nodeIdx left right).length = 80 := by
  simp [firstParentInput, tweakableHashInput, tweakBytes,
    hashDomainFields, fieldBytes, SphincsSecurity.Concrete.nodePayload, bytesLE]

theorem firstParentInput_header (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (left right : Digest)
    (i : Nat) (hi : i < 20) :
    ((firstParentInput pk index nodeIdx left right).map UInt8.toBitVec)[i]'(by
      rw [List.length_map, firstParentInput_length]; omega) =
      ((fieldBytes (tweakFields 10 0 index.val 1 nodeIdx.val)).map
        UInt8.toBitVec)[i]'(by simp [fieldBytes, bytesLE]; omega) := by
  simp only [firstParentInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega)]

theorem firstParentInput_parameter (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (left right : Digest)
    (i : Nat) (hi : i < 20) :
    ((firstParentInput pk index nodeIdx left right).map UInt8.toBitVec)[20 + i]'(by
      rw [List.length_map, firstParentInput_length]; omega) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  simp only [firstParentInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [List.length_map, fieldBytes, bytesLE]
  rfl

theorem firstParentInput_left (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (left right : Digest)
    (i : Nat) (hi : i < 20) :
    ((firstParentInput pk index nodeIdx left right).map UInt8.toBitVec)[40 + i]'(by
      rw [List.length_map, firstParentInput_length]; omega) =
      left.extractLsb' (8 * i) 8 := by
  simp only [firstParentInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [List.length_map, fieldBytes, bytesLE]
  rfl

theorem firstParentInput_right (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (left right : Digest)
    (i : Nat) (hi : i < 20) :
    ((firstParentInput pk index nodeIdx left right).map UInt8.toBitVec)[60 + i]'(by
      rw [List.length_map, firstParentInput_length]; omega) =
      right.extractLsb' (8 * i) 8 := by
  simp only [firstParentInput_eq, List.map_append]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [List.length_map, fieldBytes, bytesLE]
  rfl

theorem readyParent_hashInput (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (left right : Digest)
    (layerZero : state.getMem 0x43000 = 0)
    (positionOne : state.getMem 0x43010 = 1)
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
      toQuery (firstParentInput pk index nodeIdx left right) := by
  let ready := parentHashReadyState state
  have regs := hashRegisters_ready (parentReadyState state)
  apply Serialization.hashInput_of_list ready 0x40000
    ((firstParentInput pk index nodeIdx left right).map UInt8.toBitVec)
  · exact regs.1
  · change ((hashRegistersState (parentReadyState state)).getReg .x11).toNat = _
    rw [regs.2.1,
      List.length_map, firstParentInput_length]
    rfl
  · intro i hi
    have hi80 : i < 80 := by
      simpa [firstParentInput_length] using hi
    by_cases header : i < 20
    · let byte : Fin 20 := ⟨i, header⟩
      have actual := parentHeader_bytes state index nodeIdx layerZero
        positionOne treeIndex nodeIndex byte
      have expected := firstParentInput_header pk index nodeIdx left right i header
      simpa [ready, byte] using actual.trans expected.symm
    · by_cases parameter : i < 40
      · have smaller : i - 20 < 20 := by omega
        have split : 20 + (i - 20) = i := by omega
        have actual := parameter_bytes_of_words ready state pk
          (ready_parameter_data state) parameterEncoded (i - 20) smaller
        have expected := firstParentInput_parameter pk index nodeIdx left right
          (i - 20) smaller
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
          have expected := firstParentInput_left pk index nodeIdx left right
            (i - 40) smaller
          have joined := actual.trans expected.symm
          simp only [split] at joined
          have address : 0x40028 + (i - 40) = 0x40000 + i := by omega
          rw [address] at joined
          simpa only [ready] using joined
        · have smaller : i - 60 < 20 := by omega
          have split : 60 + (i - 60) = i := by omega
          have actual := (ready_pair_bytes state (i - 60) smaller).2.trans
            (rightEncoded (i - 60) smaller)
          have expected := firstParentInput_right pk index nodeIdx left right
            (i - 60) smaller
          have joined := actual.trans expected.symm
          simp only [split] at joined
          have address : 0x4003c + (i - 60) = 0x40000 + i := by omega
          rw [address] at joined
          simpa only [ready] using joined

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentQuery.readyParent_hashInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms readyParent_hashInput

end SigGolfCandidate.SphincsVerifierFtsParentQuery
