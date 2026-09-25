import SigGolfCandidate.SphincsVerifierFtsForestHeaderBytes
import SigGolfCandidate.SphincsVerifierFtsRootsPayload

namespace SigGolfCandidate.SphincsVerifierFtsForestQuery
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsForestHashReady
open SigGolfCandidate.SphincsVerifierFtsForestHeaderBytes
open SigGolfCandidate.SphincsVerifierFtsForestPayloadFrame
open SigGolfCandidate.SphincsVerifierFtsRootsPayload
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem forestInput_header (pk : SphincsSecurity.PublicKey)
    (index : Index) (roots : FtsTree → Digest)
    (i : Nat) (hi : i < 20) :
    ((forestInput pk index roots).map UInt8.toBitVec)[i]'(by
      rw [List.length_map, forestInput_length]; omega) =
      ((fieldBytes (tweakFields 11 0 index.val 0 0)).map
        UInt8.toBitVec)[i]'(by simp [fieldBytes, bytesLE]; omega) := by
  simp only [forestInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega)]

theorem forestInput_parameter (pk : SphincsSecurity.PublicKey)
    (index : Index) (roots : FtsTree → Digest)
    (i : Nat) (hi : i < 20) :
    ((forestInput pk index roots).map UInt8.toBitVec)[20 + i]'(by
      rw [List.length_map, forestInput_length]; omega) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  simp only [forestInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [fieldBytes, bytesLE]
  rfl

theorem forestInput_payload (pk : SphincsSecurity.PublicKey)
    (index : Index) (roots : FtsTree → Digest)
    (i : Nat) (hi : i < 480) :
    ((forestInput pk index roots).map UInt8.toBitVec)[40 + i]'(by
      rw [List.length_map, forestInput_length]; omega) =
      ((SphincsSecurity.Concrete.ftsRootsPayload roots).map
        UInt8.toBitVec)[i]'(by
          rw [rootsPayload_flat, List.length_map, List.length_ofFn]
          omega) := by
  simp only [forestInput_eq, List.map_append]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp [fieldBytes, bytesLE]

/-- The exact 520-byte HASH buffer represents the scheme forest-root query. -/
theorem readyForest_hashInput (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (roots : FtsTree → Digest)
    (layerZero : state.getMem 0x43000 = 0)
    (positionZero : state.getMem 0x43010 = 0)
    (treeIndex : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (nodeZero : state.getMem 0x43018 = 0)
    (parameterEncoded : WitnessPrefix state pk)
    (payload : ∀ i, (hi : i < 480) →
      (forestHashReadyState state).getByte
        (BitVec.ofNat 64 (0x40028 + i)) =
        ((SphincsSecurity.Concrete.ftsRootsPayload roots).map
          UInt8.toBitVec)[i]'(by
            rw [rootsPayload_flat, List.length_map, List.length_ofFn]
            omega)) :
    hashInput (forestHashReadyState state) =
      toQuery (forestInput pk index roots) := by
  let ready := forestHashReadyState state
  have source : ready.getReg .x10 = 0x40000 := by
    simp [ready, forestHashReadyState, forestHashRegistersState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  have bits : ready.getReg .x11 = 4160 := by
    simp [ready, forestHashReadyState, forestHashRegistersState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  apply forestHash_query ready pk index roots
  · exact source
  · exact bits
  · intro i hi
    by_cases header : i < 20
    · let byte : Fin 20 := ⟨i, header⟩
      have actual := forestHeader_bytes state index ⟨0, by decide⟩
        layerZero positionZero treeIndex nodeZero byte
      have expected := forestInput_header pk index roots i header
      simpa [ready, byte] using actual.trans expected.symm
    · by_cases parameter : i < 40
      · have smaller : i - 20 < 20 := by omega
        have actual := forestHashReady_parameter_byte state pk
          parameterEncoded (i - 20) smaller
        have expected := forestInput_parameter pk index roots
          (i - 20) smaller
        have joined := actual.trans expected.symm
        have split : 20 + (i - 20) = i := by omega
        have address : 0x40014 + (i - 20) = 0x40000 + i := by omega
        simpa only [ready, split, address] using joined

      · have smaller : i - 40 < 480 := by omega
        have actual := payload (i - 40) smaller
        have expected := forestInput_payload pk index roots
          (i - 40) smaller
        have joined := actual.trans expected.symm
        have split : 40 + (i - 40) = i := by omega
        have address : 0x40028 + (i - 40) = 0x40000 + i := by omega
        simpa only [ready, split, address] using joined

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestQuery.readyForest_hashInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms readyForest_hashInput

end SigGolfCandidate.SphincsVerifierFtsForestQuery
