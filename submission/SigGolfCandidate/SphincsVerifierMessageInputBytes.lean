import SigGolfCandidate.SphincsVerifierSecondHashBytes

/-!
# Serialized message-digest query fields

The abstract message-digest input is the 20-byte domain header followed by
the parameter, randomizer, root, and 32-byte message. These indexing lemmas
connect that list to the verifier's fixed buffer offsets.
-/

namespace SigGolfCandidate.SphincsVerifierMessageInputBytes
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierMessageHash

theorem input_header (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message) (randomness : Randomness)
    (i : Nat) (hi : i < 20) :
    ((messageInput pk message randomness).map UInt8.toBitVec)[i]'(by
      simpa [messageInput_length] using (show i < 112 by omega)) =
      ((fieldBytes (tweakFields 12 0 0 0 0)).map UInt8.toBitVec)[i]'(by
        simpa [fieldBytes, bytesLE] using hi) := by
  simp only [messageInput, tweakableHashInput, tweakBytes,
    hashDomainFields, List.map_append]
  rw [List.getElem_append_left (by
    simp [fieldBytes, bytesLE]
    omega)]
  rw [List.getElem_append_left (by
    simpa [fieldBytes, bytesLE] using hi)]

theorem input_parameter (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message) (randomness : Randomness)
    (i : Nat) (hi : i < 20) :
    ((messageInput pk message randomness).map UInt8.toBitVec)[20 + i]'(by
      simpa [messageInput_length] using (show 20 + i < 112 by omega)) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  simp only [messageInput, tweakableHashInput, tweakBytes,
    hashDomainFields, Concrete.messageDigestPayload, List.map_append]
  rw [List.getElem_append_left (by
    simp [fieldBytes, bytesLE]
    omega)]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.length_map]
  simp only [show (fieldBytes (tweakFields 12 0 0 0 0)).length = 20 by
    simp [fieldBytes, bytesLE], Nat.add_sub_cancel_left]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  rfl

theorem input_randomizer (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message) (randomness : Randomness)
    (i : Nat) (hi : i < 20) :
    ((messageInput pk message randomness).map UInt8.toBitVec)[40 + i]'(by
      simpa [messageInput_length] using (show 40 + i < 112 by omega)) =
      randomness.extractLsb' (8 * i) 8 := by
  simp only [messageInput, tweakableHashInput, tweakBytes,
    hashDomainFields, Concrete.messageDigestPayload, List.map_append]
  rw [List.getElem_append_right (by
    simp [fieldBytes, bytesLE])]
  simp only [List.length_map, List.length_append]
  simp only [show (fieldBytes (tweakFields 12 0 0 0 0)).length = 20 by
    simp [fieldBytes, bytesLE], show (bytesLE 20 pk.parameter).length = 20 by
    simp [bytesLE]]
  simp only [show 40 + i - (20 + 20) = i by omega]
  rw [List.getElem_append_left (by simp [bytesLE]; omega)]
  rw [List.getElem_append_left (by simpa [bytesLE] using hi)]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  rfl

theorem input_root (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message) (randomness : Randomness)
    (i : Nat) (hi : i < 20) :
    ((messageInput pk message randomness).map UInt8.toBitVec)[60 + i]'(by
      simpa [messageInput_length] using (show 60 + i < 112 by omega)) =
      pk.root.extractLsb' (8 * i) 8 := by
  simp only [messageInput, tweakableHashInput, tweakBytes,
    hashDomainFields, Concrete.messageDigestPayload, List.map_append]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE]; omega)]
  simp only [List.length_map, List.length_append]
  simp only [show (fieldBytes (tweakFields 12 0 0 0 0)).length = 20 by
    simp [fieldBytes, bytesLE], show (bytesLE 20 pk.parameter).length = 20 by
    simp [bytesLE]]
  simp only [show 60 + i - (20 + 20) = 20 + i by omega]
  rw [List.getElem_append_left (by simp [bytesLE]; omega)]
  rw [List.getElem_append_right (by simp [bytesLE])]
  simp only [List.length_map]
  simp only [show (bytesLE 20 randomness).length = 20 by simp [bytesLE],
    Nat.add_sub_cancel_left]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  rfl

theorem input_message (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message) (randomness : Randomness)
    (i : Nat) (hi : i < 32) :
    ((messageInput pk message randomness).map UInt8.toBitVec)[80 + i]'(by
      simpa [messageInput_length] using (show 80 + i < 112 by omega)) =
      message.extractLsb' (8 * i) 8 := by
  simp only [messageInput, tweakableHashInput, tweakBytes,
    hashDomainFields, Concrete.messageDigestPayload, List.map_append]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE]; omega)]
  simp only [List.length_map, List.length_append]
  simp only [show (fieldBytes (tweakFields 12 0 0 0 0)).length = 20 by
    simp [fieldBytes, bytesLE], show (bytesLE 20 pk.parameter).length = 20 by
    simp [bytesLE]]
  simp only [show 80 + i - (20 + 20) = 40 + i by omega]
  rw [List.getElem_append_right (by simp [bytesLE])]
  simp only [List.length_map, List.length_append]
  simp only [show (bytesLE 20 randomness).length = 20 by simp [bytesLE],
    show (bytesLE 20 pk.root).length = 20 by simp [bytesLE]]
  simp only [show 40 + i - (20 + 20) = i by omega]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  rfl

/-- info: 'SigGolfCandidate.SphincsVerifierMessageInputBytes.input_message' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms input_message

end SigGolfCandidate.SphincsVerifierMessageInputBytes
