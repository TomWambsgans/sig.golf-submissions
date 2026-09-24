import SigGolfCandidate.SphincsBridge
import SigGolfCandidate.Hypertree.SecurityPacking
import SigGolfCandidate.SphincsVerifierLoader
import SigGolfCandidate.SphincsVerifierLoadedMessageHash

/-!
# Exact fixed-width SPHINCS wire encoding

The abstract signature serializer and the competition's bit-vector witness
encode the same bytes. This gives the verifier refinement a concrete honest
witness instead of a free relation over arbitrary input bits.
-/

namespace SigGolfCandidate.SphincsWireEncoding
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity SigGolfCandidate.SphincsWire
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384

def encodeBytes (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) : List Byte :=
  (encodeSignature pk signature).map UInt8.toBitVec

theorem encodeBytes_length (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) :
    (encodeBytes pk signature).length = SphincsWire.signatureBytes := by
  simpa [encodeBytes] using encodeSignature_length pk signature

def wire (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) : Bytes SphincsWire.signatureBytes :=
  (Hypertree.Reference.packed (encodeBytes pk signature)).2.cast (by
    change 8 * (encodeBytes pk signature).length = 8 * SphincsWire.signatureBytes
    rw [encodeBytes_length])

private theorem packed_cast_bytes {n : Nat} (data : List Byte)
    (length : data.length = n) :
    SigGolf.bytes ((Hypertree.Reference.packed data).2.cast (by
      change 8 * data.length = 8 * n
      rw [length]) : Bytes n) = data := by
  apply Hypertree.SecurityPacking.packed_injective
  rw [SigGolfCandidate.Serialization.packed_bytes]
  apply SigGolfCandidate.Serialization.query_eq
  · change 8 * n = 8 * data.length
    rw [length]
  · simp only [BitVec.toNat_cast]

theorem wire_bytes (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) :
    SigGolf.bytes (wire pk signature) = encodeBytes pk signature := by
  exact packed_cast_bytes (encodeBytes pk signature)
    (encodeBytes_length pk signature)

theorem wire_byte (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (i : Nat)
    (hi : i < SphincsWire.signatureBytes) :
    (wire pk signature).extractLsb' (8 * i) 8 =
      (encodeBytes pk signature)[i]'(by
        rw [encodeBytes_length]
        exact hi) := by
  have h := congrArg (fun data : List Byte => data[i]?)
    (wire_bytes pk signature)
  simpa [SigGolf.bytes, encodeBytes_length, hi] using h

private def prefixBytes (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) : List UInt8 :=
  bytesLE 20 pk.root ++ bytesLE 20 pk.parameter ++
    bytesLE 20 signature.randomness

private def restBytes (signature : SphincsSecurity.Signature) : List UInt8 :=
  concatFields (ftsTrees - 1) (ftsOpening signature) ++
    layerEncoding signature topLayer ++ layerEncoding signature middleLayer ++
    layerEncoding signature middle2Layer ++ layerEncoding signature middle3Layer ++
    layerEncoding signature middle4Layer ++ layerEncoding signature bottomLayer

private theorem encodeBytes_prefix (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) :
    encodeBytes pk signature =
      (prefixBytes pk signature).map UInt8.toBitVec ++
        (restBytes signature).map UInt8.toBitVec := by
  simp [encodeBytes, encodeSignature, prefixBytes, restBytes,
    List.map_append, List.append_assoc, digestBytes]

private theorem wire_prefix_byte (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (i : Nat) (hi : i < 60) :
    (wire pk signature).extractLsb' (8 * i) 8 =
      ((prefixBytes pk signature).map UInt8.toBitVec)[i]'(by
        simpa [prefixBytes, bytesLE] using hi) := by
  have full : i < SphincsWire.signatureBytes := by
    rw [SphincsWire.signatureBytes_eq]
    omega
  rw [wire_byte pk signature i full]
  simp only [encodeBytes_prefix]
  rw [List.getElem_append_left (by
    simpa [prefixBytes, bytesLE] using hi)]

private theorem prefix_root_byte (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (i : Nat) (hi : i < 20) :
    ((prefixBytes pk signature).map UInt8.toBitVec)[i]'(by
      simpa [prefixBytes, bytesLE] using (show i < 60 by omega)) =
      pk.root.extractLsb' (8 * i) 8 := by
  simp only [prefixBytes, List.map_append]
  rw [List.getElem_append_left (by simp [bytesLE]; omega)]
  rw [List.getElem_append_left (by simpa [bytesLE] using hi)]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  rfl

private theorem prefix_parameter_byte (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (i : Nat) (hi : i < 20) :
    ((prefixBytes pk signature).map UInt8.toBitVec)[20 + i]'(by
      simpa [prefixBytes, bytesLE] using (show 20 + i < 60 by omega)) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  simp only [prefixBytes, List.map_append]
  rw [List.getElem_append_left (by simp [bytesLE]; omega)]
  rw [List.getElem_append_right (by simp [bytesLE])]
  simp only [List.length_map]
  simp only [show (bytesLE 20 pk.root).length = 20 by simp [bytesLE],
    Nat.add_sub_cancel_left]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  rfl

private theorem prefix_randomizer_byte (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (i : Nat) (hi : i < 20) :
    ((prefixBytes pk signature).map UInt8.toBitVec)[40 + i]'(by
      simpa [prefixBytes, bytesLE] using (show 40 + i < 60 by omega)) =
      signature.randomness.extractLsb' (8 * i) 8 := by
  simp only [prefixBytes, List.map_append]
  rw [List.getElem_append_right (by simp [bytesLE])]
  simp only [List.length_map, List.length_append]
  simp only [show (bytesLE 20 pk.root).length = 20 by simp [bytesLE],
    show (bytesLE 20 pk.parameter).length = 20 by simp [bytesLE]]
  simp only [show 40 + i - (20 + 20) = i by omega]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  rfl

theorem wire_encodedWitness (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) :
    SphincsVerifierLoader.EncodedWitness (wire pk signature) pk := by
  constructor
  · intro i hi
    exact (wire_prefix_byte pk signature i (by omega)).trans
      (prefix_root_byte pk signature i hi)
  · intro i hi
    exact (wire_prefix_byte pk signature (20 + i) (by omega)).trans
      (prefix_parameter_byte pk signature i hi)

theorem wire_randomizer (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (i : Nat) (hi : i < 20) :
    (wire pk signature).extractLsb' (8 * (40 + i)) 8 =
      signature.randomness.extractLsb' (8 * i) 8 :=
  (wire_prefix_byte pk signature (40 + i) (by omega)).trans
    (prefix_randomizer_byte pk signature i hi)

/-- An honestly serialized signature reaches the exact abstract message query. -/
theorem loaded_honest_message_ready (publicKey : SigGolf.PublicKey)
    (message : SigGolf.Message) (inner : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, wire inner signature) = some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64) :
    ∃ ready, OrdinarySteps SphincsImages.verify
      (writeHash
        (SphincsVerifierHashSetup.firstHashState state) answer)
      107 ready ∧ ready.pc = 0x12a0 ∧
      SphincsVerifierMessageHash.MessageReady ready inner message
        signature.randomness := by
  exact SphincsVerifierLoadedMessageHash.loaded_message_ready
    publicKey message (wire inner signature) inner signature.randomness
    state answer loaded answerMatches
    (wire_encodedWitness inner signature)
    (wire_randomizer inner signature)

theorem loaded_honest_message_query (publicKey : SigGolf.PublicKey)
    (message : SigGolf.Message) (inner : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, wire inner signature) = some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64) :
    ∃ ready, OrdinarySteps SphincsImages.verify
      (writeHash (SphincsVerifierHashSetup.firstHashState state) answer)
      107 ready ∧ ready.pc = 0x12a0 ∧
      hashInput ready = SphincsBridge.toQuery
        (SphincsVerifierMessageHash.messageInput inner message
          signature.randomness) ∧
      compressions (hashInput ready).1 = 2 := by
  obtain ⟨ready, trace, pc, prepared⟩ :=
    loaded_honest_message_ready publicKey message inner signature state answer
      loaded answerMatches
  exact ⟨ready, trace, pc,
    SphincsVerifierMessageHash.messageReady_hashInput ready inner message
      signature.randomness prepared,
    (SphincsVerifierMessageHash.messageReady_hashCost ready inner message
      signature.randomness prepared).2⟩

/-- info: 'SigGolfCandidate.SphincsWireEncoding.wire_encodedWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wire_encodedWitness

/-- info: 'SigGolfCandidate.SphincsWireEncoding.wire_randomizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wire_randomizer

/-- info: 'SigGolfCandidate.SphincsWireEncoding.loaded_honest_message_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_message_ready

/-- info: 'SigGolfCandidate.SphincsWireEncoding.loaded_honest_message_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_message_query

/-- info: 'SigGolfCandidate.SphincsWireEncoding.wire_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wire_bytes

end SigGolfCandidate.SphincsWireEncoding
