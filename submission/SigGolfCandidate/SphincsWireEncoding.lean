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

theorem concatFields_byte {n width : Nat}
    (fields : Fin n → List UInt8)
    (hlen : ∀ tree, (fields tree).length = width)
    (tree : Fin n) (i : Nat) (hi : i < width) :
    (concatFields n fields)[tree.val * width + i]'(by
      rw [concatFields_length n fields width hlen]
      have hnext : (tree.val + 1) * width ≤ n * width :=
        Nat.mul_le_mul_right width (Nat.succ_le_of_lt tree.isLt)
      have hbyte : tree.val * width + i < (tree.val + 1) * width := by
        rw [Nat.add_mul]
        omega
      exact lt_of_lt_of_le hbyte hnext) =
      (fields tree)[i]'(by rw [hlen]; exact hi) := by
  induction n with
  | zero => exact tree.elim0
  | succ n ih =>
      cases tree using Fin.cases with
      | zero =>
          simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add,
            concatFields]
          rw [List.getElem_append_left (by rw [hlen]; exact hi)]
      | succ tree =>
          simp only [Fin.val_succ, concatFields]
          rw [List.getElem_append_right (by
            rw [hlen]
            have h : width ≤ (tree.val + 1) * width := by
              rw [Nat.add_mul]
              omega
            omega)]
          simp only [hlen]
          have htail : ∀ child : Fin n,
              (fields child.succ).length = width := by
            intro child
            exact hlen child.succ
          have indexEq : (tree.val + 1) * width + i - width =
              tree.val * width + i := by
            rw [Nat.add_mul]
            omega
          simpa only [indexEq] using
            ih (fun j : Fin n => fields j.succ) htail tree

private theorem openingPosition_lt (tree : FtsTree) (j : Nat)
    (hj : j < ftsOpeningBytes) :
    tree.val * ftsOpeningBytes + j <
      (ftsTrees - 1) * ftsOpeningBytes := by
  have treeBound := tree.isLt
  norm_num [ftsTrees, ftsOpeningBytes, ftsTreeHeight, digestBytes] at *
  omega

theorem restBytes_opening_byte (signature : Signature)
    (tree : FtsTree) (j : Nat) (hj : j < ftsOpeningBytes) :
    ((restBytes signature).map UInt8.toBitVec)[tree.val * ftsOpeningBytes + j]'(by
          simp only [List.length_map, restBytes, List.length_append]
          rw [concatFields_length _ _ _ (ftsOpening_length signature)]
          have h := openingPosition_lt tree j hj
          omega) =
      ((ftsOpening signature tree).map UInt8.toBitVec)[j]'(by
        rw [List.length_map, ftsOpening_length]
        exact hj) := by
  simp only [restBytes, List.map_append, List.append_assoc]
  rw [List.getElem_append_left (by
    simp only [List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature)]
    exact openingPosition_lt tree j hj)]
  simp only [List.getElem_map]
  simpa only [List.getElem_map] using congrArg UInt8.toBitVec
    (concatFields_byte (ftsOpening signature)
      (ftsOpening_length signature) tree j hj)

theorem ftsOpening_secretByte (signature : Signature)
    (tree : FtsTree) (i : Nat) (hi : i < 20) :
    ((ftsOpening signature tree).map UInt8.toBitVec)[i]'(by
      rw [List.length_map, ftsOpening_length]
      simp [ftsOpeningBytes, digestBytes]
      omega) =
      (signature.ftsSecret tree).extractLsb' (8 * i) 8 := by
  simp only [ftsOpening, List.map_append]
  rw [List.getElem_append_left (by simp [bytesLE, digestBytes]; omega)]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  rfl

theorem digestVectorBytes_byte {n : Nat}
    (values : Fin n → Digest) (digest : Fin n)
    (i : Nat) (hi : i < digestBytes) :
    ((digestVectorBytes values).map UInt8.toBitVec)[digest.val * digestBytes + i]'(by
          rw [List.length_map, digestVectorBytes_length]
          have h := digest.isLt
          norm_num [digestBytes] at *
          omega) =
      (values digest).extractLsb' (8 * i) 8 := by
  simp only [digestVectorBytes, List.getElem_map, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  have quotient : (digest.val * digestBytes + i) / digestBytes =
      digest.val := by
    norm_num [digestBytes] at *
    omega
  have remainder : (digest.val * digestBytes + i) % digestBytes = i := by
    norm_num [digestBytes] at *
    omega
  simp only [quotient, remainder]

theorem layerEncoding_chainByte (signature : Signature) (lay : Layer)
    (chain : ChainIndex) (i : Nat) (hi : i < digestBytes) :
    ((layerEncoding signature lay).map UInt8.toBitVec)[
      counterBytes + chain.val * digestBytes + i]'(by
        rw [List.length_map, layerEncoding_length]
        have hc := chain.isLt
        simp only [layerBytes, counterBytes, numChains, digestBytes] at *
        omega) =
      ((signature.layers lay).chainValues chain).extractLsb' (8 * i) 8 := by
  simp only [layerEncoding, List.map_append]
  rw [List.getElem_append_left (by
    simp only [List.length_append, List.length_map,
      digestVectorBytes_length]
    rw [show (bytesLE counterBytes (BitVec.ofNat 32
      (signature.layers lay).counter.toNat)).length = counterBytes by
        simp [bytesLE]]
    have hc := chain.isLt
    change chain.val < 52 at hc
    simp only [counterBytes, numChains, digestBytes] at *
    omega)]
  rw [List.getElem_append_right (by simp [bytesLE, counterBytes]; omega)]
  simp only [List.length_map]
  have prefixLength :
      (bytesLE counterBytes (BitVec.ofNat 32
        (signature.layers lay).counter.toNat)).length = counterBytes := by
    simp [bytesLE]
  simp only [prefixLength]
  have indexEq : counterBytes + chain.val * digestBytes + i -
      counterBytes = chain.val * digestBytes + i := by omega
  simp only [indexEq]
  exact digestVectorBytes_byte (signature.layers lay).chainValues chain i hi

theorem ftsOpening_pathByte (signature : Signature)
    (tree : FtsTree) (level : Fin ftsTreeHeight)
    (i : Nat) (hi : i < digestBytes) :
    ((ftsOpening signature tree).map UInt8.toBitVec)[digestBytes + level.val * digestBytes + i]'(by
          rw [List.length_map, ftsOpening_length]
          have h := level.isLt
          norm_num [ftsOpeningBytes, ftsTreeHeight, digestBytes] at *
          omega) =
      (signature.ftsPath tree level).extractLsb' (8 * i) 8 := by
  simp only [ftsOpening, List.map_append]
  rw [List.getElem_append_right (by
    simp [bytesLE, digestBytes]
    omega)]
  simp only [List.length_map]
  have prefixLength : (bytesLE digestBytes (signature.ftsSecret tree)).length =
      digestBytes := by simp [bytesLE]
  simp only [prefixLength]
  have indexEq : digestBytes + level.val * digestBytes + i -
      digestBytes = level.val * digestBytes + i := by omega
  simp only [indexEq]
  exact digestVectorBytes_byte (signature.ftsPath tree) level i hi

/-- A layer's authentication path follows its counter and WOTS chain values. -/
theorem layerEncoding_pathByte (signature : Signature) (lay : Layer)
    (level : Fin (layerHeight lay)) (i : Nat) (hi : i < digestBytes) :
    ((layerEncoding signature lay).map UInt8.toBitVec)[counterBytes +
        numChains * digestBytes + level.val * digestBytes + i]'(by
          rw [List.length_map, layerEncoding_length]
          have h := level.isLt
          simp only [layerBytes, digestBytes, numChains, counterBytes]
          have hi20 : i < 20 := by simpa [digestBytes] using hi
          omega) =
      ((signature.layers lay).path level).extractLsb' (8 * i) 8 := by
  simp only [layerEncoding, List.map_append]
  rw [List.getElem_append_right (by
    simp [bytesLE, digestVectorBytes_length, digestBytes, counterBytes]
    omega)]
  simp only [List.length_map, List.length_append]
  simp only [show (bytesLE counterBytes (BitVec.ofNat 32
      (signature.layers lay).counter.toNat)).length = counterBytes by
      simp [bytesLE], digestVectorBytes_length]
  have indexEq : counterBytes + numChains * digestBytes +
      level.val * digestBytes + i -
      (counterBytes + digestBytes * numChains) =
      level.val * digestBytes + i := by
    simp only [digestBytes, numChains, counterBytes]
    omega
  simp only [indexEq]
  exact digestVectorBytes_byte (signature.layers lay).path level i hi

private theorem layer_path_index_lt (lay : Layer)
    (level : Fin (layerHeight lay)) (i : Nat) (hi : i < digestBytes) :
    counterBytes + numChains * digestBytes + level.val * digestBytes + i <
      layerBytes lay := by
  have hlevel := level.isLt
  have hi20 : i < 20 := by simpa [digestBytes] using hi
  simp only [layerBytes, counterBytes, numChains, digestBytes]
  omega

/-- Locate a layer path once the signature list is split at that layer. -/
private theorem wire_path_of_split (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (lay : Layer) (offset : Nat)
    (before after : List Byte)
    (split : encodeBytes pk signature =
      before ++ ((layerEncoding signature lay).map UInt8.toBitVec) ++ after)
    (beforeLength : before.length = offset)
    (level : Fin (layerHeight lay)) (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (offset + counterBytes + numChains * digestBytes +
        level.val * digestBytes + i)) 8 =
      ((signature.layers lay).path level).extractLsb' (8 * i) 8 := by
  let j := counterBytes + numChains * digestBytes + level.val * digestBytes + i
  have jBound : j < ((layerEncoding signature lay).map UInt8.toBitVec).length := by
    simpa only [j, List.length_map, layerEncoding_length] using
      layer_path_index_lt lay level i hi
  have full : offset + j < SphincsWire.signatureBytes := by
    rw [← encodeBytes_length pk signature, split]
    simp only [List.length_append, List.length_map, beforeLength]
    simp only [List.length_map] at jBound
    omega
  have indexEq : offset + counterBytes + numChains * digestBytes +
      level.val * digestBytes + i = offset + j := by
    dsimp [j]
    omega
  rw [indexEq, wire_byte pk signature (offset + j) full]
  simp only [split, List.append_assoc]
  rw [List.getElem_append_right (by rw [beforeLength]; omega)]
  simp only [beforeLength, Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by exact jBound)]
  simpa only [j] using layerEncoding_pathByte signature lay level i hi

/-- Locate a WOTS chain value once the signature list is split at its layer. -/
private theorem wire_chain_of_split (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (lay : Layer) (offset : Nat)
    (before after : List Byte)
    (split : encodeBytes pk signature =
      before ++ ((layerEncoding signature lay).map UInt8.toBitVec) ++ after)
    (beforeLength : before.length = offset)
    (chain : ChainIndex) (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (offset + counterBytes + chain.val * digestBytes + i)) 8 =
      ((signature.layers lay).chainValues chain).extractLsb' (8 * i) 8 := by
  let j := counterBytes + chain.val * digestBytes + i
  have jBound : j < ((layerEncoding signature lay).map UInt8.toBitVec).length := by
    rw [List.length_map, layerEncoding_length]
    have hc := chain.isLt
    change chain.val < 52 at hc
    have hi20 : i < 20 := by simpa [digestBytes] using hi
    simp only [j, layerBytes, counterBytes, numChains, digestBytes]
    omega
  have full : offset + j < SphincsWire.signatureBytes := by
    rw [← encodeBytes_length pk signature, split]
    simp only [List.length_append, List.length_map, beforeLength]
    simp only [List.length_map] at jBound
    omega
  have indexEq : offset + counterBytes + chain.val * digestBytes + i =
      offset + j := by
    dsimp [j]
    omega
  rw [indexEq, wire_byte pk signature (offset + j) full]
  simp only [split, List.append_assoc]
  rw [List.getElem_append_right (by rw [beforeLength]; omega)]
  simp only [beforeLength, Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by exact jBound)]
  simpa only [j] using layerEncoding_chainByte signature lay chain i hi

/-- The top XMSS authentication path occupies its fixed slot in the witness. -/
theorem wire_topPath (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (level : Fin (layerHeight topLayer))
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (topOffset + counterBytes + numChains * digestBytes +
        level.val * digestBytes + i)) 8 =
      ((signature.layers topLayer).path level).extractLsb' (8 * i) 8 := by
  let j := counterBytes + numChains * digestBytes + level.val * digestBytes + i
  have jBound : j < layerBytes topLayer := by
    dsimp [j, layerBytes]
    have hlevel := level.isLt
    have height : layerHeight topLayer = 11 := by decide
    have hi20 : i < 20 := by simpa [digestBytes] using hi
    simp only [counterBytes, numChains, digestBytes] at *
    omega
  have full : topOffset + j < SphincsWire.signatureBytes := by
    have size := SphincsWire.signatureBytes_eq
    have topStart : topOffset = 4380 := by decide
    have topSize : layerBytes topLayer = 1264 := by decide
    omega
  have indexEq : topOffset + counterBytes + numChains * digestBytes +
      level.val * digestBytes + i = topOffset + j := by
    dsimp [j]
    omega
  rw [indexEq]
  rw [wire_byte pk signature (topOffset + j) full]
  simp only [encodeBytes_prefix]
  rw [List.getElem_append_right (by
    simp [prefixBytes, bytesLE, topOffset, ftsOffset,
      ftsOpeningBytes, ftsTrees, digestBytes]
    omega)]
  simp only [List.length_map]
  have prefixLength : (prefixBytes pk signature).length = 60 := by
    simp [prefixBytes, bytesLE]
  simp only [prefixLength]
  have offsetEq : topOffset + j - 60 =
      (ftsTrees - 1) * ftsOpeningBytes + j := by
    simp only [topOffset, ftsOffset, randomizerOffset, parameterOffset,
      rootOffset, digestBytes]
    omega
  simp only [offsetEq, restBytes, List.map_append, List.append_assoc]
  rw [List.getElem_append_right (by
    simp only [List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature)]
    omega)]
  simp only [List.length_map,
    concatFields_length _ _ _ (ftsOpening_length signature),
    Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by
    simpa only [List.length_map, layerEncoding_length] using jBound)]
  simpa only [j] using layerEncoding_pathByte signature topLayer level i hi

/-- The verifier loader places the top XMSS path at its actual memory address. -/
theorem loaded_honest_topPath (publicKey : SigGolf.PublicKey)
    (message : SigGolf.Message) (inner : SphincsSecurity.PublicKey)
    (signature : Signature) (state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, wire inner signature) = some state)
    (level : Fin (layerHeight topLayer)) (i : Nat) (hi : i < digestBytes) :
    state.getByte (BitVec.ofNat 64
      (0x22ca0 + topOffset + counterBytes + numChains * digestBytes +
        level.val * digestBytes + i)) =
      ((signature.layers topLayer).path level).extractLsb' (8 * i) 8 := by
  have full : topOffset + counterBytes + numChains * digestBytes +
      level.val * digestBytes + i < SphincsWire.signatureBytes := by
    have hlevel := level.isLt
    have height : layerHeight topLayer = 11 := by decide
    have hi20 : i < 20 := by simpa [digestBytes] using hi
    have topStart : topOffset = 4380 := by decide
    have size := SphincsWire.signatureBytes_eq
    simp only [counterBytes, numChains, digestBytes] at *
    omega
  have addressEq : 0x22ca0 + topOffset + counterBytes +
      numChains * digestBytes + level.val * digestBytes + i =
      0x22ca0 + (topOffset + counterBytes + numChains * digestBytes +
        level.val * digestBytes + i) := by omega
  rw [addressEq, SphincsVerifierLoader.loaded_witness publicKey message
    (wire inner signature) state loaded _ full]
  exact wire_topPath inner signature level i hi

/-- The next layer's path follows the top layer in the same fixed wire image. -/
theorem wire_middlePath (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (level : Fin (layerHeight middleLayer))
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (middleOffset + counterBytes + numChains * digestBytes +
        level.val * digestBytes + i)) 8 =
      ((signature.layers middleLayer).path level).extractLsb' (8 * i) 8 := by
  let before : List Byte :=
    (prefixBytes pk signature).map UInt8.toBitVec ++
      (concatFields (ftsTrees - 1) (ftsOpening signature)).map UInt8.toBitVec ++
      (layerEncoding signature topLayer).map UInt8.toBitVec
  let after : List Byte :=
    (layerEncoding signature middle2Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle3Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle4Layer).map UInt8.toBitVec ++
      (layerEncoding signature bottomLayer).map UInt8.toBitVec
  have split : encodeBytes pk signature = before ++
      (layerEncoding signature middleLayer).map UInt8.toBitVec ++ after := by
    rw [encodeBytes_prefix]
    simp only [before, after, restBytes, List.map_append, List.append_assoc]
  have beforeLength : before.length = middleOffset := by
    simp only [before, List.length_append, List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature),
      layerEncoding_length]
    simp [prefixBytes, bytesLE, middleOffset, topOffset, ftsOffset,
      randomizerOffset, parameterOffset, rootOffset, ftsOpeningBytes,
      ftsTrees, digestBytes, layerBytes, numChains, counterBytes,
      layerHeight, maxLayerHeight]
  exact wire_path_of_split pk signature middleLayer middleOffset before after
    split beforeLength level i hi

theorem wire_middle2Path (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (level : Fin (layerHeight middle2Layer))
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (middle2Offset + counterBytes + numChains * digestBytes +
        level.val * digestBytes + i)) 8 =
      ((signature.layers middle2Layer).path level).extractLsb' (8 * i) 8 := by
  let before : List Byte :=
    (prefixBytes pk signature).map UInt8.toBitVec ++
      (concatFields (ftsTrees - 1) (ftsOpening signature)).map UInt8.toBitVec ++
      (layerEncoding signature topLayer).map UInt8.toBitVec ++
      (layerEncoding signature middleLayer).map UInt8.toBitVec
  let after : List Byte :=
    (layerEncoding signature middle3Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle4Layer).map UInt8.toBitVec ++
      (layerEncoding signature bottomLayer).map UInt8.toBitVec
  have split : encodeBytes pk signature = before ++
      (layerEncoding signature middle2Layer).map UInt8.toBitVec ++ after := by
    rw [encodeBytes_prefix]
    simp only [before, after, restBytes, List.map_append, List.append_assoc]
  have beforeLength : before.length = middle2Offset := by
    simp only [before, List.length_append, List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature)]
    simp only [layerEncoding_length]
    simp [prefixBytes, bytesLE, middle2Offset, middleOffset, topOffset,
      ftsOffset, randomizerOffset, parameterOffset, rootOffset,
      ftsOpeningBytes, ftsTrees, digestBytes, layerBytes, numChains,
      counterBytes, layerHeight, maxLayerHeight]
  exact wire_path_of_split pk signature middle2Layer middle2Offset before after
    split beforeLength level i hi

theorem wire_middle3Path (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (level : Fin (layerHeight middle3Layer))
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (middle3Offset + counterBytes + numChains * digestBytes +
        level.val * digestBytes + i)) 8 =
      ((signature.layers middle3Layer).path level).extractLsb' (8 * i) 8 := by
  let before : List Byte :=
    (prefixBytes pk signature).map UInt8.toBitVec ++
      (concatFields (ftsTrees - 1) (ftsOpening signature)).map UInt8.toBitVec ++
      (layerEncoding signature topLayer).map UInt8.toBitVec ++
      (layerEncoding signature middleLayer).map UInt8.toBitVec ++
      (layerEncoding signature middle2Layer).map UInt8.toBitVec
  let after : List Byte :=
    (layerEncoding signature middle4Layer).map UInt8.toBitVec ++
      (layerEncoding signature bottomLayer).map UInt8.toBitVec
  have split : encodeBytes pk signature = before ++
      (layerEncoding signature middle3Layer).map UInt8.toBitVec ++ after := by
    rw [encodeBytes_prefix]
    simp only [before, after, restBytes, List.map_append, List.append_assoc]
  have beforeLength : before.length = middle3Offset := by
    simp only [before, List.length_append, List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature)]
    simp only [layerEncoding_length]
    simp [prefixBytes, bytesLE, middle3Offset, middle2Offset,
      middleOffset, topOffset, ftsOffset, randomizerOffset,
      parameterOffset, rootOffset, ftsOpeningBytes, ftsTrees,
      digestBytes, layerBytes, numChains, counterBytes,
      layerHeight, maxLayerHeight]
  exact wire_path_of_split pk signature middle3Layer middle3Offset before after
    split beforeLength level i hi

theorem wire_middle4Path (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (level : Fin (layerHeight middle4Layer))
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (middle4Offset + counterBytes + numChains * digestBytes +
        level.val * digestBytes + i)) 8 =
      ((signature.layers middle4Layer).path level).extractLsb' (8 * i) 8 := by
  let before : List Byte :=
    (prefixBytes pk signature).map UInt8.toBitVec ++
      (concatFields (ftsTrees - 1) (ftsOpening signature)).map UInt8.toBitVec ++
      (layerEncoding signature topLayer).map UInt8.toBitVec ++
      (layerEncoding signature middleLayer).map UInt8.toBitVec ++
      (layerEncoding signature middle2Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle3Layer).map UInt8.toBitVec
  let after : List Byte :=
    (layerEncoding signature bottomLayer).map UInt8.toBitVec
  have split : encodeBytes pk signature = before ++
      (layerEncoding signature middle4Layer).map UInt8.toBitVec ++ after := by
    rw [encodeBytes_prefix]
    simp only [before, after, restBytes, List.map_append, List.append_assoc]
  have beforeLength : before.length = middle4Offset := by
    simp only [before, List.length_append, List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature)]
    simp only [layerEncoding_length]
    simp [prefixBytes, bytesLE, middle4Offset, middle3Offset,
      middle2Offset, middleOffset, topOffset, ftsOffset, randomizerOffset,
      parameterOffset, rootOffset, ftsOpeningBytes, ftsTrees,
      digestBytes, layerBytes, numChains, counterBytes,
      layerHeight, maxLayerHeight]
  exact wire_path_of_split pk signature middle4Layer middle4Offset before after
    split beforeLength level i hi

theorem wire_bottomPath (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (level : Fin (layerHeight bottomLayer))
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (bottomOffset + counterBytes + numChains * digestBytes +
        level.val * digestBytes + i)) 8 =
      ((signature.layers bottomLayer).path level).extractLsb' (8 * i) 8 := by
  let before : List Byte :=
    (prefixBytes pk signature).map UInt8.toBitVec ++
      (concatFields (ftsTrees - 1) (ftsOpening signature)).map UInt8.toBitVec ++
      (layerEncoding signature topLayer).map UInt8.toBitVec ++
      (layerEncoding signature middleLayer).map UInt8.toBitVec ++
      (layerEncoding signature middle2Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle3Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle4Layer).map UInt8.toBitVec
  have split : encodeBytes pk signature = before ++
      (layerEncoding signature bottomLayer).map UInt8.toBitVec ++ [] := by
    rw [encodeBytes_prefix]
    simp only [before, restBytes, List.map_append, List.append_assoc,
      List.append_nil]
  have beforeLength : before.length = bottomOffset := by
    simp only [before, List.length_append, List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature)]
    simp only [layerEncoding_length]
    simp [prefixBytes, bytesLE, bottomOffset, middle4Offset,
      middle3Offset, middle2Offset, middleOffset, topOffset, ftsOffset,
      randomizerOffset, parameterOffset, rootOffset,
      ftsOpeningBytes, ftsTrees, digestBytes, layerBytes, numChains,
      counterBytes, layerHeight, maxLayerHeight]
  exact wire_path_of_split pk signature bottomLayer bottomOffset before []
    split beforeLength level i hi

/-- The top layer's WOTS values occupy the bytes before its XMSS path. -/
theorem wire_topChain (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (chain : ChainIndex)
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (topOffset + counterBytes + chain.val * digestBytes + i)) 8 =
      ((signature.layers topLayer).chainValues chain).extractLsb' (8 * i) 8 := by
  let before : List Byte :=
    (prefixBytes pk signature).map UInt8.toBitVec ++
      (concatFields (ftsTrees - 1) (ftsOpening signature)).map UInt8.toBitVec
  let after : List Byte :=
    (layerEncoding signature middleLayer).map UInt8.toBitVec ++
      (layerEncoding signature middle2Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle3Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle4Layer).map UInt8.toBitVec ++
      (layerEncoding signature bottomLayer).map UInt8.toBitVec
  have split : encodeBytes pk signature = before ++
      (layerEncoding signature topLayer).map UInt8.toBitVec ++ after := by
    rw [encodeBytes_prefix]
    simp only [before, after, restBytes, List.map_append, List.append_assoc]
  have beforeLength : before.length = topOffset := by
    simp only [before, List.length_append, List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature)]
    simp [prefixBytes, bytesLE, topOffset, ftsOffset,
      randomizerOffset, parameterOffset, rootOffset, ftsOpeningBytes,
      ftsTrees, digestBytes, layerBytes, numChains, counterBytes]
  exact wire_chain_of_split pk signature topLayer topOffset before after
    split beforeLength chain i hi

/-- The middle layer's WOTS values occupy their encoded chain slots. -/
theorem wire_middleChain (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (chain : ChainIndex)
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (middleOffset + counterBytes + chain.val * digestBytes + i)) 8 =
      ((signature.layers middleLayer).chainValues chain).extractLsb' (8 * i) 8 := by
  let before : List Byte :=
    (prefixBytes pk signature).map UInt8.toBitVec ++
      (concatFields (ftsTrees - 1) (ftsOpening signature)).map UInt8.toBitVec ++
      (layerEncoding signature topLayer).map UInt8.toBitVec
  let after : List Byte :=
    (layerEncoding signature middle2Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle3Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle4Layer).map UInt8.toBitVec ++
      (layerEncoding signature bottomLayer).map UInt8.toBitVec
  have split : encodeBytes pk signature = before ++
      (layerEncoding signature middleLayer).map UInt8.toBitVec ++ after := by
    rw [encodeBytes_prefix]
    simp only [before, after, restBytes, List.map_append, List.append_assoc]
  have beforeLength : before.length = middleOffset := by
    simp only [before, List.length_append, List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature)]
    simp_rw [layerEncoding_length]
    simp [prefixBytes, bytesLE, middleOffset, bottomOffset,
      middle4Offset, middle3Offset, middle2Offset, middleOffset,
      topOffset, ftsOffset, randomizerOffset, parameterOffset, rootOffset,
      ftsOpeningBytes, ftsTrees, digestBytes, layerBytes,
      numChains, counterBytes, layerHeight, maxLayerHeight]
  exact wire_chain_of_split pk signature middleLayer middleOffset
    before after split beforeLength chain i hi

/-- The middle2 layer's WOTS values occupy their encoded chain slots. -/
theorem wire_middle2Chain (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (chain : ChainIndex)
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (middle2Offset + counterBytes + chain.val * digestBytes + i)) 8 =
      ((signature.layers middle2Layer).chainValues chain).extractLsb' (8 * i) 8 := by
  let before : List Byte :=
    (prefixBytes pk signature).map UInt8.toBitVec ++
      (concatFields (ftsTrees - 1) (ftsOpening signature)).map UInt8.toBitVec ++
      (layerEncoding signature topLayer).map UInt8.toBitVec ++
      (layerEncoding signature middleLayer).map UInt8.toBitVec
  let after : List Byte :=
    (layerEncoding signature middle3Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle4Layer).map UInt8.toBitVec ++
      (layerEncoding signature bottomLayer).map UInt8.toBitVec
  have split : encodeBytes pk signature = before ++
      (layerEncoding signature middle2Layer).map UInt8.toBitVec ++ after := by
    rw [encodeBytes_prefix]
    simp only [before, after, restBytes, List.map_append, List.append_assoc]
  have beforeLength : before.length = middle2Offset := by
    simp only [before, List.length_append, List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature)]
    simp_rw [layerEncoding_length]
    simp [prefixBytes, bytesLE, middle2Offset, bottomOffset,
      middle4Offset, middle3Offset, middle2Offset, middleOffset,
      topOffset, ftsOffset, randomizerOffset, parameterOffset, rootOffset,
      ftsOpeningBytes, ftsTrees, digestBytes, layerBytes,
      numChains, counterBytes, layerHeight, maxLayerHeight]
  exact wire_chain_of_split pk signature middle2Layer middle2Offset
    before after split beforeLength chain i hi

/-- The middle3 layer's WOTS values occupy their encoded chain slots. -/
theorem wire_middle3Chain (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (chain : ChainIndex)
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (middle3Offset + counterBytes + chain.val * digestBytes + i)) 8 =
      ((signature.layers middle3Layer).chainValues chain).extractLsb' (8 * i) 8 := by
  let before : List Byte :=
    (prefixBytes pk signature).map UInt8.toBitVec ++
      (concatFields (ftsTrees - 1) (ftsOpening signature)).map UInt8.toBitVec ++
      (layerEncoding signature topLayer).map UInt8.toBitVec ++
      (layerEncoding signature middleLayer).map UInt8.toBitVec ++
      (layerEncoding signature middle2Layer).map UInt8.toBitVec
  let after : List Byte :=
    (layerEncoding signature middle4Layer).map UInt8.toBitVec ++
      (layerEncoding signature bottomLayer).map UInt8.toBitVec
  have split : encodeBytes pk signature = before ++
      (layerEncoding signature middle3Layer).map UInt8.toBitVec ++ after := by
    rw [encodeBytes_prefix]
    simp only [before, after, restBytes, List.map_append, List.append_assoc]
  have beforeLength : before.length = middle3Offset := by
    simp only [before, List.length_append, List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature)]
    simp_rw [layerEncoding_length]
    simp [prefixBytes, bytesLE, middle3Offset, bottomOffset,
      middle4Offset, middle3Offset, middle2Offset, middleOffset,
      topOffset, ftsOffset, randomizerOffset, parameterOffset, rootOffset,
      ftsOpeningBytes, ftsTrees, digestBytes, layerBytes,
      numChains, counterBytes, layerHeight, maxLayerHeight]
  exact wire_chain_of_split pk signature middle3Layer middle3Offset
    before after split beforeLength chain i hi

/-- The middle4 layer's WOTS values occupy their encoded chain slots. -/
theorem wire_middle4Chain (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (chain : ChainIndex)
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (middle4Offset + counterBytes + chain.val * digestBytes + i)) 8 =
      ((signature.layers middle4Layer).chainValues chain).extractLsb' (8 * i) 8 := by
  let before : List Byte :=
    (prefixBytes pk signature).map UInt8.toBitVec ++
      (concatFields (ftsTrees - 1) (ftsOpening signature)).map UInt8.toBitVec ++
      (layerEncoding signature topLayer).map UInt8.toBitVec ++
      (layerEncoding signature middleLayer).map UInt8.toBitVec ++
      (layerEncoding signature middle2Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle3Layer).map UInt8.toBitVec
  let after : List Byte :=
    (layerEncoding signature bottomLayer).map UInt8.toBitVec
  have split : encodeBytes pk signature = before ++
      (layerEncoding signature middle4Layer).map UInt8.toBitVec ++ after := by
    rw [encodeBytes_prefix]
    simp only [before, after, restBytes, List.map_append, List.append_assoc]
  have beforeLength : before.length = middle4Offset := by
    simp only [before, List.length_append, List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature)]
    simp_rw [layerEncoding_length]
    simp [prefixBytes, bytesLE, middle4Offset, bottomOffset,
      middle4Offset, middle3Offset, middle2Offset, middleOffset,
      topOffset, ftsOffset, randomizerOffset, parameterOffset, rootOffset,
      ftsOpeningBytes, ftsTrees, digestBytes, layerBytes,
      numChains, counterBytes, layerHeight, maxLayerHeight]
  exact wire_chain_of_split pk signature middle4Layer middle4Offset
    before after split beforeLength chain i hi

/-- The bottom layer's WOTS values occupy their encoded chain slots. -/
theorem wire_bottomChain (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (chain : ChainIndex)
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (bottomOffset + counterBytes + chain.val * digestBytes + i)) 8 =
      ((signature.layers bottomLayer).chainValues chain).extractLsb' (8 * i) 8 := by
  let before : List Byte :=
    (prefixBytes pk signature).map UInt8.toBitVec ++
      (concatFields (ftsTrees - 1) (ftsOpening signature)).map UInt8.toBitVec ++
      (layerEncoding signature topLayer).map UInt8.toBitVec ++
      (layerEncoding signature middleLayer).map UInt8.toBitVec ++
      (layerEncoding signature middle2Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle3Layer).map UInt8.toBitVec ++
      (layerEncoding signature middle4Layer).map UInt8.toBitVec
  let after : List Byte :=
    []
  have split : encodeBytes pk signature = before ++
      (layerEncoding signature bottomLayer).map UInt8.toBitVec ++ after := by
    rw [encodeBytes_prefix]
    simp only [before, after, restBytes, List.map_append, List.append_assoc,
      List.append_nil]
  have beforeLength : before.length = bottomOffset := by
    simp only [before, List.length_append, List.length_map]
    rw [concatFields_length _ _ _ (ftsOpening_length signature)]
    simp_rw [layerEncoding_length]
    simp [prefixBytes, bytesLE, bottomOffset, bottomOffset,
      middle4Offset, middle3Offset, middle2Offset, middleOffset,
      topOffset, ftsOffset, randomizerOffset, parameterOffset, rootOffset,
      ftsOpeningBytes, ftsTrees, digestBytes, layerBytes,
      numChains, counterBytes, layerHeight, maxLayerHeight]
  exact wire_chain_of_split pk signature bottomLayer bottomOffset
    before after split beforeLength chain i hi


/-- Start of the encoded counter, WOTS values, and path for each layer. -/
def layerOffset (lay : Layer) : Nat :=
  if lay.val = 0 then topOffset
  else if lay.val = 1 then middleOffset
  else if lay.val = 2 then middle2Offset
  else if lay.val = 3 then middle3Offset
  else if lay.val = 4 then middle4Offset
  else bottomOffset

/-- Every XMSS sibling digest in the abstract signature occupies its wire slot. -/
theorem wire_layerPath (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (lay : Layer)
    (level : Fin (layerHeight lay)) (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (layerOffset lay + counterBytes + numChains * digestBytes +
        level.val * digestBytes + i)) 8 =
      ((signature.layers lay).path level).extractLsb' (8 * i) 8 := by
  fin_cases lay
  · simpa [layerOffset, topLayer] using wire_topPath pk signature level i hi
  · simpa [layerOffset, middleLayer] using wire_middlePath pk signature level i hi
  · simpa [layerOffset, middle2Layer] using wire_middle2Path pk signature level i hi
  · simpa [layerOffset, middle3Layer] using wire_middle3Path pk signature level i hi
  · simpa [layerOffset, middle4Layer] using wire_middle4Path pk signature level i hi
  · simpa [layerOffset, bottomLayer, numLayers] using
      wire_bottomPath pk signature level i hi

/-- Every WOTS signature digest in the abstract signature occupies its wire slot. -/
theorem wire_layerChain (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (lay : Layer)
    (chain : ChainIndex) (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb' (8 *
      (layerOffset lay + counterBytes + chain.val * digestBytes + i)) 8 =
      ((signature.layers lay).chainValues chain).extractLsb' (8 * i) 8 := by
  fin_cases lay
  · simpa [layerOffset, topLayer] using wire_topChain pk signature chain i hi
  · simpa [layerOffset, middleLayer] using wire_middleChain pk signature chain i hi
  · simpa [layerOffset, middle2Layer] using wire_middle2Chain pk signature chain i hi
  · simpa [layerOffset, middle3Layer] using wire_middle3Chain pk signature chain i hi
  · simpa [layerOffset, middle4Layer] using wire_middle4Chain pk signature chain i hi
  · simpa [layerOffset, bottomLayer, numLayers] using
      wire_bottomChain pk signature chain i hi

theorem layer_chain_offset_lt (lay : Layer)
    (chain : ChainIndex) (i : Nat) (hi : i < digestBytes) :
    layerOffset lay + counterBytes + chain.val * digestBytes + i <
      SphincsWire.signatureBytes := by
  have inner : counterBytes + chain.val * digestBytes + i <
      layerBytes lay := by
    have hc := chain.isLt
    change chain.val < 52 at hc
    have hi20 : i < 20 := by simpa [digestBytes] using hi
    simp only [layerBytes, counterBytes, numChains, digestBytes]
    omega
  have outer : layerOffset lay + layerBytes lay ≤
      SphincsWire.signatureBytes := by
    fin_cases lay <;> decide
  omega

/-- The verifier loader preserves every WOTS chain byte in an honest witness. -/
theorem loaded_honest_layerChain (publicKey : SigGolf.PublicKey)
    (message : SigGolf.Message) (inner : SphincsSecurity.PublicKey)
    (signature : Signature) (state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, wire inner signature) = some state)
    (lay : Layer) (chain : ChainIndex)
    (i : Nat) (hi : i < digestBytes) :
    state.getByte (BitVec.ofNat 64
      (0x22ca0 + layerOffset lay + counterBytes +
        chain.val * digestBytes + i)) =
      ((signature.layers lay).chainValues chain).extractLsb' (8 * i) 8 := by
  have full := layer_chain_offset_lt lay chain i hi
  have addressEq : 0x22ca0 + layerOffset lay + counterBytes +
      chain.val * digestBytes + i =
      0x22ca0 + (layerOffset lay + counterBytes +
        chain.val * digestBytes + i) := by omega
  rw [addressEq, SphincsVerifierLoader.loaded_witness publicKey message
    (wire inner signature) state loaded _ full]
  exact wire_layerChain inner signature lay chain i hi

theorem layer_path_offset_lt (lay : Layer)
    (level : Fin (layerHeight lay)) (i : Nat) (hi : i < digestBytes) :
    layerOffset lay + counterBytes + numChains * digestBytes +
      level.val * digestBytes + i < SphincsWire.signatureBytes := by
  have inner := layer_path_index_lt lay level i hi
  have outer : layerOffset lay + layerBytes lay ≤
      SphincsWire.signatureBytes := by
    fin_cases lay <;> decide
  omega

/-- All honestly encoded XMSS siblings are present after the verifier loader. -/
theorem loaded_honest_layerPath (publicKey : SigGolf.PublicKey)
    (message : SigGolf.Message) (inner : SphincsSecurity.PublicKey)
    (signature : Signature) (state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, wire inner signature) = some state)
    (lay : Layer) (level : Fin (layerHeight lay))
    (i : Nat) (hi : i < digestBytes) :
    state.getByte (BitVec.ofNat 64
      (0x22ca0 + layerOffset lay + counterBytes + numChains * digestBytes +
        level.val * digestBytes + i)) =
      ((signature.layers lay).path level).extractLsb' (8 * i) 8 := by
  have full := layer_path_offset_lt lay level i hi
  have addressEq : 0x22ca0 + layerOffset lay + counterBytes +
      numChains * digestBytes + level.val * digestBytes + i =
      0x22ca0 + (layerOffset lay + counterBytes + numChains * digestBytes +
        level.val * digestBytes + i) := by omega
  rw [addressEq, SphincsVerifierLoader.loaded_witness publicKey message
    (wire inner signature) state loaded _ full]
  exact wire_layerPath inner signature lay level i hi

/-- Every byte of every FORS opening occupies its declared wire slot. -/
theorem wire_ftsOpeningByte (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (tree : FtsTree) (j : Nat) (hj : j < ftsOpeningBytes) :
    (wire pk signature).extractLsb'
        (8 * (60 + tree.val * ftsOpeningBytes + j)) 8 =
      ((ftsOpening signature tree).map UInt8.toBitVec)[j]'(by
        rw [List.length_map, ftsOpening_length]
        exact hj) := by
  have full : 60 + tree.val * ftsOpeningBytes + j <
      SphincsWire.signatureBytes := by
    rw [SphincsWire.signatureBytes_eq]
    have h := openingPosition_lt tree j hj
    norm_num [ftsTrees, ftsOpeningBytes, ftsTreeHeight, digestBytes] at h ⊢
    omega
  rw [wire_byte pk signature
    (60 + tree.val * ftsOpeningBytes + j) full]
  simp only [encodeBytes_prefix]
  rw [List.getElem_append_right (by
    simp [prefixBytes, bytesLE]
    omega)]
  simp only [List.length_map]
  have plen : (prefixBytes pk signature).length = 60 := by
    simp [prefixBytes, bytesLE]
  simp only [plen]
  have indexEq : 60 + tree.val * ftsOpeningBytes + j - 60 =
      tree.val * ftsOpeningBytes + j := by omega
  simp only [indexEq]
  exact restBytes_opening_byte signature tree j hj

/-- Every FORS opening's secret occupies its declared wire slot. -/
theorem wire_ftsSecret (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (tree : FtsTree) (i : Nat) (hi : i < 20) :
    (wire pk signature).extractLsb'
        (8 * (60 + tree.val * ftsOpeningBytes + i)) 8 =
      (signature.ftsSecret tree).extractLsb' (8 * i) 8 := by
  have bound : i < ftsOpeningBytes := by
    norm_num [ftsOpeningBytes, ftsTreeHeight, digestBytes]
    omega
  exact (wire_ftsOpeningByte pk signature tree i bound).trans
    (ftsOpening_secretByte signature tree i hi)

/-- Authentication-path nodes follow the secret in each FORS opening. -/
theorem wire_ftsPath (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (tree : FtsTree) (level : Fin ftsTreeHeight)
    (i : Nat) (hi : i < digestBytes) :
    (wire pk signature).extractLsb'
        (8 * (60 + tree.val * ftsOpeningBytes +
          (digestBytes + level.val * digestBytes + i))) 8 =
      (signature.ftsPath tree level).extractLsb' (8 * i) 8 := by
  have bound : digestBytes + level.val * digestBytes + i <
      ftsOpeningBytes := by
    have h := level.isLt
    norm_num [ftsTreeHeight, ftsOpeningBytes, digestBytes] at *
    omega
  exact (wire_ftsOpeningByte pk signature tree
    (digestBytes + level.val * digestBytes + i) bound).trans
      (ftsOpening_pathByte signature tree level i hi)

/-- The first FORS opening is the first secret of the abstract signature. -/
theorem wire_firstFtsSecret (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (i : Nat) (hi : i < 20) :
    (wire pk signature).extractLsb' (8 * (60 + i)) 8 =
      (signature.ftsSecret ⟨0, by decide⟩).extractLsb' (8 * i) 8 := by
  simpa using wire_ftsSecret pk signature ⟨0, by decide⟩ i hi

theorem loaded_honest_ftsSecret (publicKey : SigGolf.PublicKey)
    (message : SigGolf.Message) (inner : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, wire inner signature) = some state)
    (tree : FtsTree) (i : Nat) (hi : i < 20) :
    state.getByte (BitVec.ofNat 64
      (0x22ca0 + (60 + tree.val * ftsOpeningBytes + i))) =
      (signature.ftsSecret tree).extractLsb' (8 * i) 8 := by
  have bound : 60 + tree.val * ftsOpeningBytes + i <
      SphincsWire.signatureBytes := by
    rw [SphincsWire.signatureBytes_eq]
    have fieldBound : i < ftsOpeningBytes := by
      norm_num [ftsOpeningBytes, ftsTreeHeight, digestBytes]
      omega
    have h := openingPosition_lt tree i fieldBound
    norm_num [ftsTrees, ftsOpeningBytes, ftsTreeHeight, digestBytes] at h ⊢
    omega
  rw [SphincsVerifierLoader.loaded_witness publicKey message
    (wire inner signature) state loaded
    (60 + tree.val * ftsOpeningBytes + i) bound]
  exact wire_ftsSecret inner signature tree i hi

theorem loaded_honest_ftsPath (publicKey : SigGolf.PublicKey)
    (message : SigGolf.Message) (inner : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, wire inner signature) = some state)
    (tree : FtsTree) (level : Fin ftsTreeHeight)
    (i : Nat) (hi : i < digestBytes) :
    state.getByte (BitVec.ofNat 64
      (0x22ca0 + (60 + tree.val * ftsOpeningBytes +
        (digestBytes + level.val * digestBytes + i)))) =
      (signature.ftsPath tree level).extractLsb' (8 * i) 8 := by
  have fieldBound : digestBytes + level.val * digestBytes + i <
      ftsOpeningBytes := by
    have h := level.isLt
    norm_num [ftsTreeHeight, ftsOpeningBytes, digestBytes] at *
    omega
  have bound : 60 + tree.val * ftsOpeningBytes +
      (digestBytes + level.val * digestBytes + i) <
      SphincsWire.signatureBytes := by
    rw [SphincsWire.signatureBytes_eq]
    have h := openingPosition_lt tree
      (digestBytes + level.val * digestBytes + i) fieldBound
    norm_num [ftsTrees, ftsOpeningBytes, ftsTreeHeight, digestBytes] at h ⊢
    omega
  rw [SphincsVerifierLoader.loaded_witness publicKey message
    (wire inner signature) state loaded
    (60 + tree.val * ftsOpeningBytes +
      (digestBytes + level.val * digestBytes + i)) bound]
  exact wire_ftsPath inner signature tree level i hi

theorem loaded_honest_firstFtsSecret (publicKey : SigGolf.PublicKey)
    (message : SigGolf.Message) (inner : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, wire inner signature) = some state)
    (i : Nat) (hi : i < 20) :
    state.getByte (BitVec.ofNat 64 (0x22ca0 + (60 + i))) =
      (signature.ftsSecret ⟨0, by decide⟩).extractLsb' (8 * i) 8 := by
  simpa using loaded_honest_ftsSecret publicKey message inner signature
    state loaded ⟨0, by decide⟩ i hi

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

/-- info: 'SigGolfCandidate.SphincsWireEncoding.wire_firstFtsSecret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wire_firstFtsSecret

/-- info: 'SigGolfCandidate.SphincsWireEncoding.wire_ftsPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wire_ftsPath

/-- info: 'SigGolfCandidate.SphincsWireEncoding.loaded_honest_ftsSecret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_ftsSecret

/-- info: 'SigGolfCandidate.SphincsWireEncoding.loaded_honest_ftsPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_ftsPath

/-- info: 'SigGolfCandidate.SphincsWireEncoding.loaded_honest_firstFtsSecret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_firstFtsSecret

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

/-- info: 'SigGolfCandidate.SphincsWireEncoding.layerEncoding_pathByte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms layerEncoding_pathByte

/-- info: 'SigGolfCandidate.SphincsWireEncoding.layerEncoding_chainByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms layerEncoding_chainByte

/-- info: 'SigGolfCandidate.SphincsWireEncoding.wire_topPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wire_topPath

/-- info: 'SigGolfCandidate.SphincsWireEncoding.loaded_honest_topPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_topPath

/-- info: 'SigGolfCandidate.SphincsWireEncoding.wire_layerPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wire_layerPath

/-- info: 'SigGolfCandidate.SphincsWireEncoding.wire_layerChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wire_layerChain

/-- info: 'SigGolfCandidate.SphincsWireEncoding.loaded_honest_layerChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_honest_layerChain

/-- info: 'SigGolfCandidate.SphincsWireEncoding.loaded_honest_layerPath' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_layerPath

end SigGolfCandidate.SphincsWireEncoding
