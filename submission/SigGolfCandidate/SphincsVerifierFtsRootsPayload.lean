import SigGolfCandidate.SphincsVerifierFtsLeafQueryTree

namespace SigGolfCandidate.SphincsVerifierFtsRootsPayload
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsLeafQueryTree
open SigGolfCandidate.SphincsVerifierFtsForestRoots
open SigGolfCandidate.SphincsVerifierFtsTreeWitnessStep
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- The 480-byte FORS root payload is the roots in tree order, little-endian
    within each 20-byte digest. -/
theorem rootsPayload_flat (roots : FtsTree → Digest) :
    SphincsSecurity.Concrete.ftsRootsPayload roots =
      List.ofFn (fun byte : Fin (24 * 20) =>
        UInt8.ofBitVec ((roots ⟨byte.val / 20, by
          have h := byte.isLt
          change byte.val / 20 < 24
          omega⟩).extractLsb' (8 * (byte.val % 20)) 8)) := by
  let f : Fin (24 * 20) → UInt8 := fun byte =>
    UInt8.ofBitVec ((roots ⟨byte.val / 20, by
      have h := byte.isLt
      change byte.val / 20 < 24
      omega⟩).extractLsb' (8 * (byte.val % 20)) 8)
  have split := List.ofFn_mul f
  rw [split]
  unfold SphincsSecurity.Concrete.ftsRootsPayload
  change (List.ofFn roots).flatMap (bytesLE 20) = _
  simp only [List.flatMap]
  congr 1

theorem rootsPayload_byte (roots : FtsTree → Digest)
    (tree : FtsTree) (i : Nat) (hi : i < 20) :
    ((SphincsSecurity.Concrete.ftsRootsPayload roots).map UInt8.toBitVec)[20 * tree.val + i]'(by
        rw [rootsPayload_flat, List.length_map, List.length_ofFn]
        have h := tree.isLt
        change tree.val < 24 at h
        omega) =
      (roots tree).extractLsb' (8 * i) 8 := by
  simp only [rootsPayload_flat]
  simp only [List.map_ofFn, List.getElem_ofFn, UInt8.toBitVec_ofBitVec]
  have treeEq : (20 * tree.val + i) / 20 = tree.val := by omega
  have byteEq : (20 * tree.val + i) % 20 = i := by omega
  simp [Function.comp_def, treeEq, byteEq, ftsTrees]
  congr 1

/-- The machine's final root slots encode exactly the abstract 480-byte
    scheme payload, before the forest-compression HASH call. -/
theorem forestEnd_payload_bytes (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩)
    (initialQuery : hashInput initial =
      toQuery (leafInput pk ⟨0, by decide⟩ index
        (leaves ⟨0, by decide⟩)
        (signature.ftsSecret ⟨0, by decide⟩)))
    (tree : FtsTree) (i : Nat) (hi : i < 20) :
    (forestEndState hash initial signature pk index leaves).getByte
      (BitVec.ofNat 64 (0x44100 + 20 * tree.val + i)) =
        ((SphincsSecurity.Concrete.ftsRootsPayload
          (schemeTreeValue hash signature pk index leaves)).map
            UInt8.toBitVec)[20 * tree.val + i]'(by
              rw [rootsPayload_flat, List.length_map, List.length_ofFn]
              have h := tree.isLt
              change tree.val < 24 at h
              omega) := by
  rw [forestEnd_scheme_roots hash initial signature pk index leaves
    initialInv initialQuery tree i hi]
  exact (rootsPayload_byte _ tree i hi).symm

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootsPayload.forestEnd_payload_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestEnd_payload_bytes

def forestInput (pk : SphincsSecurity.PublicKey) (index : Index)
    (roots : FtsTree → Digest) : HashInput :=
  tweakableHashInput pk.parameter (.ftsRoots index)
    (SphincsSecurity.Concrete.ftsRootsPayload roots)

theorem forestInput_eq (pk : SphincsSecurity.PublicKey) (index : Index)
    (roots : FtsTree → Digest) :
    forestInput pk index roots =
      fieldBytes (tweakFields 11 0 index.val 0 0) ++
        bytesLE 20 pk.parameter ++
          SphincsSecurity.Concrete.ftsRootsPayload roots := rfl

theorem forestInput_length (pk : SphincsSecurity.PublicKey) (index : Index)
    (roots : FtsTree → Digest) :
    (forestInput pk index roots).length = 520 := by
  have headerLength :
      (fieldBytes (tweakFields 11 0 index.val 0 0)).length = 20 := by
    change (tweakBytes (.ftsRoots index)).length = 20
    exact tweakBytes_length _
  have payloadLength :
      (SphincsSecurity.Concrete.ftsRootsPayload roots).length = 480 := by
    rw [rootsPayload_flat]
    rfl
  rw [forestInput_eq, List.length_append, List.length_append,
    headerLength, payloadLength]
  simp only [bytesLE, List.length_ofFn]

/-- The exact post-FORS HASH query follows from the 20-byte tweak, 20-byte
    public parameter, and 480 serialized forest-root bytes in the VM buffer. -/
theorem forestHash_query (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (roots : FtsTree → Digest)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 4160)
    (bytes : ∀ i, (hi : i < 520) →
      state.getByte (BitVec.ofNat 64 (0x40000 + i)) =
        ((forestInput pk index roots).map UInt8.toBitVec)[i]'(by
          rw [List.length_map, forestInput_length]; exact hi)) :
    hashInput state = toQuery (forestInput pk index roots) := by
  apply Serialization.hashInput_of_list state 0x40000
    ((forestInput pk index roots).map UInt8.toBitVec)
  · exact source
  · rw [bits, List.length_map, forestInput_length]
    rfl
  · intro i hi
    have hi520 : i < 520 := by
      simpa only [List.length_map, forestInput_length] using hi
    exact bytes i hi520

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootsPayload.forestHash_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestHash_query

end SigGolfCandidate.SphincsVerifierFtsRootsPayload
