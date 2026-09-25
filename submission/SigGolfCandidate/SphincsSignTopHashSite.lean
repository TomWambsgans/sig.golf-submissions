import SigGolfCandidate.SphincsActualCachePathBridge
import SigGolfCandidate.SphincsVerifierMessageCopy
import SigGolfCandidate.Hypertree.KeygenTrace

/-! The exact sign-image HASH site for each of the eleven top-tree nodes.
The surrounding code must still establish the register and buffer premises. -/

namespace SigGolfCandidate.SphincsSignTopHashSite
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsActualCachePathBridge
open SigGolfCandidate.SphincsVerifierMessageCopy

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem topNodeInput_length (parameter : PublicParameter) (leaf : LeafIndex)
    (level : Nat) (pair : Digest × Digest) :
    (topNodeInput parameter leaf level pair).length = 80 := by
  simp [topNodeInput, tweakableHashInput, tweakBytes,
    hashDomainFields, fieldBytes, SphincsSecurity.Concrete.nodePayload,
    bytesLE]

theorem sign_top_hash_fetch (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 42604)) :
    fetch SphincsImages.sign state = some (.base .ECALL) := by
  rw [fetch_index SphincsImages.sign state (42604 / 4) (by decide)
    (by simpa using pc)]
  decide

theorem sign_top_hash_input (state : MachineState)
    (parameter : PublicParameter) (leaf : LeafIndex)
    (level : Nat) (pair : Digest × Digest)
    (source : state.getReg .x10 = 0x40000)
    (bits : (state.getReg .x11).toNat = 640)
    (payload : ∀ i, (hi : i < 80) →
      state.getByte (BitVec.ofNat 64 (0x40000 + i)) =
        ((topNodeInput parameter leaf level pair).map UInt8.toBitVec)[i]'(by
          rw [List.length_map, topNodeInput_length]; exact hi)) :
    hashInput state = toQuery (topNodeInput parameter leaf level pair) := by
  unfold toQuery
  apply Serialization.hashInput_of_list state 0x40000
  · exact source
  · rw [List.length_map, topNodeInput_length]
    exact bits
  · intro i hi
    exact payload i (by
      simpa [topNodeInput_length] using hi)

theorem sign_top_hash_valid (state : MachineState)
    (source : state.getReg .x10 = 0x40000)
    (bits : (state.getReg .x11).toNat = 640)
    (destination : state.getReg .x12 = 0x42000) :
    hashArgumentsValid state = true := by
  simp [hashArgumentsValid, source, bits, destination,
    rangeValid, accessValid, MEMORY_BYTES]

theorem sign_top_hash_compressions (parameter : PublicParameter)
    (leaf : LeafIndex) (level : Nat) (pair : Digest × Digest) :
    compressions (toQuery (topNodeInput parameter leaf level pair)).1 = 2 := by
  simp [toQuery, Hypertree.Reference.packed,
    topNodeInput_length, compressions]

theorem sign_top_hash_step (hash : Hash) (state : MachineState)
    (parameter : PublicParameter) (leaf : LeafIndex)
    (level : Nat) (pair : Digest × Digest)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 42604))
    (service : state.getReg .x5 = 1)
    (source : state.getReg .x10 = 0x40000)
    (bits : (state.getReg .x11).toNat = 640)
    (destination : state.getReg .x12 = 0x42000)
    (payload : ∀ i, (hi : i < 80) →
      state.getByte (BitVec.ofNat 64 (0x40000 + i)) =
        ((topNodeInput parameter leaf level pair).map UInt8.toBitVec)[i]'(by
          rw [List.length_map, topNodeInput_length]; exact hi)) :
    Trace hash SphincsImages.sign state 1 16 1 2
      (writeHash state (hash (toQuery (topNodeInput parameter leaf level pair)))) := by
  have query := sign_top_hash_input state parameter leaf level pair source bits payload
  have valid := sign_top_hash_valid state source bits destination
  have fetch := sign_top_hash_fetch state pc
  have trace := Trace.hash (hash := hash) state
    (writeHash state (hash (hashInput state))) 0 0 0 0 fetch service valid
    (Trace.refl _)
  rw [query] at trace
  simpa only [sign_top_hash_compressions, Nat.zero_add] using trace

/-- info: 'SigGolfCandidate.SphincsSignTopHashSite.sign_top_hash_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_top_hash_step

end SigGolfCandidate.SphincsSignTopHashSite
