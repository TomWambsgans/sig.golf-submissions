import SigGolfCandidate.SphincsVerifierWotsLeafHashReady
import SigGolfCandidate.SphincsBridge

namespace SigGolfCandidate.SphincsVerifierWotsLeafQuery
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierWotsSemanticLeaf
open SigGolfCandidate.SphincsVerifierWotsLeafHashReady
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def leafInput (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (endpoints : ChainIndex → Digest) : HashInput :=
  tweakableHashInput parameter (.leaf lay tree leaf) (Concrete.leafPayload endpoints)

theorem leafInput_length (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (endpoints : ChainIndex → Digest) :
    (leafInput parameter lay tree leaf endpoints).length = 1080 := by
  simp [leafInput, tweakableHashInput, tweakBytes, fieldBytes,
    bytesLE, leafPayload_length]

theorem leafInput_payload_byte (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (endpoints : ChainIndex → Digest)
    (i : Nat) (hi : i < 1040) :
    ((leafInput parameter lay tree leaf endpoints).map UInt8.toBitVec)[40 + i]'(by
      rw [List.length_map, leafInput_length]; omega) =
      ((Concrete.leafPayload endpoints).map UInt8.toBitVec)[i]'(by
        rw [List.length_map, leafPayload_length]; exact hi) := by
  simp only [leafInput, tweakableHashInput, List.map_append]
  rw [List.getElem_append_right (by simp [tweakBytes, fieldBytes, bytesLE])]
  simp [tweakBytes, fieldBytes, bytesLE]

theorem readyLeaf_hashInput (state : MachineState)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (endpoints : ChainIndex → Digest)
    (header : ∀ i, (hi : i < 40) →
      (leafHashReadyState state).getByte (BitVec.ofNat 64 (0x40000 + i)) =
        ((leafInput parameter lay tree leaf endpoints).map UInt8.toBitVec)[i]'(by
          rw [List.length_map, leafInput_length]; omega))
    (payload : ∀ i, (hi : i < 1040) →
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        ((Concrete.leafPayload endpoints).map UInt8.toBitVec)[i]'(by
          rw [List.length_map, leafPayload_length]; exact hi)) :
    hashInput (leafHashReadyState state) =
      toQuery (leafInput parameter lay tree leaf endpoints) := by
  apply Serialization.hashInput_of_list (leafHashReadyState state) 0x40000
    ((leafInput parameter lay tree leaf endpoints).map UInt8.toBitVec)
  · exact (leafHashReady_regs state).1
  · rw [(leafHashReady_regs state).2.1, List.length_map, leafInput_length]
    rfl
  · intro i hi
    have hi' : i < 1080 := by
      simpa [leafInput_length] using hi
    by_cases hhead : i < 40
    · exact header i hhead
    · have hp : i - 40 < 1040 := by omega
      have frame := leafHashReady_payload_byte_frame state (i - 40) hp
      have source := payload (i - 40) hp
      have expected := leafInput_payload_byte parameter lay tree leaf endpoints
        (i - 40) hp
      have shift : 40 + (i - 40) = i := by omega
      have address : 0x40028 + (i - 40) = 0x40000 + i := by omega
      simpa only [shift, address] using (frame.trans source).trans expected.symm

/-- info: 'SigGolfCandidate.SphincsVerifierWotsLeafQuery.readyLeaf_hashInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms readyLeaf_hashInput

end SigGolfCandidate.SphincsVerifierWotsLeafQuery
