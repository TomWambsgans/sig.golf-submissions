import SigGolfCandidate.SphincsVerifierWotsSemanticAllChains
import SigGolfCandidate.SphincsWireEncoding
import SigGolfCandidate.SphincsVerifierWotsRootCopy

namespace SigGolfCandidate.SphincsVerifierWotsSemanticLeaf
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierWotsRootCopy
open SigGolfCandidate.SphincsVerifierWotsSemanticAllChains
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierWotsSemanticAllChains
set_option maxRecDepth 16384
set_option maxHeartbeats 0

private theorem leafPayload_concat (values : ChainIndex → Digest) :
    Concrete.leafPayload values =
      SphincsWire.concatFields numChains (fun chain => bytesLE 20 (values chain)) := by
  rfl

theorem leafPayload_byte (values : ChainIndex → Digest)
    (chain : ChainIndex) (i : Nat) (hi : i < 20) :
    ((Concrete.leafPayload values).map UInt8.toBitVec)[chain.val * 20 + i]'(by
      rw [leafPayload_concat]
      simp [SphincsWire.concatFields_length, bytesLE, numChains]
      have hc := chain.isLt
      simp [numChains] at hc
      omega) =
      (values chain).extractLsb' (8 * i) 8 := by
  simp only [leafPayload_concat, List.getElem_map]
  have hlen : ∀ chain : ChainIndex,
      (bytesLE 20 (values chain)).length = 20 := by
    intro chain
    simp [bytesLE]
  have atChain := SphincsWireEncoding.concatFields_byte
    (fun chain : ChainIndex => bytesLE 20 (values chain)) hlen chain i hi
  rw [atChain]
  simp only [bytesLE, List.getElem_ofFn, UInt8.toBitVec_ofBitVec]
  rfl

theorem leafPayload_length (values : ChainIndex → Digest) :
    (Concrete.leafPayload values).length = 1040 := by
  rw [leafPayload_concat]
  have hlen : ∀ chain : ChainIndex,
      (bytesLE 20 (values chain)).length = 20 := by
    intro chain
    simp [bytesLE]
  rw [SphincsWire.concatFields_length numChains
    (fun chain => bytesLE 20 (values chain)) 20 hlen]
  decide

/-- Copying all 52 recovered endpoints fills the exact abstract leaf payload. -/
theorem rootCopy_payload (state : MachineState)
    (pc : state.pc = 0x298c)
    (values : ChainIndex → Digest)
    (endpoints : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      state.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8) :
    ∃ final,
      OrdinarySteps SphincsImages.verify state 789 final ∧
      final.pc = 0x29c8 ∧
      (∀ i, (hi : i < 1040) →
        final.getByte (BitVec.ofNat 64 (0x40028 + i)) =
          ((Concrete.leafPayload values).map UInt8.toBitVec)[i]'(by
            rw [List.length_map, leafPayload_length]
            exact hi)) := by
  obtain ⟨final, trace, finalPc, copied⟩ :=
    rootCopy_setup_and_bytes state pc
  refine ⟨final, trace, finalPc, ?_⟩
  intro i hi
  let chain : ChainIndex := ⟨i / 20, by
    simp [numChains]
    omega⟩
  let j := i % 20
  have hj : j < 20 := Nat.mod_lt _ (by decide)
  have split : 20 * chain.val + j = i := by
    dsimp [chain, j]
    omega
  have index : chain.val * 20 + j = i := by omega
  have moved := copied i hi
  have source : state.getByte (BitVec.ofNat 64 (0x44300 + i)) =
      (values chain).extractLsb' (8 * j) 8 := by
    rw [← split]
    simpa only [Nat.add_assoc] using endpoints chain j hj
  have abstract := leafPayload_byte values chain j hj
  simpa only [index] using moved.trans (source.trans abstract.symm)

#print axioms leafPayload_byte
#print axioms rootCopy_payload


end SigGolfCandidate.SphincsVerifierWotsSemanticLeaf
