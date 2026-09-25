import SigGolfCandidate.SphincsVerifierFtsGenericPosition

/-! The FORS parent query at the first level, with a variable witness pointer. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericFirstQuery
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsParentQuery
open SigGolfCandidate.SphincsVerifierFtsParentWitness
open SigGolfCandidate.SphincsVerifierFtsParentFirstQuery
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
open SigGolfCandidate.SphincsVerifierFtsGenericPosition
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384

theorem positioned_children_encoded_generic (start : MachineState)
    (pointer : Word) (current sibling : Digest)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0)
    (currentEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        current.extractLsb' (8 * i) 8)
    (siblingEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (pointer.toNat + i)) =
        sibling.extractLsb' (8 * i) 8)
    (i : Nat) (hi : i < 20) :
    let positioned := firstPositionedState start
    let zero := (parityState start).getReg .x6 = 0
    positioned.getByte (BitVec.ofNat 64 (0x40028 + i)) =
      (if zero then current else sibling).extractLsb' (8 * i) 8 ∧
    positioned.getByte (BitVec.ofNat 64 (0x4003c + i)) =
      (if zero then sibling else current).extractLsb' (8 * i) 8 := by
  have pair := positioned_pair_bytes_generic start pointer pc pointerValue
    small aligned i hi
  by_cases zero : (parityState start).getReg .x6 = 0
  · simp only [zero, if_true] at pair ⊢
    exact ⟨pair.1.trans (currentEncoded i hi),
      pair.2.trans (siblingEncoded i hi)⟩
  · simp only [zero, if_false] at pair ⊢
    exact ⟨pair.1.trans (siblingEncoded i hi),
      pair.2.trans (currentEncoded i hi)⟩

theorem firstParent_hashInput_generic_pointer (start : MachineState)
    (pointer : Word)
    (pk : SphincsSecurity.PublicKey) (index : Index) (nodeIdx : FtsLeaf)
    (current sibling : Digest)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0)
    (level : start.getMem 0x43048 = 1)
    (layerZero : start.getMem 0x43000 = 0)
    (treeIndex : start.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (nodeIndex : start.getMem 0x43070 >>> 1 = BitVec.ofNat 64 nodeIdx.val)
    (witnessPrefix : WitnessPrefix start pk)
    (currentEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        current.extractLsb' (8 * i) 8)
    (siblingEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (pointer.toNat + i)) =
        sibling.extractLsb' (8 * i) 8) :
    let zero := (parityState start).getReg .x6 = 0
    hashInput (firstParentReadyState start) =
      toQuery (firstParentInput pk index nodeIdx
        (if zero then current else sibling)
        (if zero then sibling else current)) := by
  let positioned := firstPositionedState start
  have admissible :
      SigGolfCandidate.SphincsVerifierFtsGenericPairTrace.PathPointerAdmissible
        pointer := ⟨aligned, by unfold MEMORY_BYTES; omega⟩
  have front := positioned_trace_generic start pointer pc pointerValue admissible
  have layerAtPosition : positioned.getMem 0x43000 = 0 := by
    rw [positioned_scratch_frame start 0x43000 (Or.inl rfl)]
    exact layerZero
  have treeAtPosition : positioned.getMem 0x43008 =
      BitVec.ofNat 64 index.val := by
    rw [positioned_scratch_frame start 0x43008 (Or.inr rfl)]
    exact treeIndex
  have positionAtPosition : positioned.getMem 0x43010 = 1 :=
    front.2.2.2.1.trans level
  have indexAtPosition : positioned.getMem 0x43018 =
      BitVec.ofNat 64 nodeIdx.val :=
    front.2.2.2.2.2.trans nodeIndex
  have children := positioned_children_encoded_generic start pointer
    current sibling pc pointerValue small aligned currentEncoded siblingEncoded
  exact readyParent_hashInput positioned pk index nodeIdx
    (if (parityState start).getReg .x6 = 0 then current else sibling)
    (if (parityState start).getReg .x6 = 0 then sibling else current)
    layerAtPosition positionAtPosition treeAtPosition indexAtPosition
    (positioned_WitnessPrefix start pk witnessPrefix)
    (fun i hi => (children i hi).1)
    (fun i hi => (children i hi).2)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericFirstQuery.firstParent_hashInput_generic_pointer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstParent_hashInput_generic_pointer

end SigGolfCandidate.SphincsVerifierFtsGenericFirstQuery
