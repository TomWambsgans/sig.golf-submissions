import SigGolfCandidate.SphincsVerifierFtsGenericQuery

/-! The full parent HASH input from a generic FORS path-step state. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericParent
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsParentWitness
open SigGolfCandidate.SphincsVerifierFtsParentFirstQuery
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
open SigGolfCandidate.SphincsVerifierFtsGenericPosition
open SigGolfCandidate.SphincsVerifierFtsGenericQuery
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384

theorem parent_hashInput_generic (start : MachineState)
    (pointer : Word)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (level : Nat)
    (current sibling : Digest)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0)
    (levelValue : start.getMem 0x43048 = BitVec.ofNat 64 level)
    (layerZero : start.getMem 0x43000 = 0)
    (treeIndex : start.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (nodeIndex : start.getMem 0x43070 >>> 1 =
      BitVec.ofNat 64 nodeIdx.val)
    (witnessPrefix : WitnessPrefix start pk)
    (currentEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        current.extractLsb' (8 * i) 8)
    (siblingEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (pointer.toNat + i)) =
        sibling.extractLsb' (8 * i) 8) :
    let zero := (parityState start).getReg .x6 = 0
    hashInput (firstParentReadyState start) =
      toQuery (parentInput pk index nodeIdx level
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
  have positionAtPosition : positioned.getMem 0x43010 =
      BitVec.ofNat 64 level := front.2.2.2.1.trans levelValue
  have indexAtPosition : positioned.getMem 0x43018 =
      BitVec.ofNat 64 nodeIdx.val :=
    front.2.2.2.2.2.trans nodeIndex
  have children :=
    SigGolfCandidate.SphincsVerifierFtsGenericFirstQuery.positioned_children_encoded_generic
      start pointer current sibling pc pointerValue small aligned
        currentEncoded siblingEncoded
  exact readyParent_hashInput_generic positioned pk index nodeIdx level
    (if (parityState start).getReg .x6 = 0 then current else sibling)
    (if (parityState start).getReg .x6 = 0 then sibling else current)
    layerAtPosition positionAtPosition treeAtPosition indexAtPosition
    (positioned_WitnessPrefix start pk witnessPrefix)
    (fun i hi => (children i hi).1)
    (fun i hi => (children i hi).2)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericParent.parent_hashInput_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parent_hashInput_generic

end SigGolfCandidate.SphincsVerifierFtsGenericParent
