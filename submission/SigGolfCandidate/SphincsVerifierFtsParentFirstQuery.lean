import SigGolfCandidate.SphincsVerifierFtsParentChildren

/-! The first FORS parent query follows from the earlier running root and path bytes. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentFirstQuery
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsParentQuery
open SigGolfCandidate.SphincsVerifierFtsParentWitness
open SigGolfCandidate.SphincsVerifierFtsParentChildren
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384

theorem positioned_scratch_frame (start : MachineState) (address : Word)
    (supported : address = 0x43000 ∨ address = 0x43008) :
    (firstPositionedState start).getMem address =
      start.getMem address := by
  let pair := pairState start
  let advanced := advancePointerState pair
  let shifted := shiftIndexState advanced
  have frame : pair.getMem address = start.getMem address := by
    apply pair_scratch_frame
    · intro offset
      rcases supported with h | h <;> subst address <;>
        fin_cases offset <;> decide
    · intro offset
      rcases supported with h | h <;> subst address <;>
        fin_cases offset <;> decide
  change (levelPositionState shifted).getMem address = _
  rw [levelPosition_mem_frame shifted address (by rcases supported with h | h <;> subst address <;> decide),
    shiftIndex_mem_frame advanced address
      (by rcases supported with h | h <;> subst address <;> decide)
      (by rcases supported with h | h <;> subst address <;> decide),
    advancePointer_mem_frame pair address
      (by rcases supported with h | h <;> subst address <;> decide),
    frame]

theorem firstParent_hashInput (start : MachineState)
    (pk : SphincsSecurity.PublicKey) (index : Index) (nodeIdx : FtsLeaf)
    (current sibling : Digest)
    (pc : start.pc = 0x1914)
    (pointer : start.getMem 0x43028 = 0x22cf0)
    (level : start.getMem 0x43048 = 1)
    (layerZero : start.getMem 0x43000 = 0)
    (treeIndex : start.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (nodeIndex : start.getMem 0x43070 >>> 1 = BitVec.ofNat 64 nodeIdx.val)
    (witnessPrefix : WitnessPrefix start pk)
    (currentEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        current.extractLsb' (8 * i) 8)
    (siblingEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (0x22cf0 + i)) =
        sibling.extractLsb' (8 * i) 8) :
    let zero := (parityState start).getReg .x6 = 0
    hashInput (firstParentReadyState start) =
      toQuery (firstParentInput pk index nodeIdx
        (if zero then current else sibling)
        (if zero then sibling else current)) := by
  let positioned := firstPositionedState start
  have front := firstLevelPosition start pc pointer level
  have layerAtPosition : positioned.getMem 0x43000 = 0 := by
    rw [positioned_scratch_frame start 0x43000 (Or.inl rfl)]
    exact layerZero
  have treeAtPosition : positioned.getMem 0x43008 =
      BitVec.ofNat 64 index.val := by
    rw [positioned_scratch_frame start 0x43008 (Or.inr rfl)]
    exact treeIndex
  have positionAtPosition : positioned.getMem 0x43010 = 1 :=
    front.2.2.2.1
  have indexAtPosition : positioned.getMem 0x43018 =
      BitVec.ofNat 64 nodeIdx.val := by
    have shiftedIndex : positioned.getMem 0x43018 =
        start.getMem 0x43070 >>> 1 := front.2.2.2.2.2
    exact shiftedIndex.trans nodeIndex
  have children := positioned_children_encoded start current sibling pc pointer
    currentEncoded siblingEncoded
  exact readyParent_hashInput positioned pk index nodeIdx
    (if (parityState start).getReg .x6 = 0 then current else sibling)
    (if (parityState start).getReg .x6 = 0 then sibling else current)
    layerAtPosition positionAtPosition treeAtPosition indexAtPosition
    (positioned_WitnessPrefix start pk witnessPrefix)
    (fun i hi => (children i hi).1)
    (fun i hi => (children i hi).2)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentFirstQuery.firstParent_hashInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstParent_hashInput

end SigGolfCandidate.SphincsVerifierFtsParentFirstQuery
