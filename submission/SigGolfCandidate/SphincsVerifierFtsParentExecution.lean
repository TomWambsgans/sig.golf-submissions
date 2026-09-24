import SigGolfCandidate.SphincsVerifierFtsParentQuery

/-! Compose the first FORS parent-pair branch with its exact HASH call. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierFtsParentQuery
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierHashBytes
set_option maxRecDepth 16384

def firstPositionedState (start : MachineState) : MachineState :=
  levelPositionState
    (shiftIndexState (advancePointerState (pairState start)))

def firstParentReadyState (start : MachineState) : MachineState :=
  parentHashReadyState (firstPositionedState start)

theorem firstParentReady_trace (start : MachineState)
    (pc : start.pc = 0x1914)
    (pointer : start.getMem 0x43028 = 0x22cf0)
    (level : start.getMem 0x43048 = 1) :
    OrdinarySteps SphincsImages.verify (pairState start) 65
      (firstParentReadyState start) ∧
      (firstParentReadyState start).pc = 0x1b18 := by
  have front := firstLevelPosition start pc pointer level
  have back := parentHashReady_block (firstPositionedState start) front.2.1
  exact ⟨front.1.append back.1, back.2.1⟩

theorem firstParentReady_hashStep (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (nodeIdx : FtsLeaf) (left right : Digest)
    (pc : state.pc = 0x1a70)
    (layerZero : state.getMem 0x43000 = 0)
    (positionOne : state.getMem 0x43010 = 1)
    (treeIndex : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (nodeIndex : state.getMem 0x43018 = BitVec.ofNat 64 nodeIdx.val)
    (parameterEncoded : WitnessPrefix state pk)
    (leftEncoded : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        left.extractLsb' (8 * i) 8)
    (rightEncoded : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x4003c + i)) =
        right.extractLsb' (8 * i) 8)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash (parentHashReadyState state)
        (hash (toQuery (firstParentInput pk index nodeIdx left right))))
      steps result) :
    Executes hash SphincsImages.verify (parentHashReadyState state)
      (steps + 1) (result.charge 16 1 2) := by
  have ready := parentHashReady_block state pc
  have regs := hashRegisters_ready (parentReadyState state)
  have query := readyParent_hashInput state pk index nodeIdx left right
    layerZero positionOne treeIndex nodeIndex parameterEncoded
    leftEncoded rightEncoded
  have tail' : Executes hash SphincsImages.verify
      (writeHash (parentHashReadyState state)
        (hash (hashInput (parentHashReadyState state)))) steps result := by
    rw [query]
    exact tail
  exact SphincsVerifierFtsParentHash.hash_step hash
    (parentHashReadyState state) ready.2.1 regs.1 regs.2.1
    regs.2.2.1 regs.2.2.2 steps result tail'

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentExecution.firstParentReady_hashStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstParentReady_hashStep

end SigGolfCandidate.SphincsVerifierFtsParentExecution
