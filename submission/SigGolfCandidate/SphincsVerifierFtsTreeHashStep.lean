import SigGolfCandidate.SphincsVerifierFtsTreeParent

/-! One parent HASH instruction at a variable FORS level. -/

namespace SigGolfCandidate.SphincsVerifierFtsTreeHashStep
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierFtsTreeQuery
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierHashBytes
set_option maxRecDepth 16384

theorem parentReady_hashStep_tree (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (tree : FtsTree) (index : Index)
    (nodeIdx : FtsLeaf) (level : Nat) (left right : Digest)
    (pc : state.pc = 0x1a70)
    (treeValue : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (positionValue : state.getMem 0x43010 = BitVec.ofNat 64 level)
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
        (hash (toQuery (parentInputTree pk tree index nodeIdx level left right))))
      steps result) :
    Executes hash SphincsImages.verify (parentHashReadyState state)
      (steps + 1) (result.charge 16 1 2) := by
  have ready := parentHashReady_block state pc
  have regs := hashRegisters_ready (parentReadyState state)
  have query := readyParent_hashInput_tree state pk tree index nodeIdx level
    left right treeValue positionValue treeIndex nodeIndex parameterEncoded
    leftEncoded rightEncoded
  have tail' : Executes hash SphincsImages.verify
      (writeHash (parentHashReadyState state)
        (hash (hashInput (parentHashReadyState state)))) steps result := by
    rw [query]
    exact tail
  exact SphincsVerifierFtsParentHash.hash_step hash
    (parentHashReadyState state) ready.2.1 regs.1 regs.2.1
    regs.2.2.1 regs.2.2.2 steps result tail'

/-- info: 'SigGolfCandidate.SphincsVerifierFtsTreeHashStep.parentReady_hashStep_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentReady_hashStep_tree

end SigGolfCandidate.SphincsVerifierFtsTreeHashStep
