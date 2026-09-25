import SigGolfCandidate.SphincsVerifierFtsRoundInvariant
import SigGolfCandidate.SphincsVerifierFtsTreeParent

/-! The generic machine parent query is the abstract FORS fold query. -/

namespace SigGolfCandidate.SphincsVerifierFtsRoundQuery
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsTreeParent
open SigGolfCandidate.SphincsVerifierFtsTreeQuery
open SigGolfCandidate.SphincsVerifierFtsSelectorArithmetic
open SigGolfCandidate.SphincsVerifierFtsParentWitness
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384

def parentNodeIndex (leaf : FtsLeaf) (level : Nat) : FtsLeaf :=
  ⟨leaf.val / 2 ^ (level + 1),
    lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt⟩

theorem parentRound_query (start : MachineState)
    (pointer : Word) (pk : SphincsSecurity.PublicKey)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (level : Nat) (current sibling : Digest)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0)
    (levelValue : start.getMem 0x43048 = BitVec.ofNat 64 (level + 1))
    (treeValue : start.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (treeIndex : start.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (selector : start.getMem 0x43070 = BitVec.ofNat 64 leaf.val >>> level)
    (witnessPrefix : WitnessPrefix start pk)
    (currentEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        current.extractLsb' (8 * i) 8)
    (siblingEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (pointer.toNat + i)) =
        sibling.extractLsb' (8 * i) 8) :
    hashInput (firstParentReadyState start) =
      toQuery (tweakableHashInput pk.parameter
        (.ftsNode index tree (level + 1) (leaf.val / 2 ^ (level + 1)))
        (SphincsSecurity.Concrete.nodePayload
          (if leaf.val.testBit level then sibling else current)
          (if leaf.val.testBit level then current else sibling))) := by
  have nodeIndex : start.getMem 0x43070 >>> 1 =
      BitVec.ofNat 64 (parentNodeIndex leaf level).val := by
    rw [selector]
    exact selector_parent_index leaf level
  have raw := parent_hashInput_tree start pointer pk tree index
    (parentNodeIndex leaf level) (level + 1) current sibling pc pointerValue
    small aligned levelValue treeValue treeIndex nodeIndex witnessPrefix
    currentEncoded siblingEncoded
  have parity := machine_parity_testBit start leaf level selector
  change hashInput (firstParentReadyState start) =
    toQuery (parentInputTree pk tree index (parentNodeIndex leaf level)
      (level + 1)
      (if leaf.val.testBit level then sibling else current)
      (if leaf.val.testBit level then current else sibling))
  by_cases hb : leaf.val.testBit level = true
  · have nonzero : ¬ (parityState start).getReg .x6 = 0 := by
      intro zero
      have falseBit := parity.mp zero
      simp [hb] at falseBit
    simp only [hb, if_true]
    simpa only [nonzero, if_false] using raw
  · have falseBit : leaf.val.testBit level = false := by
      cases h : leaf.val.testBit level <;> simp_all
    have zero : (parityState start).getReg .x6 = 0 := parity.mpr falseBit
    simp [falseBit]
    simpa only [zero, if_true] using raw

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRoundQuery.parentRound_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentRound_query

end SigGolfCandidate.SphincsVerifierFtsRoundQuery
