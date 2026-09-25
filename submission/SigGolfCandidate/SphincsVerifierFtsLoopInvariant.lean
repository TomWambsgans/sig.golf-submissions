import SigGolfCandidate.SphincsVerifierFtsRoundPrefix

/-! The nonfinal FORS authentication levels share one machine invariant. -/

namespace SigGolfCandidate.SphincsVerifierFtsLoopInvariant
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsPathAddress
open SigGolfCandidate.SphincsVerifierFtsRoundInvariant
open SigGolfCandidate.SphincsVerifierFtsRoundTrace
open SigGolfCandidate.SphincsVerifierFtsRoundPrefix
open SigGolfCandidate.SphincsVerifierFtsWitnessQuery
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierHashBytes
set_option maxRecDepth 16384

structure FtsLoopInv (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (level : Fin ftsTreeHeight) (current : Digest) : Prop where
  pc : state.pc = 0x1914
  pointer : state.getMem 0x43028 =
    BitVec.ofNat 64 (pathAddress tree level)
  levelCell : state.getMem 0x43048 = BitVec.ofNat 64 (level.val + 1)
  treeCell : state.getMem 0x43000 = BitVec.ofNat 64 tree.val
  indexCell : state.getMem 0x43008 = BitVec.ofNat 64 index.val
  selector : state.getMem 0x43070 = BitVec.ofNat 64 leaf.val >>> level.val
  publicKeyBytes : WitnessPrefix state pk
  witness : FtsWitness state signature
  currentEncoded : ∀ i, (hi : i < 20) →
    state.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
      current.extractLsb' (8 * i) 8

theorem FtsLoopInv.query (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (level : Fin ftsTreeHeight) (current : Digest)
    (inv : FtsLoopInv state signature pk tree index leaf level current) :
    hashInput (firstParentReadyState state) =
      toQuery (tweakableHashInput pk.parameter
        (.ftsNode index tree (level.val + 1)
          (leaf.val / 2 ^ (level.val + 1)))
        (SphincsSecurity.Concrete.nodePayload
          (if leaf.val.testBit level.val then
            signature.ftsPath tree level else current)
          (if leaf.val.testBit level.val then
            current else signature.ftsPath tree level))) :=
  parentRound_query_from_witness state signature pk tree index leaf level
    current inv.pc inv.pointer inv.levelCell inv.treeCell inv.indexCell
    inv.selector inv.publicKeyBytes inv.witness inv.currentEncoded

theorem FtsLoopInv.advance (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (level : Fin ftsTreeHeight) (current : Digest)
    (inv : FtsLoopInv state signature pk tree index leaf level current)
    (nextLevel : level.val + 1 < ftsTreeHeight)
    (answer : BitVec 256) :
    FtsLoopInv (parentRoundState state answer)
      signature pk tree index leaf ⟨level.val + 1, nextLevel⟩
      (truncateHash answer) := by
  let pointer := BitVec.ofNat 64 (pathAddress tree level)
  have ready := parentRound_readyTrace state pointer inv.pc inv.pointer
    (pathPointer_admissible tree level)
  have notFinal : level.val + 1 < 8 := by
    simpa only [ftsTreeHeight] using nextLevel
  constructor
  · exact parentRound_pc_repeat state answer (level.val + 1)
      ready.2 inv.levelCell notFinal
  · rw [parentRound_pointer state answer pointer inv.pointer,
      pathAddress_next tree level nextLevel]
    simp [pointer, BitVec.ofNat_add]
  · simpa only using parentRound_level state answer (level.val + 1)
      inv.levelCell
  · rw [parentRound_tree, inv.treeCell]
  · rw [parentRound_index, inv.indexCell]
  · simpa only using parentRound_selector state answer pointer leaf level.val
      inv.pc inv.pointer (pathPointer_admissible tree level) inv.selector
  · exact parentRound_WitnessPrefix state answer pk inv.publicKeyBytes
  · exact parentRound_witness state answer signature inv.witness
  · exact parentRound_root state answer

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLoopInvariant.FtsLoopInv.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FtsLoopInv.query

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLoopInvariant.FtsLoopInv.advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FtsLoopInv.advance

end SigGolfCandidate.SphincsVerifierFtsLoopInvariant
