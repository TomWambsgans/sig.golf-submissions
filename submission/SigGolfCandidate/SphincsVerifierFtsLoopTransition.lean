import SigGolfCandidate.SphincsVerifierFtsLoopInvariant

/-! Interpret a FORS parent step using the same oracle query as the abstract fold. -/

namespace SigGolfCandidate.SphincsVerifierFtsLoopTransition
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsPathAddress
open SigGolfCandidate.SphincsVerifierFtsRoundInvariant
open SigGolfCandidate.SphincsVerifierFtsRoundTrace
open SigGolfCandidate.SphincsVerifierFtsLoopInvariant
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384

def parentQuery (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (tree : FtsTree) (index : Index)
    (leaf : FtsLeaf) (level : Fin ftsTreeHeight) (current : Digest) : Query :=
  toQuery (tweakableHashInput pk.parameter
    (.ftsNode index tree (level.val + 1)
      (leaf.val / 2 ^ (level.val + 1)))
    (SphincsSecurity.Concrete.nodePayload
      (if leaf.val.testBit level.val then
        signature.ftsPath tree level else current)
      (if leaf.val.testBit level.val then
        current else signature.ftsPath tree level)))

theorem FtsLoopInv.parentQuery_eq (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (level : Fin ftsTreeHeight) (current : Digest)
    (inv : FtsLoopInv state signature pk tree index leaf level current) :
    hashInput (firstParentReadyState state) =
      parentQuery pk signature tree index leaf level current :=
  inv.query

theorem FtsLoopInv.advanceHash (hash : Hash) (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (level : Fin ftsTreeHeight) (current : Digest)
    (inv : FtsLoopInv state signature pk tree index leaf level current)
    (nextLevel : level.val + 1 < ftsTreeHeight) :
    FtsLoopInv
      (parentRoundState state
        (hash (parentQuery pk signature tree index leaf level current)))
      signature pk tree index leaf ⟨level.val + 1, nextLevel⟩
      (truncateHash
        (hash (parentQuery pk signature tree index leaf level current))) :=
  FtsLoopInv.advance state signature pk tree index leaf level current inv
    nextLevel (hash (parentQuery pk signature tree index leaf level current))

theorem FtsLoopInv.executesRound (hash : Hash) (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (level : Fin ftsTreeHeight) (current : Digest)
    (inv : FtsLoopInv state signature pk tree index leaf level current)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (parentRoundState state
        (hash (parentQuery pk signature tree index leaf level current)))
      steps result) :
    let pre := if (SigGolfCandidate.SphincsVerifierFtsLevelBranch.parityState state).getReg .x6 = 0
      then 34 else 35
    Executes hash SphincsImages.verify state
      (((steps + 26) + 1) + (pre + 65))
      (((result.charge 26 0 0).charge 16 1 2).charge (pre + 65) 0 0) := by
  have query := FtsLoopInv.parentQuery_eq state signature pk tree index leaf
    level current inv
  have tail' : Executes hash SphincsImages.verify
      (parentRoundState state (hash (hashInput (firstParentReadyState state))))
      steps result := by
    rw [query]
    exact tail
  exact parentRound_executes hash state
    (BitVec.ofNat 64 (pathAddress tree level)) steps result inv.pc inv.pointer
    (pathPointer_admissible tree level) tail'

theorem FtsLoopInv.finish (hash : Hash) (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (level : Fin ftsTreeHeight) (current : Digest)
    (inv : FtsLoopInv state signature pk tree index leaf level current)
    (last : level.val = 7) :
    let answer := hash (parentQuery pk signature tree index leaf level current)
    let final := parentRoundState state answer
    final.pc = 0x1b84 ∧
      (∀ i, (hi : i < 20) →
        final.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (truncateHash answer).extractLsb' (8 * i) 8) ∧
      SphincsVerifierFtsEarlyFrame.FtsWitness final signature ∧
      SphincsVerifierHashBytes.WitnessPrefix final pk := by
  let pointer := BitVec.ofNat 64 (pathAddress tree level)
  let answer := hash (parentQuery pk signature tree index leaf level current)
  have ready := parentRound_readyTrace state pointer inv.pc inv.pointer
    (pathPointer_admissible tree level)
  have levelEight : state.getMem 0x43048 = 8 := by
    rw [inv.levelCell, last]
    decide
  exact ⟨parentRound_pc_done state answer ready.2 levelEight,
    parentRound_root state answer,
    parentRound_witness state answer signature inv.witness,
    SigGolfCandidate.SphincsVerifierFtsRoundPrefix.parentRound_WitnessPrefix
      state answer pk inv.publicKeyBytes⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLoopTransition.FtsLoopInv.executesRound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FtsLoopInv.executesRound

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLoopTransition.FtsLoopInv.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FtsLoopInv.finish

end SigGolfCandidate.SphincsVerifierFtsLoopTransition
