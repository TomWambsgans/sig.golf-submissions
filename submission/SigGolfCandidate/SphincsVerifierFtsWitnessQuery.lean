import SigGolfCandidate.SphincsVerifierFtsRoundQuery
import SigGolfCandidate.SphincsVerifierFtsPathAddress

/-! Supply the generic FORS parent query from the signature's path bytes. -/

namespace SigGolfCandidate.SphincsVerifierFtsWitnessQuery
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsParentWitness
open SigGolfCandidate.SphincsVerifierFtsPathAddress
open SigGolfCandidate.SphincsVerifierFtsRoundQuery
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384

theorem parentRound_query_from_witness (start : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (level : Fin ftsTreeHeight) (current : Digest)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 =
      BitVec.ofNat 64 (pathAddress tree level))
    (levelValue : start.getMem 0x43048 =
      BitVec.ofNat 64 (level.val + 1))
    (treeValue : start.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (treeIndex : start.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (selector : start.getMem 0x43070 =
      BitVec.ofNat 64 leaf.val >>> level.val)
    (witnessPrefix : WitnessPrefix start pk)
    (witness : FtsWitness start signature)
    (currentEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        current.extractLsb' (8 * i) 8) :
    hashInput (firstParentReadyState start) =
      toQuery (tweakableHashInput pk.parameter
        (.ftsNode index tree (level.val + 1)
          (leaf.val / 2 ^ (level.val + 1)))
        (SphincsSecurity.Concrete.nodePayload
          (if leaf.val.testBit level.val then
            signature.ftsPath tree level else current)
          (if leaf.val.testBit level.val then
            current else signature.ftsPath tree level))) := by
  let pointer := BitVec.ofNat 64 (pathAddress tree level)
  have encoded (i : Nat) (hi : i < 20) :
      start.getByte (BitVec.ofNat 64 (pointer.toNat + i)) =
        (signature.ftsPath tree level).extractLsb' (8 * i) 8 :=
    witness_path_at_pointer start signature witness tree level i hi
  exact parentRound_query start pointer pk tree index leaf level.val
    current (signature.ftsPath tree level) pc pointerValue
    (pathPointer_small tree level)
    (by rw [pathPointer_toNat]; exact pathAddress_aligned tree level)
    levelValue treeValue treeIndex selector witnessPrefix currentEncoded
    encoded

/-- info: 'SigGolfCandidate.SphincsVerifierFtsWitnessQuery.parentRound_query_from_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentRound_query_from_witness

end SigGolfCandidate.SphincsVerifierFtsWitnessQuery
