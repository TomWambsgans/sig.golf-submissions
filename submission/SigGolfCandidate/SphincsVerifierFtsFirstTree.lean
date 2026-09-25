import SigGolfCandidate.SphincsVerifierFtsPathCost
import SigGolfCandidate.SphincsVerifierFtsFoldBridge

/-! The first FORS tree's machine root agrees with the abstract fold. -/

namespace SigGolfCandidate.SphincsVerifierFtsFirstTree
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsFoldBridge
open SigGolfCandidate.SphincsVerifierFtsPathCost
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
set_option maxRecDepth 16384

theorem firstTree_abstract_root (hash : Hash) (state : MachineState)
    (answer : BitVec 256) (signature : Signature)
    (pk : SphincsSecurity.PublicKey) (index : Index) (leaf : FtsLeaf)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (pointer : state.getMem 0x43028 = 0x22cf0)
    (selector : state.getMem 0x43070 = BitVec.ofNat 64 leaf.val)
    (treeCell : state.getMem 0x43000 = 0)
    (indexCell : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (hprefix : WitnessPrefix state pk)
    (witness : FtsWitness state signature) :
    let start := firstLeafStartState state answer
    let final := parentPathRun hash pk signature ⟨0, by decide⟩ index leaf
      start (truncateHash answer) 8
    final.1.pc = 0x1b84 ∧
      (∀ i, (hi : i < 20) →
        final.1.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (SphincsSecurity.Concrete.ftsFoldValue
            (adaptOracle hash) pk.parameter index ⟨0, by decide⟩ leaf
            (signature.ftsPath ⟨0, by decide⟩)
            (truncateHash answer) 8).extractLsb' (8 * i) 8) ∧
      pathCycles hash pk signature ⟨0, by decide⟩ index leaf start
        (truncateHash answer) 8 ≤ 1136 := by
  have initial := firstLeafInitialInv state answer signature pk index leaf
    pc source bits destination pointer selector treeCell indexCell hprefix witness
  have root := parentPathRun_abstract_root hash pk signature
    ⟨0, by decide⟩ index leaf (firstLeafStartState state answer)
    (truncateHash answer) initial
  have cost := (fullPath_cost_le hash pk signature ⟨0, by decide⟩
    index leaf (firstLeafStartState state answer) (truncateHash answer)).1
  exact ⟨root.1, root.2, cost⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsFirstTree.firstTree_abstract_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstTree_abstract_root

end SigGolfCandidate.SphincsVerifierFtsFirstTree
