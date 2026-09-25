import SigGolfCandidate.SphincsVerifierFtsGenericInitialInvariant
import SigGolfCandidate.SphincsVerifierFtsFirstTreeExecution

/-! One certified leaf-and-path theorem, uniform in the FORS tree index. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsGenericInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsFoldBridge
open SigGolfCandidate.SphincsVerifierFtsPathCost
open SigGolfCandidate.SphincsVerifierFtsPathAddress
open SigGolfCandidate.SphincsVerifierFtsHash
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384

theorem tree_abstract_root (hash : Hash) (state : MachineState)
    (answer : BitVec 256) (signature : Signature)
    (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (pathAddress tree ⟨0, by decide⟩))
    (selector : state.getMem 0x43070 = BitVec.ofNat 64 leaf.val)
    (treeCell : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (indexCell : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (hprefix : WitnessPrefix state pk)
    (witness : FtsWitness state signature) :
    let start := firstLeafStartState state answer
    let final := parentPathRun hash pk signature tree index leaf
      start (truncateHash answer) 8
    final.1.pc = 0x1b84 ∧
      (∀ i, (hi : i < 20) →
        final.1.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (SphincsSecurity.Concrete.ftsFoldValue
            (adaptOracle hash) pk.parameter index tree leaf
            (signature.ftsPath tree)
            (truncateHash answer) 8).extractLsb' (8 * i) 8) ∧
      pathCycles hash pk signature tree index leaf start
        (truncateHash answer) 8 ≤ 1136 := by
  have initial := leafInitialInv state answer signature pk tree index leaf
    pc source bits destination pointer selector treeCell indexCell hprefix witness
  have root := parentPathRun_abstract_root hash pk signature
    tree index leaf (firstLeafStartState state answer)
    (truncateHash answer) initial
  have cost := (fullPath_cost_le hash pk signature tree
    index leaf (firstLeafStartState state answer) (truncateHash answer)).1
  exact ⟨root.1, root.2, cost⟩

theorem tree_executes (hash : Hash) (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (pathAddress tree ⟨0, by decide⟩))
    (selector : state.getMem 0x43070 = BitVec.ofNat 64 leaf.val)
    (treeCell : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (indexCell : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (hprefix : WitnessPrefix state pk)
    (witness : FtsWitness state signature)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (parentPathRun hash pk signature tree index leaf
        (firstLeafStartState state (hash (hashInput state)))
        (truncateHash (hash (hashInput state))) 8).1
      steps result) :
    ∃ totalSteps totalResult,
      Executes hash SphincsImages.verify state totalSteps totalResult ∧
      totalSteps ≤ steps + 1035 ∧
      totalResult.cycles ≤ result.cycles + 1162 ∧
      totalResult.hashCalls = result.hashCalls + 9 ∧
      totalResult.hashCompressions = result.hashCompressions + 17 := by
  let answer := hash (hashInput state)
  let start := firstLeafStartState state answer
  have initial := leafInitialInv state answer signature pk tree index leaf
    pc source bits destination pointer selector treeCell indexCell hprefix witness
  have path := parentPathRun_executes_exact hash pk signature
    tree index leaf start (truncateHash answer) initial
    8 (by decide) steps result tail
  have front := (firstFtsLevelStart state signature answer pc source bits
    destination witness).1
  have afterLeaf := front.then_executes path
  have all := hash_step hash state pc source bits destination service _ _
    afterLeaf
  refine ⟨_, _, all, ?_, ?_, ?_, ?_⟩
  · have bound := (fullPath_cost_le hash pk signature tree
      index leaf start (truncateHash answer)).2
    omega
  · have bound := (fullPath_cost_le hash pk signature tree
      index leaf start (truncateHash answer)).1
    simp only [Execution.charge] at *
    omega
  · simp [Execution.charge, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  · simp [Execution.charge, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericTree.tree_abstract_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms tree_abstract_root

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericTree.tree_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms tree_executes

end SigGolfCandidate.SphincsVerifierFtsGenericTree
