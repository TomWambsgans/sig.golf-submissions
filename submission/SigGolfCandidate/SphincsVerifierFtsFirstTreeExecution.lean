import SigGolfCandidate.SphincsVerifierFtsFirstTree

/-! Compose the first FORS leaf HASH with its eight certified parent rounds. -/

namespace SigGolfCandidate.SphincsVerifierFtsFirstTreeExecution
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsPathCost
open SigGolfCandidate.SphincsVerifierFtsHash
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
set_option maxRecDepth 16384

theorem firstTree_executes (hash : Hash) (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaf : FtsLeaf)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1)
    (pointer : state.getMem 0x43028 = 0x22cf0)
    (selector : state.getMem 0x43070 = BitVec.ofNat 64 leaf.val)
    (treeCell : state.getMem 0x43000 = 0)
    (indexCell : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (hprefix : WitnessPrefix state pk)
    (witness : FtsWitness state signature)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (parentPathRun hash pk signature ⟨0, by decide⟩ index leaf
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
  have initial := firstLeafInitialInv state answer signature pk index leaf
    pc source bits destination pointer selector treeCell indexCell hprefix witness
  have path := parentPathRun_executes_exact hash pk signature
    ⟨0, by decide⟩ index leaf start (truncateHash answer) initial
    8 (by decide) steps result tail
  have front := (firstFtsLevelStart state signature answer pc source bits
    destination witness).1
  have afterLeaf := front.then_executes path
  have all := hash_step hash state pc source bits destination service _ _
    afterLeaf
  refine ⟨_, _, all, ?_, ?_, ?_, ?_⟩
  · have bound := (fullPath_cost_le hash pk signature ⟨0, by decide⟩
      index leaf start (truncateHash answer)).2
    omega
  · have bound := (fullPath_cost_le hash pk signature ⟨0, by decide⟩
      index leaf start (truncateHash answer)).1
    simp only [Execution.charge] at *
    omega
  · simp [Execution.charge, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  · simp [Execution.charge, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

/-- info: 'SigGolfCandidate.SphincsVerifierFtsFirstTreeExecution.firstTree_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstTree_executes

end SigGolfCandidate.SphincsVerifierFtsFirstTreeExecution
