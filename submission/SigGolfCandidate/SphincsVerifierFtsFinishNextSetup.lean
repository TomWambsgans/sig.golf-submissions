import SigGolfCandidate.SphincsVerifierFtsRootFrame

namespace SigGolfCandidate.SphincsVerifierFtsFinishNextSetup
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsNextTreeSetup
open SigGolfCandidate.SphincsVerifierFtsNextPointer
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem finish_next_setup_block (state : MachineState) (tree : FtsTree)
    (pc : state.pc = 0x1b84)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (source : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x22cdc + 180 * (tree.val + 1)))
    (next : tree.val + 1 < ftsTrees - 1) :
    OrdinarySteps SphincsImages.verify state 132
      (nextTreeHashState (treeFinishState state)) := by
  have finish := treeFinish_block state tree pc counter
  have readyPc := treeFinish_pc_next state tree pc counter next
  have readyCounter : (treeFinishState state).getMem 0x43040 =
      BitVec.ofNat 64 (tree.val + 1) := treeFinish_counter state tree counter
  have readySource : (treeFinishState state).getMem 0x43028 =
      BitVec.ofNat 64 (0x22cdc + 180 * (tree.val + 1)) := by
    rw [treeFinish_pointer state tree counter]
    exact source
  let nextTree : FtsTree := ⟨tree.val + 1, next⟩
  have setup := nextTreeSetup_block (treeFinishState state) nextTree
    readyPc readyCounter readySource
  simpa only [show 33 + 99 = 132 by decide] using finish.append setup

theorem tree_through_next_ready_executes (hash : Hash)
    (state : MachineState) (signature : Signature)
    (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64
        (SphincsVerifierFtsPathAddress.pathAddress tree ⟨0, by decide⟩))
    (selector : state.getMem 0x43070 = BitVec.ofNat 64 leaf.val)
    (treeCell : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (indexCell : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (witness : SphincsVerifierFtsEarlyFrame.FtsWitness state signature)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (next : tree.val + 1 < ftsTrees - 1)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (nextTreeHashState (treeFinishState
        (SphincsVerifierFtsPathInduction.parentPathRun hash pk signature tree
          index leaf
          (SphincsVerifierFtsInitialInvariant.firstLeafStartState state
            (hash (hashInput state)))
          (truncateHash (hash (hashInput state))) 8).1))
      steps result) :
    ∃ totalSteps totalResult,
      Executes hash SphincsImages.verify state totalSteps totalResult ∧
      totalSteps ≤ steps + 1167 ∧
      totalResult.cycles ≤ result.cycles + 1294 ∧
      totalResult.hashCalls = result.hashCalls + 9 ∧
      totalResult.hashCompressions = result.hashCompressions + 17 := by
  let answer := hash (hashInput state)
  let start := SphincsVerifierFtsInitialInvariant.firstLeafStartState state answer
  let pathState := (SphincsVerifierFtsPathInduction.parentPathRun hash pk
    signature tree index leaf start (truncateHash answer) 8).1
  have pathPc : pathState.pc = 0x1b84 :=
    (tree_abstract_root hash state answer signature pk tree index leaf
      pc source bits destination pointer selector treeCell indexCell hprefix
      witness).1
  have pathCounter : pathState.getMem 0x43040 =
      BitVec.ofNat 64 tree.val := by
    calc
      _ = start.getMem 0x43040 :=
        parentPathRun_counter_frame hash pk signature tree index leaf start
          (truncateHash answer) 8
      _ = state.getMem 0x43040 :=
        SphincsVerifierFtsLevelInit.levelStart_counter_frame
          state answer destination
      _ = BitVec.ofNat 64 tree.val := counter
  have pathSource : pathState.getMem 0x43028 =
      BitVec.ofNat 64 (0x22cdc + 180 * (tree.val + 1)) := by
    have h := treeFinish_next_source hash state signature pk tree index leaf
      counter destination pointer
    dsimp only at h
    rw [treeFinish_pointer pathState tree pathCounter] at h
    exact h
  have finishReady := finish_next_setup_block pathState tree pathPc
    pathCounter pathSource next
  obtain ⟨totalSteps, totalResult, execution, stepBound, cycleBound,
      hashBound, compressionBound⟩ :=
    tree_executes hash state signature pk tree index leaf pc source bits
      destination service pointer selector treeCell indexCell hprefix witness
      (steps + 132) (result.charge 132 0 0)
      (finishReady.then_executes tail)
  refine ⟨totalSteps, totalResult, execution, ?_, ?_, ?_, ?_⟩
  · omega
  · simp only [Execution.charge] at cycleBound
    omega
  · simpa only [Execution.charge, Nat.zero_add] using hashBound
  · simpa only [Execution.charge, Nat.zero_add] using compressionBound

/-- info: 'SigGolfCandidate.SphincsVerifierFtsFinishNextSetup.tree_through_next_ready_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms tree_through_next_ready_executes

/-- info: 'SigGolfCandidate.SphincsVerifierFtsFinishNextSetup.finish_next_setup_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms finish_next_setup_block

end SigGolfCandidate.SphincsVerifierFtsFinishNextSetup
