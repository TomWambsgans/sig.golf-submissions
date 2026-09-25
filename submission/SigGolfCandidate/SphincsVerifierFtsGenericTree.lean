import SigGolfCandidate.SphincsVerifierFtsGenericInitialInvariant
import SigGolfCandidate.SphincsVerifierFtsFirstTreeExecution
import SigGolfCandidate.SphincsVerifierFtsRootStoreData
import SigGolfCandidate.SphincsVerifierFtsTreeAdvance

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
open SigGolfCandidate.SphincsVerifierFtsRootStore
open SigGolfCandidate.SphincsVerifierFtsRootStoreData
open SigGolfCandidate.SphincsVerifierFtsTreeAdvance
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsGenericPosition
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsResultControls
open SigGolfCandidate.SphincsVerifierFtsRoundInvariant
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

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

def treeFinishState (state : MachineState) : MachineState :=
  treeAdvanceState (copyRootState (rootStoreSetupState state))

theorem rootStore_counter (state : MachineState) (tree : FtsTree)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val) :
    (copyRootState (rootStoreSetupState state)).getMem 0x43040 =
      state.getMem 0x43040 := by
  let setup := rootStoreSetupState state
  have destination := rootStoreSetup_destination state tree counter
  have outside : ∀ offset : Fin 5,
      (0x43040 : Word) ≠ alignToDword
        (setup.getReg .x7 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    change (0x43040 : Word) ≠ alignToDword
      ((rootStoreSetupState state).getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val))
    rw [destination]
    fin_cases tree <;> fin_cases offset <;> decide
  rw [copyRoot_mem_frame setup 0x43040 outside]
  exact rootStoreSetup_mem state 0x43040

theorem treeFinish_block (state : MachineState) (tree : FtsTree)
    (pc : state.pc = 0x1b84)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val) :
    OrdinarySteps SphincsImages.verify state 33 (treeFinishState state) := by
  have stored := rootStore_block state tree pc counter
  exact stored.1.append (treeAdvance_block _ stored.2)

theorem treeFinish_counter (state : MachineState) (tree : FtsTree)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val) :
    (treeFinishState state).getMem 0x43040 =
      BitVec.ofNat 64 (tree.val + 1) := by
  rw [treeFinishState, treeAdvance_counter,
    rootStore_counter state tree counter, counter]
  simp [BitVec.ofNat_add]

theorem treeFinish_pc_next (state : MachineState) (tree : FtsTree)
    (pc : state.pc = 0x1b84)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (next : tree.val + 1 < ftsTrees - 1) :
    (treeFinishState state).pc = 0x173c := by
  have stored := (rootStore_block state tree pc counter).2
  exact treeAdvance_pc_next _ tree stored
    ((rootStore_counter state tree counter).trans counter) next

theorem treeFinish_pc_done (state : MachineState)
    (pc : state.pc = 0x1b84)
    (counter : state.getMem 0x43040 = 23) :
    (treeFinishState state).pc = 0x1c08 := by
  let tree : FtsTree := ⟨23, by decide⟩
  have stored := (rootStore_block state tree pc counter).2
  exact treeAdvance_pc_done _ stored
    ((rootStore_counter state tree counter).trans counter)

theorem treeFinish_root_data (state : MachineState) (tree : FtsTree)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (index : Fin 5) :
    (treeFinishState state).getWord32
      (BitVec.ofNat 64 (0x44100 + 20 * tree.val + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  simp only [MachineState.getWord32, treeFinishState]
  rw [treeAdvance_mem_frame _ _ (by
    fin_cases tree <;> fin_cases index <;> decide)]
  exact rootStore_data state tree counter index

theorem parentRound_counter_frame (state : MachineState)
    (answer : BitVec 256) :
    (parentRoundState state answer).getMem 0x43040 =
      state.getMem 0x43040 := by
  have positioned :
      (firstPositionedState state).getMem 0x43040 =
        state.getMem 0x43040 := by
    change (levelPositionState
      (shiftIndexState (advancePointerState (pairState state)))).getMem
        0x43040 = _
    rw [levelPosition_mem_frame _ 0x43040 (by decide),
      shiftIndex_mem_frame _ 0x43040 (by decide) (by decide),
      advancePointer_mem_frame _ 0x43040 (by decide)]
    apply pair_scratch_frame
    all_goals intro offset <;> fin_cases offset <;> decide
  have ready : (firstParentReadyState state).getMem 0x43040 =
      state.getMem 0x43040 := by
    change (parentHashReadyState (firstPositionedState state)).getMem
      0x43040 = _
    rw [parentHashReady_mem_frame _ 0x43040 (Or.inr (by decide)),
      positioned]
  unfold parentRoundState
  rw [fullParent_mem_frame _ answer 0x43040 (ready_destination state)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro offset
      fin_cases offset <;> decide), ready]

theorem parentPathRun_counter_frame (hash : Hash)
    (pk : SphincsSecurity.PublicKey) (signature : Signature)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (start : MachineState) (initial : Digest) (n : Nat) :
    (parentPathRun hash pk signature tree index leaf start initial n).1.getMem
      0x43040 = start.getMem 0x43040 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [parentPathRun_succ]
      exact (parentRound_counter_frame _ _).trans ih

theorem treeThroughFinish_executes (hash : Hash) (state : MachineState)
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
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (treeFinishState
        (parentPathRun hash pk signature tree index leaf
          (firstLeafStartState state (hash (hashInput state)))
          (truncateHash (hash (hashInput state))) 8).1)
      steps result) :
    ∃ totalSteps totalResult,
      Executes hash SphincsImages.verify state totalSteps totalResult ∧
      totalSteps ≤ steps + 1068 ∧
      totalResult.cycles ≤ result.cycles + 1195 ∧
      totalResult.hashCalls = result.hashCalls + 9 ∧
      totalResult.hashCompressions = result.hashCompressions + 17 := by
  let pathState :=
    (parentPathRun hash pk signature tree index leaf
      (firstLeafStartState state (hash (hashInput state)))
      (truncateHash (hash (hashInput state))) 8).1
  have pathPc : pathState.pc = 0x1b84 :=
    (tree_abstract_root hash state (hash (hashInput state)) signature
      pk tree index leaf pc source bits destination pointer selector
      treeCell indexCell hprefix witness).1
  have pathCounter : pathState.getMem 0x43040 =
      BitVec.ofNat 64 tree.val := by
    calc
      _ = (firstLeafStartState state (hash (hashInput state))).getMem
          0x43040 := parentPathRun_counter_frame _ _ _ _ _ _ _ _ _
      _ = state.getMem 0x43040 :=
        levelStart_counter_frame state (hash (hashInput state)) destination
      _ = BitVec.ofNat 64 tree.val := counter
  have finished :=
    (treeFinish_block pathState tree pathPc pathCounter).then_executes tail
  obtain ⟨totalSteps, totalResult, execution, stepBound, cycleBound,
    hashBound, compressionBound⟩ :=
    tree_executes hash state signature pk tree index leaf pc source bits
      destination service pointer selector treeCell indexCell hprefix witness
      (steps + 33) (result.charge 33 0 0) finished
  refine ⟨totalSteps, totalResult, execution, ?_, ?_, ?_, ?_⟩
  · omega
  · simp only [Execution.charge] at cycleBound
    omega
  · simpa only [Execution.charge, Nat.zero_add] using hashBound
  · simpa only [Execution.charge, Nat.zero_add] using compressionBound

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

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericTree.rootStore_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootStore_counter

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericTree.treeFinish_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeFinish_block

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericTree.treeFinish_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeFinish_counter

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericTree.treeFinish_pc_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeFinish_pc_next

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericTree.treeFinish_pc_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeFinish_pc_done

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericTree.treeFinish_root_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeFinish_root_data

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericTree.parentRound_counter_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentRound_counter_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericTree.parentPathRun_counter_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentPathRun_counter_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericTree.treeThroughFinish_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeThroughFinish_executes

end SigGolfCandidate.SphincsVerifierFtsGenericTree
