import SigGolfCandidate.SphincsVerifierFtsNextReadyControls

namespace SigGolfCandidate.SphincsVerifierFtsPersistentIndex
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsResultControls
open SigGolfCandidate.SphincsVerifierFtsRoundInvariant
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsRootStore
open SigGolfCandidate.SphincsVerifierFtsTreeAdvance
open SigGolfCandidate.SphincsVerifierFtsInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierFtsNextTreeSetup
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolfCandidate.SphincsVerifierFtsAdvance
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem parentRound_savedIndex_frame (state : MachineState)
    (answer : BitVec 256) :
    (parentRoundState state answer).getMem 0x43078 =
      state.getMem 0x43078 := by
  have pairFrame : (pairState state).getMem 0x43078 =
      state.getMem 0x43078 := by
    apply pair_scratch_frame
    all_goals intro offset <;> fin_cases offset <;> decide
  have positionedFrame : (firstPositionedState state).getMem 0x43078 =
      state.getMem 0x43078 := by
    change (levelPositionState (shiftIndexState
      (advancePointerState (pairState state)))).getMem 0x43078 = _
    rw [levelPosition_mem_frame _ 0x43078 (by decide),
      shiftIndex_mem_frame _ 0x43078 (by decide) (by decide),
      advancePointer_mem_frame _ 0x43078 (by decide), pairFrame]
  have readyFrame : (firstParentReadyState state).getMem 0x43078 =
      state.getMem 0x43078 := by
    change (parentHashReadyState (firstPositionedState state)).getMem
      0x43078 = _
    rw [parentHashReady_mem_frame _ 0x43078 (Or.inr (by decide)),
      positionedFrame]
  unfold parentRoundState
  rw [fullParent_mem_frame _ answer 0x43078 (ready_destination state)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro offset; fin_cases offset <;> decide), readyFrame]

theorem parentPathRun_savedIndex_frame (hash : Hash)
    (pk : SphincsSecurity.PublicKey) (signature : Signature)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (start : MachineState) (initial : Digest) (n : Nat) :
    (SphincsVerifierFtsPathInduction.parentPathRun hash pk signature tree
      index leaf start initial n).1.getMem 0x43078 =
        start.getMem 0x43078 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [SphincsVerifierFtsPathInduction.parentPathRun_succ]
      exact (parentRound_savedIndex_frame _ _).trans ih

theorem firstLeafStart_savedIndex_frame (state : MachineState)
    (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (firstLeafStartState state answer).getMem 0x43078 =
      state.getMem 0x43078 := by
  apply levelStart_mem_frame state answer destination 0x43078
  all_goals try { intro offset; fin_cases offset <;> decide }
  all_goals decide

theorem treeFinish_savedIndex_frame (state : MachineState)
    (tree : FtsTree)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val) :
    (treeFinishState state).getMem 0x43078 = state.getMem 0x43078 := by
  have destination := rootStoreSetup_destination state tree counter
  have outside : ∀ offset : Fin 5,
      (0x43078 : Word) ≠ alignToDword
        ((rootStoreSetupState state).getReg .x7 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [destination]
    fin_cases tree <;> fin_cases offset <;> decide
  change (treeAdvanceState (SphincsVerifierCopy.copyRootState
    (rootStoreSetupState state))).getMem 0x43078 = _
  rw [treeAdvance_mem_frame _ 0x43078 (by decide),
    SphincsVerifierCopyMemory.copyRoot_mem_frame _ 0x43078 outside,
    rootStoreSetup_mem]

theorem treeProcess_savedIndex_frame (hash : Hash)
    (state : MachineState) (signature : Signature)
    (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (destination : state.getReg .x12 = 0x42000) :
    let answer := hash (hashInput state)
    let start := firstLeafStartState state answer
    let pathState :=
      (SphincsVerifierFtsPathInduction.parentPathRun hash pk signature tree
        index leaf start (truncateHash answer) 8).1
    (treeFinishState pathState).getMem 0x43078 =
      state.getMem 0x43078 := by
  let answer := hash (hashInput state)
  let start := firstLeafStartState state answer
  let pathState :=
    (SphincsVerifierFtsPathInduction.parentPathRun hash pk signature tree
      index leaf start (truncateHash answer) 8).1
  have pathCounter : pathState.getMem 0x43040 =
      BitVec.ofNat 64 tree.val := by
    calc
      _ = start.getMem 0x43040 :=
        parentPathRun_counter_frame hash pk signature tree index leaf start
          (truncateHash answer) 8
      _ = state.getMem 0x43040 :=
        levelStart_counter_frame state answer destination
      _ = BitVec.ofNat 64 tree.val := counter
  dsimp only
  exact (treeFinish_savedIndex_frame pathState tree pathCounter).trans
    ((parentPathRun_savedIndex_frame hash pk signature tree index leaf start
      (truncateHash answer) 8).trans
      (firstLeafStart_savedIndex_frame state answer destination))

theorem nextTreeSetup_savedIndex_frame (state : MachineState) :
    (nextTreeHashState state).getMem 0x43078 =
      state.getMem 0x43078 := by
  let header := ftsTreeHeaderState state
  let selected := ftsSelectState header
  let pointers := ftsCopyPointers selected
  let copied := SphincsVerifierCopy.copyRootState pointers
  let advanced := ftsAdvanceState copied
  have readyFrame : (SphincsVerifierFtsSetup.ftsHashReadyState advanced).getMem
      0x43078 = advanced.getMem 0x43078 := by
    apply hashReady_mem_frame
    all_goals try { intro offset; fin_cases offset <;> decide }
    all_goals decide
  have advanceFrame : advanced.getMem 0x43078 = copied.getMem 0x43078 :=
    ftsAdvance_mem_frame copied 0x43078 (by decide) (by decide)
  have copyFrame : copied.getMem 0x43078 = pointers.getMem 0x43078 := by
    apply SphincsVerifierCopyMemory.copyRoot_mem_frame
    intro offset
    rw [(ftsCopyPointers_regs selected).2]
    fin_cases offset <;> decide
  have pointerFrame : pointers.getMem 0x43078 = selected.getMem 0x43078 :=
    ftsCopyPointers_mem selected 0x43078
  have selectFrame : selected.getMem 0x43078 = header.getMem 0x43078 :=
    ftsSelect_mem_frame header 0x43078 (by decide) (by decide) (by decide)
  have headerFrame : header.getMem 0x43078 = state.getMem 0x43078 :=
    ftsTreeHeader_mem_frame state 0x43078 (by decide) (by decide)
  exact readyFrame.trans (advanceFrame.trans (copyFrame.trans
    (pointerFrame.trans (selectFrame.trans headerFrame))))

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPersistentIndex.treeProcess_savedIndex_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeProcess_savedIndex_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPersistentIndex.nextTreeSetup_savedIndex_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nextTreeSetup_savedIndex_frame

end SigGolfCandidate.SphincsVerifierFtsPersistentIndex
