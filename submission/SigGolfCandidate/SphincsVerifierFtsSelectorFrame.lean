import SigGolfCandidate.SphincsVerifierFtsPersistentIndex

namespace SigGolfCandidate.SphincsVerifierFtsSelectorFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsParentSetup
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

def SelectorRegion (read : Word) : Prop :=
  0x44800 ≤ read.toNat ∧ read.toNat < 0x44820

private theorem selector_ne (read written : Word)
    (inside : SelectorRegion read)
    (outside : written.toNat < 0x44800 ∨ 0x44820 ≤ written.toNat) :
    read ≠ written := by
  intro same
  have eq := congrArg BitVec.toNat same
  rcases inside with ⟨low, high⟩
  rcases outside with below | above <;> omega

private theorem selector_ne_of_nat (read : Word) (n : Nat)
    (inside : SelectorRegion read)
    (outside : n < 0x44800 ∨ 0x44820 ≤ n)
    (small : n < 2 ^ 64) : read ≠ BitVec.ofNat 64 n := by
  apply selector_ne read _ inside
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using outside

theorem selectorSlot_region (slot : Fin 24) :
    SelectorRegion (alignToDword
      (BitVec.ofNat 64 (0x44800 + slot.val))) := by
  fin_cases slot <;> (dsimp [SelectorRegion, alignToDword]; decide)

theorem parentRound_selector_frame (state : MachineState)
    (answer : BitVec 256) (read : Word)
    (inside : SelectorRegion read) :
    (parentRoundState state answer).getMem read = state.getMem read := by
  have pairFrame : (pairState state).getMem read = state.getMem read := by
    apply pair_scratch_frame
    · intro offset
      apply selector_ne read _ inside
      fin_cases offset <;> decide
    · intro offset
      apply selector_ne read _ inside
      fin_cases offset <;> decide
  have positionedFrame : (firstPositionedState state).getMem read =
      state.getMem read := by
    change (levelPositionState (shiftIndexState
      (advancePointerState (pairState state)))).getMem read = _
    rw [levelPosition_mem_frame _ read
      (selector_ne_of_nat read 0x43010 inside (Or.inl (by decide)) (by decide)),
      shiftIndex_mem_frame _ read
        (selector_ne_of_nat read 0x43070 inside (Or.inl (by decide)) (by decide))
        (selector_ne_of_nat read 0x43018 inside (Or.inl (by decide)) (by decide)),
      advancePointer_mem_frame _ read
        (selector_ne_of_nat read 0x43028 inside (Or.inl (by decide)) (by decide)),
      pairFrame]
  have readyFrame : (firstParentReadyState state).getMem read =
      state.getMem read := by
    change (parentHashReadyState (firstPositionedState state)).getMem read = _
    rw [parentHashReady_mem_frame _ read (Or.inr (by
      rcases inside with ⟨low, _⟩
      omega)), positionedFrame]
  have notCopy : ∀ offset : Fin 5,
      read ≠ alignToDword
        (0x44a00 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    apply selector_ne read _ inside
    fin_cases offset <;> decide
  unfold parentRoundState
  rw [fullParent_mem_frame _ answer read (ready_destination state)
    (selector_ne_of_nat read 0x43048 inside (Or.inl (by decide)) (by decide))
    (selector_ne_of_nat read 0x42000 inside (Or.inl (by decide)) (by decide))
    (selector_ne_of_nat read 0x42008 inside (Or.inl (by decide)) (by decide))
    (selector_ne_of_nat read 0x42010 inside (Or.inl (by decide)) (by decide))
    (selector_ne_of_nat read 0x42018 inside (Or.inl (by decide)) (by decide))
    notCopy, readyFrame]

theorem parentPathRun_selector_frame (hash : Hash)
    (pk : SphincsSecurity.PublicKey) (signature : Signature)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (start : MachineState) (initial : Digest) (n : Nat)
    (read : Word) (inside : SelectorRegion read) :
    (SphincsVerifierFtsPathInduction.parentPathRun hash pk signature tree
      index leaf start initial n).1.getMem read = start.getMem read := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [SphincsVerifierFtsPathInduction.parentPathRun_succ]
      exact (parentRound_selector_frame _ _ read inside).trans ih

theorem firstLeafStart_selector_frame (state : MachineState)
    (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000)
    (read : Word) (inside : SelectorRegion read) :
    (firstLeafStartState state answer).getMem read = state.getMem read := by
  apply levelStart_mem_frame state answer destination read
  · exact selector_ne_of_nat read 0x43048 inside (Or.inl (by decide)) (by decide)
  · exact selector_ne_of_nat read 0x42000 inside (Or.inl (by decide)) (by decide)
  · exact selector_ne_of_nat read 0x42008 inside (Or.inl (by decide)) (by decide)
  · exact selector_ne_of_nat read 0x42010 inside (Or.inl (by decide)) (by decide)
  · exact selector_ne_of_nat read 0x42018 inside (Or.inl (by decide)) (by decide)
  · intro offset
    apply selector_ne read _ inside
    fin_cases offset <;> decide

theorem treeFinish_selector_frame (state : MachineState)
    (tree : FtsTree) (read : Word)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (inside : SelectorRegion read) :
    (treeFinishState state).getMem read = state.getMem read := by
  have destination := rootStoreSetup_destination state tree counter
  have outside : ∀ offset : Fin 5,
      read ≠ alignToDword
        ((rootStoreSetupState state).getReg .x7 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [destination]
    apply selector_ne read _ inside
    fin_cases tree <;> fin_cases offset <;> decide
  change (treeAdvanceState (SphincsVerifierCopy.copyRootState
    (rootStoreSetupState state))).getMem read = _
  rw [treeAdvance_mem_frame _ read
    (selector_ne_of_nat read 0x43040 inside (Or.inl (by decide)) (by decide)),
    SphincsVerifierCopyMemory.copyRoot_mem_frame _ read outside,
    rootStoreSetup_mem]

theorem treeProcess_selector_frame (hash : Hash)
    (state : MachineState) (signature : Signature)
    (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (destination : state.getReg .x12 = 0x42000)
    (read : Word) (inside : SelectorRegion read) :
    let answer := hash (hashInput state)
    let start := firstLeafStartState state answer
    let pathState :=
      (SphincsVerifierFtsPathInduction.parentPathRun hash pk signature tree
        index leaf start (truncateHash answer) 8).1
    (treeFinishState pathState).getMem read = state.getMem read := by
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
  exact (treeFinish_selector_frame pathState tree read pathCounter inside).trans
    ((parentPathRun_selector_frame hash pk signature tree index leaf start
      (truncateHash answer) 8 read inside).trans
      (firstLeafStart_selector_frame state answer destination read inside))

theorem nextTreeSetup_selector_frame (state : MachineState)
    (read : Word) (inside : SelectorRegion read) :
    (nextTreeHashState state).getMem read = state.getMem read := by
  let header := ftsTreeHeaderState state
  let selected := ftsSelectState header
  let pointers := ftsCopyPointers selected
  let copied := SphincsVerifierCopy.copyRootState pointers
  let advanced := ftsAdvanceState copied
  have readyFrame : (SphincsVerifierFtsSetup.ftsHashReadyState advanced).getMem
      read = advanced.getMem read := by
    apply hashReady_mem_frame
    · exact selector_ne_of_nat read 0x40000 inside (Or.inl (by decide)) (by decide)
    · exact selector_ne_of_nat read 0x40000 inside (Or.inl (by decide)) (by decide)
    · exact selector_ne_of_nat read 0x40008 inside (Or.inl (by decide)) (by decide)
    · exact selector_ne_of_nat read 0x40010 inside (Or.inl (by decide)) (by decide)
    · intro offset
      apply selector_ne read _ inside
      fin_cases offset <;> decide
  have advanceFrame : advanced.getMem read = copied.getMem read := by
    apply ftsAdvance_mem_frame
    · exact selector_ne_of_nat read 0x43028 inside (Or.inl (by decide)) (by decide)
    · exact selector_ne_of_nat read 0x43018 inside (Or.inl (by decide)) (by decide)
  have copyFrame : copied.getMem read = pointers.getMem read := by
    apply SphincsVerifierCopyMemory.copyRoot_mem_frame
    intro offset
    rw [(ftsCopyPointers_regs selected).2]
    apply selector_ne read _ inside
    fin_cases offset <;> decide
  have pointerFrame : pointers.getMem read = selected.getMem read :=
    ftsCopyPointers_mem selected read
  have selectFrame : selected.getMem read = header.getMem read := by
    apply ftsSelect_mem_frame
    · exact selector_ne_of_nat read 0x43010 inside (Or.inl (by decide)) (by decide)
    · exact selector_ne_of_nat read 0x43020 inside (Or.inl (by decide)) (by decide)
    · exact selector_ne_of_nat read 0x43070 inside (Or.inl (by decide)) (by decide)
  have headerFrame : header.getMem read = state.getMem read := by
    apply ftsTreeHeader_mem_frame
    · exact selector_ne_of_nat read 0x43000 inside (Or.inl (by decide)) (by decide)
    · exact selector_ne_of_nat read 0x43008 inside (Or.inl (by decide)) (by decide)
  exact readyFrame.trans (advanceFrame.trans (copyFrame.trans
    (pointerFrame.trans (selectFrame.trans headerFrame))))

theorem treeProcess_selector_byte_frame (hash : Hash)
    (state : MachineState) (signature : Signature)
    (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (destination : state.getReg .x12 = 0x42000)
    (slot : Fin 24) :
    let answer := hash (hashInput state)
    let start := firstLeafStartState state answer
    let pathState :=
      (SphincsVerifierFtsPathInduction.parentPathRun hash pk signature tree
        index leaf start (truncateHash answer) 8).1
    (treeFinishState pathState).getByte
        (BitVec.ofNat 64 (0x44800 + slot.val)) =
      state.getByte (BitVec.ofNat 64 (0x44800 + slot.val)) := by
  simp only [MachineState.getByte]
  rw [treeProcess_selector_frame hash state signature pk tree index leaf
    counter destination _ (selectorSlot_region slot)]

theorem nextTreeSetup_selector_byte_frame (state : MachineState)
    (slot : Fin 24) :
    (nextTreeHashState state).getByte
        (BitVec.ofNat 64 (0x44800 + slot.val)) =
      state.getByte (BitVec.ofNat 64 (0x44800 + slot.val)) := by
  simp only [MachineState.getByte]
  rw [nextTreeSetup_selector_frame state _ (selectorSlot_region slot)]

/-- info: 'SigGolfCandidate.SphincsVerifierFtsSelectorFrame.treeProcess_selector_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeProcess_selector_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsSelectorFrame.nextTreeSetup_selector_byte_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nextTreeSetup_selector_byte_frame

end SigGolfCandidate.SphincsVerifierFtsSelectorFrame
