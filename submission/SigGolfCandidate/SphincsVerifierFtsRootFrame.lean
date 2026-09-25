import SigGolfCandidate.SphincsVerifierFtsNextPointer
import SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
import SigGolfCandidate.SphincsVerifierFtsResultControls

namespace SigGolfCandidate.SphincsVerifierFtsRootFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierFtsResultControls
open SigGolfCandidate.SphincsVerifierFtsRoundInvariant
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def RootRegion (read : Word) : Prop :=
  0x44100 ≤ read.toNat ∧ read.toNat < 0x44300

private theorem root_ne (read written : Word)
    (inside : RootRegion read) (outside : written.toNat < 0x44100 ∨
      0x44300 ≤ written.toNat) : read ≠ written := by
  intro same
  have eq := congrArg BitVec.toNat same
  rcases inside with ⟨low, high⟩
  rcases outside with below | above <;> omega

private theorem root_ne_of_nat (read : Word) (n : Nat)
    (inside : RootRegion read) (outside : n < 0x44100 ∨ 0x44300 ≤ n)
    (small : n < 2 ^ 64) : read ≠ BitVec.ofNat 64 n := by
  apply root_ne read _ inside
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using outside

theorem rootSlot_region (tree : SphincsSecurity.FtsTree)
    (i : Nat) (hi : i < 20) :
    RootRegion (alignToDword
      (BitVec.ofNat 64 (0x44100 + 20 * tree.val + i))) := by
  fin_cases tree <;> interval_cases i <;> (dsimp [RootRegion, alignToDword]; decide)

theorem parentRound_root_frame (state : MachineState)
    (answer : BitVec 256) (read : Word)
    (inside : RootRegion read) :
    (parentRoundState state answer).getMem read = state.getMem read := by
  let positioned := firstPositionedState state
  let ready := firstParentReadyState state
  have pairFrame : (pairState state).getMem read = state.getMem read := by
    apply pair_scratch_frame
    · intro offset
      apply root_ne read _ inside
      fin_cases offset <;> decide
    · intro offset
      apply root_ne read _ inside
      fin_cases offset <;> decide
  have positionedFrame : positioned.getMem read = state.getMem read := by
    change (levelPositionState (shiftIndexState
      (advancePointerState (pairState state)))).getMem read = _
    rw [levelPosition_mem_frame _ read
      (root_ne_of_nat read 0x43010 inside (Or.inl (by decide)) (by decide)),
      shiftIndex_mem_frame _ read
        (root_ne_of_nat read 0x43070 inside (Or.inl (by decide)) (by decide))
        (root_ne_of_nat read 0x43018 inside (Or.inl (by decide)) (by decide)),
      advancePointer_mem_frame _ read
        (root_ne_of_nat read 0x43028 inside (Or.inl (by decide)) (by decide)),
      pairFrame]
  have outside : OutsideHashBuffer read := Or.inr (by
    rcases inside with ⟨low, _⟩
    have lower : 0x40100 ≤ 0x44100 := by decide
    omega)
  have readyFrame : ready.getMem read = state.getMem read := by
    change (parentHashReadyState positioned).getMem read = _
    rw [parentHashReady_mem_frame positioned read outside, positionedFrame]
  have notCopy : ∀ offset : Fin 5,
      read ≠ alignToDword
        (0x44a00 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    apply root_ne read _ inside
    fin_cases offset <;> decide
  have resultFrame : (parentRoundState state answer).getMem read =
      ready.getMem read := by
    exact fullParent_mem_frame ready answer read (ready_destination state)
      (root_ne_of_nat read 0x43048 inside (Or.inl (by decide)) (by decide))
      (root_ne_of_nat read 0x42000 inside (Or.inl (by decide)) (by decide))
      (root_ne_of_nat read 0x42008 inside (Or.inl (by decide)) (by decide))
      (root_ne_of_nat read 0x42010 inside (Or.inl (by decide)) (by decide))
      (root_ne_of_nat read 0x42018 inside (Or.inl (by decide)) (by decide))
      notCopy
  exact resultFrame.trans readyFrame

theorem parentPathRun_root_frame (hash : Hash)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (tree : SphincsSecurity.FtsTree)
    (index : SphincsSecurity.Index)
    (leaf : SphincsSecurity.FtsLeaf)
    (start : MachineState) (initial : SphincsSecurity.Digest)
    (n : Nat) (read : Word) (inside : RootRegion read) :
    (SphincsVerifierFtsPathInduction.parentPathRun hash pk signature tree index
      leaf start initial n).1.getMem read = start.getMem read := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [SphincsVerifierFtsPathInduction.parentPathRun_succ]
      exact (parentRound_root_frame _ _ read inside).trans ih

theorem firstLeafStart_root_frame (state : MachineState)
    (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000)
    (read : Word) (inside : RootRegion read) :
    (SphincsVerifierFtsInitialInvariant.firstLeafStartState state answer).getMem
      read = state.getMem read := by
  apply SphincsVerifierFtsLevelInit.levelStart_mem_frame state answer
    destination read
  · exact root_ne_of_nat read 0x43048 inside (Or.inl (by decide)) (by decide)
  · exact root_ne_of_nat read 0x42000 inside (Or.inl (by decide)) (by decide)
  · exact root_ne_of_nat read 0x42008 inside (Or.inl (by decide)) (by decide)
  · exact root_ne_of_nat read 0x42010 inside (Or.inl (by decide)) (by decide)
  · exact root_ne_of_nat read 0x42018 inside (Or.inl (by decide)) (by decide)
  · intro offset
    apply root_ne read _ inside
    fin_cases offset <;> decide

theorem nextTreeSetup_root_frame (state : MachineState)
    (read : Word) (inside : RootRegion read) :
    (SphincsVerifierFtsNextTreeSetup.nextTreeHashState state).getMem read =
      state.getMem read := by
  let header := SphincsVerifierFtsTreeHeader.ftsTreeHeaderState state
  let selected := SphincsVerifierFtsSelect.ftsSelectState header
  let pointers := SphincsVerifierFtsCopyPointers.ftsCopyPointers selected
  let copied := SphincsVerifierCopy.copyRootState pointers
  let advanced := SphincsVerifierFtsAdvance.ftsAdvanceState copied
  have readyFrame : (SphincsVerifierFtsSetup.ftsHashReadyState advanced).getMem
      read = advanced.getMem read := by
    apply SphincsVerifierFtsLevelInit.hashReady_mem_frame
    · exact root_ne_of_nat read 0x40000 inside (Or.inl (by decide)) (by decide)
    · exact root_ne_of_nat read 0x40000 inside (Or.inl (by decide)) (by decide)
    · exact root_ne_of_nat read 0x40008 inside (Or.inl (by decide)) (by decide)
    · exact root_ne_of_nat read 0x40010 inside (Or.inl (by decide)) (by decide)
    · intro offset
      apply root_ne read _ inside
      fin_cases offset <;> decide
  have advanceFrame : advanced.getMem read = copied.getMem read := by
    apply SphincsVerifierFtsAdvance.ftsAdvance_mem_frame
    · exact root_ne_of_nat read 0x43028 inside (Or.inl (by decide)) (by decide)
    · exact root_ne_of_nat read 0x43018 inside (Or.inl (by decide)) (by decide)
  have copyFrame : copied.getMem read = pointers.getMem read := by
    apply SphincsVerifierCopyMemory.copyRoot_mem_frame
    intro offset
    rw [(SphincsVerifierFtsCopyPointers.ftsCopyPointers_regs selected).2]
    apply root_ne read _ inside
    fin_cases offset <;> decide
  have pointerFrame : pointers.getMem read = selected.getMem read :=
    SphincsVerifierFtsCopyPointers.ftsCopyPointers_mem selected read
  have selectFrame : selected.getMem read = header.getMem read := by
    apply SphincsVerifierFtsSelect.ftsSelect_mem_frame
    · exact root_ne_of_nat read 0x43010 inside (Or.inl (by decide)) (by decide)
    · exact root_ne_of_nat read 0x43020 inside (Or.inl (by decide)) (by decide)
    · exact root_ne_of_nat read 0x43070 inside (Or.inl (by decide)) (by decide)
  have headerFrame : header.getMem read = state.getMem read := by
    apply SphincsVerifierFtsTreeHeader.ftsTreeHeader_mem_frame
    · exact root_ne_of_nat read 0x43000 inside (Or.inl (by decide)) (by decide)
    · exact root_ne_of_nat read 0x43008 inside (Or.inl (by decide)) (by decide)
  exact readyFrame.trans (advanceFrame.trans (copyFrame.trans
    (pointerFrame.trans (selectFrame.trans headerFrame))))

theorem parentPathRun_root_byte_frame (hash : Hash)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (tree prior : SphincsSecurity.FtsTree)
    (index : SphincsSecurity.Index)
    (leaf : SphincsSecurity.FtsLeaf)
    (start : MachineState) (initial : SphincsSecurity.Digest)
    (n i : Nat) (hi : i < 20) :
    (SphincsVerifierFtsPathInduction.parentPathRun hash pk signature tree index
      leaf start initial n).1.getByte
        (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) =
      start.getByte (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) := by
  simp only [MachineState.getByte]
  rw [parentPathRun_root_frame hash pk signature tree index leaf start
    initial n _ (rootSlot_region prior i hi)]

theorem firstLeafStart_root_byte_frame (state : MachineState)
    (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000)
    (prior : SphincsSecurity.FtsTree) (i : Nat) (hi : i < 20) :
    (SphincsVerifierFtsInitialInvariant.firstLeafStartState state answer).getByte
      (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) =
      state.getByte (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) := by
  simp only [MachineState.getByte]
  rw [firstLeafStart_root_frame state answer destination _
    (rootSlot_region prior i hi)]

theorem nextTreeSetup_root_byte_frame (state : MachineState)
    (prior : SphincsSecurity.FtsTree) (i : Nat) (hi : i < 20) :
    (SphincsVerifierFtsNextTreeSetup.nextTreeHashState state).getByte
      (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) =
      state.getByte (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) := by
  simp only [MachineState.getByte]
  rw [nextTreeSetup_root_frame state _ (rootSlot_region prior i hi)]

theorem treeProcess_prior_root_byte (hash : Hash)
    (state : MachineState) (signature : SphincsSecurity.Signature)
    (pk : SphincsSecurity.PublicKey)
    (tree prior : SphincsSecurity.FtsTree)
    (index : SphincsSecurity.Index) (leaf : SphincsSecurity.FtsLeaf)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (destination : state.getReg .x12 = 0x42000)
    (older : prior.val < tree.val)
    (i : Nat) (hi : i < 20) :
    let answer := hash (hashInput state)
    let start := SphincsVerifierFtsInitialInvariant.firstLeafStartState state answer
    let pathState := (SphincsVerifierFtsPathInduction.parentPathRun hash pk
      signature tree index leaf start (SphincsSecurity.truncateHash answer) 8).1
    (SphincsVerifierFtsGenericTree.treeFinishState pathState).getByte
      (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) =
      state.getByte (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) := by
  let answer := hash (hashInput state)
  let start := SphincsVerifierFtsInitialInvariant.firstLeafStartState state answer
  let pathState := (SphincsVerifierFtsPathInduction.parentPathRun hash pk
    signature tree index leaf start (SphincsSecurity.truncateHash answer) 8).1
  have pathCounter : pathState.getMem 0x43040 =
      BitVec.ofNat 64 tree.val := by
    calc
      _ = start.getMem 0x43040 :=
        SphincsVerifierFtsGenericTree.parentPathRun_counter_frame
          hash pk signature tree index leaf start
          (SphincsSecurity.truncateHash answer) 8
      _ = state.getMem 0x43040 :=
        SphincsVerifierFtsLevelInit.levelStart_counter_frame state answer destination
      _ = BitVec.ofNat 64 tree.val := counter
  dsimp only
  exact (SphincsVerifierFtsPriorRoots.treeFinish_prior_root_bytes pathState
    tree prior i hi pathCounter older).trans
    ((parentPathRun_root_byte_frame hash pk signature tree prior index leaf
      start (SphincsSecurity.truncateHash answer) 8 i hi).trans
      (firstLeafStart_root_byte_frame state answer destination prior i hi))

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootFrame.treeProcess_prior_root_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeProcess_prior_root_byte

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootFrame.rootSlot_region' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootSlot_region

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootFrame.nextTreeSetup_root_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nextTreeSetup_root_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootFrame.parentRound_root_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentRound_root_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootFrame.firstLeafStart_root_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstLeafStart_root_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootFrame.parentPathRun_root_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentPathRun_root_frame

end SigGolfCandidate.SphincsVerifierFtsRootFrame
