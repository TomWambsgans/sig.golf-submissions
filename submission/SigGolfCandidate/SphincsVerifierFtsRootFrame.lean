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
