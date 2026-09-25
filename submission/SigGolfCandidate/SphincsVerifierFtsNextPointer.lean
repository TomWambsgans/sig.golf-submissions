import SigGolfCandidate.SphincsVerifierFtsNextTreeSetup

namespace SigGolfCandidate.SphincsVerifierFtsNextPointer
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsRoundInvariant
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsRootStore
open SigGolfCandidate.SphincsVerifierFtsTreeAdvance
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierFtsPathAddress
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem parentPathRun_pointer (hash : Hash)
    (pk : SphincsSecurity.PublicKey) (signature : Signature)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (start : MachineState) (initial : Digest) (n : Nat) :
    (parentPathRun hash pk signature tree index leaf start initial n).1.getMem
      0x43028 = start.getMem 0x43028 + BitVec.ofNat 64 (20 * n) := by
  induction n with
  | zero => simp [parentPathRun]
  | succ n ih =>
      rw [parentPathRun_succ]
      change (parentRoundState
        (parentPathRun hash pk signature tree index leaf start initial n).1
        (hash (SphincsVerifierFtsLoopTransition.parentQuery pk signature tree index
          leaf ⟨n % ftsTreeHeight, Nat.mod_lt _ (by decide)⟩
          (parentPathRun hash pk signature tree index leaf start initial n).2))).getMem
        0x43028 = _
      rw [parentRound_pointer _ _ _ rfl, ih]
      simp [Nat.mul_succ, BitVec.ofNat_add, add_assoc, add_comm, add_left_comm]

theorem treeFinish_pointer (state : MachineState)
    (tree : FtsTree)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val) :
    (treeFinishState state).getMem 0x43028 = state.getMem 0x43028 := by
  have destination := rootStoreSetup_destination state tree counter
  have outside : ∀ offset : Fin 5,
      (0x43028 : Word) ≠ alignToDword
        ((rootStoreSetupState state).getReg .x7 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [destination]
    fin_cases tree <;> fin_cases offset <;> decide
  change (treeAdvanceState (copyRootState (rootStoreSetupState state))).getMem
    0x43028 = state.getMem 0x43028
  rw [treeAdvance_mem_frame _ 0x43028 (by decide),
    copyRoot_mem_frame _ 0x43028 outside, rootStoreSetup_mem]

theorem treeFinish_next_source (hash : Hash)
    (state : MachineState) (signature : Signature)
    (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (destination : state.getReg .x12 = 0x42000)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (pathAddress tree ⟨0, by decide⟩)) :
    let pathState := (parentPathRun hash pk signature tree index leaf
      (SphincsVerifierFtsInitialInvariant.firstLeafStartState state
        (hash (hashInput state)))
      (truncateHash (hash (hashInput state))) 8).1
    (treeFinishState pathState).getMem 0x43028 =
      BitVec.ofNat 64 (0x22cdc + 180 * (tree.val + 1)) := by
  let start := SphincsVerifierFtsInitialInvariant.firstLeafStartState state
    (hash (hashInput state))
  let pathState := (parentPathRun hash pk signature tree index leaf start
    (truncateHash (hash (hashInput state))) 8).1
  have startPointer : start.getMem 0x43028 =
      BitVec.ofNat 64 (pathAddress tree ⟨0, by decide⟩) := by
    exact (SphincsVerifierFtsLevelInit.levelStart_pointer_frame state
      (hash (hashInput state)) destination).trans pointer
  have pathPointer : pathState.getMem 0x43028 =
      BitVec.ofNat 64 (pathAddress tree ⟨0, by decide⟩) +
        BitVec.ofNat 64 (20 * 8) := by
    rw [parentPathRun_pointer, startPointer]
  have pathCounter : pathState.getMem 0x43040 =
      BitVec.ofNat 64 tree.val := by
    rw [parentPathRun_counter_frame]
    exact (SphincsVerifierFtsLevelInit.levelStart_counter_frame state
      (hash (hashInput state)) destination).trans counter
  dsimp only
  rw [treeFinish_pointer pathState tree pathCounter, pathPointer]
  have addressEq : pathAddress tree ⟨0, by decide⟩ + 20 * 8 =
      0x22cdc + 180 * (tree.val + 1) := by
    simp [pathAddress, ftsTreeHeight, SphincsWire.ftsOpeningBytes,
      SphincsWire.digestBytes]
    omega
  simpa only [BitVec.ofNat_add] using
    congrArg (BitVec.ofNat 64) addressEq

/-- info: 'SigGolfCandidate.SphincsVerifierFtsNextPointer.treeFinish_next_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeFinish_next_source
end SigGolfCandidate.SphincsVerifierFtsNextPointer
