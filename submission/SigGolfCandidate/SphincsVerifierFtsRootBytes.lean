import SigGolfCandidate.SphincsVerifierFtsGenericTree

namespace SigGolfCandidate.SphincsVerifierFtsRootBytes
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsResult

set_option maxHeartbeats 0
set_option maxRecDepth 16384

theorem rootSlot_word_byte (state : MachineState) (tree : FtsTree)
    (index : Fin 5) (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64
      (0x44100 + 20 * tree.val + 4 * index.val + byte.val)) =
      (state.getWord32 (BitVec.ofNat 64
        (0x44100 + 20 * tree.val + 4 * index.val))).extractLsb'
          (8 * byte.val) 8 := by
  have split := SphincsVerifierSecondHashHeader.extractByte_from_word32
    (state.getMem (alignToDword (BitVec.ofNat 64
      (0x44100 + 20 * tree.val + 4 * index.val + byte.val))))
    ⟨(0x44100 + 20 * tree.val + 4 * index.val + byte.val) % 8,
      Nat.mod_lt _ (by decide)⟩
  fin_cases tree <;> fin_cases index <;> fin_cases byte <;>
    simpa [MachineState.getByte, MachineState.getWord32,
      alignToDword, byteOffset] using split

theorem treeFinish_root_bytes (state : MachineState) (tree : FtsTree)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (i : Nat) (hi : i < 20) :
    (treeFinishState state).getByte
      (BitVec.ofNat 64 (0x44100 + 20 * tree.val + i)) =
      state.getByte (BitVec.ofNat 64 (0x44a00 + i)) := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  calc
    _ = (treeFinishState state).getByte (BitVec.ofNat 64
          (0x44100 + 20 * tree.val + 4 * index.val + byte.val)) := by
          simp only [Nat.add_assoc, split]
    _ = ((treeFinishState state).getWord32
          (BitVec.ofNat 64
            (0x44100 + 20 * tree.val + 4 * index.val))).extractLsb'
              (8 * byte.val) 8 := rootSlot_word_byte _ tree index byte
    _ = (state.getWord32
          (BitVec.ofNat 64 (0x44a00 + 4 * index.val))).extractLsb'
              (8 * byte.val) 8 := by rw [treeFinish_root_data state tree counter index]
    _ = state.getByte (BitVec.ofNat 64 (0x44a00 + i)) := by
      rw [← result_word_byte state 0x44a00 (Or.inr rfl) index byte]
      simp only [Nat.add_assoc, split]

theorem treeFinish_abstract_root_bytes (hash : Hash)
    (state : MachineState) (signature : Signature)
    (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (SphincsVerifierFtsPathAddress.pathAddress
        tree ⟨0, by decide⟩))
    (selector : state.getMem 0x43070 = BitVec.ofNat 64 leaf.val)
    (treeCell : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (indexCell : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (witness : SphincsVerifierFtsEarlyFrame.FtsWitness state signature) :
    let answer := hash (hashInput state)
    let pathState :=
      (SphincsVerifierFtsPathInduction.parentPathRun hash pk signature
        tree index leaf (SphincsVerifierFtsInitialInvariant.firstLeafStartState
          state answer) (SphincsSecurity.truncateHash answer) 8).1
    ∀ i, (hi : i < 20) →
      (treeFinishState pathState).getByte
        (BitVec.ofNat 64 (0x44100 + 20 * tree.val + i)) =
        (SphincsSecurity.Concrete.ftsFoldValue
          (SigGolfCandidate.SphincsBridge.adaptOracle hash) pk.parameter
          index tree leaf (signature.ftsPath tree)
          (SphincsSecurity.truncateHash answer) 8).extractLsb'
            (8 * i) 8 := by
  let answer := hash (hashInput state)
  let pathState :=
    (SphincsVerifierFtsPathInduction.parentPathRun hash pk signature
      tree index leaf (SphincsVerifierFtsInitialInvariant.firstLeafStartState
        state answer) (SphincsSecurity.truncateHash answer) 8).1
  have root := tree_abstract_root hash state answer signature pk tree
    index leaf pc source bits destination pointer selector treeCell
    indexCell hprefix witness
  have pathCounter : pathState.getMem 0x43040 =
      BitVec.ofNat 64 tree.val := by
    calc
      _ = (SphincsVerifierFtsInitialInvariant.firstLeafStartState state
          answer).getMem 0x43040 := parentPathRun_counter_frame _ _ _ _ _ _ _ _ _
      _ = state.getMem 0x43040 :=
        SphincsVerifierFtsLevelInit.levelStart_counter_frame state
          answer destination
      _ = BitVec.ofNat 64 tree.val := counter
  dsimp only
  intro i hi
  exact (treeFinish_root_bytes pathState tree pathCounter i hi).trans
    (root.2.1 i hi)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootBytes.rootSlot_word_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootSlot_word_byte

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootBytes.treeFinish_root_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeFinish_root_bytes

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootBytes.treeFinish_abstract_root_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeFinish_abstract_root_bytes

end SigGolfCandidate.SphincsVerifierFtsRootBytes
