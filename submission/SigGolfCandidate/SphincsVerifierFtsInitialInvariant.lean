import SigGolfCandidate.SphincsVerifierFtsPathInduction

/-! Enter the first FORS path from the certified leaf HASH result. -/

namespace SigGolfCandidate.SphincsVerifierFtsInitialInvariant
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierFtsResult
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolfCandidate.SphincsVerifierFtsPathAddress
open SigGolfCandidate.SphincsVerifierFtsLoopInvariant
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierHashBytes
set_option maxRecDepth 16384

def firstLeafStartState (state : MachineState) (answer : BitVec 256) :
    MachineState :=
  levelInitState (resultState (writeHash state answer))

private theorem low_ne (read written : Word)
    (low : read.toNat < 0x40000)
    (high : 0x40000 ≤ written.toNat) : read ≠ written := by
  intro equal
  have same := congrArg BitVec.toNat equal
  omega

theorem firstLeaf_low_mem_frame (state : MachineState)
    (answer : BitVec 256) (read : Word)
    (destination : state.getReg .x12 = 0x42000)
    (low : read.toNat < 0x40000) :
    (firstLeafStartState state answer).getMem read = state.getMem read := by
  unfold firstLeafStartState
  apply levelStart_mem_frame state answer destination read
  · exact low_ne read 0x43048 low (by decide)
  · exact low_ne read 0x42000 low (by decide)
  · exact low_ne read 0x42008 low (by decide)
  · exact low_ne read 0x42010 low (by decide)
  · exact low_ne read 0x42018 low (by decide)
  · intro offset
    apply low_ne read _ low
    fin_cases offset <;> decide

theorem firstLeaf_WitnessPrefix (state : MachineState)
    (answer : BitVec 256) (pk : SphincsSecurity.PublicKey)
    (destination : state.getReg .x12 = 0x42000)
    (hprefix : WitnessPrefix state pk) :
    WitnessPrefix (firstLeafStartState state answer) pk := by
  constructor
  · intro i hi
    have low : (alignToDword (BitVec.ofNat 64 (0x22ca0 + i))).toNat <
        0x40000 := by
      apply witnessByte_aligned_low i
      have size := SphincsWire.signatureBytes_eq
      omega
    simp only [MachineState.getByte]
    rw [firstLeaf_low_mem_frame state answer _ destination low]
    exact hprefix.root i hi
  · intro i hi
    have low : (alignToDword (BitVec.ofNat 64 (0x22cb4 + i))).toNat <
        0x40000 := by
      have same : (0x22cb4 + i : Nat) = 0x22ca0 + (20 + i) := by omega
      rw [same]
      apply witnessByte_aligned_low (20 + i)
      have size := SphincsWire.signatureBytes_eq
      omega
    simp only [MachineState.getByte]
    rw [firstLeaf_low_mem_frame state answer _ destination low]
    exact hprefix.parameter i hi

theorem firstLeafInitialInv (state : MachineState)
    (answer : BitVec 256) (signature : Signature)
    (pk : SphincsSecurity.PublicKey) (index : Index) (leaf : FtsLeaf)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (pointer : state.getMem 0x43028 = 0x22cf0)
    (selector : state.getMem 0x43070 = BitVec.ofNat 64 leaf.val)
    (treeCell : state.getMem 0x43000 = 0)
    (indexCell : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (hprefix : WitnessPrefix state pk)
    (witness : FtsWitness state signature) :
    FtsLoopInv (firstLeafStartState state answer) signature pk
      ⟨0, by decide⟩ index leaf ⟨0, by decide⟩
      (truncateHash answer) := by
  have result := firstFtsLevelStart state signature answer pc source bits
    destination witness
  have treeFrame : (firstLeafStartState state answer).getMem 0x43000 =
      state.getMem 0x43000 := by
    apply levelStart_mem_frame state answer destination
    all_goals try { intro offset; fin_cases offset <;> decide }
    all_goals decide
  have indexFrame : (firstLeafStartState state answer).getMem 0x43008 =
      state.getMem 0x43008 := by
    apply levelStart_mem_frame state answer destination
    all_goals try { intro offset; fin_cases offset <;> decide }
    all_goals decide
  constructor
  · exact result.2.1
  · rw [show pathAddress (⟨0, by decide⟩ : FtsTree)
        (⟨0, by decide⟩ : Fin ftsTreeHeight) = 0x22cf0 by decide]
    rw [show (firstLeafStartState state answer).getMem 0x43028 =
      state.getMem 0x43028 by
        apply levelStart_mem_frame state answer destination
        all_goals try { intro offset; fin_cases offset <;> decide }
        all_goals decide, pointer]
    decide
  · exact result.2.2.1
  · rw [treeFrame, treeCell]
    rfl
  · rw [indexFrame, indexCell]
  · rw [show (firstLeafStartState state answer).getMem 0x43070 =
      state.getMem 0x43070 by
        apply levelStart_mem_frame state answer destination
        all_goals try { intro offset; fin_cases offset <;> decide }
        all_goals decide, selector]
    rfl
  · exact firstLeaf_WitnessPrefix state answer pk destination hprefix
  · exact result.2.2.2.1
  · exact result.2.2.2.2

theorem firstTree_finish (hash : Hash) (state : MachineState)
    (answer : BitVec 256) (signature : Signature)
    (pk : SphincsSecurity.PublicKey) (index : Index) (leaf : FtsLeaf)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (pointer : state.getMem 0x43028 = 0x22cf0)
    (selector : state.getMem 0x43070 = BitVec.ofNat 64 leaf.val)
    (treeCell : state.getMem 0x43000 = 0)
    (indexCell : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (hprefix : WitnessPrefix state pk)
    (witness : FtsWitness state signature) :
    let start := firstLeafStartState state answer
    let final := parentPathRun hash pk signature ⟨0, by decide⟩ index leaf
      start (truncateHash answer) 8
    final.1.pc = 0x1b84 ∧
      (∀ i, (hi : i < 20) →
        final.1.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          final.2.extractLsb' (8 * i) 8) ∧
      FtsWitness final.1 signature ∧ WitnessPrefix final.1 pk := by
  have initial := firstLeafInitialInv state answer signature pk index leaf
    pc source bits destination pointer selector treeCell indexCell hprefix witness
  exact parentPathRun_finish hash pk signature ⟨0, by decide⟩ index leaf
    (firstLeafStartState state answer) (truncateHash answer) initial

/-- info: 'SigGolfCandidate.SphincsVerifierFtsInitialInvariant.firstLeafInitialInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstLeafInitialInv

/-- info: 'SigGolfCandidate.SphincsVerifierFtsInitialInvariant.firstTree_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstTree_finish

end SigGolfCandidate.SphincsVerifierFtsInitialInvariant
