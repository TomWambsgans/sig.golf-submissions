import SigGolfCandidate.SphincsVerifierFtsTreeAdvance
import SigGolfCandidate.SphincsVerifierFtsInitialInvariant

/-! A single leaf-to-parent-loop invariant for every FORS tree. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericInitialInvariant
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierFtsPathAddress
open SigGolfCandidate.SphincsVerifierFtsLoopInvariant
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolfCandidate.SphincsVerifierHashBytes
set_option maxRecDepth 16384

theorem leafInitialInv (state : MachineState)
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
    FtsLoopInv (firstLeafStartState state answer) signature pk
      tree index leaf ⟨0, by decide⟩ (truncateHash answer) := by
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
  · rw [show (firstLeafStartState state answer).getMem 0x43028 =
      state.getMem 0x43028 by
        apply levelStart_mem_frame state answer destination
        all_goals try { intro offset; fin_cases offset <;> decide }
        all_goals decide, pointer]
  · exact result.2.2.1
  · rw [treeFrame, treeCell]
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

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericInitialInvariant.leafInitialInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms leafInitialInv

end SigGolfCandidate.SphincsVerifierFtsGenericInitialInvariant
