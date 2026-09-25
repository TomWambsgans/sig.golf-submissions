import SigGolfCandidate.SphincsVerifierXmssPair
import SigGolfCandidate.SphincsVerifierFtsGenericPairData

namespace SigGolfCandidate.SphincsVerifierXmssPairSemantic
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsVerifierXmssPair
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsRightPath
open SigGolfCandidate.SphincsVerifierFtsLeftPath
open SigGolfCandidate.SphincsVerifierFtsGenericPairData
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def rightPairState (s : MachineState) : MachineState :=
  rightFinishState (copyRootState (rightPointers (nodeBranchState s)))

def leftPairState' (s : MachineState) : MachineState :=
  SphincsVerifierFtsLeftPath.leftPairState (nodeBranchState s)

theorem nodeBranch_mem (s : MachineState) (address : Word) :
    (nodeBranchState s).getMem address = s.getMem address := by
  simp [nodeBranchState, execInstrBr, parity_mem]

theorem nodeBranch_word (s : MachineState) (address : Word) :
    (nodeBranchState s).getWord32 address = s.getWord32 address := by
  simp [nodeBranchState, execInstrBr, MachineState.getWord32, parity_mem]

theorem rightPair_trace (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay)
    (odd : s.getMem 0x43070 &&& 1 ≠ 0)
    (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0) :
    OrdinarySteps SphincsImages.verify s 35 (rightPairState s) ∧
      (rightPairState s).pc = nodePc lay + 0x100 := by
  have front := nodeBranch_block lay s pc
  have branchPc : (nodeBranchState s).pc = rightPc lay := by
    rw [nodeBranch_pc lay s pc, if_neg odd]
    simp [rightPc]
  have branchPointer : (nodeBranchState s).getMem 0x43028 =
      BitVec.ofNat 64 pointer.toNat := by
    rw [nodeBranch_mem, pointerValue]
    simp
  have back := rightPath_block lay (nodeBranchState s) branchPc
    pointer.toNat branchPointer aligned (by
      have h : 0x40000 ≤ MEMORY_BYTES := by decide
      omega)
  exact ⟨by simpa [rightPairState] using front.append back.1,
    by simpa [rightPairState] using back.2⟩

theorem leftPair_trace (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay)
    (even : s.getMem 0x43070 &&& 1 = 0)
    (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0) :
    OrdinarySteps SphincsImages.verify s 34 (leftPairState' s) ∧
      (leftPairState' s).pc = nodePc lay + 0x100 := by
  have front := nodeBranch_block lay s pc
  have branchPc : (nodeBranchState s).pc = leftPc lay := by
    rw [nodeBranch_pc lay s pc, if_pos even]
    simp [leftPc]
  have branchPointer : (nodeBranchState s).getMem 0x43028 =
      BitVec.ofNat 64 pointer.toNat := by
    rw [nodeBranch_mem, pointerValue]
    simp
  have back := leftPath_block lay (nodeBranchState s) branchPc
    pointer.toNat branchPointer aligned (by
      have h : 0x40000 ≤ MEMORY_BYTES := by decide
      omega)
  exact ⟨by simpa [leftPairState'] using front.append back.1,
    by simpa [leftPairState'] using back.2⟩

theorem rightPair_words (s : MachineState) (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (i : Fin 5) :
    (rightPairState s).getWord32 (BitVec.ofNat 64 (0x40028 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (pointer.toNat + 4 * i.val)) ∧
    (rightPairState s).getWord32 (BitVec.ofNat 64 (0x4003c + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * i.val)) := by
  have bptr : (nodeBranchState s).getMem 0x43028 = pointer := by
    rw [nodeBranch_mem]
    exact pointerValue
  have h := rightPair_data_generic (nodeBranchState s) pointer bptr small i
  constructor
  · rw [rightPairState, h.1, nodeBranch_word]
  · rw [rightPairState, h.2, nodeBranch_word]

theorem leftPair_words (s : MachineState) (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (i : Fin 5) :
    (leftPairState' s).getWord32 (BitVec.ofNat 64 (0x40028 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * i.val)) ∧
    (leftPairState' s).getWord32 (BitVec.ofNat 64 (0x4003c + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (pointer.toNat + 4 * i.val)) := by
  have bptr : (nodeBranchState s).getMem 0x43028 = pointer := by
    rw [nodeBranch_mem]
    exact pointerValue
  have h := leftPair_data_generic (nodeBranchState s) pointer bptr small i
  constructor
  · rw [leftPairState', h.1, nodeBranch_word]
  · rw [leftPairState', h.2, nodeBranch_word]

#print axioms rightPair_trace
#print axioms leftPair_trace
#print axioms rightPair_words
#print axioms leftPair_words

end SigGolfCandidate.SphincsVerifierXmssPairSemantic
