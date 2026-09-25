import SigGolfCandidate.SphincsVerifierXmssNodeSite
import SigGolfCandidate.SphincsVerifierFtsLevelBranch

namespace SigGolfCandidate.SphincsVerifierXmssParity
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierXmssNodeSite
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def nodePc (lay : Layer) : Word :=
  BitVec.ofNat 64 (0x2ad4 + 0xfcc * (5 - lay.val))

def nodeParitySchedule (lay : Layer) : List (Word × Instr) := [
  (nodePc lay, .LUI .x28 67),
  (nodePc lay + 4, .ADDI .x28 .x28 112),
  (nodePc lay + 8, .LD .x6 .x28 0),
  (nodePc lay + 12, .ANDI .x6 .x6 1)]

theorem nodeParity_code (lay : Layer) : ∀ entry ∈ nodeParitySchedule lay,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by
  fin_cases lay <;> decide

theorem nodeParity_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay) : Checked (nodeParitySchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, nodeParitySchedule, nodePc, execInstrBr, ordinaryStep,
      memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
      signExtend12, MachineState.getReg_setReg_eq, pc]

theorem nodeParity_block (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay) :
    OrdinarySteps SphincsImages.verify s 4 (parityState s) := by
  have block := checked_sound _ (nodeParitySchedule lay)
    (nodeParity_code lay) s (nodeParity_checked lay s pc)
  simpa [nodeParitySchedule, runSchedule, parityState] using block

theorem nodeParity_reg (s : MachineState) :
    (parityState s).getReg .x6 = s.getMem 0x43070 &&& 1 :=
  parity_reg s

theorem nodeParity_pc (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay) :
    (parityState s).pc = nodePc lay + 16 := by
  simp [parityState, execInstrBr, pc]
  bv_decide

theorem nodeBranch_site (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay + 16) :
    fetch SphincsImages.verify s = some (.base (.BEQ .x6 .x0 124)) := by
  fin_cases lay
  · rw [SphincsVerifierMessageCopy.fetch_index SphincsImages.verify s 6776
      (by decide) (by simpa [nodePc] using pc)]; decide
  · rw [SphincsVerifierMessageCopy.fetch_index SphincsImages.verify s 5765
      (by decide) (by simpa [nodePc] using pc)]; decide
  · rw [SphincsVerifierMessageCopy.fetch_index SphincsImages.verify s 4754
      (by decide) (by simpa [nodePc] using pc)]; decide
  · rw [SphincsVerifierMessageCopy.fetch_index SphincsImages.verify s 3743
      (by decide) (by simpa [nodePc] using pc)]; decide
  · rw [SphincsVerifierMessageCopy.fetch_index SphincsImages.verify s 2732
      (by decide) (by simpa [nodePc] using pc)]; decide
  · rw [SphincsVerifierMessageCopy.fetch_index SphincsImages.verify s 1721
      (by decide) (by simpa [nodePc] using pc)]; decide

def nodeBranchState (s : MachineState) : MachineState :=
  execInstrBr (parityState s) (.BEQ .x6 .x0 124)

theorem nodeBranch_block (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay) :
    OrdinarySteps SphincsImages.verify s 5 (nodeBranchState s) := by
  have headTrace := nodeParity_block lay s pc
  have branch : OrdinarySteps SphincsImages.verify (parityState s) 1
      (nodeBranchState s) := by
    apply OrdinarySteps.step (parityState s) (nodeBranchState s) _
      (.base (.BEQ .x6 .x0 124)) 0
    · exact nodeBranch_site lay (parityState s) (nodeParity_pc lay s pc)
    · rfl
    · exact OrdinarySteps.refl _
  simpa [nodeBranchState] using headTrace.append branch

theorem nodeBranch_pc (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay) :
    (nodeBranchState s).pc =
      if s.getMem 0x43070 &&& 1 = 0 then nodePc lay + 0x8c
      else nodePc lay + 20 := by
  have parityPc := nodeParity_pc lay s pc
  simp [nodeBranchState, execInstrBr, nodeParity_reg, parityPc,
    signExtend13]
  split_ifs <;> bv_decide

#print axioms nodeParity_block
#print axioms nodeBranch_site
#print axioms nodeBranch_block
#print axioms nodeBranch_pc

end SigGolfCandidate.SphincsVerifierXmssParity
