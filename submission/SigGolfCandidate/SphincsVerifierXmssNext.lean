import SigGolfCandidate.SphincsVerifierXmssNodeReady
import SigGolfCandidate.SphincsVerifierFtsParentLoop

namespace SigGolfCandidate.SphincsVerifierXmssNext
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssNodeSite
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsVerifierFtsParentLevel
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def advancePc (lay : Layer) : Word := nodeHashPc lay + 60

def advanceSchedule (lay : Layer) : List (Word × Instr) := [
  (advancePc lay, .LUI .x28 0x43),
  (advancePc lay + 4, .ADDI .x28 .x28 72),
  (advancePc lay + 8, .LD .x6 .x28 0),
  (advancePc lay + 12, .ADDI .x6 .x6 1),
  (advancePc lay + 16, .LUI .x28 0x43),
  (advancePc lay + 20, .ADDI .x28 .x28 72),
  (advancePc lay + 24, .SD .x28 .x6 0)]

theorem advance_code (lay : Layer) : ∀ entry ∈ advanceSchedule lay,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by
  fin_cases lay <;> decide

theorem advance_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = advancePc lay) : Checked (advanceSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, advanceSchedule, advancePc, nodeHashPc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

theorem advance_block (lay : Layer) (s : MachineState)
    (pc : s.pc = advancePc lay) :
    OrdinarySteps SphincsImages.verify s 7 (advanceLevelState s) := by
  have block := checked_sound _ (advanceSchedule lay)
    (advance_code lay) s (advance_checked lay s pc)
  simpa [advanceSchedule, runSchedule, advanceLevelState] using block

def checkPc (lay : Layer) : Word := advancePc lay + 28

def checkSchedule (lay : Layer) : List (Word × Instr) := [
  (checkPc lay, .LUI .x28 0x43),
  (checkPc lay + 4, .ADDI .x28 .x28 72),
  (checkPc lay + 8, .LD .x6 .x28 0),
  (checkPc lay + 12,
    .ADDI .x7 .x0 (BitVec.ofNat 12 (layerHeight lay + 1)))]

theorem check_code (lay : Layer) : ∀ entry ∈ checkSchedule lay,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by
  fin_cases lay <;> decide

theorem check_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = checkPc lay) : Checked (checkSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, checkSchedule, checkPc, advancePc, nodeHashPc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, signExtend12,
      MachineState.getReg_setReg_eq, pc]

def checkState (lay : Layer) (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x43)
  let s := execInstrBr s (.ADDI .x28 .x28 72)
  let s := execInstrBr s (.LD .x6 .x28 0)
  execInstrBr s (.ADDI .x7 .x0 (BitVec.ofNat 12 (layerHeight lay + 1)))

theorem check_block (lay : Layer) (s : MachineState)
    (pc : s.pc = checkPc lay) :
    OrdinarySteps SphincsImages.verify s 4 (checkState lay s) := by
  have block := checked_sound _ (checkSchedule lay)
    (check_code lay) s (check_checked lay s pc)
  simpa [checkSchedule, runSchedule, checkState] using block

def branchPc (lay : Layer) : Word := checkPc lay + 16

theorem branch_site (lay : Layer) (s : MachineState)
    (pc : s.pc = branchPc lay) :
    fetch SphincsImages.verify s = some (.base (.BNE .x6 .x7 (-616))) := by
  fin_cases lay
  · rw [fetch_index SphincsImages.verify s 6926 (by decide)
      (by simpa [branchPc, checkPc, advancePc, nodeHashPc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify s 5915 (by decide)
      (by simpa [branchPc, checkPc, advancePc, nodeHashPc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify s 4904 (by decide)
      (by simpa [branchPc, checkPc, advancePc, nodeHashPc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify s 3893 (by decide)
      (by simpa [branchPc, checkPc, advancePc, nodeHashPc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify s 2882 (by decide)
      (by simpa [branchPc, checkPc, advancePc, nodeHashPc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify s 1871 (by decide)
      (by simpa [branchPc, checkPc, advancePc, nodeHashPc] using pc)]; decide

def branchState (s : MachineState) : MachineState :=
  execInstrBr s (.BNE .x6 .x7 (-616))

theorem branch_block (lay : Layer) (s : MachineState)
    (pc : s.pc = branchPc lay) :
    OrdinarySteps SphincsImages.verify s 1 (branchState s) := by
  apply OrdinarySteps.step s _ _ (.base (.BNE .x6 .x7 (-616))) 0
  · exact branch_site lay s pc
  · rfl
  · exact OrdinarySteps.refl _

theorem check_values (lay : Layer) (s : MachineState) :
    (checkState lay s).getReg .x6 = s.getMem 0x43048 ∧
    (checkState lay s).getReg .x7 =
      BitVec.ofNat 64 (layerHeight lay + 1) := by
  fin_cases lay <;>
    simp [checkState, execInstrBr, signExtend12, layerHeight,
      maxLayerHeight, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

theorem branch_pc_repeat (lay : Layer) (s : MachineState)
    (pc : s.pc = branchPc lay)
    (again : s.getReg .x6 ≠ s.getReg .x7) :
    (branchState s).pc = nodePc lay := by
  fin_cases lay <;>
    simp [branchState, execInstrBr, pc, again, branchPc,
      checkPc, advancePc, nodeHashPc, nodePc, signExtend13]

theorem branch_pc_done (lay : Layer) (s : MachineState)
    (pc : s.pc = branchPc lay)
    (done : s.getReg .x6 = s.getReg .x7) :
    (branchState s).pc = branchPc lay + 4 := by
  simp [branchState, execInstrBr, pc, done]

def nextState (lay : Layer) (s : MachineState) : MachineState :=
  branchState (checkState lay (advanceLevelState s))

theorem next_block (lay : Layer) (s : MachineState)
    (pc : s.pc = advancePc lay) :
    OrdinarySteps SphincsImages.verify s 12 (nextState lay s) := by
  let a := advanceLevelState s
  let c := checkState lay a
  have first := advance_block lay s pc
  have apc : a.pc = checkPc lay := by
    simp [a, advanceLevelState, execInstrBr, pc, checkPc]
    bv_decide
  have second := check_block lay a apc
  have cpc : c.pc = branchPc lay := by
    simp [c, checkState, execInstrBr, apc, branchPc, checkPc]
    bv_decide
  have third := branch_block lay c cpc
  simpa [nextState, a, c] using (first.append second).append third

#print axioms advance_block
#print axioms check_block
#print axioms next_block
#print axioms branch_pc_repeat

end SigGolfCandidate.SphincsVerifierXmssNext
