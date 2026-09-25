import SigGolfCandidate.SphincsVerifierXmssPairSemantic
import SigGolfCandidate.SphincsVerifierFtsLevelPosition

namespace SigGolfCandidate.SphincsVerifierXmssPrefix
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def pairPc (lay : Layer) : Word := nodePc lay + 0x100

def advanceSchedule (lay : Layer) : List (Word × Instr) := [
  (pairPc lay, .LUI .x28 0x43),
  (pairPc lay + 4, .ADDI .x28 .x28 40),
  (pairPc lay + 8, .LD .x6 .x28 0),
  (pairPc lay + 12, .ADDI .x6 .x6 20),
  (pairPc lay + 16, .LUI .x28 0x43),
  (pairPc lay + 20, .ADDI .x28 .x28 40),
  (pairPc lay + 24, .SD .x28 .x6 0)]

theorem advance_code (lay : Layer) : ∀ entry ∈ advanceSchedule lay,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by
  fin_cases lay <;> decide

theorem advance_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = pairPc lay) : Checked (advanceSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, advanceSchedule, pairPc, nodePc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      pc]

theorem advance_block (lay : Layer) (s : MachineState)
    (pc : s.pc = pairPc lay) :
    OrdinarySteps SphincsImages.verify s 7 (advancePointerState s) := by
  have block := checked_sound _ (advanceSchedule lay)
    (advance_code lay) s (advance_checked lay s pc)
  simpa [advanceSchedule, runSchedule, advancePointerState] using block

def shiftPc (lay : Layer) : Word := pairPc lay + 28

def shiftSchedule (lay : Layer) : List (Word × Instr) := [
  (shiftPc lay, .LUI .x28 0x43),
  (shiftPc lay + 4, .ADDI .x28 .x28 112),
  (shiftPc lay + 8, .LD .x6 .x28 0),
  (shiftPc lay + 12, .SRLI .x6 .x6 1),
  (shiftPc lay + 16, .LUI .x28 0x43),
  (shiftPc lay + 20, .ADDI .x28 .x28 112),
  (shiftPc lay + 24, .SD .x28 .x6 0),
  (shiftPc lay + 28, .LUI .x28 0x43),
  (shiftPc lay + 32, .ADDI .x28 .x28 24),
  (shiftPc lay + 36, .SD .x28 .x6 0)]

theorem shift_code (lay : Layer) : ∀ entry ∈ shiftSchedule lay,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by
  fin_cases lay <;> decide

theorem shift_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = shiftPc lay) : Checked (shiftSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, shiftSchedule, shiftPc, pairPc, nodePc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

theorem shift_block (lay : Layer) (s : MachineState)
    (pc : s.pc = shiftPc lay) :
    OrdinarySteps SphincsImages.verify s 10 (shiftIndexState s) := by
  have block := checked_sound _ (shiftSchedule lay)
    (shift_code lay) s (shift_checked lay s pc)
  simpa [shiftSchedule, runSchedule, shiftIndexState] using block

def positionPc (lay : Layer) : Word := pairPc lay + 68

def positionSchedule (lay : Layer) : List (Word × Instr) := [
  (positionPc lay, .LUI .x28 0x43),
  (positionPc lay + 4, .ADDI .x28 .x28 72),
  (positionPc lay + 8, .LD .x6 .x28 0),
  (positionPc lay + 12, .LUI .x28 0x43),
  (positionPc lay + 16, .ADDI .x28 .x28 16),
  (positionPc lay + 20, .SD .x28 .x6 0)]

theorem position_code (lay : Layer) : ∀ entry ∈ positionSchedule lay,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by
  fin_cases lay <;> decide

theorem position_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = positionPc lay) : Checked (positionSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, positionSchedule, positionPc, pairPc, nodePc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

theorem position_block (lay : Layer) (s : MachineState)
    (pc : s.pc = positionPc lay) :
    OrdinarySteps SphincsImages.verify s 6 (levelPositionState s) := by
  have block := checked_sound _ (positionSchedule lay)
    (position_code lay) s (position_checked lay s pc)
  simpa [positionSchedule, runSchedule, levelPositionState] using block

def nodePrefixState (s : MachineState) : MachineState :=
  levelPositionState (shiftIndexState (advancePointerState s))

theorem prefix_block (lay : Layer) (s : MachineState)
    (pc : s.pc = pairPc lay) :
    OrdinarySteps SphincsImages.verify s 23 (nodePrefixState s) ∧
      (nodePrefixState s).pc = pairPc lay + 92 := by
  let a := advancePointerState s
  let b := shiftIndexState a
  have first := advance_block lay s pc
  have apc : a.pc = shiftPc lay := by
    simp [a, advancePointerState, execInstrBr, pc, shiftPc]
    bv_decide
  have second := shift_block lay a apc
  have bpc : b.pc = positionPc lay := by
    simp [b, shiftIndexState, execInstrBr, apc, positionPc, shiftPc]
    bv_decide
  have third := position_block lay b bpc
  constructor
  · simpa [nodePrefixState, a, b] using
      (first.append second).append third
  · change (levelPositionState b).pc = pairPc lay + 92
    have h : (levelPositionState b).pc = b.pc + 24 := by
      simp [levelPositionState, execInstrBr]
      bv_decide
    rw [h, bpc]
    unfold positionPc
    bv_decide

#print axioms advance_block
#print axioms shift_block
#print axioms prefix_block

end SigGolfCandidate.SphincsVerifierXmssPrefix
