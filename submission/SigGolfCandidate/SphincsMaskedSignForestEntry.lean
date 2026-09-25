import SigGolfCandidate.SphincsMaskedSignRootValue

namespace SigGolfCandidate.SphincsMaskedSignForestEntry
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- The fixed bridge from a successful nonce search to the first FORS leaf. -/
def entrySchedule : List (Word × Instr) := [
  (0x1cc8, .ADDI .x6 .x0 0),
  (0x1ccc, .LUI .x28 67),
  (0x1cd0, .ADDI .x28 .x28 64),
  (0x1cd4, .SD .x28 .x6 0),
  (0x1cd8, .LUI .x6 32),
  (0x1cdc, .ADDI .x6 .x6 156),
  (0x1ce0, .LUI .x28 67),
  (0x1ce4, .ADDI .x28 .x28 160),
  (0x1ce8, .SD .x28 .x6 0),
  (0x1cec, .LUI .x28 67),
  (0x1cf0, .ADDI .x28 .x28 64),
  (0x1cf4, .LD .x6 .x28 0),
  (0x1cf8, .LUI .x28 67),
  (0x1cfc, .ADDI .x28 .x28 0),
  (0x1d00, .SD .x28 .x6 0),
  (0x1d04, .LUI .x28 67),
  (0x1d08, .ADDI .x28 .x28 120),
  (0x1d0c, .LD .x6 .x28 0),
  (0x1d10, .LUI .x28 67),
  (0x1d14, .ADDI .x28 .x28 8),
  (0x1d18, .SD .x28 .x6 0),
  (0x1d1c, .LUI .x6 69),
  (0x1d20, .ADDI .x6 .x6 (-2048)),
  (0x1d24, .LUI .x28 67),
  (0x1d28, .ADDI .x28 .x28 64),
  (0x1d2c, .LD .x7 .x28 0),
  (0x1d30, .ADD .x6 .x6 .x7),
  (0x1d34, .LBU .x10 .x6 0),
  (0x1d38, .LUI .x28 67),
  (0x1d3c, .ADDI .x28 .x28 168),
  (0x1d40, .SD .x28 .x10 0),
  (0x1d44, .ADDI .x6 .x0 0),
  (0x1d48, .LUI .x28 67),
  (0x1d4c, .ADDI .x28 .x28 32),
  (0x1d50, .SD .x28 .x6 0)]

def entryState (s : MachineState) : MachineState := runSchedule entrySchedule s

theorem schedule_code : ∀ e ∈ entrySchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by
  decide

theorem schedule_checked (s : MachineState) (pc : s.pc = 0x1cc8) :
    Checked entrySchedule s := by
  simp [Checked, entrySchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc]

theorem entry_block (s : MachineState) (pc : s.pc = 0x1cc8) :
    OrdinarySteps SphincsMaskedImages.sign s 35 (entryState s) := by
  exact checked_sound _ entrySchedule schedule_code s (schedule_checked s pc)

theorem entry_pc (s : MachineState) (pc : s.pc = 0x1cc8) :
    (entryState s).pc = 0x1d54 := by
  simp [entryState, runSchedule, entrySchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc]

theorem entry_tree (s : MachineState) :
    (entryState s).getMem 0x43008 = s.getMem 0x43078 := by
  simp [entryState, runSchedule, entrySchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem entry_counters (s : MachineState) :
    (entryState s).getMem 0x43040 = 0 ∧
    (entryState s).getMem 0x43000 = 0 ∧
    (entryState s).getMem 0x43020 = 0 ∧
    (entryState s).getMem 0x430a0 = 0x2009c := by
  simp [entryState, runSchedule, entrySchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem entry_leafByte (s : MachineState) :
    (entryState s).getByte 0x44800 = s.getByte 0x44800 := by
  simp [MachineState.getByte, entryState, runSchedule, entrySchedule,
    execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, alignToDword, byteOffset]

theorem entry_selected (s : MachineState) :
    (entryState s).getMem 0x430a8 =
      (s.getByte 0x44800).zeroExtend 64 := by
  simp [entryState, runSchedule, entrySchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, MachineState.getByte,
    alignToDword, byteOffset]

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.entry_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_block

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.entry_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_tree

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.entry_counters' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_counters

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.entry_leafByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_leafByte

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.entry_selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_selected

end SigGolfCandidate.SphincsMaskedSignForestEntry
