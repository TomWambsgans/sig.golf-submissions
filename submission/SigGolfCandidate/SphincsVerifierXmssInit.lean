import SigGolfCandidate.SphincsVerifierWotsLeafResult

namespace SigGolfCandidate.SphincsVerifierXmssInit
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def xmssInitSchedule : List (Word × Instr) := [
  (0x2aac, .LUI .x28 67), (0x2ab0, .ADDI .x28 .x28 32),
  (0x2ab4, .LD .x6 .x28 0),
  (0x2ab8, .LUI .x28 67), (0x2abc, .ADDI .x28 .x28 112),
  (0x2ac0, .SD .x28 .x6 0),
  (0x2ac4, .ADDI .x6 .x0 1),
  (0x2ac8, .LUI .x28 67), (0x2acc, .ADDI .x28 .x28 72),
  (0x2ad0, .SD .x28 .x6 0)]

theorem xmssInit_code : ∀ entry ∈ xmssInitSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by decide

def xmssInitState (s : MachineState) : MachineState := runSchedule xmssInitSchedule s

theorem xmssInit_checked (s : MachineState) (pc : s.pc = 0x2aac) :
    Checked xmssInitSchedule s := by
  simp [Checked, xmssInitSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc]

theorem xmssInit_block (s : MachineState) (pc : s.pc = 0x2aac) :
    OrdinarySteps SphincsImages.verify s 10 (xmssInitState s) := by
  simpa only [xmssInitState, show xmssInitSchedule.length = 10 by decide]
    using checked_sound _ xmssInitSchedule xmssInit_code s (xmssInit_checked s pc)

theorem xmssInit_pc (s : MachineState) (pc : s.pc = 0x2aac) :
    (xmssInitState s).pc = 0x2ad4 := by
  simp [xmssInitState, xmssInitSchedule, runSchedule, execInstrBr, pc]

theorem xmssInit_bit (s : MachineState) :
    (xmssInitState s).getMem 0x43070 = s.getMem 0x43020 := by
  simp [xmssInitState, xmssInitSchedule, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem xmssInit_level (s : MachineState) :
    (xmssInitState s).getMem 0x43048 = 1 := by
  simp [xmssInitState, xmssInitSchedule, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem xmssInit_below_frame (s : MachineState) (read : Word)
    (below : read.toNat < 0x43048) :
    (xmssInitState s).getMem read = s.getMem read := by
  have hlevel : read ≠ (274504#64) := by
    intro h; subst read
    have impossible : ¬ ((274504#64).toNat < 0x43048) := by decide
    exact impossible below
  have hbit : read ≠ (274544#64) := by
    intro h; subst read
    have impossible : ¬ ((274544#64).toNat < 0x43048) := by decide
    exact impossible below
  simp [xmssInitState, xmssInitSchedule, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, hlevel, hbit]

theorem xmssInit_current (s : MachineState) (read : Word)
    (inside : 0x44a00 ≤ read.toNat ∧ read.toNat < 0x44a18) :
    (xmssInitState s).getMem read = s.getMem read := by
  have hlevel : read ≠ (274504#64) := by
    intro h; subst read
    have impossible : ¬ (0x44a00 ≤ (274504#64).toNat) := by decide
    exact impossible inside.1
  have hbit : read ≠ (274544#64) := by
    intro h; subst read
    have impossible : ¬ (0x44a00 ≤ (274544#64).toNat) := by decide
    exact impossible inside.1
  simp [xmssInitState, xmssInitSchedule, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, hlevel, hbit]

#print axioms xmssInit_block
#print axioms xmssInit_bit
#print axioms xmssInit_level

/-- info: 'SigGolfCandidate.SphincsVerifierXmssInit.xmssInit_below_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms xmssInit_below_frame

end SigGolfCandidate.SphincsVerifierXmssInit
