import SigGolfCandidate.SphincsMaskedSignTagFrame
import SigGolfCandidate.SphincsMaskedMaskNode

namespace SigGolfCandidate.SphincsMaskedSignRootPad
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The signer selects the top-tree root pad, node 4094. -/
def initSchedule : List (Word × Instr) := [
  (0x132c, .ADDI .x6 .x0 0),
  (0x1330, .LUI .x28 67),
  (0x1334, .ADDI .x28 .x28 0),
  (0x1338, .SD .x28 .x6 0),
  (0x133c, .ADDI .x6 .x0 0),
  (0x1340, .LUI .x28 67),
  (0x1344, .ADDI .x28 .x28 8),
  (0x1348, .SD .x28 .x6 0),
  (0x134c, .LUI .x6 1),
  (0x1350, .ADDI .x6 .x6 (-2)),
  (0x1354, .LUI .x28 67),
  (0x1358, .ADDI .x28 .x28 16),
  (0x135c, .SD .x28 .x6 0),
  (0x1360, .ADDI .x6 .x0 0),
  (0x1364, .LUI .x28 67),
  (0x1368, .ADDI .x28 .x28 24),
  (0x136c, .SD .x28 .x6 0)]

def init (s : MachineState) : MachineState := runSchedule initSchedule s

theorem init_code : ∀ e ∈ initSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem init_checked (s : MachineState) (pc : s.pc = 0x132c) :
    Checked initSchedule s := by
  simp [initSchedule, Checked, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, signExtend13, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, MachineState.setWord32,
    MachineState.getWord32, alignToDword, byteOffset, pc]

theorem init_block (s : MachineState) (pc : s.pc = 0x132c) :
    OrdinarySteps SphincsMaskedImages.sign s 17 (init s) :=
  checked_sound _ initSchedule init_code s (init_checked s pc)

theorem init_pc (s : MachineState) (pc : s.pc = 0x132c) :
    (init s).pc = 0x1370 := by
  simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
    signExtend13,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def padSchedule : List (Word × Instr) :=
  (SphincsMaskedMaskCode.prepareSchedule.drop 6).map fun e => (e.1 - 0x720, e.2)

def padPrepare (s : MachineState) : MachineState := runSchedule padSchedule s

theorem pad_code : ∀ e ∈ padSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem pad_checked (s : MachineState) (pc : s.pc = 0x1370) :
    Checked padSchedule s := by
  simp [padSchedule,SphincsMaskedMaskCode.prepareSchedule,Checked,
    execInstrBr,ordinaryStep,memoryArgumentsValid,accessValid,rangeValid,
    MEMORY_BYTES,signExtend12,signExtend13,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.setWord32,
    MachineState.getWord32,alignToDword,byteOffset,pc]

theorem pad_block (s : MachineState) (pc : s.pc = 0x1370) :
    OrdinarySteps SphincsMaskedImages.sign s 69 (padPrepare s) := by
  exact checked_sound _ padSchedule pad_code s (pad_checked s pc)

theorem pad_pc (s : MachineState) (pc : s.pc = 0x1370) :
    (padPrepare s).pc = 0x143c := by
  simp [padPrepare,runSchedule,padSchedule,
    SphincsMaskedMaskCode.prepareSchedule,
    execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem pad_registers (s : MachineState) :
    (padPrepare s).getReg .x10 = 0x40000 ∧
    (padPrepare s).getReg .x11 = 576 ∧
    (padPrepare s).getReg .x12 = 0x42000 ∧
    (padPrepare s).getReg .x5 = 1 := by
  simp [padPrepare,runSchedule,padSchedule,
    SphincsMaskedMaskCode.prepareSchedule,execInstrBr,signExtend12,
    signExtend13,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.setWord32,
    MachineState.getWord32,alignToDword,byteOffset]


def padAnswer (hash : Hash) (s : MachineState) : MachineState :=
  writeHash (padPrepare s) (hash (hashInput (padPrepare s)))

theorem pad_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x1370) :
    Trace hash SphincsMaskedImages.sign s 70 85 1 2 (padAnswer hash s) := by
  obtain ⟨src,bits,dst,service⟩ := pad_registers s
  have fetch : fetch SphincsMaskedImages.sign (padPrepare s) =
      some (.base .ECALL) := by
    rw [fetch_at,pad_pc s pc]
    decide
  have valid : hashArgumentsValid (padPrepare s) = true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (padPrepare s)).1 = 576 := by simp [hashInput,bits]
  have h := Trace.hash (hash := hash) (image := SphincsMaskedImages.sign)
    (padPrepare s) _ 0 0 0 0 fetch service valid (Trace.refl _)
  have hs : Trace hash SphincsMaskedImages.sign (padPrepare s)
      1 16 1 2 (padAnswer hash s) := by
    simp only [len] at h
    exact h
  exact (pad_block s pc).trace.trans hs

theorem init_pad_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x132c) :
    Trace hash SphincsMaskedImages.sign s 87 102 1 2
      (padAnswer hash (init s)) := by
  exact (init_block s pc).trace.trans (pad_trace hash (init s) (init_pc s pc))

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootPad.init_pad_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms init_pad_trace

end SigGolfCandidate.SphincsMaskedSignRootPad
