import SigGolfCandidate.SphincsMaskedKeygenCommitment
import SigGolfCandidate.SphincsMaskedMacRestoration

namespace SigGolfCandidate.SphincsMaskedMaskCode
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def initSchedule : List (Word × Instr) := [
  (0x1a18, .ADDI .x6 .x0 (0)),
  (0x1a1c, .LUI .x28 67),
  (0x1a20, .ADDI .x28 .x28 (0)),
  (0x1a24, .SD .x28 .x6 (0)),
  (0x1a28, .ADDI .x6 .x0 (0)),
  (0x1a2c, .LUI .x28 67),
  (0x1a30, .ADDI .x28 .x28 (8)),
  (0x1a34, .SD .x28 .x6 (0)),
  (0x1a38, .ADDI .x6 .x0 (0)),
  (0x1a3c, .LUI .x28 67),
  (0x1a40, .ADDI .x28 .x28 (16)),
  (0x1a44, .SD .x28 .x6 (0)),
  (0x1a48, .ADDI .x6 .x0 (0)),
  (0x1a4c, .LUI .x28 67),
  (0x1a50, .ADDI .x28 .x28 (24)),
  (0x1a54, .SD .x28 .x6 (0)),
  (0x1a58, .ADDI .x6 .x0 (0)),
  (0x1a5c, .LUI .x28 67),
  (0x1a60, .ADDI .x28 .x28 (208)),
  (0x1a64, .SD .x28 .x6 (0)),
  (0x1a68, .ADDI .x6 .x0 (136)),
  (0x1a6c, .LUI .x28 67),
  (0x1a70, .ADDI .x28 .x28 (216)),
  (0x1a74, .SD .x28 .x6 (0))]

def init (s : MachineState) : MachineState := runSchedule initSchedule s

theorem init_code : ∀ e ∈ initSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem init_checked (s : MachineState) (pc : s.pc = 0x1a18) : Checked initSchedule s := by
  simp [initSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem init_block (s : MachineState) (pc : s.pc = 0x1a18) :
    OrdinarySteps SphincsMaskedImages.keygen s 24 (init s) :=
  checked_sound _ initSchedule init_code s (init_checked s pc)

theorem init_pc (s : MachineState) (pc : s.pc = 0x1a18) :
    (init s).pc = 0x1a78 := by
  simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def prepareSchedule : List (Word × Instr) := [
  (0x1a78, .LUI .x28 67),
  (0x1a7c, .ADDI .x28 .x28 (208)),
  (0x1a80, .LD .x6 .x28 (0)),
  (0x1a84, .LUI .x28 67),
  (0x1a88, .ADDI .x28 .x28 (16)),
  (0x1a8c, .SD .x28 .x6 (0)),
  (0x1a90, .ADDI .x6 .x0 (32)),
  (0x1a94, .LUI .x7 64),
  (0x1a98, .ADDI .x7 .x7 (40)),
  (0x1a9c, .ADDI .x10 .x0 (4)),
  (0x1aa0, .LD .x11 .x6 (0)),
  (0x1aa4, .SD .x7 .x11 (0)),
  (0x1aa8, .ADDI .x6 .x6 (8)),
  (0x1aac, .ADDI .x7 .x7 (8)),
  (0x1ab0, .ADDI .x10 .x10 (-1)),
  (0x1ab4, .BNE .x10 .x0 (-20)),
  (0x1aa0, .LD .x11 .x6 (0)),
  (0x1aa4, .SD .x7 .x11 (0)),
  (0x1aa8, .ADDI .x6 .x6 (8)),
  (0x1aac, .ADDI .x7 .x7 (8)),
  (0x1ab0, .ADDI .x10 .x10 (-1)),
  (0x1ab4, .BNE .x10 .x0 (-20)),
  (0x1aa0, .LD .x11 .x6 (0)),
  (0x1aa4, .SD .x7 .x11 (0)),
  (0x1aa8, .ADDI .x6 .x6 (8)),
  (0x1aac, .ADDI .x7 .x7 (8)),
  (0x1ab0, .ADDI .x10 .x10 (-1)),
  (0x1ab4, .BNE .x10 .x0 (-20)),
  (0x1aa0, .LD .x11 .x6 (0)),
  (0x1aa4, .SD .x7 .x11 (0)),
  (0x1aa8, .ADDI .x6 .x6 (8)),
  (0x1aac, .ADDI .x7 .x7 (8)),
  (0x1ab0, .ADDI .x10 .x10 (-1)),
  (0x1ab4, .BNE .x10 .x0 (-20)),
  (0x1ab8, .LUI .x6 1),
  (0x1abc, .ADDI .x6 .x6 (-511)),
  (0x1ac0, .LUI .x28 67),
  (0x1ac4, .ADDI .x28 .x28 (0)),
  (0x1ac8, .LD .x7 .x28 (0)),
  (0x1acc, .SLLI .x7 .x7 (16)),
  (0x1ad0, .ADD .x6 .x6 .x7),
  (0x1ad4, .LUI .x7 64),
  (0x1ad8, .ADDI .x7 .x7 (0)),
  (0x1adc, .SW .x7 .x6 (0)),
  (0x1ae0, .LUI .x28 67),
  (0x1ae4, .ADDI .x28 .x28 (16)),
  (0x1ae8, .LD .x6 .x28 (0)),
  (0x1aec, .SW .x7 .x6 (4)),
  (0x1af0, .LUI .x28 67),
  (0x1af4, .ADDI .x28 .x28 (8)),
  (0x1af8, .LD .x6 .x28 (0)),
  (0x1afc, .SD .x7 .x6 (8)),
  (0x1b00, .LUI .x28 67),
  (0x1b04, .ADDI .x28 .x28 (24)),
  (0x1b08, .LD .x6 .x28 (0)),
  (0x1b0c, .SW .x7 .x6 (16)),
  (0x1b10, .ADDI .x6 .x0 (116)),
  (0x1b14, .LUI .x7 64),
  (0x1b18, .ADDI .x7 .x7 (20)),
  (0x1b1c, .LWU .x13 .x6 (0)),
  (0x1b20, .SW .x7 .x13 (0)),
  (0x1b24, .LWU .x13 .x6 (4)),
  (0x1b28, .SW .x7 .x13 (4)),
  (0x1b2c, .LWU .x13 .x6 (8)),
  (0x1b30, .SW .x7 .x13 (8)),
  (0x1b34, .LWU .x13 .x6 (12)),
  (0x1b38, .SW .x7 .x13 (12)),
  (0x1b3c, .LWU .x13 .x6 (16)),
  (0x1b40, .SW .x7 .x13 (16)),
  (0x1b44, .LUI .x10 64),
  (0x1b48, .ADDI .x10 .x10 (0)),
  (0x1b4c, .ADDI .x11 .x0 (576)),
  (0x1b50, .LUI .x12 66),
  (0x1b54, .ADDI .x12 .x12 (0)),
  (0x1b58, .ADDI .x5 .x0 (1))]

def prepare (s : MachineState) : MachineState := runSchedule prepareSchedule s

theorem prepare_code : ∀ e ∈ prepareSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem prepare_checked (s : MachineState) (pc : s.pc = 0x1a78) : Checked prepareSchedule s := by
  simp [prepareSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem prepare_block (s : MachineState) (pc : s.pc = 0x1a78) :
    OrdinarySteps SphincsMaskedImages.keygen s 75 (prepare s) :=
  checked_sound _ prepareSchedule prepare_code s (prepare_checked s pc)

theorem prepare_pc (s : MachineState) (pc : s.pc = 0x1a78) :
    (prepare s).pc = 0x1b5c := by
  simp [prepare,runSchedule,prepareSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def xorSetupSchedule : List (Word × Instr) := [
  (0x1b60, .LUI .x28 67),
  (0x1b64, .ADDI .x28 .x28 (216)),
  (0x1b68, .LD .x6 .x28 (0)),
  (0x1b6c, .LUI .x12 66),
  (0x1b70, .ADDI .x12 .x12 (0))]

def xorSetup (s : MachineState) : MachineState := runSchedule xorSetupSchedule s

theorem xorSetup_code : ∀ e ∈ xorSetupSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem xorSetup_checked (s : MachineState) (pc : s.pc = 0x1b60) : Checked xorSetupSchedule s := by
  simp [xorSetupSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem xorSetup_block (s : MachineState) (pc : s.pc = 0x1b60) :
    OrdinarySteps SphincsMaskedImages.keygen s 5 (xorSetup s) :=
  checked_sound _ xorSetupSchedule xorSetup_code s (xorSetup_checked s pc)

theorem xorSetup_pc (s : MachineState) (pc : s.pc = 0x1b60) :
    (xorSetup s).pc = 0x1b74 := by
  simp [xorSetup,runSchedule,xorSetupSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def xorSchedule : List (Word × Instr) := [
  (0x1b74, .LWU .x13 .x6 (0)),
  (0x1b78, .LWU .x14 .x12 (0)),
  (0x1b7c, .XOR .x15 .x13 .x14),
  (0x1b80, .SW .x6 .x15 (0)),
  (0x1b84, .LWU .x13 .x6 (4)),
  (0x1b88, .LWU .x14 .x12 (4)),
  (0x1b8c, .XOR .x15 .x13 .x14),
  (0x1b90, .SW .x6 .x15 (4)),
  (0x1b94, .LWU .x13 .x6 (8)),
  (0x1b98, .LWU .x14 .x12 (8)),
  (0x1b9c, .XOR .x15 .x13 .x14),
  (0x1ba0, .SW .x6 .x15 (8)),
  (0x1ba4, .LWU .x13 .x6 (12)),
  (0x1ba8, .LWU .x14 .x12 (12)),
  (0x1bac, .XOR .x15 .x13 .x14),
  (0x1bb0, .SW .x6 .x15 (12)),
  (0x1bb4, .LWU .x13 .x6 (16)),
  (0x1bb8, .LWU .x14 .x12 (16)),
  (0x1bbc, .XOR .x15 .x13 .x14),
  (0x1bc0, .SW .x6 .x15 (16))]

def applyXor (s : MachineState) : MachineState := runSchedule xorSchedule s

theorem xor_code : ∀ e ∈ xorSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

def finishSchedule : List (Word × Instr) := [
  (0x1bc4, .LUI .x28 67),
  (0x1bc8, .ADDI .x28 .x28 (208)),
  (0x1bcc, .LD .x6 .x28 (0)),
  (0x1bd0, .ADDI .x6 .x6 (1)),
  (0x1bd4, .LUI .x28 67),
  (0x1bd8, .ADDI .x28 .x28 (208)),
  (0x1bdc, .SD .x28 .x6 (0)),
  (0x1be0, .LUI .x28 67),
  (0x1be4, .ADDI .x28 .x28 (216)),
  (0x1be8, .LD .x6 .x28 (0)),
  (0x1bec, .ADDI .x6 .x6 (20)),
  (0x1bf0, .LUI .x28 67),
  (0x1bf4, .ADDI .x28 .x28 (216)),
  (0x1bf8, .SD .x28 .x6 (0)),
  (0x1bfc, .LUI .x28 67),
  (0x1c00, .ADDI .x28 .x28 (208)),
  (0x1c04, .LD .x6 .x28 (0)),
  (0x1c08, .LUI .x7 1),
  (0x1c0c, .ADDI .x7 .x7 (-1)),
  (0x1c10, .BNE .x6 .x7 (-408))]

def finish (s : MachineState) : MachineState := runSchedule finishSchedule s

theorem finish_code : ∀ e ∈ finishSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem finish_checked (s : MachineState) (pc : s.pc = 0x1bc4) : Checked finishSchedule s := by
  simp [finishSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem finish_block (s : MachineState) (pc : s.pc = 0x1bc4) :
    OrdinarySteps SphincsMaskedImages.keygen s 20 (finish s) :=
  checked_sound _ finishSchedule finish_code s (finish_checked s pc)

def rootCopySchedule : List (Word × Instr) := [
  (0x1c14, .LUI .x6 20),
  (0x1c18, .ADDI .x6 .x6 (96)),
  (0x1c1c, .ADDI .x7 .x0 (96)),
  (0x1c20, .LWU .x13 .x6 (0)),
  (0x1c24, .SW .x7 .x13 (0)),
  (0x1c28, .LWU .x13 .x6 (4)),
  (0x1c2c, .SW .x7 .x13 (4)),
  (0x1c30, .LWU .x13 .x6 (8)),
  (0x1c34, .SW .x7 .x13 (8)),
  (0x1c38, .LWU .x13 .x6 (12)),
  (0x1c3c, .SW .x7 .x13 (12)),
  (0x1c40, .LWU .x13 .x6 (16)),
  (0x1c44, .SW .x7 .x13 (16))]

def rootCopy (s : MachineState) : MachineState := runSchedule rootCopySchedule s

theorem rootCopy_code : ∀ e ∈ rootCopySchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem rootCopy_checked (s : MachineState) (pc : s.pc = 0x1c14) : Checked rootCopySchedule s := by
  simp [rootCopySchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem rootCopy_block (s : MachineState) (pc : s.pc = 0x1c14) :
    OrdinarySteps SphincsMaskedImages.keygen s 13 (rootCopy s) :=
  checked_sound _ rootCopySchedule rootCopy_code s (rootCopy_checked s pc)

theorem rootCopy_pc (s : MachineState) (pc : s.pc = 0x1c14) :
    (rootCopy s).pc = 0x1c48 := by
  simp [rootCopy,runSchedule,rootCopySchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def tagCopySchedule : List (Word × Instr) := [
  (0x1dd0, .LUI .x6 132),
  (0x1dd4, .ADDI .x6 .x6 (0)),
  (0x1dd8, .LUI .x7 32),
  (0x1ddc, .ADDI .x7 .x7 (76)),
  (0x1de0, .LWU .x13 .x6 (0)),
  (0x1de4, .SW .x7 .x13 (0)),
  (0x1de8, .LWU .x13 .x6 (4)),
  (0x1dec, .SW .x7 .x13 (4)),
  (0x1df0, .LWU .x13 .x6 (8)),
  (0x1df4, .SW .x7 .x13 (8)),
  (0x1df8, .LWU .x13 .x6 (12)),
  (0x1dfc, .SW .x7 .x13 (12)),
  (0x1e00, .LWU .x13 .x6 (16)),
  (0x1e04, .SW .x7 .x13 (16))]

def tagCopy (s : MachineState) : MachineState := runSchedule tagCopySchedule s

theorem tagCopy_code : ∀ e ∈ tagCopySchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem tagCopy_checked (s : MachineState) (pc : s.pc = 0x1dd0) : Checked tagCopySchedule s := by
  simp [tagCopySchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem tagCopy_block (s : MachineState) (pc : s.pc = 0x1dd0) :
    OrdinarySteps SphincsMaskedImages.keygen s 14 (tagCopy s) :=
  checked_sound _ tagCopySchedule tagCopy_code s (tagCopy_checked s pc)

theorem tagCopy_pc (s : MachineState) (pc : s.pc = 0x1dd0) :
    (tagCopy s).pc = 0x1e08 := by
  simp [tagCopy,runSchedule,tagCopySchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def haltPrepareSchedule : List (Word × Instr) := [
  (0x1e08, .ADDI .x5 .x0 (0)),
  (0x1e0c, .ADDI .x10 .x0 (1))]

def haltPrepare (s : MachineState) : MachineState := runSchedule haltPrepareSchedule s

theorem haltPrepare_code : ∀ e ∈ haltPrepareSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem haltPrepare_checked (s : MachineState) (pc : s.pc = 0x1e08) : Checked haltPrepareSchedule s := by
  simp [haltPrepareSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem haltPrepare_block (s : MachineState) (pc : s.pc = 0x1e08) :
    OrdinarySteps SphincsMaskedImages.keygen s 2 (haltPrepare s) :=
  checked_sound _ haltPrepareSchedule haltPrepare_code s (haltPrepare_checked s pc)

theorem haltPrepare_pc (s : MachineState) (pc : s.pc = 0x1e08) :
    (haltPrepare s).pc = 0x1e10 := by
  simp [haltPrepare,runSchedule,haltPrepareSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

/-- info: 'SigGolfCandidate.SphincsMaskedMaskCode.prepare_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prepare_block

end SigGolfCandidate.SphincsMaskedMaskCode
