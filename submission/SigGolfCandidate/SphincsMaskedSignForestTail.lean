import SigGolfCandidate.SphincsMaskedSignForestParents

/-! Exact FORS root storage, selected-secret output, eight sibling copies,
next-tree transition, and final root combination in the masked sign image.
The local traces use only incoming control/address bounds. `forest_execution`
composes 24 trees under the explicit leaf+parent `BodyExecution` contract;
this module does not silently assume that missing body frame refinement.
-/

namespace SigGolfCandidate.SphincsMaskedSignForestTail
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy SphincsVerifierCopy SphincsVerifierCopyMemory
open SphincsVerifierMessageCopy SphincsVerifierFtsCopyAccess SphincsVerifierFtsPriorRoots
open SphincsVerifierFtsGenericCopyData SphincsMaskedChainDomain
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def rootSetupSchedule : List (Word × Instr) := [
  (0x22c0, .LUI .x28 67),
  (0x22c4, .ADDI .x28 .x28 104),
  (0x22c8, .LD .x6 .x28 0),
  (0x22cc, .LUI .x7 68),
  (0x22d0, .ADDI .x7 .x7 256),
  (0x22d4, .LUI .x28 67),
  (0x22d8, .ADDI .x28 .x28 64),
  (0x22dc, .LD .x10 .x28 0),
  (0x22e0, .SLLI .x12 .x10 2),
  (0x22e4, .SLLI .x11 .x10 4),
  (0x22e8, .ADD .x12 .x12 .x11),
  (0x22ec, .ADD .x7 .x7 .x12)]

def rootSetup (s : MachineState) : MachineState := runSchedule rootSetupSchedule s

theorem rootSetup_code : ∀ e ∈ rootSetupSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem rootSetup_checked (s : MachineState) (pc : s.pc = 0x22c0) :
    Checked rootSetupSchedule s := by
  simp [rootSetupSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem rootSetup_block (s : MachineState) (pc : s.pc = 0x22c0) :
    OrdinarySteps SphincsMaskedImages.sign s 12 (rootSetup s) :=
  checked_sound _ rootSetupSchedule rootSetup_code s (rootSetup_checked s pc)

theorem rootSetup_pc (s : MachineState) (pc : s.pc = 0x22c0) :
    (rootSetup s).pc = 0x22f0 := by
  simp [rootSetup, runSchedule, rootSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def secretSetupSchedule : List (Word × Instr) := [
  (0x2318, .ADDI .x6 .x0 0),
  (0x231c, .LUI .x28 67),
  (0x2320, .ADDI .x28 .x28 16),
  (0x2324, .SD .x28 .x6 0),
  (0x2328, .LUI .x28 67),
  (0x232c, .ADDI .x28 .x28 168),
  (0x2330, .LD .x6 .x28 0),
  (0x2334, .LUI .x28 67),
  (0x2338, .ADDI .x28 .x28 24),
  (0x233c, .SD .x28 .x6 0),
  (0x2340, .ADDI .x6 .x0 32),
  (0x2344, .LUI .x7 64),
  (0x2348, .ADDI .x7 .x7 40),
  (0x234c, .ADDI .x10 .x0 4)]

def secretSetup (s : MachineState) : MachineState := runSchedule secretSetupSchedule s

theorem secretSetup_code : ∀ e ∈ secretSetupSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem secretSetup_checked (s : MachineState) (pc : s.pc = 0x2318) :
    Checked secretSetupSchedule s := by
  simp [secretSetupSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem secretSetup_block (s : MachineState) (pc : s.pc = 0x2318) :
    OrdinarySteps SphincsMaskedImages.sign s 14 (secretSetup s) :=
  checked_sound _ secretSetupSchedule secretSetup_code s (secretSetup_checked s pc)

theorem secretSetup_pc (s : MachineState) (pc : s.pc = 0x2318) :
    (secretSetup s).pc = 0x2350 := by
  simp [secretSetup, runSchedule, secretSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def secretHeaderSchedule : List (Word × Instr) := [
  (0x2368, .LUI .x6 1),
  (0x236c, .ADDI .x6 .x6 (-2047)),
  (0x2370, .LUI .x28 67),
  (0x2374, .ADDI .x28 .x28 0),
  (0x2378, .LD .x7 .x28 0),
  (0x237c, .SLLI .x7 .x7 16),
  (0x2380, .ADD .x6 .x6 .x7),
  (0x2384, .LUI .x7 64),
  (0x2388, .ADDI .x7 .x7 0),
  (0x238c, .SW .x7 .x6 0),
  (0x2390, .LUI .x28 67),
  (0x2394, .ADDI .x28 .x28 16),
  (0x2398, .LD .x6 .x28 0),
  (0x239c, .SW .x7 .x6 4),
  (0x23a0, .LUI .x28 67),
  (0x23a4, .ADDI .x28 .x28 8),
  (0x23a8, .LD .x6 .x28 0),
  (0x23ac, .SD .x7 .x6 8),
  (0x23b0, .LUI .x28 67),
  (0x23b4, .ADDI .x28 .x28 24),
  (0x23b8, .LD .x6 .x28 0),
  (0x23bc, .SW .x7 .x6 16),
  (0x23c0, .ADDI .x6 .x0 116),
  (0x23c4, .LUI .x7 64),
  (0x23c8, .ADDI .x7 .x7 20),
  (0x23cc, .LWU .x13 .x6 0),
  (0x23d0, .SW .x7 .x13 0),
  (0x23d4, .LWU .x13 .x6 4),
  (0x23d8, .SW .x7 .x13 4),
  (0x23dc, .LWU .x13 .x6 8),
  (0x23e0, .SW .x7 .x13 8),
  (0x23e4, .LWU .x13 .x6 12),
  (0x23e8, .SW .x7 .x13 12),
  (0x23ec, .LWU .x13 .x6 16),
  (0x23f0, .SW .x7 .x13 16),
  (0x23f4, .LUI .x10 64),
  (0x23f8, .ADDI .x10 .x10 0),
  (0x23fc, .ADDI .x11 .x0 576),
  (0x2400, .LUI .x12 66),
  (0x2404, .ADDI .x12 .x12 0),
  (0x2408, .ADDI .x5 .x0 1)]

def secretHeader (s : MachineState) : MachineState := runSchedule secretHeaderSchedule s

theorem secretHeader_code : ∀ e ∈ secretHeaderSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem secretHeader_checked (s : MachineState) (pc : s.pc = 0x2368) :
    Checked secretHeaderSchedule s := by
  simp [secretHeaderSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem secretHeader_block (s : MachineState) (pc : s.pc = 0x2368) :
    OrdinarySteps SphincsMaskedImages.sign s 41 (secretHeader s) :=
  checked_sound _ secretHeaderSchedule secretHeader_code s (secretHeader_checked s pc)

theorem secretHeader_pc (s : MachineState) (pc : s.pc = 0x2368) :
    (secretHeader s).pc = 0x240c := by
  simp [secretHeader, runSchedule, secretHeaderSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def signatureSetupSchedule : List (Word × Instr) := [
  (0x2410, .LUI .x6 66),
  (0x2414, .ADDI .x6 .x6 0),
  (0x2418, .LUI .x28 67),
  (0x241c, .ADDI .x28 .x28 160),
  (0x2420, .LD .x7 .x28 0)]

def signatureSetup (s : MachineState) : MachineState := runSchedule signatureSetupSchedule s

theorem signatureSetup_code : ∀ e ∈ signatureSetupSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem signatureSetup_checked (s : MachineState) (pc : s.pc = 0x2410) :
    Checked signatureSetupSchedule s := by
  simp [signatureSetupSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem signatureSetup_block (s : MachineState) (pc : s.pc = 0x2410) :
    OrdinarySteps SphincsMaskedImages.sign s 5 (signatureSetup s) :=
  checked_sound _ signatureSetupSchedule signatureSetup_code s (signatureSetup_checked s pc)

theorem signatureSetup_pc (s : MachineState) (pc : s.pc = 0x2410) :
    (signatureSetup s).pc = 0x2424 := by
  simp [signatureSetup, runSchedule, signatureSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def signatureAdvanceSchedule : List (Word × Instr) := [
  (0x244c, .LUI .x28 67),
  (0x2450, .ADDI .x28 .x28 160),
  (0x2454, .LD .x6 .x28 0),
  (0x2458, .ADDI .x6 .x6 20),
  (0x245c, .LUI .x28 67),
  (0x2460, .ADDI .x28 .x28 160),
  (0x2464, .SD .x28 .x6 0)]

def signatureAdvance (s : MachineState) : MachineState := runSchedule signatureAdvanceSchedule s

theorem signatureAdvance_code : ∀ e ∈ signatureAdvanceSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem signatureAdvance_checked (s : MachineState) (pc : s.pc = 0x244c) :
    Checked signatureAdvanceSchedule s := by
  simp [signatureAdvanceSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem signatureAdvance_block (s : MachineState) (pc : s.pc = 0x244c) :
    OrdinarySteps SphincsMaskedImages.sign s 7 (signatureAdvance s) :=
  checked_sound _ signatureAdvanceSchedule signatureAdvance_code s (signatureAdvance_checked s pc)

theorem signatureAdvance_pc (s : MachineState) (pc : s.pc = 0x244c) :
    (signatureAdvance s).pc = 0x2468 := by
  simp [signatureAdvance, runSchedule, signatureAdvanceSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def pathInitSchedule : List (Word × Instr) := [
  (0x2468, .LUI .x6 80),
  (0x246c, .ADDI .x6 .x6 0),
  (0x2470, .LUI .x28 67),
  (0x2474, .ADDI .x28 .x28 192),
  (0x2478, .SD .x28 .x6 0),
  (0x247c, .ADDI .x6 .x0 256),
  (0x2480, .LUI .x28 67),
  (0x2484, .ADDI .x28 .x28 144),
  (0x2488, .SD .x28 .x6 0),
  (0x248c, .ADDI .x6 .x0 0),
  (0x2490, .LUI .x28 67),
  (0x2494, .ADDI .x28 .x28 72),
  (0x2498, .SD .x28 .x6 0),
  (0x249c, .LUI .x28 67),
  (0x24a0, .ADDI .x28 .x28 168),
  (0x24a4, .LD .x6 .x28 0),
  (0x24a8, .LUI .x28 67),
  (0x24ac, .ADDI .x28 .x28 112),
  (0x24b0, .SD .x28 .x6 0)]

def pathInit (s : MachineState) : MachineState := runSchedule pathInitSchedule s

theorem pathInit_code : ∀ e ∈ pathInitSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem pathInit_checked (s : MachineState) (pc : s.pc = 0x2468) :
    Checked pathInitSchedule s := by
  simp [pathInitSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem pathInit_block (s : MachineState) (pc : s.pc = 0x2468) :
    OrdinarySteps SphincsMaskedImages.sign s 19 (pathInit s) :=
  checked_sound _ pathInitSchedule pathInit_code s (pathInit_checked s pc)

theorem pathInit_pc (s : MachineState) (pc : s.pc = 0x2468) :
    (pathInit s).pc = 0x24b4 := by
  simp [pathInit, runSchedule, pathInitSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def pathSetupSchedule : List (Word × Instr) := [
  (0x24b4, .LUI .x28 67),
  (0x24b8, .ADDI .x28 .x28 112),
  (0x24bc, .LD .x6 .x28 0),
  (0x24c0, .XORI .x6 .x6 1),
  (0x24c4, .SLLI .x10 .x6 2),
  (0x24c8, .SLLI .x11 .x6 4),
  (0x24cc, .ADD .x10 .x10 .x11),
  (0x24d0, .LUI .x28 67),
  (0x24d4, .ADDI .x28 .x28 192),
  (0x24d8, .LD .x6 .x28 0),
  (0x24dc, .ADD .x6 .x6 .x10),
  (0x24e0, .LUI .x28 67),
  (0x24e4, .ADDI .x28 .x28 160),
  (0x24e8, .LD .x7 .x28 0)]

def pathSetup (s : MachineState) : MachineState := runSchedule pathSetupSchedule s

theorem pathSetup_code : ∀ e ∈ pathSetupSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem pathSetup_checked (s : MachineState) (pc : s.pc = 0x24b4) :
    Checked pathSetupSchedule s := by
  simp [pathSetupSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem pathSetup_block (s : MachineState) (pc : s.pc = 0x24b4) :
    OrdinarySteps SphincsMaskedImages.sign s 14 (pathSetup s) :=
  checked_sound _ pathSetupSchedule pathSetup_code s (pathSetup_checked s pc)

theorem pathSetup_pc (s : MachineState) (pc : s.pc = 0x24b4) :
    (pathSetup s).pc = 0x24ec := by
  simp [pathSetup, runSchedule, pathSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def pathFinishSchedule : List (Word × Instr) := [
  (0x2514, .LUI .x28 67),
  (0x2518, .ADDI .x28 .x28 160),
  (0x251c, .LD .x6 .x28 0),
  (0x2520, .ADDI .x6 .x6 20),
  (0x2524, .LUI .x28 67),
  (0x2528, .ADDI .x28 .x28 160),
  (0x252c, .SD .x28 .x6 0),
  (0x2530, .LUI .x28 67),
  (0x2534, .ADDI .x28 .x28 192),
  (0x2538, .LD .x6 .x28 0),
  (0x253c, .LUI .x28 67),
  (0x2540, .ADDI .x28 .x28 144),
  (0x2544, .LD .x7 .x28 0),
  (0x2548, .SLLI .x10 .x7 2),
  (0x254c, .SLLI .x11 .x7 4),
  (0x2550, .ADD .x10 .x10 .x11),
  (0x2554, .ADD .x6 .x6 .x10),
  (0x2558, .LUI .x28 67),
  (0x255c, .ADDI .x28 .x28 192),
  (0x2560, .SD .x28 .x6 0),
  (0x2564, .LUI .x28 67),
  (0x2568, .ADDI .x28 .x28 144),
  (0x256c, .LD .x6 .x28 0),
  (0x2570, .SRLI .x6 .x6 1),
  (0x2574, .LUI .x28 67),
  (0x2578, .ADDI .x28 .x28 144),
  (0x257c, .SD .x28 .x6 0),
  (0x2580, .LUI .x28 67),
  (0x2584, .ADDI .x28 .x28 112),
  (0x2588, .LD .x6 .x28 0),
  (0x258c, .SRLI .x6 .x6 1),
  (0x2590, .LUI .x28 67),
  (0x2594, .ADDI .x28 .x28 112),
  (0x2598, .SD .x28 .x6 0),
  (0x259c, .LUI .x28 67),
  (0x25a0, .ADDI .x28 .x28 72),
  (0x25a4, .LD .x6 .x28 0),
  (0x25a8, .ADDI .x6 .x6 1),
  (0x25ac, .LUI .x28 67),
  (0x25b0, .ADDI .x28 .x28 72),
  (0x25b4, .SD .x28 .x6 0),
  (0x25b8, .LUI .x28 67),
  (0x25bc, .ADDI .x28 .x28 72),
  (0x25c0, .LD .x6 .x28 0),
  (0x25c4, .ADDI .x7 .x0 8),
  (0x25c8, .BNE .x6 .x7 (-276))]

def pathFinish (s : MachineState) : MachineState := runSchedule pathFinishSchedule s

theorem pathFinish_code : ∀ e ∈ pathFinishSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem pathFinish_checked (s : MachineState) (pc : s.pc = 0x2514) :
    Checked pathFinishSchedule s := by
  simp [pathFinishSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem pathFinish_block (s : MachineState) (pc : s.pc = 0x2514) :
    OrdinarySteps SphincsMaskedImages.sign s 46 (pathFinish s) :=
  checked_sound _ pathFinishSchedule pathFinish_code s (pathFinish_checked s pc)

def treeFinishSchedule : List (Word × Instr) := [
  (0x25cc, .LUI .x28 67),
  (0x25d0, .ADDI .x28 .x28 64),
  (0x25d4, .LD .x6 .x28 0),
  (0x25d8, .ADDI .x6 .x6 1),
  (0x25dc, .LUI .x28 67),
  (0x25e0, .ADDI .x28 .x28 64),
  (0x25e4, .SD .x28 .x6 0),
  (0x25e8, .LUI .x28 67),
  (0x25ec, .ADDI .x28 .x28 64),
  (0x25f0, .LD .x6 .x28 0),
  (0x25f4, .ADDI .x7 .x0 24),
  (0x25f8, .BNE .x6 .x7 (-2316))]

def treeFinish (s : MachineState) : MachineState := runSchedule treeFinishSchedule s

theorem treeFinish_code : ∀ e ∈ treeFinishSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem treeFinish_checked (s : MachineState) (pc : s.pc = 0x25cc) :
    Checked treeFinishSchedule s := by
  simp [treeFinishSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem treeFinish_block (s : MachineState) (pc : s.pc = 0x25cc) :
    OrdinarySteps SphincsMaskedImages.sign s 12 (treeFinish s) :=
  checked_sound _ treeFinishSchedule treeFinish_code s (treeFinish_checked s pc)

def combineSetupSchedule : List (Word × Instr) := [
  (0x25fc, .ADDI .x6 .x0 0),
  (0x2600, .LUI .x28 67),
  (0x2604, .ADDI .x28 .x28 0),
  (0x2608, .SD .x28 .x6 0),
  (0x260c, .ADDI .x6 .x0 0),
  (0x2610, .LUI .x28 67),
  (0x2614, .ADDI .x28 .x28 8),
  (0x2618, .SD .x28 .x6 0),
  (0x261c, .ADDI .x6 .x0 0),
  (0x2620, .LUI .x28 67),
  (0x2624, .ADDI .x28 .x28 16),
  (0x2628, .SD .x28 .x6 0),
  (0x262c, .ADDI .x6 .x0 0),
  (0x2630, .LUI .x28 67),
  (0x2634, .ADDI .x28 .x28 24),
  (0x2638, .SD .x28 .x6 0),
  (0x263c, .LUI .x28 67),
  (0x2640, .ADDI .x28 .x28 120),
  (0x2644, .LD .x6 .x28 0),
  (0x2648, .LUI .x28 67),
  (0x264c, .ADDI .x28 .x28 8),
  (0x2650, .SD .x28 .x6 0),
  (0x2654, .LUI .x6 68),
  (0x2658, .ADDI .x6 .x6 256),
  (0x265c, .LUI .x7 64),
  (0x2660, .ADDI .x7 .x7 40),
  (0x2664, .ADDI .x10 .x0 60)]

def combineSetup (s : MachineState) : MachineState := runSchedule combineSetupSchedule s

theorem combineSetup_code : ∀ e ∈ combineSetupSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem combineSetup_checked (s : MachineState) (pc : s.pc = 0x25fc) :
    Checked combineSetupSchedule s := by
  simp [combineSetupSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem combineSetup_block (s : MachineState) (pc : s.pc = 0x25fc) :
    OrdinarySteps SphincsMaskedImages.sign s 27 (combineSetup s) :=
  checked_sound _ combineSetupSchedule combineSetup_code s (combineSetup_checked s pc)

theorem combineSetup_pc (s : MachineState) (pc : s.pc = 0x25fc) :
    (combineSetup s).pc = 0x2668 := by
  simp [combineSetup, runSchedule, combineSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def combineHeaderSchedule : List (Word × Instr) := [
  (0x2680, .LUI .x6 1),
  (0x2684, .ADDI .x6 .x6 (-1279)),
  (0x2688, .LUI .x28 67),
  (0x268c, .ADDI .x28 .x28 0),
  (0x2690, .LD .x7 .x28 0),
  (0x2694, .SLLI .x7 .x7 16),
  (0x2698, .ADD .x6 .x6 .x7),
  (0x269c, .LUI .x7 64),
  (0x26a0, .ADDI .x7 .x7 0),
  (0x26a4, .SW .x7 .x6 0),
  (0x26a8, .LUI .x28 67),
  (0x26ac, .ADDI .x28 .x28 16),
  (0x26b0, .LD .x6 .x28 0),
  (0x26b4, .SW .x7 .x6 4),
  (0x26b8, .LUI .x28 67),
  (0x26bc, .ADDI .x28 .x28 8),
  (0x26c0, .LD .x6 .x28 0),
  (0x26c4, .SD .x7 .x6 8),
  (0x26c8, .LUI .x28 67),
  (0x26cc, .ADDI .x28 .x28 24),
  (0x26d0, .LD .x6 .x28 0),
  (0x26d4, .SW .x7 .x6 16),
  (0x26d8, .ADDI .x6 .x0 116),
  (0x26dc, .LUI .x7 64),
  (0x26e0, .ADDI .x7 .x7 20),
  (0x26e4, .LWU .x13 .x6 0),
  (0x26e8, .SW .x7 .x13 0),
  (0x26ec, .LWU .x13 .x6 4),
  (0x26f0, .SW .x7 .x13 4),
  (0x26f4, .LWU .x13 .x6 8),
  (0x26f8, .SW .x7 .x13 8),
  (0x26fc, .LWU .x13 .x6 12),
  (0x2700, .SW .x7 .x13 12),
  (0x2704, .LWU .x13 .x6 16),
  (0x2708, .SW .x7 .x13 16),
  (0x270c, .LUI .x10 64),
  (0x2710, .ADDI .x10 .x10 0),
  (0x2714, .LUI .x11 1),
  (0x2718, .ADDI .x11 .x11 64),
  (0x271c, .LUI .x12 66),
  (0x2720, .ADDI .x12 .x12 0),
  (0x2724, .ADDI .x5 .x0 1)]

def combineHeader (s : MachineState) : MachineState := runSchedule combineHeaderSchedule s

theorem combineHeader_code : ∀ e ∈ combineHeaderSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem combineHeader_checked (s : MachineState) (pc : s.pc = 0x2680) :
    Checked combineHeaderSchedule s := by
  simp [combineHeaderSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem combineHeader_block (s : MachineState) (pc : s.pc = 0x2680) :
    OrdinarySteps SphincsMaskedImages.sign s 42 (combineHeader s) :=
  checked_sound _ combineHeaderSchedule combineHeader_code s (combineHeader_checked s pc)

theorem combineHeader_pc (s : MachineState) (pc : s.pc = 0x2680) :
    (combineHeader s).pc = 0x2728 := by
  simp [combineHeader, runSchedule, combineHeaderSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def combineStoreSchedule : List (Word × Instr) := [
  (0x272c, .LUI .x6 66),
  (0x2730, .ADDI .x6 .x6 0),
  (0x2734, .LUI .x7 69),
  (0x2738, .ADDI .x7 .x7 (-1536)),
  (0x273c, .LWU .x13 .x6 0),
  (0x2740, .SW .x7 .x13 0),
  (0x2744, .LWU .x13 .x6 4),
  (0x2748, .SW .x7 .x13 4),
  (0x274c, .LWU .x13 .x6 8),
  (0x2750, .SW .x7 .x13 8),
  (0x2754, .LWU .x13 .x6 12),
  (0x2758, .SW .x7 .x13 12),
  (0x275c, .LWU .x13 .x6 16),
  (0x2760, .SW .x7 .x13 16)]

def combineStore (s : MachineState) : MachineState := runSchedule combineStoreSchedule s

theorem combineStore_code : ∀ e ∈ combineStoreSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem combineStore_checked (s : MachineState) (pc : s.pc = 0x272c) :
    Checked combineStoreSchedule s := by
  simp [combineStoreSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem combineStore_block (s : MachineState) (pc : s.pc = 0x272c) :
    OrdinarySteps SphincsMaskedImages.sign s 14 (combineStore s) :=
  checked_sound _ combineStoreSchedule combineStore_code s (combineStore_checked s pc)

theorem combineStore_pc (s : MachineState) (pc : s.pc = 0x272c) :
    (combineStore s).pc = 0x2764 := by
  simp [combineStore, runSchedule, combineStoreSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def treeInitSchedule : List (Word × Instr) := [
  (0x1cc8, .ADDI .x6 .x0 0),
  (0x1ccc, .LUI .x28 67),
  (0x1cd0, .ADDI .x28 .x28 64),
  (0x1cd4, .SD .x28 .x6 0),
  (0x1cd8, .LUI .x6 32),
  (0x1cdc, .ADDI .x6 .x6 156),
  (0x1ce0, .LUI .x28 67),
  (0x1ce4, .ADDI .x28 .x28 160),
  (0x1ce8, .SD .x28 .x6 0)]

def treeInit (s : MachineState) : MachineState := runSchedule treeInitSchedule s

theorem treeInit_code : ∀ e ∈ treeInitSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem treeInit_checked (s : MachineState) (pc : s.pc = 0x1cc8) :
    Checked treeInitSchedule s := by
  simp [treeInitSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem treeInit_block (s : MachineState) (pc : s.pc = 0x1cc8) :
    OrdinarySteps SphincsMaskedImages.sign s 9 (treeInit s) :=
  checked_sound _ treeInitSchedule treeInit_code s (treeInit_checked s pc)

theorem treeInit_pc (s : MachineState) (pc : s.pc = 0x1cc8) :
    (treeInit s).pc = 0x1cec := by
  simp [treeInit, runSchedule, treeInitSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def treeEntrySchedule : List (Word × Instr) := [
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

def treeEntry (s : MachineState) : MachineState := runSchedule treeEntrySchedule s

theorem treeEntry_code : ∀ e ∈ treeEntrySchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide


theorem combine_copy_code : CopyCode SphincsMaskedImages.sign 0x2668 := by decide

theorem combine_copyInvariant (s : MachineState) (pc : s.pc = 0x25fc) :
    CopyInvariant 0x2668 0x44100 0x40028 60 60 (combineSetup s) := by
  simp [CopyInvariant,combineSetup,runSchedule,combineSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem combine_registers (s : MachineState) :
    (combineHeader s).getReg .x10 = 0x40000 ∧ (combineHeader s).getReg .x11 = 4160 ∧
    (combineHeader s).getReg .x12 = 0x42000 ∧ (combineHeader s).getReg .x5 = 1 := by
  simp [combineHeader,runSchedule,combineHeaderSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

def combined (hash : Hash) (s : MachineState) :=
  writeHash (combineHeader s) (hash (hashInput (combineHeader s)))

theorem combine_hash (hash : Hash) (s : MachineState) (pc : s.pc = 0x2680) :
    Trace hash SphincsMaskedImages.sign s 43 114 1 9 (combined hash s) := by
  obtain ⟨src,bits,dst,service⟩ := combine_registers s
  have fetched : fetch SphincsMaskedImages.sign (combineHeader s) = some (.base .ECALL) := by
    rw [fetch_at,combineHeader_pc s pc];decide
  have valid : hashArgumentsValid (combineHeader s) = true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (combineHeader s)).1 = 4160 := by simp [hashInput,bits]
  have step := Trace.hash (hash := hash) (image := SphincsMaskedImages.sign)
    (combineHeader s) _ 0 0 0 0 fetched service valid (Trace.refl _)
  simp only [len] at step
  exact (combineHeader_block s pc).trace.trans step

theorem combined_pc (hash : Hash) (s : MachineState) (pc : s.pc = 0x2680) :
    (combined hash s).pc = 0x272c := by
  simp [combined,writeHash,combineHeader_pc s pc]

/-- Unconditional root-combination trace after the last FORS tree. -/
theorem combine_execution (hash : Hash) (s : MachineState) (pc : s.pc = 0x25fc) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 444 515 1 9 t ∧ t.pc = 0x2764 := by
  obtain ⟨copied,copyTrace,copyInv,_,_⟩ := copy_all SphincsMaskedImages.sign 0x2668 combine_copy_code
    0x44100 0x40028 60 (combineSetup s) (combine_copyInvariant s pc)
    (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))
  have copyPc : copied.pc = 0x2680 := by simpa [CopyInvariant] using copyInv.2.2.1
  refine ⟨combineStore (combined hash copied),?_,combineStore_pc _ (combined_pc hash copied copyPc)⟩
  exact (combineSetup_block s pc).trace.trans (copyTrace.trace.trans
    ((combine_hash hash copied copyPc).trans (combineStore_block _ (combined_pc hash copied copyPc)).trace))

theorem combineStore_word (s : MachineState) (i : Fin 5) :
    (combineStore s).getWord32 (BitVec.ofNat 64 (0x44a00+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) := by
  fin_cases i <;>
    simp [combineStore,runSchedule,combineStoreSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,MachineState.setWord32,
      MachineState.getWord32,alignToDword,byteOffset,
      SphincsMaskedChainStep.extract_replace_low,SphincsMaskedChainStep.extract_replace_high,
      SphincsMaskedChainStep.extract_replace_low_other,SphincsMaskedChainStep.extract_replace_high_other]

theorem combined_words (hash : Hash) (s : MachineState) (i : Fin 5) :
    (combined hash s).getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) =
      (hash (hashInput (combineHeader s))).extractLsb' (32*i.val) 32 := by
  have dst := (combine_registers s).2.2.1
  fin_cases i <;> simp [combined,writeHash,dst,MachineState.writeWords,
    MachineState.getWord32,alignToDword,byteOffset,extractWord32]
  all_goals ext b hb;interval_cases b <;> simp

theorem combined_value (hash : Hash) (s : MachineState) :
    Words20 (combineStore (combined hash s)) 0x44a00
      ((hash (hashInput (combineHeader s))).extractLsb' 0 160) := by
  intro i
  rw [combineStore_word,combined_words]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm


def signatureBase (tree : Nat) : Nat := 0x2009c+180*tree

theorem rootSetup_registers (s : MachineState) (tree : Fin 24)
    (base : s.getMem 0x43068 = 0x527d8) (counter : s.getMem 0x43040 = BitVec.ofNat 64 tree.val) :
    (rootSetup s).getReg .x6 = 0x527d8 ∧
    (rootSetup s).getReg .x7 = BitVec.ofNat 64 (0x44100+20*tree.val) := by
  change s.getMem 0x43068#64 = _ at base
  change s.getMem 0x43040#64 = _ at counter
  simp [rootSetup,runSchedule,rootSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,base,counter]
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 0x44100 + (BitVec.ofNat 64 tree.val * BitVec.ofNat 64 4 +
    BitVec.ofNat 64 tree.val * BitVec.ofNat 64 16) = _
  rw [← BitVec.ofNat_mul,← BitVec.ofNat_mul,← BitVec.ofNat_add,← BitVec.ofNat_add]
  congr 1;omega

def rootSaved (s : MachineState) := copyRootState (rootSetup s)

theorem root_copy_code : Copy20Code SphincsMaskedImages.sign 1212 := by
  constructor <;> intro i <;> fin_cases i <;> decide

theorem root_saved (s : MachineState) (tree : Fin 24) (pc : s.pc = 0x22c0)
    (base : s.getMem 0x43068 = 0x527d8) (counter : s.getMem 0x43040 = BitVec.ofNat 64 tree.val) :
    OrdinarySteps SphincsMaskedImages.sign s 22 (rootSaved s) ∧ (rootSaved s).pc = 0x2318 := by
  have regs := rootSetup_registers s tree base counter
  have copy := copy20_block_general SphincsMaskedImages.sign 1212 root_copy_code
    (rootSetup s) 0x527d8 (0x44100+20*tree.val) (rootSetup_pc s pc) regs.1 regs.2
    (by decide) (by decide) (by omega) (by dsimp [MEMORY_BYTES];omega) (by decide)
  refine ⟨ordinary_trans _ _ _ _ 12 10 (rootSetup_block s pc) copy,?_⟩
  rw [rootSaved,SphincsMaskedSignForestParents.copyRoot_pc,rootSetup_pc s pc];rfl

theorem root_saved_word (s : MachineState) (tree : Fin 24)
    (base : s.getMem 0x43068 = 0x527d8) (counter : s.getMem 0x43040 = BitVec.ofNat 64 tree.val) (i : Fin 5) :
    (rootSaved s).getWord32 (BitVec.ofNat 64 (0x44100+20*tree.val+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x527d8+4*i.val)) := by
  have regs := rootSetup_registers s tree base counter
  rw [rootSaved,SphincsMaskedSignForestParents.copy_data _ 0x527d8 (0x44100+20*tree.val)
    (by decide) (by omega) (by decide) (by omega) (Or.inr (by omega)) regs.1 regs.2 i]
  simp [MachineState.getWord32,rootSetup,runSchedule,rootSetupSchedule,execInstrBr]


theorem cell_bounds (address lower upper : Nat) (small : upper < 2^64)
    (lo : lower ≤ address) (hi : address < upper) (aligned : lower%8=0) :
    lower ≤ (alignToDword (BitVec.ofNat 64 address)).toNat ∧
      (alignToDword (BitVec.ofNat 64 address)).toNat < upper := by
  constructor
  · have ha : (BitVec.ofNat 64 lower).toNat % 8 = 0 := by
      simpa [Nat.mod_eq_of_lt (show lower<2^64 by omega)] using aligned
    have hover : (BitVec.ofNat 64 lower).toNat + (address-lower) < 2^64 := by
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show lower<2^64 by omega)];omega
    have eq := alignToDword_add_ofNat_of_aligned ha hover
    rw [← BitVec.ofNat_add] at eq
    rw [show address=lower+(address-lower) by omega,eq,← BitVec.ofNat_add,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  · unfold alignToDword
    rw [BitVec.toNat_and]
    apply lt_of_le_of_lt Nat.and_le_left
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show address<2^64 by omega)]
    exact hi

/-- Frame a 20-byte copy using a containing aligned interval. -/
theorem copy_memory_frame (s : MachineState) (destination lower upper : Nat)
    (dst : s.getReg .x7 = BitVec.ofNat 64 destination) (small : upper<2^64)
    (lo : lower ≤ destination) (hi : destination+20 ≤ upper) (aligned : lower%8=0)
    (a : Word) (outside : a.toNat<lower ∨ upper≤a.toNat) :
    (copyRootState s).getMem a = s.getMem a := by
  apply copyRoot_mem_frame
  intro i
  rw [dst]
  have addr : BitVec.ofNat 64 destination + signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
      BitVec.ofNat 64 (destination+4*i.val) := by
    fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
  rw [addr]
  intro eq
  have bounds := cell_bounds (destination+4*i.val) lower upper small (by omega) (by omega) aligned
  rw [← eq] at bounds
  omega

theorem root_saved_frame (s : MachineState) (tree : Fin 24)
    (base : s.getMem 0x43068 = 0x527d8) (counter : s.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (a : Word) (outside : a.toNat<0x44100 ∨ 0x44300≤a.toNat) :
    (rootSaved s).getMem a = s.getMem a := by
  have regs := rootSetup_registers s tree base counter
  rw [rootSaved,copy_memory_frame _ (0x44100+20*tree.val) 0x44100 0x44300
    regs.2 (by decide) (by omega) (by omega) (by decide) a outside]
  simp [rootSetup,runSchedule,rootSetupSchedule,execInstrBr]

theorem secret_copy_code : CopyCode SphincsMaskedImages.sign 0x2350 := by decide

theorem secret_copyInvariant (s : MachineState) (pc : s.pc = 0x2318) :
    CopyInvariant 0x2350 0x20 0x40028 4 4 (secretSetup s) := by
  simp [CopyInvariant,secretSetup,runSchedule,secretSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem secret_registers (s : MachineState) :
    (secretHeader s).getReg .x10=0x40000 ∧ (secretHeader s).getReg .x11=576 ∧
    (secretHeader s).getReg .x12=0x42000 ∧ (secretHeader s).getReg .x5=1 := by
  simp [secretHeader,runSchedule,secretHeaderSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

def secretAnswer (hash : Hash) (s : MachineState) :=
  writeHash (secretHeader s) (hash (hashInput (secretHeader s)))

theorem secret_hash (hash : Hash) (s : MachineState) (pc : s.pc=0x2368) :
    Trace hash SphincsMaskedImages.sign s 42 57 1 2 (secretAnswer hash s) := by
  obtain ⟨src,bits,dst,service⟩ := secret_registers s
  have fetched : fetch SphincsMaskedImages.sign (secretHeader s)=some (.base .ECALL) := by
    rw [fetch_at,secretHeader_pc s pc];decide
  have valid : hashArgumentsValid (secretHeader s)=true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (secretHeader s)).1=576 := by simp [hashInput,bits]
  have step := Trace.hash (hash := hash) (image := SphincsMaskedImages.sign)
    (secretHeader s) _ 0 0 0 0 fetched service valid (Trace.refl _)
  simp only [len] at step
  exact (secretHeader_block s pc).trace.trans step

theorem secret_pc (hash : Hash) (s : MachineState) (pc : s.pc=0x2368) :
    (secretAnswer hash s).pc=0x2410 := by
  simp [secretAnswer,writeHash,secretHeader_pc s pc]

abbrev SecretRetained (a : Word) : Prop := a.toNat<0x40000 ∨ 0x43020≤a.toNat

theorem secretSetup_frame (s : MachineState) (a : Word) (outside : SecretRetained a) :
    (secretSetup s).getMem a=s.getMem a := by
  have h0 : a ≠ 0x43010#64 := by intro eq;subst a;norm_num [SecretRetained] at outside
  have h1 : a ≠ 0x43018#64 := by intro eq;subst a;norm_num [SecretRetained] at outside
  simp [secretSetup,runSchedule,secretSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1]

theorem secretHeader_frame (s : MachineState) (a : Word) (outside : SecretRetained a) :
    (secretHeader s).getMem a=s.getMem a := by
  have ne (b : Word) (hb : b=0x40000#64 ∨ b=0x40008#64 ∨ b=0x40010#64 ∨ b=0x40018#64 ∨ b=0x40020#64) : a≠b := by
    intro eq;subst b
    rcases hb with h|h|h|h|h <;> subst a <;> norm_num [SecretRetained] at outside
  simp [secretHeader,runSchedule,secretHeaderSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,
    ne (0x40000#64) (by simp),ne (0x40008#64) (by simp),ne (0x40010#64) (by simp),ne (0x40018#64) (by simp),ne (0x40020#64) (by simp)]

theorem secretAnswer_frame (hash : Hash) (s : MachineState) (a : Word) (outside : SecretRetained a) :
    (secretAnswer hash s).getMem a=s.getMem a := by
  have ne (b : Word) (hb : b=0x42000#64 ∨ b=0x42008#64 ∨ b=0x42010#64 ∨ b=0x42018#64) : a≠b := by
    intro eq;subst b
    rcases hb with h|h|h|h <;> subst a <;> norm_num [SecretRetained] at outside
  have dst := (secret_registers s).2.2.1
  simp [secretAnswer,writeHash,dst,MachineState.writeWords,
    ne (0x42000#64) (by simp),ne (0x42008#64) (by simp),ne (0x42010#64) (by simp),ne (0x42018#64) (by simp)]
  exact secretHeader_frame s a outside

/-- The selected secret derivation always completes and retains the forest controls. -/
theorem secret_execution (hash : Hash) (s : MachineState) (pc : s.pc=0x2318) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 80 95 1 2 t ∧ t.pc=0x2410 ∧
      ∀ a, SecretRetained a → t.getMem a=s.getMem a := by
  obtain ⟨copied,copyTrace,copyInv,_,frame⟩ := copy_all SphincsMaskedImages.sign 0x2350 secret_copy_code
    0x20 0x40028 4 (secretSetup s) (secret_copyInvariant s pc)
    (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
  have copyPc : copied.pc=0x2368 := by simpa [CopyInvariant] using copyInv.2.2.1
  refine ⟨secretAnswer hash copied,(secretSetup_block s pc).trace.trans
    (copyTrace.trace.trans (secret_hash hash copied copyPc)),secret_pc hash copied copyPc,?_⟩
  intro a ha
  rw [secretAnswer_frame hash copied a ha,frame]
  · exact secretSetup_frame s a ha
  · intro i hi eq
    have val := congrArg BitVec.toNat eq
    simp only [wordAddress,BitVec.toNat_ofNat] at val
    rw [Nat.mod_eq_of_lt (by omega)] at val
    rcases ha with low|high <;> omega


theorem signatureSetup_registers (s : MachineState) (pointer : Nat)
    (hp : s.getMem 0x430a0 = BitVec.ofNat 64 pointer) :
    (signatureSetup s).getReg .x6 = 0x42000 ∧ (signatureSetup s).getReg .x7 = BitVec.ofNat 64 pointer := by
  change s.getMem 0x430a0#64 = _ at hp
  simp [signatureSetup,runSchedule,signatureSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,hp]

def signatureCopied (s : MachineState) := copyRootState (signatureSetup s)
def signatureSaved (s : MachineState) := signatureAdvance (signatureCopied s)

theorem signature_copy_code : Copy20Code SphincsMaskedImages.sign 1289 := by
  constructor <;> intro i <;> fin_cases i <;> decide

theorem signatureCopied_pc (s : MachineState) (pc : s.pc=0x2410) :
    (signatureCopied s).pc=0x244c := by
  rw [signatureCopied,SphincsMaskedSignForestParents.copyRoot_pc,signatureSetup_pc s pc];rfl

theorem signatureCopied_frame (s : MachineState) (pointer : Nat)
    (hp : s.getMem 0x430a0 = BitVec.ofNat 64 pointer) (bounded : pointer+20 ≤ 0x40000)
    (a : Word) (high : 0x40000 ≤ a.toNat) :
    (signatureCopied s).getMem a = s.getMem a := by
  have regs := signatureSetup_registers s pointer hp
  rw [signatureCopied,copy_memory_frame _ pointer 0 0x40000 regs.2 (by decide)
    (by omega) bounded (by decide) a (Or.inr high)]
  simp [signatureSetup,runSchedule,signatureSetupSchedule,execInstrBr]

theorem signature_saved (s : MachineState) (pointer : Nat) (pc : s.pc=0x2410)
    (hp : s.getMem 0x430a0 = BitVec.ofNat 64 pointer)
    (bounded : pointer+20 ≤ 0x40000) (aligned : pointer%4=0) :
    OrdinarySteps SphincsMaskedImages.sign s 22 (signatureSaved s) ∧
    (signatureSaved s).pc=0x2468 ∧
    (signatureSaved s).getMem 0x430a0 = BitVec.ofNat 64 (pointer+20) := by
  have regs := signatureSetup_registers s pointer hp
  have copied := copy20_block_general SphincsMaskedImages.sign 1289 signature_copy_code
    (signatureSetup s) 0x42000 pointer (signatureSetup_pc s pc) regs.1 regs.2
    (by decide) (by decide) aligned (by dsimp [MEMORY_BYTES];omega) (by decide)
  refine ⟨ordinary_trans _ _ _ _ 5 17 (signatureSetup_block s pc)
    (ordinary_trans _ _ _ _ 10 7 copied (signatureAdvance_block _ (signatureCopied_pc s pc))),
    signatureAdvance_pc _ (signatureCopied_pc s pc),?_⟩
  have old := (signatureCopied_frame s pointer hp bounded 0x430a0 (by decide)).trans hp
  change (signatureCopied s).getMem 0x430a0#64 = _ at old
  simp [signatureSaved,signatureAdvance,runSchedule,signatureAdvanceSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,old,BitVec.ofNat_add]

structure PathControls (s : MachineState) (level bit pointer : Nat) : Prop where
  base : s.getMem 0x430c0 = BitVec.ofNat 64 (SphincsMaskedSignForestParents.cacheBase level)
  count : s.getMem 0x43090 = BitVec.ofNat 64 (SphincsMaskedSignForestParents.width level)
  level : s.getMem 0x43048 = BitVec.ofNat 64 level
  bit : s.getMem 0x43070 = BitVec.ofNat 64 bit
  pointer : s.getMem 0x430a0 = BitVec.ofNat 64 pointer

theorem pathInit_controls (s : MachineState) (selected pointer : Nat)
    (hs : s.getMem 0x430a8 = BitVec.ofNat 64 selected)
    (hp : s.getMem 0x430a0 = BitVec.ofNat 64 pointer) : PathControls (pathInit s) 0 selected pointer := by
  change s.getMem 0x430a8#64 = _ at hs
  change s.getMem 0x430a0#64 = _ at hp
  constructor <;>
    simp [pathInit,runSchedule,pathInitSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,hs,hp,
      SphincsMaskedSignForestParents.cacheBase,SphincsMaskedSignForestParents.width]

theorem pathSetup_registers (s : MachineState) (level bit pointer : Nat)
    (ctrl : PathControls s level bit pointer) :
    (pathSetup s).getReg .x6 = BitVec.ofNat 64
      (SphincsMaskedSignForestParents.cacheBase level+20*(bit ^^^ 1)) ∧
    (pathSetup s).getReg .x7 = BitVec.ofNat 64 pointer := by
  have hb := ctrl.bit
  have hbase := ctrl.base
  have hp := ctrl.pointer
  change s.getMem 0x43070#64 = _ at hb
  change s.getMem 0x430c0#64 = _ at hbase
  change s.getMem 0x430a0#64 = _ at hp
  simp [pathSetup,runSchedule,pathSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,hb,hbase,hp]
  change BitVec.ofNat 64 (SphincsMaskedSignForestParents.cacheBase level) +
    (((BitVec.ofNat 64 bit ^^^ BitVec.ofNat 64 1) <<< 2) +
    ((BitVec.ofNat 64 bit ^^^ BitVec.ofNat 64 1) <<< 4)) = _
  rw [← BitVec.ofNat_xor]
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 (SphincsMaskedSignForestParents.cacheBase level) +
    (BitVec.ofNat 64 (bit ^^^ 1) * BitVec.ofNat 64 4 +
    BitVec.ofNat 64 (bit ^^^ 1) * BitVec.ofNat 64 16) = _
  rw [← BitVec.ofNat_mul,← BitVec.ofNat_mul,← BitVec.ofNat_add,← BitVec.ofNat_add]
  congr 1;omega

def pathCopied (s : MachineState) := copyRootState (pathSetup s)
def pathNext (s : MachineState) := pathFinish (pathCopied s)

theorem path_copy_code : Copy20Code SphincsMaskedImages.sign 1339 := by
  constructor <;> intro i <;> fin_cases i <;> decide

theorem pathCopied_pc (s : MachineState) (pc : s.pc=0x24b4) : (pathCopied s).pc=0x2514 := by
  rw [pathCopied,SphincsMaskedSignForestParents.copyRoot_pc,pathSetup_pc s pc];rfl

theorem pathCopied_frame (s : MachineState) (level bit pointer : Nat)
    (ctrl : PathControls s level bit pointer) (bounded : pointer+20 ≤ 0x40000)
    (a : Word) (high : 0x40000 ≤ a.toNat) :
    (pathCopied s).getMem a=s.getMem a := by
  have regs := pathSetup_registers s level bit pointer ctrl
  rw [pathCopied,copy_memory_frame _ pointer 0 0x40000 regs.2 (by decide)
    (by omega) bounded (by decide) a (Or.inr high)]
  simp [pathSetup,runSchedule,pathSetupSchedule,execInstrBr]

theorem pathCopied_controls (s : MachineState) (level bit pointer : Nat)
    (ctrl : PathControls s level bit pointer) (bounded : pointer+20 ≤ 0x40000) :
    PathControls (pathCopied s) level bit pointer := by
  constructor
  · exact (pathCopied_frame s level bit pointer ctrl bounded _ (by decide)).trans ctrl.base
  · exact (pathCopied_frame s level bit pointer ctrl bounded _ (by decide)).trans ctrl.count
  · exact (pathCopied_frame s level bit pointer ctrl bounded _ (by decide)).trans ctrl.level
  · exact (pathCopied_frame s level bit pointer ctrl bounded _ (by decide)).trans ctrl.bit
  · exact (pathCopied_frame s level bit pointer ctrl bounded _ (by decide)).trans ctrl.pointer

theorem ofNat_half (n : Nat) (small : n<2^64) :
    (BitVec.ofNat 64 n >>> 1) = BitVec.ofNat 64 (n/2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem pathFinish_controls (s : MachineState) (level : Fin 8) (bit pointer : Nat)
    (ctrl : PathControls s level.val bit pointer) (bitBound : bit<256) :
    PathControls (pathFinish s) (level.val+1) (bit/2) (pointer+20) := by
  have base := ctrl.base
  have count := ctrl.count
  have lev := ctrl.level
  have bits := ctrl.bit
  have ptr := ctrl.pointer
  change s.getMem 0x430c0#64 = _ at base
  change s.getMem 0x43090#64 = _ at count
  change s.getMem 0x43048#64 = _ at lev
  change s.getMem 0x43070#64 = _ at bits
  change s.getMem 0x430a0#64 = _ at ptr
  constructor <;>
    simp [pathFinish,runSchedule,pathFinishSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,base,count,lev,bits,ptr,
      ofNat_half bit (by omega),BitVec.ofNat_add]
  all_goals fin_cases level <;> decide

theorem pathFinish_pc (s : MachineState) (level : Fin 8) (pc : s.pc=0x2514)
    (lev : s.getMem 0x43048 = BitVec.ofNat 64 level.val) :
    (pathFinish s).pc = if level.val+1=8 then 0x25cc else 0x24b4 := by
  change s.getMem 0x43048#64 = _ at lev
  simp [pathFinish,runSchedule,pathFinishSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc,lev]
  fin_cases level <;> decide

theorem sibling_bound (level : Fin 8) (bit : Nat)
    (bound : bit < SphincsMaskedSignForestParents.width level.val) :
    bit ^^^ 1 < SphincsMaskedSignForestParents.width level.val := by
  have hb : bit < 2^(8-level.val) := by simpa [SphincsMaskedSignForestParents.width,show level.val≤8 by omega] using bound
  have h1 : 1 < 2^(8-level.val) := by fin_cases level <;> decide
  simpa [SphincsMaskedSignForestParents.width,show level.val≤8 by omega] using Nat.xor_lt_two_pow hb h1

/-- A single authentication sibling is copied with fixed cost. -/
theorem path_step (s : MachineState) (level : Fin 8) (bit pointer : Nat)
    (pc : s.pc=0x24b4) (ctrl : PathControls s level.val bit pointer)
    (bitBound : bit<SphincsMaskedSignForestParents.width level.val)
    (pointerBound : pointer+20≤0x40000) (aligned : pointer%4=0) :
    OrdinarySteps SphincsMaskedImages.sign s 70 (pathNext s) ∧
    PathControls (pathNext s) (level.val+1) (bit/2) (pointer+20) ∧
    (pathNext s).pc = (if level.val+1=8 then 0x25cc else 0x24b4) := by
  have regs := pathSetup_registers s level.val bit pointer ctrl
  have sibling := sibling_bound level bit bitBound
  have bounds := SphincsMaskedSignForestParents.layout level
  have align : SphincsMaskedSignForestParents.cacheBase level.val%4=0 := bounds.2.2.2.1
  have within : SphincsMaskedSignForestParents.cacheBase level.val+20*(bit ^^^ 1)+20≤MEMORY_BYTES := by
    dsimp [MEMORY_BYTES];omega
  have copied := copy20_block_general SphincsMaskedImages.sign 1339 path_copy_code
    (pathSetup s) (SphincsMaskedSignForestParents.cacheBase level.val+20*(bit ^^^ 1)) pointer
    (pathSetup_pc s pc) regs.1 regs.2 (by omega) within aligned
    (by dsimp [MEMORY_BYTES];omega) (by decide)
  have copiedCtrl := pathCopied_controls s level.val bit pointer ctrl pointerBound
  have small : bit<256 := by
    have h : SphincsMaskedSignForestParents.width level.val ≤ 256 := by fin_cases level <;> decide
    omega
  refine ⟨ordinary_trans _ _ _ _ 14 56 (pathSetup_block s pc)
    (ordinary_trans _ _ _ _ 10 46 copied (pathFinish_block _ (pathCopied_pc s pc))),
    pathFinish_controls _ level bit pointer copiedCtrl small,
    pathFinish_pc _ level (pathCopied_pc s pc) copiedCtrl.level⟩


def pathWrites : List Word := [0x430a0#64,0x430c0#64,0x43090#64,0x43070#64,0x43048#64]
abbrev PathRetained (a : Word) : Prop := 0x40000≤a.toNat ∧ a ∉ pathWrites

theorem signatureAdvance_frame (s : MachineState) (a : Word) (ne : a≠0x430a0#64) :
    (signatureAdvance s).getMem a=s.getMem a := by
  simp [signatureAdvance,runSchedule,signatureAdvanceSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ne]

theorem signatureSaved_frame (s : MachineState) (pointer : Nat)
    (hp : s.getMem 0x430a0=BitVec.ofNat 64 pointer) (bounded : pointer+20≤0x40000)
    (a : Word) (high : 0x40000≤a.toNat) (ne : a≠0x430a0#64) :
    (signatureSaved s).getMem a=s.getMem a := by
  rw [signatureSaved,signatureAdvance_frame _ a ne,signatureCopied_frame s pointer hp bounded a high]

theorem pathInit_frame (s : MachineState) (a : Word) (ha : PathRetained a) :
    (pathInit s).getMem a=s.getMem a := by
  obtain ⟨_,ha⟩ := ha
  simp only [pathWrites,List.mem_cons,List.not_mem_nil,not_or] at ha
  obtain ⟨h0,h1,h2,h3,h4⟩ := ha
  simp [pathInit,runSchedule,pathInitSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3,h4]

theorem pathFinish_memory (s : MachineState) (a : Word) (ha : a ∉ pathWrites) :
    (pathFinish s).getMem a=s.getMem a := by
  simp only [pathWrites,List.mem_cons,List.not_mem_nil,not_or] at ha
  obtain ⟨h0,h1,h2,h3,h4⟩ := ha
  simp [pathFinish,runSchedule,pathFinishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3,h4]

theorem pathFinish_frame (s : MachineState) (a : Word) (ha : PathRetained a) :
    (pathFinish s).getMem a=s.getMem a := pathFinish_memory s a ha.2

theorem pathNext_frame (s : MachineState) (level bit pointer : Nat)
    (ctrl : PathControls s level bit pointer) (bounded : pointer+20≤0x40000)
    (a : Word) (ha : PathRetained a) : (pathNext s).getMem a=s.getMem a := by
  rw [pathNext,pathFinish_frame _ a ha,pathCopied_frame s level bit pointer ctrl bounded a ha.1]

theorem divided_selector_bound (selected : Fin 256) (level : Fin 8) :
    selected.val / 2^level.val < SphincsMaskedSignForestParents.width level.val := by
  fin_cases level <;> simp [SphincsMaskedSignForestParents.width] <;> omega

/-- The eight sibling copies have exact cost, bounded addresses, and a retained control frame. -/
theorem paths_execution (s : MachineState) (selected : Fin 256) (pointer : Nat)
    (pc : s.pc=0x24b4) (ctrl : PathControls s 0 selected.val pointer)
    (pointerBound : pointer+160≤0x40000) (aligned : pointer%4=0)
    (n : Nat) (bound : n≤8) :
    ∃ t, OrdinarySteps SphincsMaskedImages.sign s (70*n) t ∧
      PathControls t n (selected.val/2^n) (pointer+20*n) ∧
      t.pc=(if n=8 then 0x25cc else 0x24b4) ∧
      ∀ a, PathRetained a → t.getMem a=s.getMem a := by
  induction n with
  | zero => exact ⟨s,OrdinarySteps.refl _,by simpa using ctrl,pc,by intro _ _;rfl⟩
  | succ n ih =>
    obtain ⟨mid,first,midCtrl,midPc,frame⟩ := ih (by omega)
    have here : mid.pc=0x24b4 := by simpa only [if_neg (show n≠8 by omega)] using midPc
    let level : Fin 8 := ⟨n,by omega⟩
    have bitBound := divided_selector_bound selected level
    obtain ⟨step,done,loc⟩ := path_step mid level (selected.val/2^n) (pointer+20*n)
      here midCtrl bitBound (by omega) (by omega)
    refine ⟨pathNext mid,?_,?_,loc,?_⟩
    · simpa only [Nat.mul_add,Nat.mul_one,Nat.add_comm] using first.append step
    · convert done using 1
      · simp [level,Nat.pow_succ,Nat.div_div_eq_div_mul]
      · omega
    · intro a ha
      rw [pathNext_frame mid n (selected.val/2^n) (pointer+20*n) midCtrl (by omega) a ha,frame a ha]

theorem treeFinish_counter (s : MachineState) :
    (treeFinish s).getMem 0x43040=s.getMem 0x43040+1 := by
  simp [treeFinish,runSchedule,treeFinishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem treeFinish_frame (s : MachineState) (a : Word) (ne : a≠0x43040#64) :
    (treeFinish s).getMem a=s.getMem a := by
  simp [treeFinish,runSchedule,treeFinishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ne]

theorem treeFinish_pc (s : MachineState) (tree : Fin 24) (pc : s.pc=0x25cc)
    (counter : s.getMem 0x43040=BitVec.ofNat 64 tree.val) :
    (treeFinish s).pc=(if tree.val+1=24 then 0x25fc else 0x1cec) := by
  change s.getMem 0x43040#64 = _ at counter
  simp [treeFinish,runSchedule,treeFinishSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc,counter]
  fin_cases tree <;> decide

abbrev ForestRetained (a : Word) : Prop := a=0x43078#64 ∨ (0x44800≤a.toNat ∧ a.toNat<0x44818)

theorem forest_path_retained (a : Word) (ha : ForestRetained a) : PathRetained a := by
  constructor
  · rcases ha with eq|bounds
    · rw [eq];decide
    · omega
  · simp only [pathWrites,List.mem_cons,List.not_mem_nil,or_false]
    intro h
    rcases h with h|h|h|h|h <;> subst a <;> norm_num [ForestRetained,BitVec.reduceEq] at ha <;> (have bad := congrArg BitVec.toNat ha; norm_num at bad)

/-- Concrete post-root execution for one FORS tree. -/
theorem tail_execution (hash : Hash) (s : MachineState) (tree : Fin 24) (selected : Fin 256)
    (pc : s.pc=0x22c0) (base : s.getMem 0x43068=0x527d8)
    (counter : s.getMem 0x43040=BitVec.ofNat 64 tree.val)
    (pointer : s.getMem 0x430a0=BitVec.ofNat 64 (signatureBase tree.val))
    (selector : s.getMem 0x430a8=BitVec.ofNat 64 selected.val) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 715 730 1 2 t ∧
      t.pc=(if tree.val+1=24 then 0x25fc else 0x1cec) ∧
      t.getMem 0x43040=BitVec.ofNat 64 (tree.val+1) ∧
      t.getMem 0x430a0=BitVec.ofNat 64 (signatureBase (tree.val+1)) ∧
      ∀ a, ForestRetained a → t.getMem a=s.getMem a := by
  obtain ⟨rootTrace,rootPc⟩ := root_saved s tree pc base counter
  obtain ⟨hashed,hashTrace,hashPc,hashFrame⟩ := secret_execution hash (rootSaved s) rootPc
  have hp : hashed.getMem 0x430a0=BitVec.ofNat 64 (signatureBase tree.val) :=
    (hashFrame _ (by decide)).trans ((root_saved_frame s tree base counter _ (Or.inl (by decide))).trans pointer)
  have hc : hashed.getMem 0x43040=BitVec.ofNat 64 tree.val :=
    (hashFrame _ (by decide)).trans ((root_saved_frame s tree base counter _ (Or.inl (by decide))).trans counter)
  have hs : hashed.getMem 0x430a8=BitVec.ofNat 64 selected.val :=
    (hashFrame _ (by decide)).trans ((root_saved_frame s tree base counter _ (Or.inl (by decide))).trans selector)
  have ptrBound : signatureBase tree.val+20≤0x40000 := by dsimp [signatureBase];omega
  obtain ⟨storeTrace,storePc,storePointer⟩ := signature_saved hashed (signatureBase tree.val) hashPc hp ptrBound (by dsimp [signatureBase];omega)
  have storedSelector : (signatureSaved hashed).getMem 0x430a8=BitVec.ofNat 64 selected.val :=
    (signatureSaved_frame hashed _ hp ptrBound _ (by decide) (by decide)).trans hs
  have storedCounter : (signatureSaved hashed).getMem 0x43040=BitVec.ofNat 64 tree.val :=
    (signatureSaved_frame hashed _ hp ptrBound _ (by decide) (by decide)).trans hc
  have initial := pathInit_controls (signatureSaved hashed) selected.val (signatureBase tree.val+20) storedSelector storePointer
  obtain ⟨pathed,pathTrace,pathCtrl,pathPc,pathFrame⟩ := paths_execution
    (pathInit (signatureSaved hashed)) selected (signatureBase tree.val+20)
    (pathInit_pc _ storePc) initial (by dsimp [signatureBase];omega) (by dsimp [signatureBase];omega) 8 (by decide)
  have here : pathed.pc=0x25cc := by simpa using pathPc
  have pathCounter : pathed.getMem 0x43040=BitVec.ofNat 64 tree.val :=
    (pathFrame _ (by decide)).trans ((pathInit_frame _ _ (by decide)).trans storedCounter)
  refine ⟨treeFinish pathed,?_,treeFinish_pc pathed tree here pathCounter,?_,?_,?_⟩
  · exact rootTrace.trace.trans (hashTrace.trans (storeTrace.trace.trans
      ((pathInit_block _ storePc).trace.trans (pathTrace.trace.trans (treeFinish_block pathed here).trace))))
  · rw [treeFinish_counter,pathCounter]
    exact (BitVec.ofNat_add _ _).symm
  · rw [treeFinish_frame _ _ (by decide),pathCtrl.pointer]
    congr 1 <;> dsimp [signatureBase] <;> omega
  · intro a ha
    have retained := forest_path_retained a ha
    have nePtr : a≠0x430a0#64 := by intro eq;subst a;norm_num [ForestRetained,BitVec.reduceEq] at ha <;> (have bad := congrArg BitVec.toNat ha; norm_num at bad)
    have neTree : a≠0x43040#64 := by intro eq;subst a;norm_num [ForestRetained,BitVec.reduceEq] at ha <;> (have bad := congrArg BitVec.toNat ha; norm_num at bad)
    have secretRetained : SecretRetained a := by
      rcases ha with eq|bounds
      · rw [eq];decide
      · exact Or.inr (by omega)
    have outside : a.toNat<0x44100 ∨ 0x44300≤a.toNat := by
      rcases ha with eq|bounds
      · rw [eq];exact Or.inl (by decide)
      · exact Or.inr (by omega)
    rw [treeFinish_frame _ a neTree,pathFrame a retained,pathInit_frame _ a retained,
      signatureSaved_frame hashed _ hp ptrBound a retained.1 nePtr,hashFrame a secretRetained,
      root_saved_frame s tree base counter a outside]


theorem treeInit_controls (s : MachineState) :
    (treeInit s).getMem 0x43040=0 ∧ (treeInit s).getMem 0x430a0=BitVec.ofNat 64 (signatureBase 0) := by
  simp [treeInit,runSchedule,treeInitSchedule,execInstrBr,signExtend12,signatureBase,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem treeEntry_checked (s : MachineState) (tree : Fin 24) (pc : s.pc=0x1cec)
    (counter : s.getMem 0x43040=BitVec.ofNat 64 tree.val) : Checked treeEntrySchedule s := by
  change s.getMem 0x43040#64 = _ at counter
  have small : 0x44800+tree.val<2^64 := by omega
  simp [treeEntrySchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,counter,pc,
    ← BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  omega

theorem treeEntry_block (s : MachineState) (tree : Fin 24) (pc : s.pc=0x1cec)
    (counter : s.getMem 0x43040=BitVec.ofNat 64 tree.val) :
    OrdinarySteps SphincsMaskedImages.sign s 26 (treeEntry s) :=
  checked_sound _ treeEntrySchedule treeEntry_code s (treeEntry_checked s tree pc counter)

theorem treeEntry_pc (s : MachineState) (pc : s.pc=0x1cec) : (treeEntry s).pc=0x1d54 := by
  simp [treeEntry,runSchedule,treeEntrySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem treeEntry_controls (s : MachineState) :
    (treeEntry s).getMem 0x43040=s.getMem 0x43040 ∧
    (treeEntry s).getMem 0x430a0=s.getMem 0x430a0 ∧
    (treeEntry s).getMem 0x43020=0 := by
  simp [treeEntry,runSchedule,treeEntrySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem treeEntry_selector_bound (s : MachineState) :
    ((treeEntry s).getMem 0x430a8).toNat<256 := by
  simp [treeEntry,runSchedule,treeEntrySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (BitVec.isLt _)

theorem treeEntry_frame (s : MachineState) (a : Word) (ha : ForestRetained a) :
    (treeEntry s).getMem a=s.getMem a := by
  have ne (b : Word) (hb : b=0x43000#64 ∨ b=0x43008#64 ∨ b=0x430a8#64 ∨ b=0x43020#64) : a≠b := by
    intro eq;subst b
    rcases hb with h|h|h|h <;> subst a <;> norm_num [ForestRetained,BitVec.reduceEq] at ha <;> (have bad := congrArg BitVec.toNat ha; norm_num at bad)
  simp [treeEntry,runSchedule,treeEntrySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    ne (0x43000#64) (by simp),ne (0x43008#64) (by simp),ne (0x430a8#64) (by simp),ne (0x43020#64) (by simp)]

/-- Precisely the state retained across the independently proved leaf+parent
    block. No oracle-query identity appears in this execution contract. -/
def BodyExecution (hash : Hash) : Prop :=
  ∀ (tree : Fin 24) (selected : Fin 256) (s : MachineState), s.pc=0x1d54 →
    s.getMem 0x43020=0 → s.getMem 0x43040=BitVec.ofNat 64 tree.val →
    s.getMem 0x430a0=BitVec.ofNat 64 (signatureBase tree.val) →
    s.getMem 0x430a8=BitVec.ofNat 64 selected.val →
    ∃ t, Trace hash SphincsMaskedImages.sign s 79053 88510 767 1278 t ∧
      t.pc=0x22c0 ∧ t.getMem 0x43068=0x527d8 ∧
      t.getMem 0x43040=BitVec.ofNat 64 tree.val ∧
      t.getMem 0x430a0=BitVec.ofNat 64 (signatureBase tree.val) ∧
      t.getMem 0x430a8=BitVec.ofNat 64 selected.val ∧
      ∀ a, ForestRetained a → t.getMem a=s.getMem a

/-- Complete one forest tree, reusing the body contract and concrete tail. -/
theorem tree_execution (hash : Hash) (body : BodyExecution hash) (s : MachineState)
    (tree : Fin 24) (pc : s.pc=0x1cec)
    (counter : s.getMem 0x43040=BitVec.ofNat 64 tree.val)
    (pointer : s.getMem 0x430a0=BitVec.ofNat 64 (signatureBase tree.val)) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 79794 89266 768 1280 t ∧
      t.pc=(if tree.val+1=24 then 0x25fc else 0x1cec) ∧
      t.getMem 0x43040=BitVec.ofNat 64 (tree.val+1) ∧
      t.getMem 0x430a0=BitVec.ofNat 64 (signatureBase (tree.val+1)) ∧
      ∀ a, ForestRetained a → t.getMem a=s.getMem a := by
  have ctrl := treeEntry_controls s
  let selected : Fin 256 := ⟨((treeEntry s).getMem 0x430a8).toNat,treeEntry_selector_bound s⟩
  have selector : (treeEntry s).getMem 0x430a8=BitVec.ofNat 64 selected.val := by simp [selected]
  obtain ⟨root,bodyTrace,bodyPc,base,bodyCounter,bodyPointer,bodySelector,bodyFrame⟩ :=
    body tree selected (treeEntry s) (treeEntry_pc s pc) ctrl.2.2 (ctrl.1.trans counter)
      (ctrl.2.1.trans pointer) selector
  obtain ⟨final,tailTrace,tailPc,tailCounter,tailPointer,tailFrame⟩ :=
    tail_execution hash root tree selected bodyPc base bodyCounter bodyPointer bodySelector
  refine ⟨final,(treeEntry_block s tree pc counter).trace.trans (bodyTrace.trans tailTrace),
    tailPc,tailCounter,tailPointer,?_⟩
  intro a ha
  rw [tailFrame a ha,bodyFrame a ha,treeEntry_frame s a ha]

/-- Reusable outer induction; every tree appends exactly 180 signature bytes. -/
theorem trees_execution (hash : Hash) (body : BodyExecution hash) (s : MachineState)
    (pc : s.pc=0x1cec) (counter : s.getMem 0x43040=0)
    (pointer : s.getMem 0x430a0=BitVec.ofNat 64 (signatureBase 0))
    (n : Nat) (bound : n≤24) :
    ∃ t, Trace hash SphincsMaskedImages.sign s (79794*n) (89266*n) (768*n) (1280*n) t ∧
      t.pc=(if n=24 then 0x25fc else 0x1cec) ∧
      t.getMem 0x43040=BitVec.ofNat 64 n ∧
      t.getMem 0x430a0=BitVec.ofNat 64 (signatureBase n) ∧
      ∀ a, ForestRetained a → t.getMem a=s.getMem a := by
  induction n with
  | zero => exact ⟨s,Trace.refl _,pc,counter,pointer,by intro _ _;rfl⟩
  | succ n ih =>
    obtain ⟨mid,first,midPc,midCounter,midPointer,frame⟩ := ih (by omega)
    have here : mid.pc=0x1cec := by simpa only [if_neg (show n≠24 by omega)] using midPc
    obtain ⟨t,last,loc,count,ptr,retained⟩ := tree_execution hash body mid ⟨n,by omega⟩ here midCounter midPointer
    refine ⟨t,?_,loc,count,ptr,?_⟩
    · simpa only [Nat.mul_add,Nat.mul_one] using first.trans last
    · intro a ha;rw [retained a ha,frame a ha]

/-- All 24 trees and the final forest-root HASH, conditional only on the
    explicit leaf+parent execution/frame contract. -/
theorem forest_execution (hash : Hash) (body : BodyExecution hash) (s : MachineState)
    (pc : s.pc=0x1cc8) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 1915509 2142908 18433 30729 t ∧ t.pc=0x2764 := by
  have initial := treeInit_controls s
  obtain ⟨mid,trees,loc,_,_,_⟩ := trees_execution hash body (treeInit s)
    (treeInit_pc s pc) initial.1 initial.2 24 (by decide)
  have here : mid.pc=0x25fc := by simpa using loc
  obtain ⟨t,last,done⟩ := combine_execution hash mid here
  exact ⟨t,(treeInit_block s pc).trace.trans (trees.trans last),done⟩


/-- Selected-secret output, at 32-bit granularity to handle the shared cell
    between the nonce prefix and the first FORS signature element. -/
theorem signature_saved_word (s : MachineState) (pointer : Nat)
    (hp : s.getMem 0x430a0=BitVec.ofNat 64 pointer) (bounded : pointer+20≤0x40000)
    (aligned : pointer%4=0) (i : Fin 5) :
    (signatureSaved s).getWord32 (BitVec.ofNat 64 (pointer+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) := by
  have regs := signatureSetup_registers s pointer hp
  change (signatureAdvance (copyRootState (signatureSetup s))).getWord32 _ = _
  simp only [MachineState.getWord32]
  rw [signatureAdvance_frame]
  · change (copyRootState (signatureSetup s)).getWord32 _ = _
    rw [SphincsMaskedSignForestParents.copy_data _ 0x42000 pointer (by decide) (by omega)
      (by decide) aligned (Or.inr (by omega)) regs.1 regs.2 i]
    simp [MachineState.getWord32,signatureSetup,runSchedule,signatureSetupSchedule,execInstrBr]
  · intro eq
    have bound := (cell_bounds (pointer+4*i.val) 0 0x40000 (by decide) (by omega) (by omega) (by decide)).2
    rw [eq] at bound;contradiction

theorem pathFinish_low_word (s : MachineState) (address : Nat) (bounded : address<0x40000) :
    (pathFinish s).getWord32 (BitVec.ofNat 64 address)=s.getWord32 (BitVec.ofNat 64 address) := by
  simp only [MachineState.getWord32]
  rw [pathFinish_memory]
  have bound := (cell_bounds address 0 0x40000 (by decide) (by omega) bounded (by decide)).2
  simp only [pathWrites,List.mem_cons,List.not_mem_nil,or_false]
  intro h
  rcases h with h|h|h|h|h <;> rw [h] at bound <;> contradiction

/-- The emitted authentication value is exactly the indexed cached sibling. -/
theorem path_step_word (s : MachineState) (level : Fin 8) (bit pointer : Nat)
    (ctrl : PathControls s level.val bit pointer)
    (bitBound : bit<SphincsMaskedSignForestParents.width level.val)
    (pointerBound : pointer+20≤0x40000) (aligned : pointer%4=0) (i : Fin 5) :
    (pathNext s).getWord32 (BitVec.ofNat 64 (pointer+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64
        (SphincsMaskedSignForestParents.cacheBase level.val+20*(bit ^^^ 1)+4*i.val)) := by
  have regs := pathSetup_registers s level.val bit pointer ctrl
  have sibling := sibling_bound level bit bitBound
  obtain ⟨sourceEnd,targetEnd,targetBound,baseAlign,targetAlign,baseAbove,targetAbove,positive,small,twice,half,total⟩ :=
    SphincsMaskedSignForestParents.layout level
  rw [pathNext,pathFinish_low_word _ _ (by omega)]
  rw [pathCopied,SphincsMaskedSignForestParents.copy_data _
    (SphincsMaskedSignForestParents.cacheBase level.val+20*(bit ^^^ 1)) pointer
    (by omega) (by omega) (by omega) aligned (Or.inr (by omega)) regs.1 regs.2 i]
  simp [MachineState.getWord32,pathSetup,runSchedule,pathSetupSchedule,execInstrBr]

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestTail.combine_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combine_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestTail.combined_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combined_value

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestTail.root_saved_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms root_saved_word

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestTail.secret_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms secret_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestTail.path_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms path_step

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestTail.paths_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paths_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestTail.tail_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tail_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestTail.tree_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tree_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestTail.trees_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trees_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestTail.forest_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forest_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestTail.signature_saved_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signature_saved_word

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestTail.path_step_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms path_step_word


end SigGolfCandidate.SphincsMaskedSignForestTail
