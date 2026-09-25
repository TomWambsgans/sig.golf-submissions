import SigGolfCandidate.SphincsMaskedLeafRefinement

namespace SigGolfCandidate.SphincsMaskedParentCode
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def initSchedule : List (Word × Instr) := [
  (0x15cc, .ADDI .x6 .x0 (1)),
  (0x15d0, .LUI .x28 67),
  (0x15d4, .ADDI .x28 .x28 (72)),
  (0x15d8, .SD .x28 .x6 (0)),
  (0x15dc, .ADDI .x6 .x0 (136)),
  (0x15e0, .LUI .x28 67),
  (0x15e4, .ADDI .x28 .x28 (104)),
  (0x15e8, .SD .x28 .x6 (0)),
  (0x15ec, .LUI .x6 10),
  (0x15f0, .ADDI .x6 .x6 (136)),
  (0x15f4, .LUI .x28 67),
  (0x15f8, .ADDI .x28 .x28 (128)),
  (0x15fc, .SD .x28 .x6 (0)),
  (0x1600, .ADDI .x6 .x0 (1024)),
  (0x1604, .LUI .x28 67),
  (0x1608, .ADDI .x28 .x28 (144)),
  (0x160c, .SD .x28 .x6 (0))]

def init (s : MachineState) : MachineState := runSchedule initSchedule s

theorem init_code : ∀ e ∈ initSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem init_checked (s : MachineState) (pc : s.pc = 0x15cc) : Checked initSchedule s := by
  simp [initSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem init_block (s : MachineState) (pc : s.pc = 0x15cc) :
    OrdinarySteps SphincsMaskedImages.keygen s 17 (init s) :=
  checked_sound _ initSchedule init_code s (init_checked s pc)

theorem init_pc (s : MachineState) (pc : s.pc = 0x15cc) :
    (init s).pc = 0x1610 := by
  simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def levelEntrySchedule : List (Word × Instr) := [
  (0x1610, .ADDI .x6 .x0 (0)),
  (0x1614, .LUI .x28 67),
  (0x1618, .ADDI .x28 .x28 (136)),
  (0x161c, .SD .x28 .x6 (0))]

def levelEntry (s : MachineState) : MachineState := runSchedule levelEntrySchedule s

theorem levelEntry_code : ∀ e ∈ levelEntrySchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem levelEntry_checked (s : MachineState) (pc : s.pc = 0x1610) : Checked levelEntrySchedule s := by
  simp [levelEntrySchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem levelEntry_block (s : MachineState) (pc : s.pc = 0x1610) :
    OrdinarySteps SphincsMaskedImages.keygen s 4 (levelEntry s) :=
  checked_sound _ levelEntrySchedule levelEntry_code s (levelEntry_checked s pc)

theorem levelEntry_pc (s : MachineState) (pc : s.pc = 0x1610) :
    (levelEntry s).pc = 0x1620 := by
  simp [levelEntry,runSchedule,levelEntrySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def leftSetupSchedule : List (Word × Instr) := [
  (0x1620, .LUI .x28 67),
  (0x1624, .ADDI .x28 .x28 (136)),
  (0x1628, .LD .x6 .x28 (0)),
  (0x162c, .SLLI .x10 .x6 (3)),
  (0x1630, .SLLI .x11 .x6 (5)),
  (0x1634, .ADD .x10 .x10 .x11),
  (0x1638, .LUI .x28 67),
  (0x163c, .ADDI .x28 .x28 (104)),
  (0x1640, .LD .x6 .x28 (0)),
  (0x1644, .ADD .x6 .x6 .x10),
  (0x1648, .LUI .x7 64),
  (0x164c, .ADDI .x7 .x7 (40))]

def leftSetup (s : MachineState) : MachineState := runSchedule leftSetupSchedule s

theorem leftSetup_code : ∀ e ∈ leftSetupSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem leftSetup_checked (s : MachineState) (pc : s.pc = 0x1620) : Checked leftSetupSchedule s := by
  simp [leftSetupSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem leftSetup_block (s : MachineState) (pc : s.pc = 0x1620) :
    OrdinarySteps SphincsMaskedImages.keygen s 12 (leftSetup s) :=
  checked_sound _ leftSetupSchedule leftSetup_code s (leftSetup_checked s pc)

theorem leftSetup_pc (s : MachineState) (pc : s.pc = 0x1620) :
    (leftSetup s).pc = 0x1650 := by
  simp [leftSetup,runSchedule,leftSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def rightSetupSchedule : List (Word × Instr) := [
  (0x1678, .ADDI .x6 .x6 (20)),
  (0x167c, .LUI .x7 64),
  (0x1680, .ADDI .x7 .x7 (60))]

def rightSetup (s : MachineState) : MachineState := runSchedule rightSetupSchedule s

theorem rightSetup_code : ∀ e ∈ rightSetupSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem rightSetup_checked (s : MachineState) (pc : s.pc = 0x1678) : Checked rightSetupSchedule s := by
  simp [rightSetupSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem rightSetup_block (s : MachineState) (pc : s.pc = 0x1678) :
    OrdinarySteps SphincsMaskedImages.keygen s 3 (rightSetup s) :=
  checked_sound _ rightSetupSchedule rightSetup_code s (rightSetup_checked s pc)

theorem rightSetup_pc (s : MachineState) (pc : s.pc = 0x1678) :
    (rightSetup s).pc = 0x1684 := by
  simp [rightSetup,runSchedule,rightSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def hashPrepareSchedule : List (Word × Instr) := [
  (0x16ac, .LUI .x28 67),
  (0x16b0, .ADDI .x28 .x28 (72)),
  (0x16b4, .LD .x6 .x28 (0)),
  (0x16b8, .LUI .x28 67),
  (0x16bc, .ADDI .x28 .x28 (16)),
  (0x16c0, .SD .x28 .x6 (0)),
  (0x16c4, .LUI .x28 67),
  (0x16c8, .ADDI .x28 .x28 (136)),
  (0x16cc, .LD .x6 .x28 (0)),
  (0x16d0, .LUI .x28 67),
  (0x16d4, .ADDI .x28 .x28 (24)),
  (0x16d8, .SD .x28 .x6 (0)),
  (0x16dc, .ADDI .x6 .x0 (769)),
  (0x16e0, .LUI .x28 67),
  (0x16e4, .ADDI .x28 .x28 (0)),
  (0x16e8, .LD .x7 .x28 (0)),
  (0x16ec, .SLLI .x7 .x7 (16)),
  (0x16f0, .ADD .x6 .x6 .x7),
  (0x16f4, .LUI .x7 64),
  (0x16f8, .ADDI .x7 .x7 (0)),
  (0x16fc, .SW .x7 .x6 (0)),
  (0x1700, .LUI .x28 67),
  (0x1704, .ADDI .x28 .x28 (16)),
  (0x1708, .LD .x6 .x28 (0)),
  (0x170c, .SW .x7 .x6 (4)),
  (0x1710, .LUI .x28 67),
  (0x1714, .ADDI .x28 .x28 (8)),
  (0x1718, .LD .x6 .x28 (0)),
  (0x171c, .SD .x7 .x6 (8)),
  (0x1720, .LUI .x28 67),
  (0x1724, .ADDI .x28 .x28 (24)),
  (0x1728, .LD .x6 .x28 (0)),
  (0x172c, .SW .x7 .x6 (16)),
  (0x1730, .ADDI .x6 .x0 (116)),
  (0x1734, .LUI .x7 64),
  (0x1738, .ADDI .x7 .x7 (20)),
  (0x173c, .LWU .x13 .x6 (0)),
  (0x1740, .SW .x7 .x13 (0)),
  (0x1744, .LWU .x13 .x6 (4)),
  (0x1748, .SW .x7 .x13 (4)),
  (0x174c, .LWU .x13 .x6 (8)),
  (0x1750, .SW .x7 .x13 (8)),
  (0x1754, .LWU .x13 .x6 (12)),
  (0x1758, .SW .x7 .x13 (12)),
  (0x175c, .LWU .x13 .x6 (16)),
  (0x1760, .SW .x7 .x13 (16)),
  (0x1764, .LUI .x10 64),
  (0x1768, .ADDI .x10 .x10 (0)),
  (0x176c, .ADDI .x11 .x0 (640)),
  (0x1770, .LUI .x12 66),
  (0x1774, .ADDI .x12 .x12 (0)),
  (0x1778, .ADDI .x5 .x0 (1))]

def hashPrepare (s : MachineState) : MachineState := runSchedule hashPrepareSchedule s

theorem hashPrepare_code : ∀ e ∈ hashPrepareSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem hashPrepare_checked (s : MachineState) (pc : s.pc = 0x16ac) : Checked hashPrepareSchedule s := by
  simp [hashPrepareSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem hashPrepare_block (s : MachineState) (pc : s.pc = 0x16ac) :
    OrdinarySteps SphincsMaskedImages.keygen s 52 (hashPrepare s) :=
  checked_sound _ hashPrepareSchedule hashPrepare_code s (hashPrepare_checked s pc)

theorem hashPrepare_pc (s : MachineState) (pc : s.pc = 0x16ac) :
    (hashPrepare s).pc = 0x177c := by
  simp [hashPrepare,runSchedule,hashPrepareSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def storeSetupSchedule : List (Word × Instr) := [
  (0x1780, .LUI .x28 67),
  (0x1784, .ADDI .x28 .x28 (136)),
  (0x1788, .LD .x7 .x28 (0)),
  (0x178c, .SLLI .x10 .x7 (2)),
  (0x1790, .SLLI .x11 .x7 (4)),
  (0x1794, .ADD .x10 .x10 .x11),
  (0x1798, .LUI .x28 67),
  (0x179c, .ADDI .x28 .x28 (128)),
  (0x17a0, .LD .x7 .x28 (0)),
  (0x17a4, .ADD .x7 .x7 .x10),
  (0x17a8, .LUI .x6 66),
  (0x17ac, .ADDI .x6 .x6 (0))]

def storeSetup (s : MachineState) : MachineState := runSchedule storeSetupSchedule s

theorem storeSetup_code : ∀ e ∈ storeSetupSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem storeSetup_checked (s : MachineState) (pc : s.pc = 0x1780) : Checked storeSetupSchedule s := by
  simp [storeSetupSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem storeSetup_block (s : MachineState) (pc : s.pc = 0x1780) :
    OrdinarySteps SphincsMaskedImages.keygen s 12 (storeSetup s) :=
  checked_sound _ storeSetupSchedule storeSetup_code s (storeSetup_checked s pc)

theorem storeSetup_pc (s : MachineState) (pc : s.pc = 0x1780) :
    (storeSetup s).pc = 0x17b0 := by
  simp [storeSetup,runSchedule,storeSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def nodeFinishSchedule : List (Word × Instr) := [
  (0x17d8, .LUI .x28 67),
  (0x17dc, .ADDI .x28 .x28 (136)),
  (0x17e0, .LD .x6 .x28 (0)),
  (0x17e4, .ADDI .x6 .x6 (1)),
  (0x17e8, .LUI .x28 67),
  (0x17ec, .ADDI .x28 .x28 (136)),
  (0x17f0, .SD .x28 .x6 (0)),
  (0x17f4, .LUI .x28 67),
  (0x17f8, .ADDI .x28 .x28 (136)),
  (0x17fc, .LD .x6 .x28 (0)),
  (0x1800, .LUI .x28 67),
  (0x1804, .ADDI .x28 .x28 (144)),
  (0x1808, .LD .x7 .x28 (0)),
  (0x180c, .BNE .x6 .x7 (-492))]

def nodeFinish (s : MachineState) : MachineState := runSchedule nodeFinishSchedule s

theorem nodeFinish_code : ∀ e ∈ nodeFinishSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem nodeFinish_checked (s : MachineState) (pc : s.pc = 0x17d8) : Checked nodeFinishSchedule s := by
  simp [nodeFinishSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem nodeFinish_block (s : MachineState) (pc : s.pc = 0x17d8) :
    OrdinarySteps SphincsMaskedImages.keygen s 14 (nodeFinish s) :=
  checked_sound _ nodeFinishSchedule nodeFinish_code s (nodeFinish_checked s pc)

def levelFinishSchedule : List (Word × Instr) := [
  (0x1810, .LUI .x28 67),
  (0x1814, .ADDI .x28 .x28 (128)),
  (0x1818, .LD .x6 .x28 (0)),
  (0x181c, .LUI .x28 67),
  (0x1820, .ADDI .x28 .x28 (104)),
  (0x1824, .SD .x28 .x6 (0)),
  (0x1828, .LUI .x28 67),
  (0x182c, .ADDI .x28 .x28 (144)),
  (0x1830, .LD .x7 .x28 (0)),
  (0x1834, .SLLI .x10 .x7 (2)),
  (0x1838, .SLLI .x11 .x7 (4)),
  (0x183c, .ADD .x10 .x10 .x11),
  (0x1840, .ADD .x6 .x6 .x10),
  (0x1844, .LUI .x28 67),
  (0x1848, .ADDI .x28 .x28 (128)),
  (0x184c, .SD .x28 .x6 (0)),
  (0x1850, .LUI .x28 67),
  (0x1854, .ADDI .x28 .x28 (144)),
  (0x1858, .LD .x6 .x28 (0)),
  (0x185c, .SRLI .x6 .x6 (1)),
  (0x1860, .LUI .x28 67),
  (0x1864, .ADDI .x28 .x28 (144)),
  (0x1868, .SD .x28 .x6 (0)),
  (0x186c, .LUI .x28 67),
  (0x1870, .ADDI .x28 .x28 (72)),
  (0x1874, .LD .x6 .x28 (0)),
  (0x1878, .ADDI .x6 .x6 (1)),
  (0x187c, .LUI .x28 67),
  (0x1880, .ADDI .x28 .x28 (72)),
  (0x1884, .SD .x28 .x6 (0)),
  (0x1888, .LUI .x28 67),
  (0x188c, .ADDI .x28 .x28 (72)),
  (0x1890, .LD .x6 .x28 (0)),
  (0x1894, .ADDI .x7 .x0 (12)),
  (0x1898, .BNE .x6 .x7 (-648))]

def levelFinish (s : MachineState) : MachineState := runSchedule levelFinishSchedule s

theorem levelFinish_code : ∀ e ∈ levelFinishSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem levelFinish_checked (s : MachineState) (pc : s.pc = 0x1810) : Checked levelFinishSchedule s := by
  simp [levelFinishSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem levelFinish_block (s : MachineState) (pc : s.pc = 0x1810) :
    OrdinarySteps SphincsMaskedImages.keygen s 35 (levelFinish s) :=
  checked_sound _ levelFinishSchedule levelFinish_code s (levelFinish_checked s pc)

def rootSetupSchedule : List (Word × Instr) := [
  (0x189c, .LUI .x28 67),
  (0x18a0, .ADDI .x28 .x28 (104)),
  (0x18a4, .LD .x6 .x28 (0)),
  (0x18a8, .ADDI .x7 .x0 (96))]

def rootSetup (s : MachineState) : MachineState := runSchedule rootSetupSchedule s

theorem rootSetup_code : ∀ e ∈ rootSetupSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem rootSetup_checked (s : MachineState) (pc : s.pc = 0x189c) : Checked rootSetupSchedule s := by
  simp [rootSetupSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem rootSetup_block (s : MachineState) (pc : s.pc = 0x189c) :
    OrdinarySteps SphincsMaskedImages.keygen s 4 (rootSetup s) :=
  checked_sound _ rootSetupSchedule rootSetup_code s (rootSetup_checked s pc)

theorem rootSetup_pc (s : MachineState) (pc : s.pc = 0x189c) :
    (rootSetup s).pc = 0x18ac := by
  simp [rootSetup,runSchedule,rootSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def commitPrepareSchedule : List (Word × Instr) := [
  (0x18d4, .ADDI .x6 .x0 (0)),
  (0x18d8, .LUI .x28 67),
  (0x18dc, .ADDI .x28 .x28 (0)),
  (0x18e0, .SD .x28 .x6 (0)),
  (0x18e4, .ADDI .x6 .x0 (0)),
  (0x18e8, .LUI .x28 67),
  (0x18ec, .ADDI .x28 .x28 (8)),
  (0x18f0, .SD .x28 .x6 (0)),
  (0x18f4, .ADDI .x6 .x0 (0)),
  (0x18f8, .LUI .x28 67),
  (0x18fc, .ADDI .x28 .x28 (16)),
  (0x1900, .SD .x28 .x6 (0)),
  (0x1904, .ADDI .x6 .x0 (0)),
  (0x1908, .LUI .x28 67),
  (0x190c, .ADDI .x28 .x28 (24)),
  (0x1910, .SD .x28 .x6 (0)),
  (0x1914, .ADDI .x6 .x0 (96)),
  (0x1918, .LUI .x7 64),
  (0x191c, .ADDI .x7 .x7 (20)),
  (0x1920, .LWU .x13 .x6 (0)),
  (0x1924, .SW .x7 .x13 (0)),
  (0x1928, .LWU .x13 .x6 (4)),
  (0x192c, .SW .x7 .x13 (4)),
  (0x1930, .LWU .x13 .x6 (8)),
  (0x1934, .SW .x7 .x13 (8)),
  (0x1938, .LWU .x13 .x6 (12)),
  (0x193c, .SW .x7 .x13 (12)),
  (0x1940, .LWU .x13 .x6 (16)),
  (0x1944, .SW .x7 .x13 (16)),
  (0x1948, .ADDI .x6 .x0 (116)),
  (0x194c, .LUI .x7 64),
  (0x1950, .ADDI .x7 .x7 (40)),
  (0x1954, .LWU .x13 .x6 (0)),
  (0x1958, .SW .x7 .x13 (0)),
  (0x195c, .LWU .x13 .x6 (4)),
  (0x1960, .SW .x7 .x13 (4)),
  (0x1964, .LWU .x13 .x6 (8)),
  (0x1968, .SW .x7 .x13 (8)),
  (0x196c, .LWU .x13 .x6 (12)),
  (0x1970, .SW .x7 .x13 (12)),
  (0x1974, .LWU .x13 .x6 (16)),
  (0x1978, .SW .x7 .x13 (16)),
  (0x197c, .LUI .x6 1),
  (0x1980, .ADDI .x6 .x6 (-767)),
  (0x1984, .LUI .x28 67),
  (0x1988, .ADDI .x28 .x28 (0)),
  (0x198c, .LD .x7 .x28 (0)),
  (0x1990, .SLLI .x7 .x7 (16)),
  (0x1994, .ADD .x6 .x6 .x7),
  (0x1998, .LUI .x7 64),
  (0x199c, .ADDI .x7 .x7 (0)),
  (0x19a0, .SW .x7 .x6 (0)),
  (0x19a4, .LUI .x28 67),
  (0x19a8, .ADDI .x28 .x28 (16)),
  (0x19ac, .LD .x6 .x28 (0)),
  (0x19b0, .SW .x7 .x6 (4)),
  (0x19b4, .LUI .x28 67),
  (0x19b8, .ADDI .x28 .x28 (8)),
  (0x19bc, .LD .x6 .x28 (0)),
  (0x19c0, .SD .x7 .x6 (8)),
  (0x19c4, .LUI .x28 67),
  (0x19c8, .ADDI .x28 .x28 (24)),
  (0x19cc, .LD .x6 .x28 (0)),
  (0x19d0, .SW .x7 .x6 (16)),
  (0x19d4, .LUI .x10 64),
  (0x19d8, .ADDI .x10 .x10 (0)),
  (0x19dc, .ADDI .x11 .x0 (480)),
  (0x19e0, .LUI .x12 66),
  (0x19e4, .ADDI .x12 .x12 (0)),
  (0x19e8, .ADDI .x5 .x0 (1))]

def commitPrepare (s : MachineState) : MachineState := runSchedule commitPrepareSchedule s

theorem commitPrepare_code : ∀ e ∈ commitPrepareSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem commitPrepare_checked (s : MachineState) (pc : s.pc = 0x18d4) : Checked commitPrepareSchedule s := by
  simp [commitPrepareSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem commitPrepare_block (s : MachineState) (pc : s.pc = 0x18d4) :
    OrdinarySteps SphincsMaskedImages.keygen s 70 (commitPrepare s) :=
  checked_sound _ commitPrepareSchedule commitPrepare_code s (commitPrepare_checked s pc)

theorem commitPrepare_pc (s : MachineState) (pc : s.pc = 0x18d4) :
    (commitPrepare s).pc = 0x19ec := by
  simp [commitPrepare,runSchedule,commitPrepareSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

def commitCopySetupSchedule : List (Word × Instr) := [
  (0x19f0, .LUI .x6 66),
  (0x19f4, .ADDI .x6 .x6 (0)),
  (0x19f8, .ADDI .x7 .x0 (64)),
  (0x19fc, .ADDI .x10 .x0 (2))]

def commitCopySetup (s : MachineState) : MachineState := runSchedule commitCopySetupSchedule s

theorem commitCopySetup_code : ∀ e ∈ commitCopySetupSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem commitCopySetup_checked (s : MachineState) (pc : s.pc = 0x19f0) : Checked commitCopySetupSchedule s := by
  simp [commitCopySetupSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem commitCopySetup_block (s : MachineState) (pc : s.pc = 0x19f0) :
    OrdinarySteps SphincsMaskedImages.keygen s 4 (commitCopySetup s) :=
  checked_sound _ commitCopySetupSchedule commitCopySetup_code s (commitCopySetup_checked s pc)

theorem commitCopySetup_pc (s : MachineState) (pc : s.pc = 0x19f0) :
    (commitCopySetup s).pc = 0x1a00 := by
  simp [commitCopySetup,runSchedule,commitCopySetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

/-- info: 'SigGolfCandidate.SphincsMaskedParentCode.commitPrepare_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms commitPrepare_block

end SigGolfCandidate.SphincsMaskedParentCode
