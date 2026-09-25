import SigGolfCandidate.SphincsMaskedSignForestLoop

/-! Exact masked signer FORS parent-tree execution and semantic induction.
`parents_execution` is unconditional apart from the entry PC. The semantic
`parents_complete` additionally uses an explicit local `NodeContract`;
`node_contract_of_query` reduces that contract to query identification and
memory-based context stability. All eight levels share the same node proof.
-/

namespace SigGolfCandidate.SphincsMaskedSignForestParents
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy SphincsVerifierCopy SphincsVerifierCopyMemory
open SphincsVerifierMessageCopy SphincsVerifierFtsCopyAccess SphincsVerifierFtsPriorRoots
open SphincsVerifierFtsGenericCopyData SphincsMaskedChainDomain
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def initSchedule : List (Word × Instr) := [
  (0x1fe8, .ADDI .x6 .x0 1),
  (0x1fec, .LUI .x28 67),
  (0x1ff0, .ADDI .x28 .x28 72),
  (0x1ff4, .SD .x28 .x6 0),
  (0x1ff8, .LUI .x6 80),
  (0x1ffc, .ADDI .x6 .x6 0),
  (0x2000, .LUI .x28 67),
  (0x2004, .ADDI .x28 .x28 104),
  (0x2008, .SD .x28 .x6 0),
  (0x200c, .LUI .x6 81),
  (0x2010, .ADDI .x6 .x6 1024),
  (0x2014, .LUI .x28 67),
  (0x2018, .ADDI .x28 .x28 128),
  (0x201c, .SD .x28 .x6 0),
  (0x2020, .ADDI .x6 .x0 128),
  (0x2024, .LUI .x28 67),
  (0x2028, .ADDI .x28 .x28 144),
  (0x202c, .SD .x28 .x6 0)]

def init (s : MachineState) : MachineState := runSchedule initSchedule s

theorem init_code : ∀ e ∈ initSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem init_checked (s : MachineState) (pc : s.pc = 0x1fe8) :
    Checked initSchedule s := by
  simp [initSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem init_block (s : MachineState) (pc : s.pc = 0x1fe8) :
    OrdinarySteps SphincsMaskedImages.sign s 18 (init s) :=
  checked_sound _ initSchedule init_code s (init_checked s pc)

theorem init_pc (s : MachineState) (pc : s.pc = 0x1fe8) :
    (init s).pc = 0x2030 := by
  simp [init, runSchedule, initSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def levelEntrySchedule : List (Word × Instr) := [
  (0x2030, .ADDI .x6 .x0 0),
  (0x2034, .LUI .x28 67),
  (0x2038, .ADDI .x28 .x28 136),
  (0x203c, .SD .x28 .x6 0)]

def levelEntry (s : MachineState) : MachineState := runSchedule levelEntrySchedule s

theorem levelEntry_code : ∀ e ∈ levelEntrySchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem levelEntry_checked (s : MachineState) (pc : s.pc = 0x2030) :
    Checked levelEntrySchedule s := by
  simp [levelEntrySchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem levelEntry_block (s : MachineState) (pc : s.pc = 0x2030) :
    OrdinarySteps SphincsMaskedImages.sign s 4 (levelEntry s) :=
  checked_sound _ levelEntrySchedule levelEntry_code s (levelEntry_checked s pc)

theorem levelEntry_pc (s : MachineState) (pc : s.pc = 0x2030) :
    (levelEntry s).pc = 0x2040 := by
  simp [levelEntry, runSchedule, levelEntrySchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def leftSetupSchedule : List (Word × Instr) := [
  (0x2040, .LUI .x28 67),
  (0x2044, .ADDI .x28 .x28 136),
  (0x2048, .LD .x6 .x28 0),
  (0x204c, .SLLI .x10 .x6 3),
  (0x2050, .SLLI .x11 .x6 5),
  (0x2054, .ADD .x10 .x10 .x11),
  (0x2058, .LUI .x28 67),
  (0x205c, .ADDI .x28 .x28 104),
  (0x2060, .LD .x6 .x28 0),
  (0x2064, .ADD .x6 .x6 .x10),
  (0x2068, .LUI .x7 64),
  (0x206c, .ADDI .x7 .x7 40)]

def leftSetup (s : MachineState) : MachineState := runSchedule leftSetupSchedule s

theorem leftSetup_code : ∀ e ∈ leftSetupSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem leftSetup_checked (s : MachineState) (pc : s.pc = 0x2040) :
    Checked leftSetupSchedule s := by
  simp [leftSetupSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem leftSetup_block (s : MachineState) (pc : s.pc = 0x2040) :
    OrdinarySteps SphincsMaskedImages.sign s 12 (leftSetup s) :=
  checked_sound _ leftSetupSchedule leftSetup_code s (leftSetup_checked s pc)

theorem leftSetup_pc (s : MachineState) (pc : s.pc = 0x2040) :
    (leftSetup s).pc = 0x2070 := by
  simp [leftSetup, runSchedule, leftSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def rightSetupSchedule : List (Word × Instr) := [
  (0x2098, .ADDI .x6 .x6 20),
  (0x209c, .LUI .x7 64),
  (0x20a0, .ADDI .x7 .x7 60)]

def rightSetup (s : MachineState) : MachineState := runSchedule rightSetupSchedule s

theorem rightSetup_code : ∀ e ∈ rightSetupSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem rightSetup_checked (s : MachineState) (pc : s.pc = 0x2098) :
    Checked rightSetupSchedule s := by
  simp [rightSetupSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem rightSetup_block (s : MachineState) (pc : s.pc = 0x2098) :
    OrdinarySteps SphincsMaskedImages.sign s 3 (rightSetup s) :=
  checked_sound _ rightSetupSchedule rightSetup_code s (rightSetup_checked s pc)

theorem rightSetup_pc (s : MachineState) (pc : s.pc = 0x2098) :
    (rightSetup s).pc = 0x20a4 := by
  simp [rightSetup, runSchedule, rightSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def hashPrepareSchedule : List (Word × Instr) := [
  (0x20cc, .LUI .x28 67),
  (0x20d0, .ADDI .x28 .x28 72),
  (0x20d4, .LD .x6 .x28 0),
  (0x20d8, .LUI .x28 67),
  (0x20dc, .ADDI .x28 .x28 16),
  (0x20e0, .SD .x28 .x6 0),
  (0x20e4, .LUI .x28 67),
  (0x20e8, .ADDI .x28 .x28 136),
  (0x20ec, .LD .x6 .x28 0),
  (0x20f0, .LUI .x28 67),
  (0x20f4, .ADDI .x28 .x28 24),
  (0x20f8, .SD .x28 .x6 0),
  (0x20fc, .LUI .x6 1),
  (0x2100, .ADDI .x6 .x6 (-1535)),
  (0x2104, .LUI .x28 67),
  (0x2108, .ADDI .x28 .x28 0),
  (0x210c, .LD .x7 .x28 0),
  (0x2110, .SLLI .x7 .x7 16),
  (0x2114, .ADD .x6 .x6 .x7),
  (0x2118, .LUI .x7 64),
  (0x211c, .ADDI .x7 .x7 0),
  (0x2120, .SW .x7 .x6 0),
  (0x2124, .LUI .x28 67),
  (0x2128, .ADDI .x28 .x28 16),
  (0x212c, .LD .x6 .x28 0),
  (0x2130, .SW .x7 .x6 4),
  (0x2134, .LUI .x28 67),
  (0x2138, .ADDI .x28 .x28 8),
  (0x213c, .LD .x6 .x28 0),
  (0x2140, .SD .x7 .x6 8),
  (0x2144, .LUI .x28 67),
  (0x2148, .ADDI .x28 .x28 24),
  (0x214c, .LD .x6 .x28 0),
  (0x2150, .SW .x7 .x6 16),
  (0x2154, .ADDI .x6 .x0 116),
  (0x2158, .LUI .x7 64),
  (0x215c, .ADDI .x7 .x7 20),
  (0x2160, .LWU .x13 .x6 0),
  (0x2164, .SW .x7 .x13 0),
  (0x2168, .LWU .x13 .x6 4),
  (0x216c, .SW .x7 .x13 4),
  (0x2170, .LWU .x13 .x6 8),
  (0x2174, .SW .x7 .x13 8),
  (0x2178, .LWU .x13 .x6 12),
  (0x217c, .SW .x7 .x13 12),
  (0x2180, .LWU .x13 .x6 16),
  (0x2184, .SW .x7 .x13 16),
  (0x2188, .LUI .x10 64),
  (0x218c, .ADDI .x10 .x10 0),
  (0x2190, .ADDI .x11 .x0 640),
  (0x2194, .LUI .x12 66),
  (0x2198, .ADDI .x12 .x12 0),
  (0x219c, .ADDI .x5 .x0 1)]

def hashPrepare (s : MachineState) : MachineState := runSchedule hashPrepareSchedule s

theorem hashPrepare_code : ∀ e ∈ hashPrepareSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem hashPrepare_checked (s : MachineState) (pc : s.pc = 0x20cc) :
    Checked hashPrepareSchedule s := by
  simp [hashPrepareSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem hashPrepare_block (s : MachineState) (pc : s.pc = 0x20cc) :
    OrdinarySteps SphincsMaskedImages.sign s 53 (hashPrepare s) :=
  checked_sound _ hashPrepareSchedule hashPrepare_code s (hashPrepare_checked s pc)

theorem hashPrepare_pc (s : MachineState) (pc : s.pc = 0x20cc) :
    (hashPrepare s).pc = 0x21a0 := by
  simp [hashPrepare, runSchedule, hashPrepareSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def storeSetupSchedule : List (Word × Instr) := [
  (0x21a4, .LUI .x28 67),
  (0x21a8, .ADDI .x28 .x28 136),
  (0x21ac, .LD .x7 .x28 0),
  (0x21b0, .SLLI .x10 .x7 2),
  (0x21b4, .SLLI .x11 .x7 4),
  (0x21b8, .ADD .x10 .x10 .x11),
  (0x21bc, .LUI .x28 67),
  (0x21c0, .ADDI .x28 .x28 128),
  (0x21c4, .LD .x7 .x28 0),
  (0x21c8, .ADD .x7 .x7 .x10),
  (0x21cc, .LUI .x6 66),
  (0x21d0, .ADDI .x6 .x6 0)]

def storeSetup (s : MachineState) : MachineState := runSchedule storeSetupSchedule s

theorem storeSetup_code : ∀ e ∈ storeSetupSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem storeSetup_checked (s : MachineState) (pc : s.pc = 0x21a4) :
    Checked storeSetupSchedule s := by
  simp [storeSetupSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem storeSetup_block (s : MachineState) (pc : s.pc = 0x21a4) :
    OrdinarySteps SphincsMaskedImages.sign s 12 (storeSetup s) :=
  checked_sound _ storeSetupSchedule storeSetup_code s (storeSetup_checked s pc)

theorem storeSetup_pc (s : MachineState) (pc : s.pc = 0x21a4) :
    (storeSetup s).pc = 0x21d4 := by
  simp [storeSetup, runSchedule, storeSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def nodeFinishSchedule : List (Word × Instr) := [
  (0x21fc, .LUI .x28 67),
  (0x2200, .ADDI .x28 .x28 136),
  (0x2204, .LD .x6 .x28 0),
  (0x2208, .ADDI .x6 .x6 1),
  (0x220c, .LUI .x28 67),
  (0x2210, .ADDI .x28 .x28 136),
  (0x2214, .SD .x28 .x6 0),
  (0x2218, .LUI .x28 67),
  (0x221c, .ADDI .x28 .x28 136),
  (0x2220, .LD .x6 .x28 0),
  (0x2224, .LUI .x28 67),
  (0x2228, .ADDI .x28 .x28 144),
  (0x222c, .LD .x7 .x28 0),
  (0x2230, .BNE .x6 .x7 (-496))]

def nodeFinish (s : MachineState) : MachineState := runSchedule nodeFinishSchedule s

theorem nodeFinish_code : ∀ e ∈ nodeFinishSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem nodeFinish_checked (s : MachineState) (pc : s.pc = 0x21fc) :
    Checked nodeFinishSchedule s := by
  simp [nodeFinishSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem nodeFinish_block (s : MachineState) (pc : s.pc = 0x21fc) :
    OrdinarySteps SphincsMaskedImages.sign s 14 (nodeFinish s) :=
  checked_sound _ nodeFinishSchedule nodeFinish_code s (nodeFinish_checked s pc)

def levelFinishSchedule : List (Word × Instr) := [
  (0x2234, .LUI .x28 67),
  (0x2238, .ADDI .x28 .x28 128),
  (0x223c, .LD .x6 .x28 0),
  (0x2240, .LUI .x28 67),
  (0x2244, .ADDI .x28 .x28 104),
  (0x2248, .SD .x28 .x6 0),
  (0x224c, .LUI .x28 67),
  (0x2250, .ADDI .x28 .x28 144),
  (0x2254, .LD .x7 .x28 0),
  (0x2258, .SLLI .x10 .x7 2),
  (0x225c, .SLLI .x11 .x7 4),
  (0x2260, .ADD .x10 .x10 .x11),
  (0x2264, .ADD .x6 .x6 .x10),
  (0x2268, .LUI .x28 67),
  (0x226c, .ADDI .x28 .x28 128),
  (0x2270, .SD .x28 .x6 0),
  (0x2274, .LUI .x28 67),
  (0x2278, .ADDI .x28 .x28 144),
  (0x227c, .LD .x6 .x28 0),
  (0x2280, .SRLI .x6 .x6 1),
  (0x2284, .LUI .x28 67),
  (0x2288, .ADDI .x28 .x28 144),
  (0x228c, .SD .x28 .x6 0),
  (0x2290, .LUI .x28 67),
  (0x2294, .ADDI .x28 .x28 72),
  (0x2298, .LD .x6 .x28 0),
  (0x229c, .ADDI .x6 .x6 1),
  (0x22a0, .LUI .x28 67),
  (0x22a4, .ADDI .x28 .x28 72),
  (0x22a8, .SD .x28 .x6 0),
  (0x22ac, .LUI .x28 67),
  (0x22b0, .ADDI .x28 .x28 72),
  (0x22b4, .LD .x6 .x28 0),
  (0x22b8, .ADDI .x7 .x0 9),
  (0x22bc, .BNE .x6 .x7 (-652))]

def levelFinish (s : MachineState) : MachineState := runSchedule levelFinishSchedule s

theorem levelFinish_code : ∀ e ∈ levelFinishSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem levelFinish_checked (s : MachineState) (pc : s.pc = 0x2234) :
    Checked levelFinishSchedule s := by
  simp [levelFinishSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem levelFinish_block (s : MachineState) (pc : s.pc = 0x2234) :
    OrdinarySteps SphincsMaskedImages.sign s 35 (levelFinish s) :=
  checked_sound _ levelFinishSchedule levelFinish_code s (levelFinish_checked s pc)

theorem leftSetup_registers (s : MachineState) (base node : Nat)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node) :
    (leftSetup s).getReg .x6 = BitVec.ofNat 64 (base + 40 * node) ∧
      (leftSetup s).getReg .x7 = 0x40028 := by
  change s.getMem 0x43068#64 = BitVec.ofNat 64 base at hb
  change s.getMem 0x43088#64 = BitVec.ofNat 64 node at hn
  simp [leftSetup,runSchedule,leftSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,hb,hn]
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 base + (BitVec.ofNat 64 node * BitVec.ofNat 64 8 +
    BitVec.ofNat 64 node * BitVec.ofNat 64 32) = _
  rw [← BitVec.ofNat_mul,← BitVec.ofNat_mul,← BitVec.ofNat_add,← BitVec.ofNat_add]
  congr 1;omega

theorem leftSetup_frame (s : MachineState) (a : Word) : (leftSetup s).getMem a = s.getMem a := by
  simp [leftSetup,runSchedule,leftSetupSchedule,execInstrBr]

theorem rightSetup_frame (s : MachineState) (a : Word) : (rightSetup s).getMem a = s.getMem a := by
  simp [rightSetup,runSchedule,rightSetupSchedule,execInstrBr]

theorem rightSetup_registers (s : MachineState) (source : Nat) (hs : s.getReg .x6 = BitVec.ofNat 64 source) :
    (rightSetup s).getReg .x6 = BitVec.ofNat 64 (source + 20) ∧ (rightSetup s).getReg .x7 = 0x4003c := by
  simp [rightSetup,runSchedule,rightSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,hs,BitVec.ofNat_add]

def leftCopied (s : MachineState) := copyRootState (leftSetup s)
def children (s : MachineState) := copyRootState (rightSetup (leftCopied s))

theorem copyRoot_pc (s : MachineState) : (copyRootState s).pc = s.pc + 40 := by
  simp [copyRootState,copyWordState,execInstrBr,BitVec.add_assoc]

theorem copyRoot_registers (s : MachineState) :
    (copyRootState s).getReg .x6 = s.getReg .x6 ∧ (copyRootState s).getReg .x7 = s.getReg .x7 := by
  simp [copyRootState,copyWordState,execInstrBr,MachineState.getReg_setReg_ne,MachineState.setWord32]

theorem leftCopied_pc (s : MachineState) (pc : s.pc = 0x2040) : (leftCopied s).pc = 0x2098 := by
  rw [leftCopied,copyRoot_pc,leftSetup_pc s pc];rfl

theorem children_pc (s : MachineState) (pc : s.pc = 0x2040) : (children s).pc = 0x20cc := by
  rw [children,copyRoot_pc,rightSetup_pc _ (leftCopied_pc s pc)];rfl

theorem left_copy_code : Copy20Code SphincsMaskedImages.sign 1052 := by
  constructor <;> intro i <;> fin_cases i <;> decide

theorem right_copy_code : Copy20Code SphincsMaskedImages.sign 1065 := by
  constructor <;> intro i <;> fin_cases i <;> decide

theorem children_block (s : MachineState) (base node : Nat) (pc : s.pc = 0x2040)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : base + 40 * node + 40 ≤ 0x60000) (aligned : base % 4 = 0) :
    OrdinarySteps SphincsMaskedImages.sign s 35 (children s) := by
  have left := leftSetup_registers s base node hb hn
  have lcopy := copy20_block_general SphincsMaskedImages.sign 1052 left_copy_code
    (leftSetup s) (base + 40 * node) 0x40028 (leftSetup_pc s pc) left.1 left.2
    (by omega) (by dsimp [MEMORY_BYTES];omega) (by decide) (by decide) (by decide)
  have source : (leftCopied s).getReg .x6 = BitVec.ofNat 64 (base + 40 * node) :=
    (copyRoot_registers (leftSetup s)).1.trans left.1
  have right := rightSetup_registers (leftCopied s) (base + 40 * node) source
  have rcopy := copy20_block_general SphincsMaskedImages.sign 1065 right_copy_code
    (rightSetup (leftCopied s)) (base + 40 * node + 20) 0x4003c
    (rightSetup_pc _ (leftCopied_pc s pc)) right.1 right.2
    (by omega) (by dsimp [MEMORY_BYTES];omega) (by decide) (by decide) (by decide)
  exact ordinary_trans _ _ _ _ 12 23 (leftSetup_block s pc)
    (ordinary_trans _ _ _ _ 10 13 lcopy (ordinary_trans _ _ _ _ 3 10
      (rightSetup_block _ (leftCopied_pc s pc)) rcopy))

def payloadWrites : List Word := [0x40028#64,0x40030#64,0x40038#64,0x40040#64,0x40048#64]

theorem children_frame (s : MachineState) (a : Word) (outside : a ∉ payloadWrites) :
    (children s).getMem a = s.getMem a := by
  have left : (leftSetup s).getReg .x7 = 0x40028 := by
    simp [leftSetup,runSchedule,leftSetupSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have right : (rightSetup (leftCopied s)).getReg .x7 = 0x4003c := by
    simp [rightSetup,runSchedule,rightSetupSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  change (copyRootState (rightSetup (leftCopied s))).getMem a = _
  rw [copyRoot_mem_frame]
  · rw [rightSetup_frame]
    change (copyRootState (leftSetup s)).getMem a = _
    rw [copyRoot_mem_frame]
    · exact leftSetup_frame s a
    · intro i;rw [left]
      fin_cases i <;> simp_all [payloadWrites,signExtend12,alignToDword]
  · intro i;rw [right]
    fin_cases i <;> simp_all [payloadWrites,signExtend12,alignToDword]

def headerWrites : List Word := [0x43010#64,0x43018#64,0x40000#64,0x40008#64,0x40010#64,0x40018#64,0x40020#64]

theorem hashPrepare_frame (s : MachineState) (a : Word) (outside : a ∉ headerWrites) :
    (hashPrepare s).getMem a = s.getMem a := by
  simp only [headerWrites,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := outside
  simp [hashPrepare,runSchedule,hashPrepareSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,h0,h1,h2,h3,h4,h5,h6]

theorem hashPrepare_registers (s : MachineState) :
    (hashPrepare s).getReg .x10 = 0x40000 ∧ (hashPrepare s).getReg .x11 = 640 ∧
      (hashPrepare s).getReg .x12 = 0x42000 ∧ (hashPrepare s).getReg .x5 = 1 := by
  simp [hashPrepare,runSchedule,hashPrepareSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

def answer (hash : Hash) (s : MachineState) :=
  writeHash (hashPrepare (children s)) (hash (hashInput (hashPrepare (children s))))

theorem answer_pc (hash : Hash) (s : MachineState) (pc : s.pc = 0x2040) :
    (answer hash s).pc = 0x21a4 := by
  simp [answer,writeHash,hashPrepare_pc _ (children_pc s pc)]

def answerWrites : List Word := [0x42000#64,0x42008#64,0x42010#64,0x42018#64]
def preWrites := payloadWrites ++ headerWrites ++ answerWrites

theorem answer_frame (hash : Hash) (s : MachineState) (a : Word) (outside : a ∉ preWrites) :
    (answer hash s).getMem a = s.getMem a := by
  have split : (a ∉ payloadWrites ∧ a ∉ headerWrites) ∧ a ∉ answerWrites := by
    simpa only [preWrites,List.mem_append,not_or] using outside
  obtain ⟨⟨payload,header⟩,ans⟩ := split
  simp only [answerWrites,List.mem_cons,List.not_mem_nil,not_or] at ans
  obtain ⟨h0,h1,h2,h3⟩ := ans
  have dst := (hashPrepare_registers (children s)).2.2.1
  simp [answer,writeHash,dst,MachineState.writeWords,h0,h1,h2,h3]
  rw [hashPrepare_frame _ a header,children_frame s a payload]

theorem answer_trace (hash : Hash) (s : MachineState) (base node : Nat) (pc : s.pc = 0x2040)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : base + 40 * node + 40 ≤ 0x60000) (aligned : base % 4 = 0) :
    Trace hash SphincsMaskedImages.sign s 89 104 1 2 (answer hash s) := by
  obtain ⟨src,bits,dst,service⟩ := hashPrepare_registers (children s)
  have fetch : fetch SphincsMaskedImages.sign (hashPrepare (children s)) = some (.base .ECALL) := by
    rw [fetch_at,hashPrepare_pc _ (children_pc s pc)];decide
  have valid : hashArgumentsValid (hashPrepare (children s)) = true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (hashPrepare (children s))).1 = 640 := by simp [hashInput,bits]
  have step := Trace.hash (hash := hash) (image := SphincsMaskedImages.sign)
    (hashPrepare (children s)) _ 0 0 0 0 fetch service valid (Trace.refl _)
  have hstep : Trace hash SphincsMaskedImages.sign (hashPrepare (children s)) 1 16 1 2 (answer hash s) := by
    simp only [len] at step;exact step
  exact (children_block s base node pc hb hn bounded aligned).trace.trans
    ((hashPrepare_block _ (children_pc s pc)).trace.trans hstep)



theorem storeSetup_frame (s : MachineState) (a : Word) : (storeSetup s).getMem a = s.getMem a := by
  simp [storeSetup,runSchedule,storeSetupSchedule,execInstrBr]

theorem storeSetup_registers (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node) :
    (storeSetup s).getReg .x6 = 0x42000 ∧
      (storeSetup s).getReg .x7 = BitVec.ofNat 64 (target + 20 * node) := by
  change s.getMem 0x43080#64 = BitVec.ofNat 64 target at ht
  change s.getMem 0x43088#64 = BitVec.ofNat 64 node at hn
  simp [storeSetup,runSchedule,storeSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ht,hn]
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 target + (BitVec.ofNat 64 node * BitVec.ofNat 64 4 +
    BitVec.ofNat 64 node * BitVec.ofNat 64 16) = _
  rw [← BitVec.ofNat_mul,← BitVec.ofNat_mul,← BitVec.ofNat_add,← BitVec.ofNat_add]
  congr 1;omega

def stored (s : MachineState) := copyRootState (storeSetup s)
def next (hash : Hash) (s : MachineState) := nodeFinish (stored (answer hash s))

theorem store_code : Copy20Code SphincsMaskedImages.sign 1141 := by
  constructor <;> intro i <;> fin_cases i <;> decide

theorem stored_pc (s : MachineState) (pc : s.pc = 0x21a4) : (stored s).pc = 0x21fc := by
  rw [stored,copyRoot_pc,storeSetup_pc s pc];rfl

theorem stored_control (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : target + 20 * node + 20 ≤ 0x60000) (above : 0x50000 ≤ target)
    (a : Word) (low : a.toNat < 0x50000) :
    (stored s).getMem a = s.getMem a := by
  change (copyRootState (storeSetup s)).getMem a = _
  rw [copyRoot_mem_frame]
  · exact storeSetup_frame s a
  · intro i
    rw [(storeSetup_registers s target node ht hn).2]
    have address : BitVec.ofNat 64 (target + 20 * node) + signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
        BitVec.ofNat 64 (target + 20 * node + 4 * i.val) := by
      fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [address]
    intro eq
    let offset := target + 20*node + 4*i.val - 0x50000
    have ha : (BitVec.ofNat 64 0x50000).toNat % 8 = 0 := by decide
    have hover : (BitVec.ofNat 64 0x50000).toNat + offset < 2^64 := by
      change 0x50000 + offset < 2^64;dsimp [offset];omega
    have aligned := alignToDword_add_ofNat_of_aligned ha hover
    rw [← BitVec.ofNat_add] at aligned
    have lower : 0x50000 ≤ (alignToDword (BitVec.ofNat 64 (target+20*node+4*i.val))).toNat := by
      rw [show target+20*node+4*i.val = 0x50000 + offset by dsimp [offset];omega,
        aligned,← BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      omega
    rw [← eq] at lower;omega

theorem nodeFinish_counter (s : MachineState) :
    (nodeFinish s).getMem 0x43088 = s.getMem 0x43088 + 1 := by
  simp [nodeFinish,runSchedule,nodeFinishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem nodeFinish_frame (s : MachineState) (a : Word) (ha : a ≠ 0x43088#64) :
    (nodeFinish s).getMem a = s.getMem a := by
  simp [nodeFinish,runSchedule,nodeFinishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ha]

theorem nodeFinish_pc (s : MachineState) (pc : s.pc = 0x21fc) :
    (nodeFinish s).pc = if s.getMem 0x43088 + 1 = s.getMem 0x43090 then 0x2234 else 0x2040 := by
  simp [nodeFinish,runSchedule,nodeFinishSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem node_trace (hash : Hash) (s : MachineState) (base target node count : Nat) (pc : s.pc = 0x2040)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (ht : s.getMem 0x43080 = BitVec.ofNat 64 target)
    (hn : s.getMem 0x43088 = BitVec.ofNat 64 node) (hc : s.getMem 0x43090 = BitVec.ofNat 64 count)
    (sourceBound : base + 40 * node + 40 ≤ 0x60000) (sourceAlign : base % 4 = 0)
    (targetBound : target + 20 * node + 20 ≤ 0x60000) (targetAlign : target % 4 = 0)
    (above : 0x50000 ≤ target) (countBound : count < 2048) :
    Trace hash SphincsMaskedImages.sign s 125 140 1 2 (next hash s) ∧
      (next hash s).getMem 0x43088 = BitVec.ofNat 64 (node + 1) ∧
      (next hash s).pc = if node + 1 = count then 0x2234 else 0x2040 := by
  have atarget : (answer hash s).getMem 0x43080 = BitVec.ofNat 64 target :=
    (answer_frame hash s _ (by decide)).trans ht
  have anode : (answer hash s).getMem 0x43088 = BitVec.ofNat 64 node :=
    (answer_frame hash s _ (by decide)).trans hn
  have acount : (answer hash s).getMem 0x43090 = BitVec.ofNat 64 count :=
    (answer_frame hash s _ (by decide)).trans hc
  have regs := storeSetup_registers (answer hash s) target node atarget anode
  have apc := answer_pc hash s pc
  have copied := copy20_block_general SphincsMaskedImages.sign 1141 store_code
    (storeSetup (answer hash s)) 0x42000 (target + 20 * node)
    (storeSetup_pc _ apc) regs.1 regs.2 (by decide) (by decide)
    (by omega) (by dsimp [MEMORY_BYTES];omega) (by decide)
  have storedNode := (stored_control (answer hash s) target node atarget anode targetBound above 0x43088 (by decide)).trans anode
  have storedCount := (stored_control (answer hash s) target node atarget anode targetBound above 0x43090 (by decide)).trans acount
  refine ⟨?_,?_,?_⟩
  · exact (answer_trace hash s base node pc hb hn sourceBound sourceAlign).trans
      ((storeSetup_block _ apc).trace.trans (copied.trace.trans (nodeFinish_block _ (stored_pc _ apc)).trace))
  · change (nodeFinish (stored (answer hash s))).getMem _ = _
    rw [nodeFinish_counter,storedNode]
    exact (BitVec.ofNat_add _ _).symm
  · change (nodeFinish (stored (answer hash s))).pc = _
    rw [nodeFinish_pc _ (stored_pc _ apc),storedNode,storedCount]
    rw [show BitVec.ofNat 64 node + 1 = BitVec.ofNat 64 (node + 1) from (BitVec.ofNat_add _ _).symm]
    have eq : (BitVec.ofNat 64 (node + 1) : Word) = BitVec.ofNat 64 count ↔ node + 1 = count := by
      constructor
      · intro h
        have h := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show node + 1 < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show count < 2 ^ 64 by omega)] at h
        exact h
      · intro h;rw [h]
    simp only [eq]




def width (level : Nat) : Nat := if level ≤ 8 then 2^(8-level) else 0
def cacheBase (level : Nat) : Nat := 0x50000 + 20*(512-2^(9-level))
def totalNodes (levels : Nat) : Nat := 256 - 2^(8-levels)

theorem layout : ∀ k : Fin 8,
    cacheBase k.val + 40*width (k.val+1) = cacheBase (k.val+1) ∧
    cacheBase (k.val+1) + 20*width (k.val+1) = cacheBase (k.val+2) ∧
    cacheBase (k.val+2) ≤ 0x60000 ∧
    cacheBase k.val % 4 = 0 ∧ cacheBase (k.val+1) % 4 = 0 ∧
    0x50000 ≤ cacheBase k.val ∧ 0x50000 ≤ cacheBase (k.val+1) ∧
    0 < width (k.val+1) ∧ width (k.val+1) < 256 ∧
    2*width (k.val+1) = width k.val ∧
    width (k.val+1)/2 = width (k.val+2) ∧
    totalNodes (k.val+1) = totalNodes k.val + width (k.val+1) := by decide

theorem earlier_layout : ∀ (k : Fin 8) (l : Fin 9), l.val ≤ k.val →
    cacheBase l.val + 20*width l.val ≤ cacheBase (k.val+1) ∧
    cacheBase l.val % 4 = 0 ∧ 0x50000 ≤ cacheBase l.val := by decide

structure Controls (s : MachineState) (k node : Nat) : Prop where
  base : s.getMem 0x43068 = BitVec.ofNat 64 (cacheBase k)
  target : s.getMem 0x43080 = BitVec.ofNat 64 (cacheBase (k+1))
  level : s.getMem 0x43048 = BitVec.ofNat 64 (k+1)
  count : s.getMem 0x43090 = BitVec.ofNat 64 (width (k+1))
  node : s.getMem 0x43088 = BitVec.ofNat 64 node

structure LevelControls (s : MachineState) (k : Nat) : Prop where
  base : s.getMem 0x43068 = BitVec.ofNat 64 (cacheBase k)
  target : s.getMem 0x43080 = BitVec.ofNat 64 (cacheBase (k+1))
  level : s.getMem 0x43048 = BitVec.ofNat 64 (k+1)
  count : s.getMem 0x43090 = BitVec.ofNat 64 (width (k+1))

def loopWrites : List Word := [0x43048#64,0x43068#64,0x43080#64,0x43088#64,0x43090#64]

/-- A context is stable under changes to the five parent-loop control cells. -/
def LoopStable (context : MachineState → Prop) : Prop :=
  ∀ s t, context s → (∀ a, a ∉ loopWrites → t.getMem a = s.getMem a) → context t

theorem init_frame (s : MachineState) (a : Word) (outside : a ∉ loopWrites) :
    (init s).getMem a = s.getMem a := by
  simp only [loopWrites,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4⟩ := outside
  simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3,h4]

theorem levelEntry_frame (s : MachineState) (a : Word) (outside : a ≠ 0x43088#64) :
    (levelEntry s).getMem a = s.getMem a := by
  simp [levelEntry,runSchedule,levelEntrySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,outside]

theorem levelFinish_frame (s : MachineState) (a : Word) (outside : a ∉ loopWrites) :
    (levelFinish s).getMem a = s.getMem a := by
  simp only [loopWrites,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4⟩ := outside
  simp [levelFinish,runSchedule,levelFinishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3,h4]

theorem init_controls (s : MachineState) : LevelControls (init s) 0 := by
  constructor <;> simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,cacheBase,width]

theorem levelEntry_controls (s : MachineState) (k : Nat) (ctrl : LevelControls s k) :
    Controls (levelEntry s) k 0 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (levelEntry_frame s _ (by decide)).trans ctrl.base
  · exact (levelEntry_frame s _ (by decide)).trans ctrl.target
  · exact (levelEntry_frame s _ (by decide)).trans ctrl.level
  · exact (levelEntry_frame s _ (by decide)).trans ctrl.count
  · simp [levelEntry,runSchedule,levelEntrySchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem levelFinish_controls (s : MachineState) (k : Fin 8)
    (ctrl : Controls s k.val (width (k.val+1))) : LevelControls (levelFinish s) (k.val+1) := by
  have target := ctrl.target
  have count := ctrl.count
  have level := ctrl.level
  change s.getMem 0x43080#64 = _ at target
  change s.getMem 0x43090#64 = _ at count
  change s.getMem 0x43048#64 = _ at level
  constructor <;>
    simp [levelFinish,runSchedule,levelFinishSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,target,count,level]
  all_goals fin_cases k <;> decide

theorem levelFinish_pc (s : MachineState) (k : Fin 8) (pc : s.pc = 0x2234)
    (level : s.getMem 0x43048 = BitVec.ofNat 64 (k.val+1)) :
    (levelFinish s).pc = if k.val+1 = 8 then 0x22c0 else 0x2030 := by
  change s.getMem 0x43048#64 = _ at level
  simp [levelFinish,runSchedule,levelFinishSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc,level]
  fin_cases k <;> decide

theorem cache_cell_lower (address : Nat) (lower : 0x50000 ≤ address) (upper : address < 0x60000) :
    0x50000 ≤ (alignToDword (BitVec.ofNat 64 address)).toNat := by
  have ha : (BitVec.ofNat 64 0x50000).toNat % 8 = 0 := by decide
  have hover : (BitVec.ofNat 64 0x50000).toNat + (address-0x50000) < 2^64 := by
    change 0x50000 + (address-0x50000) < 2^64;omega
  have aligned := alignToDword_add_ofNat_of_aligned ha hover
  rw [← BitVec.ofNat_add] at aligned
  rw [show address = 0x50000 + (address-0x50000) by omega,aligned,
    ← BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  omega

theorem cache_word_frame (s t : MachineState)
    (frame : ∀ a, a ∉ loopWrites → t.getMem a = s.getMem a)
    (address : Nat) (lower : 0x50000 ≤ address) (upper : address < 0x60000) :
    t.getWord32 (BitVec.ofNat 64 address) = s.getWord32 (BitVec.ofNat 64 address) := by
  simp only [MachineState.getWord32]
  rw [frame]
  have bound := cache_cell_lower address lower upper
  simp only [loopWrites,List.mem_cons,List.not_mem_nil,or_false]
  intro h
  rcases h with h|h|h|h|h <;> rw [h] at bound <;> contradiction

/-- Semantic nodes in every already completed level. -/
def TreeValues (values : Nat → Nat → BitVec 160) (s : MachineState) (k : Nat) : Prop :=
  ∀ level, level ≤ k → ∀ node, node < width level →
    Words20 s (cacheBase level + 20*node) (values level node)

/-- Local parent-node obligation. Only the two child values are assumed.
    The word frame covers previous levels and earlier outputs of this level. -/
def NodeContract (hash : Hash) (context : MachineState → Prop)
    (values : Nat → Nat → BitVec 160) : Prop :=
  ∀ (k : Fin 8) (node : Nat), node < width (k.val+1) → ∀ s,
    context s → s.pc = 0x2040 → Controls s k.val node →
    Words20 s (cacheBase k.val + 20*(2*node)) (values k.val (2*node)) →
    Words20 s (cacheBase k.val + 20*(2*node+1)) (values k.val (2*node+1)) →
    ∃ t, Trace hash SphincsMaskedImages.sign s 125 140 1 2 t ∧
      context t ∧ Controls t k.val (node+1) ∧
      t.pc = (if node+1 = width (k.val+1) then 0x2234 else 0x2040) ∧
      Words20 t (cacheBase (k.val+1) + 20*node) (values (k.val+1) node) ∧
      ∀ address, 0x50000 ≤ address → address < cacheBase (k.val+1)+20*node → address%4=0 →
        t.getWord32 (BitVec.ofNat 64 address) = s.getWord32 (BitVec.ofNat 64 address)

/-- Reusable induction over the nodes of a single level. -/
theorem nodes_contract (hash : Hash) (context : MachineState → Prop)
    (values : Nat → Nat → BitVec 160) (contract : NodeContract hash context values)
    (s : MachineState) (k : Fin 8) (pc : s.pc = 0x2040)
    (ctx : context s) (ctrl : Controls s k.val 0) (old : TreeValues values s k.val)
    (n : Nat) (hn : n ≤ width (k.val+1)) :
    ∃ t, Trace hash SphincsMaskedImages.sign s (125*n) (140*n) n (2*n) t ∧
      context t ∧ Controls t k.val n ∧
      t.pc = (if n = width (k.val+1) then 0x2234 else 0x2040) ∧
      TreeValues values t k.val ∧
      (∀ node, node < n → Words20 t (cacheBase (k.val+1)+20*node) (values (k.val+1) node)) := by
  obtain ⟨sourceEnd,targetEnd,targetBound,baseAlign,targetAlign,baseAbove,targetAbove,positive,small,twice,half,total⟩ := layout k
  induction n with
  | zero =>
    refine ⟨s,Trace.refl _,ctx,ctrl,?_,old,?_⟩
    · simpa only [if_neg (show 0 ≠ width (k.val+1) by omega)] using pc
    · intro node h;omega
  | succ n ih =>
    obtain ⟨mid,first,midCtx,midCtrl,midPc,midOld,prior⟩ := ih (by omega)
    have here : mid.pc = 0x2040 := by simpa only [if_neg (show n ≠ width (k.val+1) by omega)] using midPc
    obtain ⟨t,step,tCtx,tCtrl,tPc,written,frame⟩ := contract k n (by omega) mid midCtx here midCtrl
      (midOld k.val (by omega) (2*n) (by omega))
      (midOld k.val (by omega) (2*n+1) (by omega))
    refine ⟨t,?_,tCtx,tCtrl,tPc,?_,?_⟩
    · simpa only [Nat.mul_add,Nat.mul_one] using first.trans step
    · intro level hlevel node hnode i
      have before := earlier_layout k ⟨level,by omega⟩ hlevel
      change cacheBase level + 20*width level ≤ cacheBase (k.val+1) ∧
        cacheBase level%4=0 ∧ 0x50000 ≤ cacheBase level at before
      rw [frame _ (by omega) (by omega) (by omega)]
      exact midOld level hlevel node hnode i
    · intro node hnode
      by_cases eq : node=n
      · subst node;exact written
      · intro i
        rw [frame _ (by omega) (by omega) (by omega)]
        exact prior node (by omega) i

/-- One complete level, including its two fixed control blocks. -/
theorem level_contract (hash : Hash) (context : MachineState → Prop)
    (stable : LoopStable context) (values : Nat → Nat → BitVec 160)
    (contract : NodeContract hash context values)
    (s : MachineState) (k : Fin 8) (pc : s.pc = 0x2030)
    (ctx : context s) (ctrl : LevelControls s k.val) (old : TreeValues values s k.val) :
    ∃ t, Trace hash SphincsMaskedImages.sign s (39+125*width (k.val+1))
      (39+140*width (k.val+1)) (width (k.val+1)) (2*width (k.val+1)) t ∧
      context t ∧ LevelControls t (k.val+1) ∧
      t.pc = (if k.val+1 = 8 then 0x22c0 else 0x2030) ∧ TreeValues values t (k.val+1) := by
  have entryFrame : ∀ a, a ∉ loopWrites → (levelEntry s).getMem a = s.getMem a := by
    intro a ha;apply levelEntry_frame
    intro eq;apply ha;simp [loopWrites,eq]
  have entered := stable s (levelEntry s) ctx entryFrame
  have entryValues : TreeValues values (levelEntry s) k.val := by
    intro level hlevel node hnode i
    have before := earlier_layout k ⟨level,by omega⟩ hlevel
    have bound := layout k
    change cacheBase level + 20*width level ≤ cacheBase (k.val+1) ∧
      cacheBase level%4=0 ∧ 0x50000 ≤ cacheBase level at before
    rw [cache_word_frame s _ entryFrame _ (by omega) (by omega)]
    exact old level hlevel node hnode i
  obtain ⟨mid,run,midCtx,midCtrl,midPc,midOld,done⟩ := nodes_contract hash context values contract
    (levelEntry s) k (levelEntry_pc s pc) entered (levelEntry_controls s k.val ctrl)
    entryValues (width (k.val+1)) (by omega)
  have here : mid.pc = 0x2234 := by simpa using midPc
  refine ⟨levelFinish mid,?_,stable mid _ midCtx (levelFinish_frame mid),
    levelFinish_controls mid k midCtrl,levelFinish_pc mid k here midCtrl.level,?_⟩
  · have trace := (levelEntry_block s pc).trace.trans (run.trans (levelFinish_block mid here).trace)
    convert trace using 1 <;> omega
  · intro level hlevel node hnode i
    by_cases eq : level=k.val+1
    · subst level
      have bounds := layout k
      rw [cache_word_frame mid _ (levelFinish_frame mid) _ (by omega) (by omega)]
      exact done node hnode i
    · have earlier : level ≤ k.val := by omega
      have before := earlier_layout k ⟨level,by omega⟩ earlier
      have bounds := layout k
      change cacheBase level + 20*width level ≤ cacheBase (k.val+1) ∧
        cacheBase level%4=0 ∧ 0x50000 ≤ cacheBase level at before
      rw [cache_word_frame mid _ (levelFinish_frame mid) _ (by omega) (by omega)]
      exact midOld level earlier node hnode i

/-- Enclosing induction over all eight levels. -/
theorem levels_contract (hash : Hash) (context : MachineState → Prop)
    (stable : LoopStable context) (values : Nat → Nat → BitVec 160)
    (contract : NodeContract hash context values)
    (s : MachineState) (pc : s.pc = 0x2030) (ctx : context s)
    (ctrl : LevelControls s 0) (leaves : TreeValues values s 0)
    (n : Nat) (hn : n ≤ 8) :
    ∃ t, Trace hash SphincsMaskedImages.sign s (39*n+125*totalNodes n)
      (39*n+140*totalNodes n) (totalNodes n) (2*totalNodes n) t ∧
      context t ∧ LevelControls t n ∧
      t.pc = (if n=8 then 0x22c0 else 0x2030) ∧ TreeValues values t n := by
  induction n with
  | zero => exact ⟨s,Trace.refl _,ctx,ctrl,pc,leaves⟩
  | succ n ih =>
    obtain ⟨mid,first,midCtx,midCtrl,midPc,old⟩ := ih (by omega)
    have here : mid.pc = 0x2030 := by simpa only [if_neg (show n≠8 by omega)] using midPc
    let k : Fin 8 := ⟨n,by omega⟩
    obtain ⟨t,last,tCtx,tCtrl,tPc,done⟩ := level_contract hash context stable values contract mid k here midCtx midCtrl old
    refine ⟨t,?_,tCtx,tCtrl,tPc,done⟩
    have total : totalNodes (n+1) = totalNodes n + width (n+1) := (layout k).2.2.2.2.2.2.2.2.2.2.2
    have trace := first.trans last
    dsimp [k] at trace
    rw [total]
    convert trace using 1 <;> omega

/-- The parent block computes all 255 parents with exact cost, conditional
    only on the local semantic node contract and memory-stable context. -/
theorem parents_complete (hash : Hash) (context : MachineState → Prop)
    (stable : LoopStable context) (values : Nat → Nat → BitVec 160)
    (contract : NodeContract hash context values) (s : MachineState)
    (pc : s.pc = 0x1fe8) (ctx : context s)
    (leaves : ∀ node : Fin 256, Words20 s (0x50000+20*node.val) (values 0 node.val)) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 32205 36030 255 510 t ∧
      context t ∧ t.pc = 0x22c0 ∧ t.getMem 0x43068 = 0x527d8 ∧
      TreeValues values t 8 ∧ Words20 t 0x527d8 (values 8 0) := by
  have initialCtx := stable s (init s) ctx (init_frame s)
  have initialValues : TreeValues values (init s) 0 := by
    intro level hlevel node hnode i
    have eq : level=0 := by omega
    subst level
    have bound : node < 256 := by simpa [width] using hnode
    change (init s).getWord32 (BitVec.ofNat 64 (0x50000+20*node+4*i.val)) = _
    rw [cache_word_frame s _ (init_frame s) _ (by omega) (by omega)]
    exact leaves ⟨node,bound⟩ i
  obtain ⟨t,run,tCtx,tCtrl,tPc,done⟩ := levels_contract hash context stable values contract
    (init s) (init_pc s pc) initialCtx (init_controls s) initialValues 8 (by decide)
  refine ⟨t,(init_block s pc).trace.trans run,tCtx,?_,?_,done,?_⟩
  · simpa using tPc
  · exact tCtrl.base
  · exact done 8 (by omega) 0 (by decide)


private def CopyInvariant (original : MachineState) (source destination count : Nat)
    (s : MachineState) : Prop :=
  s.getReg .x6 = BitVec.ofNat 64 source ∧ s.getReg .x7 = BitVec.ofNat 64 destination ∧
  (∀ i : Fin 5, s.getWord32 (BitVec.ofNat 64 (source+4*i.val)) =
    original.getWord32 (BitVec.ofNat 64 (source+4*i.val))) ∧
  (∀ i : Fin 5, i.val < count → s.getWord32 (BitVec.ofNat 64 (destination+4*i.val)) =
    original.getWord32 (BitVec.ofNat 64 (source+4*i.val)))

private theorem copyStep (original s : MachineState) (source destination : Nat)
    (sourceBound : source+20 < 2^64) (targetBound : destination+20 < 2^64)
    (sourceAlign : source%4=0) (targetAlign : destination%4=0)
    (separate : source+20 ≤ destination ∨ destination+20 ≤ source)
    (slot : Fin 5) (inv : CopyInvariant original source destination slot.val s) :
    CopyInvariant original source destination (slot.val+1) (copyWordState slot s) := by
  obtain ⟨src,dst,sourceWords,copied⟩ := inv
  obtain ⟨srcAfter,dstAfter⟩ := copyWord_pointers slot s
  refine ⟨srcAfter.trans src,dstAfter.trans dst,?_,?_⟩
  · intro i
    rw [SphincsMaskedChainEndpoints.copyWord_lane_frame s destination (source+4*i.val) slot dst
      targetBound (by omega) targetAlign (by omega) (by omega)]
    exact sourceWords i
  · intro i hi
    by_cases eq : slot=i
    · subst i
      rw [SphincsVerifierCopy20DataGeneral.copyWord_data_general slot s source destination src dst]
      exact sourceWords slot
    · have ne : slot.val ≠ i.val := fun h => eq (Fin.ext h)
      rw [SphincsMaskedChainEndpoints.copyWord_lane_frame s destination (destination+4*i.val) slot dst
        targetBound (by omega) targetAlign (by omega) (by omega)]
      exact copied i (by omega)

/-- Twenty-byte copy semantics independent of the old below-0x50000 helper bound. -/
theorem copy_data (s : MachineState) (source destination : Nat)
    (sourceBound : source+20 < 2^64) (targetBound : destination+20 < 2^64)
    (sourceAlign : source%4=0) (targetAlign : destination%4=0)
    (separate : source+20 ≤ destination ∨ destination+20 ≤ source)
    (src : s.getReg .x6 = BitVec.ofNat 64 source) (dst : s.getReg .x7 = BitVec.ofNat 64 destination)
    (i : Fin 5) :
    (copyRootState s).getWord32 (BitVec.ofNat 64 (destination+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (source+4*i.val)) := by
  have inv : CopyInvariant s source destination 0 s := ⟨src,dst,fun _ => rfl,by intro _ h;omega⟩
  have s0 := copyStep s s source destination sourceBound targetBound sourceAlign targetAlign separate 0 inv
  have s1 := copyStep s (copyWordState 0 s) source destination sourceBound targetBound sourceAlign targetAlign separate 1 s0
  have s2 := copyStep s (copyWordState 1 (copyWordState 0 s)) source destination sourceBound targetBound sourceAlign targetAlign separate 2 s1
  have s3 := copyStep s (copyWordState 2 (copyWordState 1 (copyWordState 0 s))) source destination sourceBound targetBound sourceAlign targetAlign separate 3 s2
  have s4 := copyStep s (copyWordState 3 (copyWordState 2 (copyWordState 1 (copyWordState 0 s)))) source destination sourceBound targetBound sourceAlign targetAlign separate 4 s3
  exact s4.2.2.2 i (by omega)

theorem children_left (s : MachineState) (base node : Nat)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (above : 0x50000 ≤ base) (bounded : base+40*node+40 ≤ 0x60000)
    (aligned : base%4=0) (i : Fin 5) :
    (children s).getWord32 (BitVec.ofNat 64 (0x40028+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (base+40*node+4*i.val)) := by
  have regs := leftSetup_registers s base node hb hn
  have source := (copyRoot_registers (leftSetup s)).1.trans regs.1
  have right := rightSetup_registers (leftCopied s) (base+40*node) source
  change (copyRootState (rightSetup (leftCopied s))).getWord32 _ = _
  rw [copyRoot_word_frame]
  · simp only [MachineState.getWord32,rightSetup_frame]
    change (copyRootState (leftSetup s)).getWord32 _ = _
    rw [copy_data _ (base+40*node) 0x40028 (by omega) (by decide) (by omega) (by decide)
      (Or.inr (by omega)) regs.1 regs.2 i]
    simp only [MachineState.getWord32,leftSetup_frame]
  · intro j;rw [right.2];fin_cases i <;> fin_cases j <;> decide

theorem children_right (s : MachineState) (base node : Nat)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (above : 0x50000 ≤ base) (bounded : base+40*node+40 ≤ 0x60000)
    (aligned : base%4=0) (i : Fin 5) :
    (children s).getWord32 (BitVec.ofNat 64 (0x4003c+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (base+40*node+20+4*i.val)) := by
  have regs := leftSetup_registers s base node hb hn
  have source := (copyRoot_registers (leftSetup s)).1.trans regs.1
  have right := rightSetup_registers (leftCopied s) (base+40*node) source
  change (copyRootState (rightSetup (leftCopied s))).getWord32 _ = _
  rw [copy_data _ (base+40*node+20) 0x4003c (by omega) (by decide) (by omega) (by decide)
    (Or.inr (by omega)) right.1 right.2 i]
  simp only [MachineState.getWord32,rightSetup_frame]
  change (copyRootState (leftSetup s)).getWord32 _ = _
  rw [copyRoot_word_frame]
  · simp only [MachineState.getWord32,leftSetup_frame]
  · intro j;rw [regs.2]
    have address : (0x40028 : Word) + signExtend12 (4#12 * BitVec.ofNat 12 j.val) =
        BitVec.ofNat 64 (0x40028+4*j.val) := by fin_cases j <;> decide
    rw [address]
    exact wordLaneDistinct _ _ (by omega) (by omega) (by omega) (by omega) (by omega)

def queryWord (s : MachineState) (i : Fin 20) : BitVec 32 :=
  if i.val=0 then (2561#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val=1 then (s.getMem 0x43048).setWidth 32
  else if i.val=2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val=3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val=4 then (s.getMem 0x43088).setWidth 32
  else if i.val<10 then s.getWord32 (BitVec.ofNat 64 (0x74+4*(i.val-5)))
  else s.getWord32 (BitVec.ofNat 64 (0x40000+4*i.val))

/-- Exact domain-10 query header and concatenated child payload words. -/
theorem prepare_words (s : MachineState) (i : Fin 20) :
    (hashPrepare s).getWord32 (BitVec.ofNat 64 (0x40000+4*i.val)) = queryWord s i := by
  fin_cases i <;>
    simp [hashPrepare,runSchedule,hashPrepareSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,MachineState.setWord32,
      MachineState.getWord32,alignToDword,byteOffset,queryWord]

theorem next_data (hash : Hash) (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (above : 0x50000 ≤ target) (bounded : target+20*node+20 ≤ 0x60000)
    (aligned : target%4=0) (i : Fin 5) :
    (next hash s).getWord32 (BitVec.ofNat 64 (target+20*node+4*i.val)) =
      (answer hash s).getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) := by
  have atarget := (answer_frame hash s _ (by decide)).trans ht
  have anode := (answer_frame hash s _ (by decide)).trans hn
  have regs := storeSetup_registers (answer hash s) target node atarget anode
  change (nodeFinish (stored (answer hash s))).getWord32 _ = _
  simp only [MachineState.getWord32]
  rw [nodeFinish_frame]
  · change (copyRootState (storeSetup (answer hash s))).getWord32 _ = _
    rw [copy_data _ 0x42000 (target+20*node) (by decide) (by omega) (by decide) (by omega)
      (Or.inl (by omega)) regs.1 regs.2 i]
    simp only [MachineState.getWord32,storeSetup_frame]
  · intro eq
    have lower := cache_cell_lower (target+20*node+4*i.val) (by omega) (by omega)
    rw [eq] at lower;contradiction

theorem answer_words (hash : Hash) (s : MachineState) (i : Fin 5) :
    (answer hash s).getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) =
      (hash (hashInput (hashPrepare (children s)))).extractLsb' (32*i.val) 32 := by
  have dst := (hashPrepare_registers (children s)).2.2.1
  fin_cases i <;>
    simp [answer,writeHash,dst,MachineState.writeWords,MachineState.getWord32,alignToDword,byteOffset,extractWord32]
  all_goals ext b hb;interval_cases b <;> simp

/-- The concrete parent slot receives the low 160 bits of the actual oracle answer. -/
theorem node_value (hash : Hash) (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (above : 0x50000 ≤ target) (bounded : target+20*node+20 ≤ 0x60000) (aligned : target%4=0) :
    Words20 (next hash s) (target+20*node)
      ((hash (hashInput (hashPrepare (children s)))).extractLsb' 0 160) := by
  intro i
  rw [next_data hash s target node ht hn above bounded aligned i,answer_words]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

theorem next_control (hash : Hash) (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (above : 0x50000 ≤ target) (bounded : target+20*node+20 ≤ 0x60000)
    (a : Word) (low : a.toNat < 0x50000) (outside : a ∉ preWrites) (notNode : a ≠ 0x43088#64) :
    (next hash s).getMem a = s.getMem a := by
  have atarget := (answer_frame hash s _ (by decide)).trans ht
  have anode := (answer_frame hash s _ (by decide)).trans hn
  change (nodeFinish (stored (answer hash s))).getMem a = _
  rw [nodeFinish_frame _ a notNode,stored_control _ target node atarget anode bounded above a low,
    answer_frame hash s a outside]

theorem next_prior_word (hash : Hash) (s : MachineState) (target node address : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (above : 0x50000 ≤ target) (bounded : target+20*node+20 ≤ 0x60000) (aligned : target%4=0)
    (readLower : 0x50000 ≤ address) (readUpper : address < target+20*node) (readAlign : address%4=0) :
    (next hash s).getWord32 (BitVec.ofNat 64 address) = s.getWord32 (BitVec.ofNat 64 address) := by
  have atarget := (answer_frame hash s _ (by decide)).trans ht
  have anode := (answer_frame hash s _ (by decide)).trans hn
  have regs := storeSetup_registers (answer hash s) target node atarget anode
  change (nodeFinish (stored (answer hash s))).getWord32 _ = _
  have lower := cache_cell_lower address readLower (by omega)
  simp only [MachineState.getWord32]
  rw [nodeFinish_frame _ _ (by intro eq;rw [eq] at lower;contradiction)]
  change (copyRootState (storeSetup (answer hash s))).getWord32 _ = _
  rw [copyRoot_word_frame]
  · simp only [MachineState.getWord32,storeSetup_frame]
    rw [answer_frame]
    intro member
    have upper : ∀ a ∈ preWrites, a.toNat < 0x50000 := by
      simp [preWrites,payloadWrites,headerWrites,answerWrites]
    have bad := upper _ member
    omega
  · intro i
    rw [regs.2]
    have addr : BitVec.ofNat 64 (target+20*node) + signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
        BitVec.ofNat 64 (target+20*node+4*i.val) := by
      fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [addr]
    exact wordLaneDistinct _ _ (by omega) (by omega) (by omega) readAlign (by omega)


/-- A concrete node iteration retains all enclosing loop controls. -/
theorem node_execution (hash : Hash) (s : MachineState) (k : Fin 8) (node : Nat)
    (bounded : node < width (k.val+1)) (pc : s.pc = 0x2040) (ctrl : Controls s k.val node) :
    Trace hash SphincsMaskedImages.sign s 125 140 1 2 (next hash s) ∧
    Controls (next hash s) k.val (node+1) ∧
    (next hash s).pc = (if node+1 = width (k.val+1) then 0x2234 else 0x2040) := by
  obtain ⟨sourceEnd,targetEnd,targetBound,baseAlign,targetAlign,baseAbove,targetAbove,positive,small,twice,half,total⟩ := layout k
  have bound : cacheBase (k.val+1)+20*node+20 ≤ 0x60000 := by omega
  obtain ⟨run,counter,loc⟩ := node_trace hash s (cacheBase k.val) (cacheBase (k.val+1))
    node (width (k.val+1)) pc ctrl.base ctrl.target ctrl.node ctrl.count
    (by omega) baseAlign bound targetAlign targetAbove (by omega)
  refine ⟨run,⟨?_,?_,?_,?_,counter⟩,loc⟩
  · exact (next_control hash s _ node ctrl.target ctrl.node targetAbove bound _
      (by decide) (by decide) (by decide)).trans ctrl.base
  · exact (next_control hash s _ node ctrl.target ctrl.node targetAbove bound _
      (by decide) (by decide) (by decide)).trans ctrl.target
  · exact (next_control hash s _ node ctrl.target ctrl.node targetAbove bound _
      (by decide) (by decide) (by decide)).trans ctrl.level
  · exact (next_control hash s _ node ctrl.target ctrl.node targetAbove bound _
      (by decide) (by decide) (by decide)).trans ctrl.count

def nodes (hash : Hash) (s : MachineState) : Nat → MachineState
  | 0 => s
  | n+1 => next hash (nodes hash s n)

/-- Resource/termination induction with no abstract hash or value premise. -/
theorem nodes_execution (hash : Hash) (s : MachineState) (k : Fin 8)
    (pc : s.pc = 0x2040) (ctrl : Controls s k.val 0)
    (n : Nat) (bound : n ≤ width (k.val+1)) :
    Trace hash SphincsMaskedImages.sign s (125*n) (140*n) n (2*n) (nodes hash s n) ∧
    Controls (nodes hash s n) k.val n ∧
    (nodes hash s n).pc = (if n = width (k.val+1) then 0x2234 else 0x2040) := by
  have positive := (layout k).2.2.2.2.2.2.2.1
  induction n with
  | zero =>
    refine ⟨Trace.refl s,ctrl,?_⟩
    simpa only [nodes,if_neg (show 0 ≠ width (k.val+1) by omega)] using pc
  | succ n ih =>
    obtain ⟨first,midCtrl,midPc⟩ := ih (by omega)
    have here : (nodes hash s n).pc = 0x2040 := by
      simpa only [if_neg (show n ≠ width (k.val+1) by omega)] using midPc
    obtain ⟨last,done,loc⟩ := node_execution hash (nodes hash s n) k n (by omega) here midCtrl
    refine ⟨?_,done,loc⟩
    simpa only [nodes,Nat.mul_add,Nat.mul_one] using first.trans last

-- Keep later whole-tree execution proofs symbolic in the finite node count.
attribute [irreducible] nodes

theorem level_execution (hash : Hash) (s : MachineState) (k : Fin 8)
    (pc : s.pc = 0x2030) (ctrl : LevelControls s k.val) :
    ∃ t, Trace hash SphincsMaskedImages.sign s (39+125*width (k.val+1))
      (39+140*width (k.val+1)) (width (k.val+1)) (2*width (k.val+1)) t ∧
      LevelControls t (k.val+1) ∧ t.pc = (if k.val+1=8 then 0x22c0 else 0x2030) := by
  obtain ⟨run,done,loc⟩ := nodes_execution hash (levelEntry s) k
    (levelEntry_pc s pc) (levelEntry_controls s k.val ctrl) (width (k.val+1)) (by omega)
  let mid := nodes hash (levelEntry s) (width (k.val+1))
  have here : mid.pc = 0x2234 := by simpa using loc
  refine ⟨levelFinish mid,?_,levelFinish_controls mid k done,levelFinish_pc mid k here done.level⟩
  have trace := (levelEntry_block s pc).trace.trans (run.trans (levelFinish_block mid here).trace)
  convert trace using 1 <;> omega

theorem levels_execution (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x2030) (ctrl : LevelControls s 0) (n : Nat) (bound : n ≤ 8) :
    ∃ t, Trace hash SphincsMaskedImages.sign s (39*n+125*totalNodes n)
      (39*n+140*totalNodes n) (totalNodes n) (2*totalNodes n) t ∧
      LevelControls t n ∧ t.pc = (if n=8 then 0x22c0 else 0x2030) := by
  induction n with
  | zero => exact ⟨s,Trace.refl s,ctrl,pc⟩
  | succ n ih =>
    obtain ⟨mid,first,midCtrl,midPc⟩ := ih (by omega)
    have here : mid.pc = 0x2030 := by simpa only [if_neg (show n≠8 by omega)] using midPc
    let k : Fin 8 := ⟨n,by omega⟩
    obtain ⟨t,last,done,loc⟩ := level_execution hash mid k here midCtrl
    refine ⟨t,?_,done,loc⟩
    have total : totalNodes (n+1) = totalNodes n + width (n+1) := (layout k).2.2.2.2.2.2.2.2.2.2.2
    have trace := first.trans last
    dsimp [k] at trace
    rw [total]
    convert trace using 1 <;> omega

/-- Unconditional exact execution of all 255 FORS parent nodes, for every
    oracle and incoming memory state. This requires only the entry PC. -/
theorem parents_execution (hash : Hash) (s : MachineState) (pc : s.pc = 0x1fe8) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 32205 36030 255 510 t ∧
      t.pc = 0x22c0 ∧ t.getMem 0x43068 = 0x527d8 := by
  obtain ⟨t,run,ctrl,loc⟩ := levels_execution hash (init s) (init_pc s pc) (init_controls s) 8 (by decide)
  refine ⟨t,(init_block s pc).trace.trans run,?_,ctrl.base⟩
  simpa using loc


/-- A signing context depends only on memory retained by a parent iteration. -/
def NodeStable (context : MachineState → Prop) : Prop :=
  ∀ s t, context s →
    (∀ a, a.toNat < 0x50000 → a ∉ preWrites → a ≠ 0x43088#64 → t.getMem a = s.getMem a) →
    context t

/-- Instantiate the reusable node contract using only query identification.
    Execution, counter updates, output storage, and prior-node preservation
    are discharged by the concrete bytecode lemmas in this module. -/
theorem node_contract_of_query (hash : Hash) (context : MachineState → Prop)
    (stable : NodeStable context) (values : Nat → Nat → BitVec 160)
    (query : ∀ (k : Fin 8) (node : Nat), node < width (k.val+1) → ∀ s,
      context s → Controls s k.val node →
      Words20 s (cacheBase k.val+20*(2*node)) (values k.val (2*node)) →
      Words20 s (cacheBase k.val+20*(2*node+1)) (values k.val (2*node+1)) →
      (hash (hashInput (hashPrepare (children s)))).extractLsb' 0 160 = values (k.val+1) node) :
    NodeContract hash context values := by
  intro k node bound s ctx pc ctrl left right
  obtain ⟨sourceEnd,targetEnd,targetBound,baseAlign,targetAlign,baseAbove,targetAbove,positive,small,twice,half,total⟩ := layout k
  have outputBound : cacheBase (k.val+1)+20*node+20 ≤ 0x60000 := by omega
  obtain ⟨run,done,loc⟩ := node_execution hash s k node bound pc ctrl
  refine ⟨next hash s,run,?_,done,loc,?_,?_⟩
  · apply stable s _ ctx
    intro a low outside notNode
    exact next_control hash s _ node ctrl.target ctrl.node targetAbove outputBound a low outside notNode
  · rw [← query k node bound s ctx ctrl left right]
    exact node_value hash s _ node ctrl.target ctrl.node targetAbove outputBound targetAlign
  · intro address lower upper aligned
    exact next_prior_word hash s _ node address ctrl.target ctrl.node targetAbove outputBound targetAlign lower upper aligned

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParents.node_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms node_trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParents.parents_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parents_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParents.parents_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parents_complete

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParents.nodes_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodes_contract

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParents.levels_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms levels_contract

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParents.copy_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copy_data

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParents.children_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms children_left

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParents.children_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms children_right

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParents.prepare_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prepare_words

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParents.node_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms node_value

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParents.next_prior_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms next_prior_word

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParents.node_contract_of_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms node_contract_of_query


end SigGolfCandidate.SphincsMaskedSignForestParents
