import SigGolfCandidate.SphincsMaskedChainStep
import SigGolfCandidate.SphincsVerifierFtsPriorRoots
import SigGolfCandidate.SphincsVerifierCopy20DataGeneral

namespace SigGolfCandidate.SphincsMaskedChainLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix
open SphincsVerifierFtsRootCopy
open SphincsVerifierMessageCopy SphincsVerifierCopy SphincsVerifierCopyMemory SphincsVerifierFtsCopyAccess
open SphincsVerifierFtsPriorRoots SphincsVerifierCopy20DataGeneral
set_option maxRecDepth 16384
set_option maxHeartbeats 400000

def secretPrepareSchedule : List (Word × Instr) := [
  (0x112c, .LUI .x28 67),
  (0x1130, .ADDI .x28 .x28 (80)),
  (0x1134, .LD .x6 .x28 (0)),
  (0x1138, .LUI .x28 67),
  (0x113c, .ADDI .x28 .x28 (16)),
  (0x1140, .SD .x28 .x6 (0)),
  (0x1144, .LUI .x28 67),
  (0x1148, .ADDI .x28 .x28 (32)),
  (0x114c, .LD .x6 .x28 (0)),
  (0x1150, .LUI .x28 67),
  (0x1154, .ADDI .x28 .x28 (24)),
  (0x1158, .SD .x28 .x6 (0)),
  (0x115c, .ADDI .x6 .x0 (32)),
  (0x1160, .LUI .x7 64),
  (0x1164, .ADDI .x7 .x7 (40)),
  (0x1168, .ADDI .x10 .x0 (4)),
  (0x116c, .LD .x11 .x6 (0)),
  (0x1170, .SD .x7 .x11 (0)),
  (0x1174, .ADDI .x6 .x6 (8)),
  (0x1178, .ADDI .x7 .x7 (8)),
  (0x117c, .ADDI .x10 .x10 (-1)),
  (0x1180, .BNE .x10 .x0 (-20)),
  (0x116c, .LD .x11 .x6 (0)),
  (0x1170, .SD .x7 .x11 (0)),
  (0x1174, .ADDI .x6 .x6 (8)),
  (0x1178, .ADDI .x7 .x7 (8)),
  (0x117c, .ADDI .x10 .x10 (-1)),
  (0x1180, .BNE .x10 .x0 (-20)),
  (0x116c, .LD .x11 .x6 (0)),
  (0x1170, .SD .x7 .x11 (0)),
  (0x1174, .ADDI .x6 .x6 (8)),
  (0x1178, .ADDI .x7 .x7 (8)),
  (0x117c, .ADDI .x10 .x10 (-1)),
  (0x1180, .BNE .x10 .x0 (-20)),
  (0x116c, .LD .x11 .x6 (0)),
  (0x1170, .SD .x7 .x11 (0)),
  (0x1174, .ADDI .x6 .x6 (8)),
  (0x1178, .ADDI .x7 .x7 (8)),
  (0x117c, .ADDI .x10 .x10 (-1)),
  (0x1180, .BNE .x10 .x0 (-20)),
  (0x1184, .ADDI .x6 .x0 (1)),
  (0x1188, .LUI .x28 67),
  (0x118c, .ADDI .x28 .x28 (0)),
  (0x1190, .LD .x7 .x28 (0)),
  (0x1194, .SLLI .x7 .x7 (16)),
  (0x1198, .ADD .x6 .x6 .x7),
  (0x119c, .LUI .x7 64),
  (0x11a0, .ADDI .x7 .x7 (0)),
  (0x11a4, .SW .x7 .x6 (0)),
  (0x11a8, .LUI .x28 67),
  (0x11ac, .ADDI .x28 .x28 (16)),
  (0x11b0, .LD .x6 .x28 (0)),
  (0x11b4, .SW .x7 .x6 (4)),
  (0x11b8, .LUI .x28 67),
  (0x11bc, .ADDI .x28 .x28 (8)),
  (0x11c0, .LD .x6 .x28 (0)),
  (0x11c4, .SD .x7 .x6 (8)),
  (0x11c8, .LUI .x28 67),
  (0x11cc, .ADDI .x28 .x28 (24)),
  (0x11d0, .LD .x6 .x28 (0)),
  (0x11d4, .SW .x7 .x6 (16)),
  (0x11d8, .ADDI .x6 .x0 (116)),
  (0x11dc, .LUI .x7 64),
  (0x11e0, .ADDI .x7 .x7 (20)),
  (0x11e4, .LWU .x13 .x6 (0)),
  (0x11e8, .SW .x7 .x13 (0)),
  (0x11ec, .LWU .x13 .x6 (4)),
  (0x11f0, .SW .x7 .x13 (4)),
  (0x11f4, .LWU .x13 .x6 (8)),
  (0x11f8, .SW .x7 .x13 (8)),
  (0x11fc, .LWU .x13 .x6 (12)),
  (0x1200, .SW .x7 .x13 (12)),
  (0x1204, .LWU .x13 .x6 (16)),
  (0x1208, .SW .x7 .x13 (16)),
  (0x120c, .LUI .x10 64),
  (0x1210, .ADDI .x10 .x10 (0)),
  (0x1214, .ADDI .x11 .x0 (576)),
  (0x1218, .LUI .x12 66),
  (0x121c, .ADDI .x12 .x12 (0)),
  (0x1220, .ADDI .x5 .x0 (1))]

def secretPrepare (s : MachineState) : MachineState := runSchedule secretPrepareSchedule s

theorem secretPrepare_code : ∀ entry ∈ secretPrepareSchedule,
    instructionAt SphincsMaskedImages.keygen entry.1 = some (.base entry.2) := by decide

theorem secretPrepare_checked (s : MachineState) (pc : s.pc = 0x112c) :
    Checked secretPrepareSchedule s := by
  simp [secretPrepareSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

theorem secretPrepare_block (s : MachineState) (pc : s.pc = 0x112c) :
    OrdinarySteps SphincsMaskedImages.keygen s 80 (secretPrepare s) :=
  checked_sound _ secretPrepareSchedule secretPrepare_code s (secretPrepare_checked s pc)

theorem secretPrepare_pc (s : MachineState) (pc : s.pc = 0x112c) :
    (secretPrepare s).pc = 0x1224 := by
  simp [secretPrepare, runSchedule, secretPrepareSchedule, execInstrBr, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

def secretFinishSchedule : List (Word × Instr) := [
  (0x1228, .LUI .x6 66),
  (0x122c, .ADDI .x6 .x6 (0)),
  (0x1230, .LUI .x7 69),
  (0x1234, .ADDI .x7 .x7 (-1280)),
  (0x1238, .LWU .x13 .x6 (0)),
  (0x123c, .SW .x7 .x13 (0)),
  (0x1240, .LWU .x13 .x6 (4)),
  (0x1244, .SW .x7 .x13 (4)),
  (0x1248, .LWU .x13 .x6 (8)),
  (0x124c, .SW .x7 .x13 (8)),
  (0x1250, .LWU .x13 .x6 (12)),
  (0x1254, .SW .x7 .x13 (12)),
  (0x1258, .LWU .x13 .x6 (16)),
  (0x125c, .SW .x7 .x13 (16)),
  (0x1260, .ADDI .x6 .x0 (0)),
  (0x1264, .LUI .x28 67),
  (0x1268, .ADDI .x28 .x28 (88)),
  (0x126c, .SD .x28 .x6 (0))]

def secretFinish (s : MachineState) : MachineState := runSchedule secretFinishSchedule s

theorem secretFinish_code : ∀ entry ∈ secretFinishSchedule,
    instructionAt SphincsMaskedImages.keygen entry.1 = some (.base entry.2) := by decide

theorem secretFinish_checked (s : MachineState) (pc : s.pc = 0x1228) :
    Checked secretFinishSchedule s := by
  simp [secretFinishSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

theorem secretFinish_block (s : MachineState) (pc : s.pc = 0x1228) :
    OrdinarySteps SphincsMaskedImages.keygen s 18 (secretFinish s) :=
  checked_sound _ secretFinishSchedule secretFinish_code s (secretFinish_checked s pc)

theorem secretFinish_pc (s : MachineState) (pc : s.pc = 0x1228) :
    (secretFinish s).pc = 0x1270 := by
  simp [secretFinish, runSchedule, secretFinishSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

def endpointSetupSchedule : List (Word × Instr) := [
  (0x13e0, .LUI .x6 68),
  (0x13e4, .ADDI .x6 .x6 (768)),
  (0x13e8, .LUI .x28 67),
  (0x13ec, .ADDI .x28 .x28 (80)),
  (0x13f0, .LD .x7 .x28 (0)),
  (0x13f4, .SLLI .x10 .x7 (2)),
  (0x13f8, .SLLI .x11 .x7 (4)),
  (0x13fc, .ADD .x10 .x10 .x11),
  (0x1400, .ADD .x7 .x6 .x10),
  (0x1404, .LUI .x6 69),
  (0x1408, .ADDI .x6 .x6 (-1280))]

def endpointSetup (s : MachineState) : MachineState := runSchedule endpointSetupSchedule s

theorem endpointSetup_code : ∀ entry ∈ endpointSetupSchedule,
    instructionAt SphincsMaskedImages.keygen entry.1 = some (.base entry.2) := by decide

theorem endpointSetup_checked (s : MachineState) (pc : s.pc = 0x13e0) :
    Checked endpointSetupSchedule s := by
  simp [endpointSetupSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc]

theorem endpointSetup_block (s : MachineState) (pc : s.pc = 0x13e0) :
    OrdinarySteps SphincsMaskedImages.keygen s 11 (endpointSetup s) :=
  checked_sound _ endpointSetupSchedule endpointSetup_code s (endpointSetup_checked s pc)

theorem endpointSetup_pc (s : MachineState) (pc : s.pc = 0x13e0) :
    (endpointSetup s).pc = 0x140c := by
  simp [endpointSetup, runSchedule, endpointSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc]

def endpointFinishSchedule : List (Word × Instr) := [
  (0x1434, .LUI .x28 67),
  (0x1438, .ADDI .x28 .x28 (80)),
  (0x143c, .LD .x6 .x28 (0)),
  (0x1440, .ADDI .x6 .x6 (1)),
  (0x1444, .LUI .x28 67),
  (0x1448, .ADDI .x28 .x28 (80)),
  (0x144c, .SD .x28 .x6 (0)),
  (0x1450, .LUI .x28 67),
  (0x1454, .ADDI .x28 .x28 (80)),
  (0x1458, .LD .x6 .x28 (0)),
  (0x145c, .ADDI .x7 .x0 (52)),
  (0x1460, .BNE .x6 .x7 (-820))]

def endpointFinish (s : MachineState) : MachineState := runSchedule endpointFinishSchedule s

theorem endpointFinish_code : ∀ entry ∈ endpointFinishSchedule,
    instructionAt SphincsMaskedImages.keygen entry.1 = some (.base entry.2) := by decide

theorem endpointFinish_checked (s : MachineState) (pc : s.pc = 0x1434) :
    Checked endpointFinishSchedule s := by
  simp [endpointFinishSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc]

theorem endpointFinish_block (s : MachineState) (pc : s.pc = 0x1434) :
    OrdinarySteps SphincsMaskedImages.keygen s 12 (endpointFinish s) :=
  checked_sound _ endpointFinishSchedule endpointFinish_code s (endpointFinish_checked s pc)

theorem secretPrepare_registers (s : MachineState) :
    (secretPrepare s).getReg .x10 = 0x40000 ∧ (secretPrepare s).getReg .x11 = 576 ∧
    (secretPrepare s).getReg .x12 = 0x42000 ∧ (secretPrepare s).getReg .x5 = 1 := by
  simp [secretPrepare, runSchedule, secretPrepareSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, MachineState.setWord32,
    MachineState.getWord32, alignToDword, byteOffset]


def secretAnswer (hash : Hash) (s : MachineState) : MachineState :=
  writeHash (secretPrepare s) (hash (hashInput (secretPrepare s)))
def initialChain (hash : Hash) (s : MachineState) : MachineState := secretFinish (secretAnswer hash s)

theorem initialChain_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x112c) :
    Trace hash SphincsMaskedImages.keygen s 99 114 1 2 (initialChain hash s) := by
  obtain ⟨src, bits, dst, service⟩ := secretPrepare_registers s
  have fetch : fetch SphincsMaskedImages.keygen (secretPrepare s) = some (.base .ECALL) := by
    rw [fetch_at, secretPrepare_pc s pc]; decide
  have valid : hashArgumentsValid (secretPrepare s) = true := by
    simp [hashArgumentsValid, src, bits, dst, accessValid, rangeValid, MEMORY_BYTES]
  have len : (hashInput (secretPrepare s)).1 = 576 := by simp [hashInput, bits]
  have one := Trace.hash (hash := hash) (image := SphincsMaskedImages.keygen)
    (secretPrepare s) _ 0 0 0 0 fetch service valid (Trace.refl _)
  have hashStep : Trace hash SphincsMaskedImages.keygen (secretPrepare s) 1 16 1 2
      (secretAnswer hash s) := by simp only [len] at one; exact one
  have apc : (secretAnswer hash s).pc = 0x1228 := by
    simp [secretAnswer, writeHash, secretPrepare_pc s pc]
  exact (secretPrepare_block s pc).trace.trans (hashStep.trans (secretFinish_block _ apc).trace)


theorem initialChain_pc (hash : Hash) (s : MachineState) (pc : s.pc = 0x112c) :
    (initialChain hash s).pc = 0x1270 := by
  have apc : (secretAnswer hash s).pc = 0x1228 := by
    simp [secretAnswer, writeHash, secretPrepare_pc s pc]
  exact secretFinish_pc (secretAnswer hash s) apc


theorem secretFinish_step_zero (s : MachineState) :
    (secretFinish s).getMem 0x43058 = 0 := by
  simp [secretFinish, runSchedule, secretFinishSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, MachineState.setWord32,
    MachineState.getWord32, alignToDword, byteOffset]

theorem initialChain_step_zero (hash : Hash) (s : MachineState) :
    (initialChain hash s).getMem 0x43058 = 0 := secretFinish_step_zero _


theorem endpointSetup_frame (s : MachineState) (a : Word) :
    (endpointSetup s).getMem a = s.getMem a := by
  simp [endpointSetup, runSchedule, endpointSetupSchedule, execInstrBr]

theorem endpointSetup_registers (s : MachineState) (c : Nat)
    (chain : s.getMem 0x43050 = BitVec.ofNat 64 c) :
    (endpointSetup s).getReg .x6 = 0x44b00 ∧
    (endpointSetup s).getReg .x7 = BitVec.ofNat 64 (0x44300 + 20 * c) := by
  change s.getMem 0x43050#64 = BitVec.ofNat 64 c at chain
  simp [endpointSetup, runSchedule, endpointSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, chain]
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 0x44300 + (BitVec.ofNat 64 c * BitVec.ofNat 64 4 +
    BitVec.ofNat 64 c * BitVec.ofNat 64 16) = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1; omega


theorem endpoint_copy_code : Copy20Code SphincsMaskedImages.keygen 259 := by
  constructor <;> intro i <;> fin_cases i <;> decide

def endpointStored (s : MachineState) := copyRootState (endpointSetup s)
def endpointNext (s : MachineState) := endpointFinish (endpointStored s)

theorem endpointStored_pc (s : MachineState) (pc : s.pc = 0x13e0) :
    (endpointStored s).pc = 0x1434 := by
  simp [endpointStored, copyRootState, copyWordState, execInstrBr, endpointSetup_pc s pc]

theorem endpoint_block (s : MachineState) (c : Fin 52) (pc : s.pc = 0x13e0)
    (chain : s.getMem 0x43050 = BitVec.ofNat 64 c.val) :
    OrdinarySteps SphincsMaskedImages.keygen s 33 (endpointNext s) := by
  have regs := endpointSetup_registers s c.val chain
  have copied := copy20_block_general SphincsMaskedImages.keygen 259 endpoint_copy_code
    (endpointSetup s) 0x44b00 (0x44300 + 20 * c.val) (endpointSetup_pc s pc)
    regs.1 regs.2 (by decide) (by decide) (by omega) (by dsimp [MEMORY_BYTES]; omega) (by decide)
  exact ordinary_trans _ _ _ _ 11 22 (endpointSetup_block s pc)
    (ordinary_trans _ _ _ _ 10 12 copied
      (endpointFinish_block _ (endpointStored_pc s pc)))


def secretPrepareWrites : List Word := [0x43010#64, 0x43018#64, 0x40000#64, 0x40008#64, 0x40010#64, 0x40018#64, 0x40020#64, 0x40028#64, 0x40030#64, 0x40038#64, 0x40040#64]
theorem secretPrepare_frame (s : MachineState) (a : Word) (outside : a ∉ secretPrepareWrites) :
    (secretPrepare s).getMem a = s.getMem a := by
  simp only [secretPrepareWrites, List.mem_cons, List.not_mem_nil, not_or] at outside
  rcases outside with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  simp [secretPrepare, runSchedule, secretPrepareSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

def secretFinishWrites : List Word := [0x43058#64, 0x44b00#64, 0x44b08#64, 0x44b10#64]
theorem secretFinish_frame (s : MachineState) (a : Word) (outside : a ∉ secretFinishWrites) :
    (secretFinish s).getMem a = s.getMem a := by
  simp only [secretFinishWrites, List.mem_cons, List.not_mem_nil, not_or] at outside
  rcases outside with ⟨h0, h1, h2, h3⟩
  simp [secretFinish, runSchedule, secretFinishSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, h0, h1, h2, h3]

def initialWrites : List Word := secretPrepareWrites ++ SphincsMaskedChainStep.answerWrites ++ secretFinishWrites

theorem initialChain_frame (hash : Hash) (s : MachineState) (a : Word)
    (outside : a ∉ initialWrites) : (initialChain hash s).getMem a = s.getMem a := by
  have all : (a ∉ secretPrepareWrites ∧ a ∉ SphincsMaskedChainStep.answerWrites) ∧
      a ∉ secretFinishWrites := by
    simpa only [initialWrites, List.mem_append, not_or] using outside
  obtain ⟨⟨hp, ha⟩, hf⟩ := all
  change (secretFinish (secretAnswer hash s)).getMem a = _
  rw [secretFinish_frame _ a hf]
  have dst := (secretPrepare_registers s).2.2.1
  simp only [SphincsMaskedChainStep.answerWrites, List.mem_cons, List.not_mem_nil, not_or] at ha
  obtain ⟨h0,h1,h2,h3⟩ := ha
  simp [secretAnswer, writeHash, dst, MachineState.writeWords, h0,h1,h2,h3]
  exact secretPrepare_frame s a hp

theorem endpointStored_counter (s : MachineState) (c : Fin 52)
    (chain : s.getMem 0x43050 = BitVec.ofNat 64 c.val) :
    (endpointStored s).getMem 0x43050 = s.getMem 0x43050 := by
  change (copyRootState (endpointSetup s)).getMem 0x43050 = _
  rw [copyRoot_mem_frame]
  · exact endpointSetup_frame s _
  · intro i
    rw [(endpointSetup_registers s c.val chain).2]
    fin_cases c <;> fin_cases i <;> decide

theorem endpointFinish_counter (s : MachineState) :
    (endpointFinish s).getMem 0x43050 = s.getMem 0x43050 + 1 := by
  simp [endpointFinish, runSchedule, endpointFinishSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem endpointFinish_pc (s : MachineState) (pc : s.pc = 0x1434) :
    (endpointFinish s).pc = if s.getMem 0x43050 + 1 = 52 then 0x1464 else 0x112c := by
  simp [endpointFinish, runSchedule, endpointFinishSchedule, execInstrBr, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def chainValue (hash : Hash) (s : MachineState) : MachineState :=
  SphincsMaskedChainStep.walk hash 7 (initialChain hash s)
def chainNext (hash : Hash) (s : MachineState) : MachineState := endpointNext (chainValue hash s)

theorem chainValue_counter (hash : Hash) (s : MachineState) :
    (chainValue hash s).getMem 0x43050 = s.getMem 0x43050 := by
  change (SphincsMaskedChainStep.walk hash 7 (initialChain hash s)).getMem _ = _
  rw [SphincsMaskedChainStep.walk_frame hash 7 _ _ (by decide)]
  exact initialChain_frame hash s _ (by decide)

theorem chain_trace (hash : Hash) (s : MachineState) (c : Fin 52)
    (pc : s.pc = 0x112c) (chain : s.getMem 0x43050 = BitVec.ofNat 64 c.val) :
    Trace hash SphincsMaskedImages.keygen s 776 840 8 9 (chainNext hash s) ∧
    (chainNext hash s).getMem 0x43050 = BitVec.ofNat 64 (c.val + 1) ∧
    (chainNext hash s).pc = if c.val + 1 = 52 then 0x1464 else 0x112c := by
  obtain ⟨steps, _, loc⟩ := SphincsMaskedChainStep.seven_steps hash (initialChain hash s)
    (initialChain_pc hash s pc) (initialChain_step_zero hash s)
  have count : (chainValue hash s).getMem 0x43050 = BitVec.ofNat 64 c.val :=
    (chainValue_counter hash s).trans chain
  have vpc : (chainValue hash s).pc = 0x13e0 := loc
  have stored : (endpointStored (chainValue hash s)).getMem 0x43050 = BitVec.ofNat 64 c.val :=
    (endpointStored_counter _ c count).trans count
  refine ⟨?_, ?_, ?_⟩
  · exact (initialChain_trace hash s pc).trans
      (steps.trans (endpoint_block _ c vpc count).trace)
  · change (endpointFinish (endpointStored (chainValue hash s))).getMem _ = _
    rw [endpointFinish_counter, stored]
    exact (BitVec.ofNat_add _ _).symm
  · change (endpointFinish (endpointStored (chainValue hash s))).pc = _
    rw [endpointFinish_pc _ (endpointStored_pc _ vpc), stored]
    have next : BitVec.ofNat 64 c.val + 1 = BitVec.ofNat 64 (c.val + 1) := (BitVec.ofNat_add _ _).symm
    rw [next]
    have eq : (BitVec.ofNat 64 (c.val + 1) : Word) = 52 ↔ c.val + 1 = 52 := by
      constructor
      · intro h
        have hh := congrArg BitVec.toNat h
        change (c.val + 1) % 2 ^ 64 = 52 at hh
        rw [Nat.mod_eq_of_lt (by omega)] at hh
        exact hh
      · intro h; rw [h]; rfl
    simp only [eq]


def chains (hash : Hash) : Nat → MachineState → MachineState
  | 0, s => s
  | n + 1, s => chainNext hash (chains hash n s)

theorem chains_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x112c)
    (counter : s.getMem 0x43050 = 0) (n : Nat) (hn : n ≤ 52) :
    Trace hash SphincsMaskedImages.keygen s (776 * n) (840 * n) (8 * n) (9 * n) (chains hash n s) ∧
      (chains hash n s).getMem 0x43050 = BitVec.ofNat 64 n ∧
      (chains hash n s).pc = if n = 52 then 0x1464 else 0x112c := by
  induction n with
  | zero => exact ⟨Trace.refl _, counter, pc⟩
  | succ n ih =>
    obtain ⟨trace, count, loc⟩ := ih (by omega)
    have npc : (chains hash n s).pc = 0x112c := by rw [loc, if_neg (by omega)]
    obtain ⟨step, nextCount, nextPc⟩ := chain_trace hash (chains hash n s) ⟨n, by omega⟩ npc count
    refine ⟨?_, nextCount, nextPc⟩
    simpa only [chains, Nat.mul_succ] using trace.trans step

/-- The complete WOTS endpoint loop for one leaf, including every secret derivation. -/
theorem fifty_two_chains (hash : Hash) (s : MachineState) (pc : s.pc = 0x112c)
    (counter : s.getMem 0x43050 = 0) :
    Trace hash SphincsMaskedImages.keygen s 40352 43680 416 468 (chains hash 52 s) ∧
      (chains hash 52 s).getMem 0x43050 = 52 ∧ (chains hash 52 s).pc = 0x1464 := by
  simpa using chains_trace hash s pc counter 52 (by decide)

/-- info: 'SigGolfCandidate.SphincsMaskedChainLoop.initialChain_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initialChain_trace

/-- info: 'SigGolfCandidate.SphincsMaskedChainLoop.initialChain_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initialChain_frame

/-- info: 'SigGolfCandidate.SphincsMaskedChainLoop.endpoint_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms endpoint_block

/-- info: 'SigGolfCandidate.SphincsMaskedChainLoop.chain_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chain_trace

/-- info: 'SigGolfCandidate.SphincsMaskedChainLoop.fifty_two_chains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fifty_two_chains

end SigGolfCandidate.SphincsMaskedChainLoop
