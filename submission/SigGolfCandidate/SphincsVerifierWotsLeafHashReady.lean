import SigGolfCandidate.SphincsVerifierWotsSemanticLeaf
import SigGolfCandidate.SphincsMaskedKeygenPrefix

namespace SigGolfCandidate.SphincsVerifierWotsLeafHashReady
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def leafHashSchedule : List (Word × Instr) := [
  (0x29c8, .ADDI .x6 .x0 513),
  (0x29cc, .LUI .x28 67),
  (0x29d0, .ADDI .x28 .x28 0),
  (0x29d4, .LD .x7 .x28 0),
  (0x29d8, .SLLI .x7 .x7 16),
  (0x29dc, .ADD .x6 .x6 .x7),
  (0x29e0, .LUI .x7 64),
  (0x29e4, .ADDI .x7 .x7 0),
  (0x29e8, .SW .x7 .x6 0),
  (0x29ec, .LUI .x28 67),
  (0x29f0, .ADDI .x28 .x28 16),
  (0x29f4, .LD .x6 .x28 0),
  (0x29f8, .SW .x7 .x6 4),
  (0x29fc, .LUI .x28 67),
  (0x2a00, .ADDI .x28 .x28 8),
  (0x2a04, .LD .x6 .x28 0),
  (0x2a08, .SD .x7 .x6 8),
  (0x2a0c, .LUI .x28 67),
  (0x2a10, .ADDI .x28 .x28 24),
  (0x2a14, .LD .x6 .x28 0),
  (0x2a18, .SW .x7 .x6 16),
  (0x2a1c, .LUI .x6 35),
  (0x2a20, .ADDI .x6 .x6 (-844)),
  (0x2a24, .LUI .x7 64),
  (0x2a28, .ADDI .x7 .x7 20),
  (0x2a2c, .LWU .x13 .x6 0),
  (0x2a30, .SW .x7 .x13 0),
  (0x2a34, .LWU .x13 .x6 4),
  (0x2a38, .SW .x7 .x13 4),
  (0x2a3c, .LWU .x13 .x6 8),
  (0x2a40, .SW .x7 .x13 8),
  (0x2a44, .LWU .x13 .x6 12),
  (0x2a48, .SW .x7 .x13 12),
  (0x2a4c, .LWU .x13 .x6 16),
  (0x2a50, .SW .x7 .x13 16),
  (0x2a54, .LUI .x10 64),
  (0x2a58, .ADDI .x10 .x10 0),
  (0x2a5c, .LUI .x11 2),
  (0x2a60, .ADDI .x11 .x11 448),
  (0x2a64, .LUI .x12 66),
  (0x2a68, .ADDI .x12 .x12 0),
  (0x2a6c, .ADDI .x5 .x0 1)]

theorem leafHashSchedule_code : ∀ entry ∈ leafHashSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by decide

def leafHashReadyState (s : MachineState) : MachineState :=
  runSchedule leafHashSchedule s

theorem leafHashSchedule_checked (s : MachineState) (pc : s.pc = 0x29c8) :
    Checked leafHashSchedule s := by
  simp [Checked, leafHashSchedule, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

theorem leafHashReady_block (s : MachineState) (pc : s.pc = 0x29c8) :
    OrdinarySteps SphincsImages.verify s 42 (leafHashReadyState s) := by
  simpa only [leafHashReadyState, show leafHashSchedule.length = 42 by decide] using
    checked_sound _ leafHashSchedule leafHashSchedule_code s
      (leafHashSchedule_checked s pc)

private theorem runSchedule_append (xs ys : List (Word × Instr)) (s : MachineState) :
    runSchedule (xs ++ ys) s = runSchedule ys (runSchedule xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

private def leafHashPrelude : List (Word × Instr) := leafHashSchedule.take 35
private def leafHashRegisters : List (Word × Instr) := leafHashSchedule.drop 35
private theorem leafHash_split : leafHashSchedule = leafHashPrelude ++ leafHashRegisters := by
  decide

private theorem leafHashRegisters_eq : leafHashRegisters = [
    (0x2a54, .LUI .x10 64), (0x2a58, .ADDI .x10 .x10 0),
    (0x2a5c, .LUI .x11 2), (0x2a60, .ADDI .x11 .x11 448),
    (0x2a64, .LUI .x12 66), (0x2a68, .ADDI .x12 .x12 0),
    (0x2a6c, .ADDI .x5 .x0 1)] := by decide

private theorem leafHashRegisters_regs (t : MachineState) :
    (runSchedule leafHashRegisters t).getReg .x10 = 0x40000 ∧
    (runSchedule leafHashRegisters t).getReg .x11 = 8640 ∧
    (runSchedule leafHashRegisters t).getReg .x12 = 0x42000 ∧
    (runSchedule leafHashRegisters t).getReg .x5 = 1 := by
  rw [leafHashRegisters_eq]
  simp [runSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem leafHashReady_regs (s : MachineState) :
    (leafHashReadyState s).getReg .x10 = 0x40000 ∧
    (leafHashReadyState s).getReg .x11 = 8640 ∧
    (leafHashReadyState s).getReg .x12 = 0x42000 ∧
    (leafHashReadyState s).getReg .x5 = 1 := by
  rw [leafHashReadyState, leafHash_split, runSchedule_append]
  exact leafHashRegisters_regs _

private def leafHashChunk0 : List (Word × Instr) := (leafHashSchedule.drop 0).take 7
private theorem leafHashChunk0_pc (s : MachineState) (pc : s.pc = 0x29c8) :
    (runSchedule leafHashChunk0 s).pc = 0x29e4 := by
  simp [leafHashChunk0, leafHashSchedule, runSchedule, execInstrBr, pc]

private def leafHashChunk1 : List (Word × Instr) := (leafHashSchedule.drop 7).take 7
private def leafHashChunk2 : List (Word × Instr) := (leafHashSchedule.drop 14).take 7
private def leafHashChunk3 : List (Word × Instr) := (leafHashSchedule.drop 21).take 7
private def leafHashChunk4 : List (Word × Instr) := (leafHashSchedule.drop 28).take 7
private def leafHashChunk5 : List (Word × Instr) := (leafHashSchedule.drop 35).take 7

private theorem leafHashChunk1_pc (s : MachineState) (pc : s.pc = 0x29e4) :
    (runSchedule leafHashChunk1 s).pc = 0x2a00 := by
  simp [leafHashChunk1, leafHashSchedule, runSchedule, execInstrBr, pc]
private theorem leafHashChunk2_pc (s : MachineState) (pc : s.pc = 0x2a00) :
    (runSchedule leafHashChunk2 s).pc = 0x2a1c := by
  simp [leafHashChunk2, leafHashSchedule, runSchedule, execInstrBr, pc]
private theorem leafHashChunk3_pc (s : MachineState) (pc : s.pc = 0x2a1c) :
    (runSchedule leafHashChunk3 s).pc = 0x2a38 := by
  simp [leafHashChunk3, leafHashSchedule, runSchedule, execInstrBr, pc]
private theorem leafHashChunk4_pc (s : MachineState) (pc : s.pc = 0x2a38) :
    (runSchedule leafHashChunk4 s).pc = 0x2a54 := by
  simp [leafHashChunk4, leafHashSchedule, runSchedule, execInstrBr, pc]
private theorem leafHashChunk5_pc (s : MachineState) (pc : s.pc = 0x2a54) :
    (runSchedule leafHashChunk5 s).pc = 0x2a70 := by
  simp [leafHashChunk5, leafHashSchedule, runSchedule, execInstrBr, pc]

private theorem leafHash_chunks : leafHashSchedule =
    leafHashChunk0 ++ leafHashChunk1 ++ leafHashChunk2 ++
      leafHashChunk3 ++ leafHashChunk4 ++ leafHashChunk5 := by decide

theorem leafHashReady_pc (s : MachineState) (pc : s.pc = 0x29c8) :
    (leafHashReadyState s).pc = 0x2a70 := by
  have p0 := leafHashChunk0_pc s pc
  have p1 := leafHashChunk1_pc (runSchedule leafHashChunk0 s) p0
  have p2 := leafHashChunk2_pc
    (runSchedule leafHashChunk1 (runSchedule leafHashChunk0 s)) p1
  have p3 := leafHashChunk3_pc
    (runSchedule leafHashChunk2
      (runSchedule leafHashChunk1 (runSchedule leafHashChunk0 s))) p2
  have p4 := leafHashChunk4_pc
    (runSchedule leafHashChunk3
      (runSchedule leafHashChunk2
        (runSchedule leafHashChunk1 (runSchedule leafHashChunk0 s)))) p3
  have p5 := leafHashChunk5_pc
    (runSchedule leafHashChunk4
      (runSchedule leafHashChunk3
        (runSchedule leafHashChunk2
          (runSchedule leafHashChunk1 (runSchedule leafHashChunk0 s))))) p4
  simpa only [leafHashReadyState, leafHash_chunks, runSchedule_append] using p5

#print axioms leafHashReady_block
#print axioms leafHashReady_regs
#print axioms leafHashReady_pc

end SigGolfCandidate.SphincsVerifierWotsLeafHashReady
