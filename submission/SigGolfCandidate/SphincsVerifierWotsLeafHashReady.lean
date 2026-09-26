import SigGolfCandidate.SphincsVerifierWotsSemanticLeaf
import SigGolfCandidate.SphincsMaskedKeygenPrefix
import SigGolfCandidate.SphincsVerifierCopyMemory

namespace SigGolfCandidate.SphincsVerifierWotsLeafHashReady
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsMaskedKeygenPrefix
open SigGolfCandidate.SphincsVerifierCopyMemory
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

private theorem leafHashChunk0_memory (s : MachineState) (read : Word) :
    (runSchedule leafHashChunk0 s).getMem read = s.getMem read := by
  simp [leafHashChunk0, leafHashSchedule, runSchedule, execInstrBr]

private theorem leafHashChunk0_pointer (s : MachineState) :
    (runSchedule leafHashChunk0 s).getReg .x7 = 0x40000 := by
  simp [leafHashChunk0, leafHashSchedule, runSchedule, execInstrBr,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

private theorem leafHashChunk0_tag (s : MachineState) :
    (runSchedule leafHashChunk0 s).getReg .x6 =
      (513#64) + (s.getMem 0x43000 <<< 16) := by
  simp [leafHashChunk0, leafHashSchedule, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

private def leafHashChunk1 : List (Word × Instr) := (leafHashSchedule.drop 7).take 7
private def leafHashChunk2 : List (Word × Instr) := (leafHashSchedule.drop 14).take 7
private def leafHashChunk3 : List (Word × Instr) := (leafHashSchedule.drop 21).take 7
private def leafHashChunk4 : List (Word × Instr) := (leafHashSchedule.drop 28).take 7
private def leafHashChunk5 : List (Word × Instr) := (leafHashSchedule.drop 35).take 7

private theorem leafHashChunk1_pc (s : MachineState) (pc : s.pc = 0x29e4) :
    (runSchedule leafHashChunk1 s).pc = 0x2a00 := by
  simp [leafHashChunk1, leafHashSchedule, runSchedule, execInstrBr, pc]

private theorem leafHashChunk1_memory (s : MachineState) (read : Word)
    (pointer : s.getReg .x7 = 0x40000)
    (outside : read.toNat < 0x40000 ∨ 0x40028 ≤ read.toNat) :
    (runSchedule leafHashChunk1 s).getMem read = s.getMem read := by
  have hne : read ≠ (262144#64) := by
    intro h
    subst read
    have impossible : ¬ ((262144#64).toNat < 0x40000 ∨
      0x40028 ≤ (262144#64).toNat) := by decide
    exact impossible outside
  simp [leafHashChunk1, leafHashSchedule, runSchedule, execInstrBr,
    setWord32_eq, pointer, MachineState.getMem_setMem_ne, hne,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    signExtend12, alignToDword, byteOffset]

private theorem leafHashChunk1_pointer (s : MachineState)
    (pointer : s.getReg .x7 = 0x40000) :
    (runSchedule leafHashChunk1 s).getReg .x7 = 0x40000 := by
  simp [leafHashChunk1, leafHashSchedule, runSchedule, execInstrBr,
    pointer, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
private theorem leafHashChunk2_pc (s : MachineState) (pc : s.pc = 0x2a00) :
    (runSchedule leafHashChunk2 s).pc = 0x2a1c := by
  simp [leafHashChunk2, leafHashSchedule, runSchedule, execInstrBr, pc]

private theorem leafHashChunk2_memory (s : MachineState) (read : Word)
    (pointer : s.getReg .x7 = 0x40000)
    (outside : read.toNat < 0x40000 ∨ 0x40028 ≤ read.toNat) :
    (runSchedule leafHashChunk2 s).getMem read = s.getMem read := by
  have hne8 : read ≠ (262152#64) := by
    intro h; subst read
    have impossible : ¬ ((0x40008 : Word).toNat < 0x40000 ∨
      0x40028 ≤ (0x40008 : Word).toNat) := by decide
    exact impossible outside
  have hne16 : read ≠ (262160#64) := by
    intro h; subst read
    have impossible : ¬ ((0x40010 : Word).toNat < 0x40000 ∨
      0x40028 ≤ (0x40010 : Word).toNat) := by decide
    exact impossible outside
  simp [leafHashChunk2, leafHashSchedule, runSchedule, execInstrBr,
    setWord32_eq, pointer, hne8, hne16,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    signExtend12, alignToDword, byteOffset]

private theorem leafHashChunk2_pointer (s : MachineState)
    (pointer : s.getReg .x7 = 0x40000) :
    (runSchedule leafHashChunk2 s).getReg .x7 = 0x40000 := by
  simp [leafHashChunk2, leafHashSchedule, runSchedule, execInstrBr,
    pointer, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

private theorem leafHashChunk1_scratchPointer (s : MachineState) :
    (runSchedule leafHashChunk1 s).getReg .x28 = 0x43000 := by
  simp [leafHashChunk1, leafHashSchedule, runSchedule, execInstrBr,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

private theorem leafHashChunk1_tag_position (s : MachineState)
    (pointer : s.getReg .x7 = 0x40000) :
    (runSchedule leafHashChunk1 s).getWord32 0x40000 =
      (s.getReg .x6).truncate 32 ∧
    (runSchedule leafHashChunk1 s).getWord32 0x40004 =
      (s.getMem 0x43010).truncate 32 := by
  constructor
  · simp [leafHashChunk1, leafHashSchedule, runSchedule, execInstrBr,
      pointer, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
    rw [getWord32_setWord32_other (other := by decide)]
    simp [getWord32_setWord32_same]
  · simp [leafHashChunk1, leafHashSchedule, runSchedule, execInstrBr,
      pointer, signExtend12, getWord32_setWord32_same,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    rw [setWord32_eq, MachineState.getMem_setMem_ne (by decide)]
    rfl

private theorem leafHashChunk2_tree (s : MachineState)
    (pointer : s.getReg .x7 = 0x40000)
    (scratch : s.getReg .x28 = 0x43000) :
    (runSchedule leafHashChunk2 s).getMem 0x40008 = s.getMem 0x43008 := by
  simp [leafHashChunk2, leafHashSchedule, runSchedule, execInstrBr,
    pointer, scratch, signExtend12, setWord32_eq,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_ne, alignToDword, byteOffset]

private theorem leafHashChunk2_index (s : MachineState)
    (pointer : s.getReg .x7 = 0x40000)
    (scratch : s.getReg .x28 = 0x43000) :
    (runSchedule leafHashChunk2 s).getWord32 0x40010 =
      (s.getMem 0x43018).truncate 32 := by
  simp [leafHashChunk2, leafHashSchedule, runSchedule, execInstrBr,
    pointer, scratch, signExtend12, getWord32_setWord32_same,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_ne]

private theorem leafHashChunk2_headerFrame (s : MachineState)
    (pointer : s.getReg .x7 = 0x40000) (slot : Fin 2) :
    (runSchedule leafHashChunk2 s).getWord32
        (BitVec.ofNat 64 (0x40000 + 4 * slot.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x40000 + 4 * slot.val)) := by
  fin_cases slot <;>
    simp [leafHashChunk2, leafHashSchedule, runSchedule, execInstrBr,
      pointer, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] <;>
    rw [getWord32_setWord32_other (other := by decide)] <;>
    simp [MachineState.getWord32, alignToDword, byteOffset]
private theorem leafHashChunk3_pc (s : MachineState) (pc : s.pc = 0x2a1c) :
    (runSchedule leafHashChunk3 s).pc = 0x2a38 := by
  simp [leafHashChunk3, leafHashSchedule, runSchedule, execInstrBr, pc]
private theorem leafHashChunk3_memory (s : MachineState) (read : Word)
    (outside : read.toNat < 0x40000 ∨ 0x40028 ≤ read.toNat) :
    (runSchedule leafHashChunk3 s).getMem read = s.getMem read := by
  have hne : read ≠ (262160#64) := by
    intro h; subst read
    have impossible : ¬ ((0x40010 : Word).toNat < 0x40000 ∨
      0x40028 ≤ (0x40010 : Word).toNat) := by decide
    exact impossible outside
  simp [leafHashChunk3, leafHashSchedule, runSchedule, execInstrBr,
    setWord32_eq, hne, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12, alignToDword, byteOffset]

private theorem leafHashChunk3_pointer (s : MachineState) :
    (runSchedule leafHashChunk3 s).getReg .x7 = 0x40014 := by
  simp [leafHashChunk3, leafHashSchedule, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

private theorem leafHashChunk3_treeFrame (s : MachineState) :
    (runSchedule leafHashChunk3 s).getMem 0x40008 = s.getMem 0x40008 := by
  simp [leafHashChunk3, leafHashSchedule, runSchedule, execInstrBr,
    setWord32_eq, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12, alignToDword, byteOffset]

private theorem leafHashChunk3_indexFrame (s : MachineState) :
    (runSchedule leafHashChunk3 s).getWord32 0x40010 = s.getWord32 0x40010 := by
  simp [leafHashChunk3, leafHashSchedule, runSchedule, execInstrBr,
    getWord32_setWord32_other, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12, alignToDword, byteOffset]

private theorem leafHashChunk3_headerFrame (s : MachineState) (slot : Fin 2) :
    (runSchedule leafHashChunk3 s).getWord32
        (BitVec.ofNat 64 (0x40000 + 4 * slot.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x40000 + 4 * slot.val)) := by
  fin_cases slot <;>
    simp [leafHashChunk3, leafHashSchedule, runSchedule, execInstrBr,
      setWord32_eq, MachineState.getWord32,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      signExtend12, alignToDword, byteOffset]
private theorem leafHashChunk4_pc (s : MachineState) (pc : s.pc = 0x2a38) :
    (runSchedule leafHashChunk4 s).pc = 0x2a54 := by
  simp [leafHashChunk4, leafHashSchedule, runSchedule, execInstrBr, pc]
private theorem leafHashChunk4_memory (s : MachineState) (read : Word)
    (pointer : s.getReg .x7 = 0x40014)
    (outside : read.toNat < 0x40000 ∨ 0x40028 ≤ read.toNat) :
    (runSchedule leafHashChunk4 s).getMem read = s.getMem read := by
  have hne24 : read ≠ (262168#64) := by
    intro h; subst read
    have impossible : ¬ ((0x40018 : Word).toNat < 0x40000 ∨
      0x40028 ≤ (0x40018 : Word).toNat) := by decide
    exact impossible outside
  have hne32 : read ≠ (262176#64) := by
    intro h; subst read
    have impossible : ¬ ((0x40020 : Word).toNat < 0x40000 ∨
      0x40028 ≤ (0x40020 : Word).toNat) := by decide
    exact impossible outside
  simp [leafHashChunk4, leafHashSchedule, runSchedule, execInstrBr,
    setWord32_eq, pointer, hne24, hne32,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    signExtend12, alignToDword, byteOffset]

private theorem leafHashChunk4_treeFrame (s : MachineState)
    (pointer : s.getReg .x7 = 0x40014) :
    (runSchedule leafHashChunk4 s).getMem 0x40008 = s.getMem 0x40008 := by
  simp [leafHashChunk4, leafHashSchedule, runSchedule, execInstrBr,
    setWord32_eq, pointer, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12, alignToDword, byteOffset]

private theorem leafHashChunk4_indexFrame (s : MachineState)
    (pointer : s.getReg .x7 = 0x40014) :
    (runSchedule leafHashChunk4 s).getWord32 0x40010 = s.getWord32 0x40010 := by
  simp [leafHashChunk4, leafHashSchedule, runSchedule, execInstrBr,
    getWord32_setWord32_other, pointer, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12, alignToDword, byteOffset]

private theorem leafHashChunk4_headerFrame (s : MachineState)
    (pointer : s.getReg .x7 = 0x40014) (slot : Fin 2) :
    (runSchedule leafHashChunk4 s).getWord32
        (BitVec.ofNat 64 (0x40000 + 4 * slot.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x40000 + 4 * slot.val)) := by
  fin_cases slot <;>
    simp [leafHashChunk4, leafHashSchedule, runSchedule, execInstrBr,
      setWord32_eq, MachineState.getWord32, pointer,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      signExtend12, alignToDword, byteOffset]
private theorem leafHashChunk5_pc (s : MachineState) (pc : s.pc = 0x2a54) :
    (runSchedule leafHashChunk5 s).pc = 0x2a70 := by
  simp [leafHashChunk5, leafHashSchedule, runSchedule, execInstrBr, pc]
private theorem leafHashChunk5_memory (s : MachineState) (read : Word) :
    (runSchedule leafHashChunk5 s).getMem read = s.getMem read := by
  simp [leafHashChunk5, leafHashSchedule, runSchedule, execInstrBr]
private theorem leafHashChunk5_wordFrame (s : MachineState) (read : Word) :
    (runSchedule leafHashChunk5 s).getWord32 read = s.getWord32 read := by
  simp [leafHashChunk5, leafHashSchedule, runSchedule, execInstrBr,
    MachineState.getWord32]

private theorem leafHash_chunks : leafHashSchedule =
    leafHashChunk0 ++ leafHashChunk1 ++ leafHashChunk2 ++
      leafHashChunk3 ++ leafHashChunk4 ++ leafHashChunk5 := by decide

theorem leafHashReady_mem_frame (s : MachineState) (read : Word)
    (outside : read.toNat < 0x40000 ∨ 0x40028 ≤ read.toNat) :
    (leafHashReadyState s).getMem read = s.getMem read := by
  let s0 := runSchedule leafHashChunk0 s
  let s1 := runSchedule leafHashChunk1 s0
  let s2 := runSchedule leafHashChunk2 s1
  let s3 := runSchedule leafHashChunk3 s2
  let s4 := runSchedule leafHashChunk4 s3
  have p0 : s0.getReg .x7 = 0x40000 := leafHashChunk0_pointer s
  have p1 : s1.getReg .x7 = 0x40000 := leafHashChunk1_pointer s0 p0
  have p2 : s2.getReg .x7 = 0x40000 := leafHashChunk2_pointer s1 p1
  have p3 : s3.getReg .x7 = 0x40014 := leafHashChunk3_pointer s2
  have m0 := leafHashChunk0_memory s read
  have m1 := leafHashChunk1_memory s0 read p0 outside
  have m2 := leafHashChunk2_memory s1 read p1 outside
  have m3 := leafHashChunk3_memory s2 read outside
  have m4 := leafHashChunk4_memory s3 read p3 outside
  have m5 := leafHashChunk5_memory s4 read
  simpa only [leafHashReadyState, leafHash_chunks, runSchedule_append,
    s0, s1, s2, s3, s4] using
    m5.trans (m4.trans (m3.trans (m2.trans (m1.trans m0))))

theorem leafHashReady_payload_mem_frame (s : MachineState) (read : Word)
    (outside : 0x40028 ≤ read.toNat) :
    (leafHashReadyState s).getMem read = s.getMem read :=
  leafHashReady_mem_frame s read (Or.inr outside)

theorem leafHashReady_tree (s : MachineState) :
    (leafHashReadyState s).getMem 0x40008 = s.getMem 0x43008 := by
  let s0 := runSchedule leafHashChunk0 s
  let s1 := runSchedule leafHashChunk1 s0
  let s2 := runSchedule leafHashChunk2 s1
  let s3 := runSchedule leafHashChunk3 s2
  let s4 := runSchedule leafHashChunk4 s3
  have p0 : s0.getReg .x7 = 0x40000 := leafHashChunk0_pointer s
  have p1 : s1.getReg .x7 = 0x40000 := leafHashChunk1_pointer s0 p0
  have scratch : s1.getReg .x28 = 0x43000 := leafHashChunk1_scratchPointer s0
  have tree := leafHashChunk2_tree s1 p1 scratch
  have m0 := leafHashChunk0_memory s 0x43008
  have m1 := leafHashChunk1_memory s0 0x43008 p0 (by decide)
  have f3 := leafHashChunk3_treeFrame s2
  have p3 : s3.getReg .x7 = 0x40014 := leafHashChunk3_pointer s2
  have f4 := leafHashChunk4_treeFrame s3 p3
  have f5 := leafHashChunk5_memory s4 0x40008
  simpa only [leafHashReadyState, leafHash_chunks, runSchedule_append,
    s0, s1, s2, s3, s4] using
    f5.trans (f4.trans (f3.trans (tree.trans (m1.trans m0))))

theorem leafHashReady_index (s : MachineState) :
    (leafHashReadyState s).getWord32 0x40010 =
      (s.getMem 0x43018).truncate 32 := by
  let s0 := runSchedule leafHashChunk0 s
  let s1 := runSchedule leafHashChunk1 s0
  let s2 := runSchedule leafHashChunk2 s1
  let s3 := runSchedule leafHashChunk3 s2
  let s4 := runSchedule leafHashChunk4 s3
  have p0 : s0.getReg .x7 = 0x40000 := leafHashChunk0_pointer s
  have p1 : s1.getReg .x7 = 0x40000 := leafHashChunk1_pointer s0 p0
  have scratch : s1.getReg .x28 = 0x43000 := leafHashChunk1_scratchPointer s0
  have index := leafHashChunk2_index s1 p1 scratch
  have scratch0 := leafHashChunk0_memory s 0x43018
  have scratch1 := leafHashChunk1_memory s0 0x43018 p0 (by decide)
  have f3 := leafHashChunk3_indexFrame s2
  have p3 : s3.getReg .x7 = 0x40014 := leafHashChunk3_pointer s2
  have f4 := leafHashChunk4_indexFrame s3 p3
  have f5 := leafHashChunk5_wordFrame s4 0x40010
  simpa only [leafHashReadyState, leafHash_chunks, runSchedule_append,
    s0, s1, s2, s3, s4] using
    f5.trans (f4.trans (f3.trans (index.trans
      (congrArg (fun value : Word => value.truncate 32) (scratch1.trans scratch0)))))

theorem leafHashReady_tag_position (s : MachineState) :
    (leafHashReadyState s).getWord32 0x40000 =
      ((513#64) + (s.getMem 0x43000 <<< 16)).truncate 32 ∧
    (leafHashReadyState s).getWord32 0x40004 =
      (s.getMem 0x43010).truncate 32 := by
  let s0 := runSchedule leafHashChunk0 s
  let s1 := runSchedule leafHashChunk1 s0
  let s2 := runSchedule leafHashChunk2 s1
  let s3 := runSchedule leafHashChunk3 s2
  let s4 := runSchedule leafHashChunk4 s3
  have p0 : s0.getReg .x7 = 0x40000 := leafHashChunk0_pointer s
  have p1 : s1.getReg .x7 = 0x40000 := leafHashChunk1_pointer s0 p0
  have p3 : s3.getReg .x7 = 0x40014 := leafHashChunk3_pointer s2
  have values := leafHashChunk1_tag_position s0 p0
  constructor
  · have f2 := leafHashChunk2_headerFrame s1 p1 0
    have f3 := leafHashChunk3_headerFrame s2 0
    have f4 := leafHashChunk4_headerFrame s3 p3 0
    have f5 := leafHashChunk5_wordFrame s4 0x40000
    have tag := leafHashChunk0_tag s
    have joined := f5.trans (f4.trans (f3.trans (f2.trans
      (values.1.trans (congrArg (fun value : Word => value.truncate 32) tag)))))
    simpa only [leafHashReadyState, leafHash_chunks, runSchedule_append,
      s0, s1, s2, s3, s4] using joined
  · have f2 := leafHashChunk2_headerFrame s1 p1 1
    have f3 := leafHashChunk3_headerFrame s2 1
    have f4 := leafHashChunk4_headerFrame s3 p3 1
    have f5 := leafHashChunk5_wordFrame s4 0x40004
    have source := leafHashChunk0_memory s 0x43010
    have joined := f5.trans (f4.trans (f3.trans (f2.trans
      (values.2.trans (congrArg (fun value : Word => value.truncate 32) source)))))
    simpa only [leafHashReadyState, leafHash_chunks, runSchedule_append,
      s0, s1, s2, s3, s4] using joined

theorem leafHashReady_payload_byte_frame (s : MachineState) (i : Nat)
    (hi : i < 1040) :
    (leafHashReadyState s).getByte (BitVec.ofNat 64 (0x40028 + i)) =
      s.getByte (BitVec.ofNat 64 (0x40028 + i)) := by
  have aligned : alignToDword (BitVec.ofNat 64 (0x40028 + i)) =
      BitVec.ofNat 64 (0x40028 + 8 * (i / 8)) := by
    have ha : ((BitVec.ofNat 64 0x40028).toNat % 8 = 0) := by decide
    have hover : (BitVec.ofNat 64 0x40028).toNat + i < 2 ^ 64 := by
      simpa using (show 0x40028 + i < 2 ^ 64 by omega)
    simpa only [BitVec.ofNat_add] using
      (alignToDword_add_ofNat_of_aligned ha hover)
  have outside : 0x40028 ≤
      (alignToDword (BitVec.ofNat 64 (0x40028 + i))).toNat := by
    rw [aligned]
    have small : 0x40028 + 8 * (i / 8) < 2 ^ 64 := by omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    omega
  simp only [MachineState.getByte]
  rw [leafHashReady_payload_mem_frame s _ outside]

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
#print axioms leafHashReady_payload_mem_frame
#print axioms leafHashReady_payload_byte_frame
#print axioms leafHashReady_tree
#print axioms leafHashReady_index
#print axioms leafHashReady_tag_position

/-- info: 'SigGolfCandidate.SphincsVerifierWotsLeafHashReady.leafHashReady_mem_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms leafHashReady_mem_frame

end SigGolfCandidate.SphincsVerifierWotsLeafHashReady
