import SigGolfCandidate.SphincsMaskedKeygenPrefix

namespace SigGolfCandidate.SphincsMaskedMacTrace
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def prepareSchedule (p : Word) : List (Word × Instr) := [
  (p + 0x0, .ADDI .x6 .x0 (0)),
  (p + 0x4, .LUI .x28 67),
  (p + 0x8, .ADDI .x28 .x28 (0)),
  (p + 0xc, .SD .x28 .x6 (0)),
  (p + 0x10, .ADDI .x6 .x0 (0)),
  (p + 0x14, .LUI .x28 67),
  (p + 0x18, .ADDI .x28 .x28 (8)),
  (p + 0x1c, .SD .x28 .x6 (0)),
  (p + 0x20, .ADDI .x6 .x0 (0)),
  (p + 0x24, .LUI .x28 67),
  (p + 0x28, .ADDI .x28 .x28 (16)),
  (p + 0x2c, .SD .x28 .x6 (0)),
  (p + 0x30, .ADDI .x6 .x0 (0)),
  (p + 0x34, .LUI .x28 67),
  (p + 0x38, .ADDI .x28 .x28 (24)),
  (p + 0x3c, .SD .x28 .x6 (0)),
  (p + 0x40, .LUI .x6 1),
  (p + 0x44, .ADDI .x6 .x6 (-255)),
  (p + 0x48, .LUI .x28 67),
  (p + 0x4c, .ADDI .x28 .x28 (0)),
  (p + 0x50, .LD .x7 .x28 (0)),
  (p + 0x54, .SLLI .x7 .x7 (16)),
  (p + 0x58, .ADD .x6 .x6 .x7),
  (p + 0x5c, .LUI .x7 64),
  (p + 0x60, .ADDI .x7 .x7 (0)),
  (p + 0x64, .SW .x7 .x6 (0)),
  (p + 0x68, .LUI .x28 67),
  (p + 0x6c, .ADDI .x28 .x28 (16)),
  (p + 0x70, .LD .x6 .x28 (0)),
  (p + 0x74, .SW .x7 .x6 (4)),
  (p + 0x78, .LUI .x28 67),
  (p + 0x7c, .ADDI .x28 .x28 (8)),
  (p + 0x80, .LD .x6 .x28 (0)),
  (p + 0x84, .SD .x7 .x6 (8)),
  (p + 0x88, .LUI .x28 67),
  (p + 0x8c, .ADDI .x28 .x28 (24)),
  (p + 0x90, .LD .x6 .x28 (0)),
  (p + 0x94, .SW .x7 .x6 (16)),
  (p + 0x98, .ADDI .x6 .x0 (116)),
  (p + 0x9c, .LUI .x7 64),
  (p + 0xa0, .ADDI .x7 .x7 (20)),
  (p + 0xa4, .LWU .x13 .x6 (0)),
  (p + 0xa8, .SW .x7 .x13 (0)),
  (p + 0xac, .LWU .x13 .x6 (4)),
  (p + 0xb0, .SW .x7 .x13 (4)),
  (p + 0xb4, .LWU .x13 .x6 (8)),
  (p + 0xb8, .SW .x7 .x13 (8)),
  (p + 0xbc, .LWU .x13 .x6 (12)),
  (p + 0xc0, .SW .x7 .x13 (12)),
  (p + 0xc4, .LWU .x13 .x6 (16)),
  (p + 0xc8, .SW .x7 .x13 (16)),
  (p + 0xcc, .ADDI .x6 .x0 (24)),
  (p + 0xd0, .LUI .x7 133),
  (p + 0xd4, .ADDI .x7 .x7 (0)),
  (p + 0xd8, .ADDI .x10 .x0 (9)),
  (p + 0xdc, .LD .x11 .x6 (0)),
  (p + 0xe0, .SD .x7 .x11 (0)),
  (p + 0xe4, .ADDI .x6 .x6 (8)),
  (p + 0xe8, .ADDI .x7 .x7 (8)),
  (p + 0xec, .ADDI .x10 .x10 (-1)),
  (p + 0xf0, .BNE .x10 .x0 (-20)),
  (p + 0xdc, .LD .x11 .x6 (0)),
  (p + 0xe0, .SD .x7 .x11 (0)),
  (p + 0xe4, .ADDI .x6 .x6 (8)),
  (p + 0xe8, .ADDI .x7 .x7 (8)),
  (p + 0xec, .ADDI .x10 .x10 (-1)),
  (p + 0xf0, .BNE .x10 .x0 (-20)),
  (p + 0xdc, .LD .x11 .x6 (0)),
  (p + 0xe0, .SD .x7 .x11 (0)),
  (p + 0xe4, .ADDI .x6 .x6 (8)),
  (p + 0xe8, .ADDI .x7 .x7 (8)),
  (p + 0xec, .ADDI .x10 .x10 (-1)),
  (p + 0xf0, .BNE .x10 .x0 (-20)),
  (p + 0xdc, .LD .x11 .x6 (0)),
  (p + 0xe0, .SD .x7 .x11 (0)),
  (p + 0xe4, .ADDI .x6 .x6 (8)),
  (p + 0xe8, .ADDI .x7 .x7 (8)),
  (p + 0xec, .ADDI .x10 .x10 (-1)),
  (p + 0xf0, .BNE .x10 .x0 (-20)),
  (p + 0xdc, .LD .x11 .x6 (0)),
  (p + 0xe0, .SD .x7 .x11 (0)),
  (p + 0xe4, .ADDI .x6 .x6 (8)),
  (p + 0xe8, .ADDI .x7 .x7 (8)),
  (p + 0xec, .ADDI .x10 .x10 (-1)),
  (p + 0xf0, .BNE .x10 .x0 (-20)),
  (p + 0xdc, .LD .x11 .x6 (0)),
  (p + 0xe0, .SD .x7 .x11 (0)),
  (p + 0xe4, .ADDI .x6 .x6 (8)),
  (p + 0xe8, .ADDI .x7 .x7 (8)),
  (p + 0xec, .ADDI .x10 .x10 (-1)),
  (p + 0xf0, .BNE .x10 .x0 (-20)),
  (p + 0xdc, .LD .x11 .x6 (0)),
  (p + 0xe0, .SD .x7 .x11 (0)),
  (p + 0xe4, .ADDI .x6 .x6 (8)),
  (p + 0xe8, .ADDI .x7 .x7 (8)),
  (p + 0xec, .ADDI .x10 .x10 (-1)),
  (p + 0xf0, .BNE .x10 .x0 (-20)),
  (p + 0xdc, .LD .x11 .x6 (0)),
  (p + 0xe0, .SD .x7 .x11 (0)),
  (p + 0xe4, .ADDI .x6 .x6 (8)),
  (p + 0xe8, .ADDI .x7 .x7 (8)),
  (p + 0xec, .ADDI .x10 .x10 (-1)),
  (p + 0xf0, .BNE .x10 .x0 (-20)),
  (p + 0xdc, .LD .x11 .x6 (0)),
  (p + 0xe0, .SD .x7 .x11 (0)),
  (p + 0xe4, .ADDI .x6 .x6 (8)),
  (p + 0xe8, .ADDI .x7 .x7 (8)),
  (p + 0xec, .ADDI .x10 .x10 (-1)),
  (p + 0xf0, .BNE .x10 .x0 (-20)),
  (p + 0xf4, .LUI .x6 64),
  (p + 0xf8, .ADDI .x6 .x6 (0)),
  (p + 0xfc, .ADDI .x7 .x0 (24)),
  (p + 0x100, .ADDI .x10 .x0 (5)),
  (p + 0x104, .LD .x11 .x6 (0)),
  (p + 0x108, .SD .x7 .x11 (0)),
  (p + 0x10c, .ADDI .x6 .x6 (8)),
  (p + 0x110, .ADDI .x7 .x7 (8)),
  (p + 0x114, .ADDI .x10 .x10 (-1)),
  (p + 0x118, .BNE .x10 .x0 (-20)),
  (p + 0x104, .LD .x11 .x6 (0)),
  (p + 0x108, .SD .x7 .x11 (0)),
  (p + 0x10c, .ADDI .x6 .x6 (8)),
  (p + 0x110, .ADDI .x7 .x7 (8)),
  (p + 0x114, .ADDI .x10 .x10 (-1)),
  (p + 0x118, .BNE .x10 .x0 (-20)),
  (p + 0x104, .LD .x11 .x6 (0)),
  (p + 0x108, .SD .x7 .x11 (0)),
  (p + 0x10c, .ADDI .x6 .x6 (8)),
  (p + 0x110, .ADDI .x7 .x7 (8)),
  (p + 0x114, .ADDI .x10 .x10 (-1)),
  (p + 0x118, .BNE .x10 .x0 (-20)),
  (p + 0x104, .LD .x11 .x6 (0)),
  (p + 0x108, .SD .x7 .x11 (0)),
  (p + 0x10c, .ADDI .x6 .x6 (8)),
  (p + 0x110, .ADDI .x7 .x7 (8)),
  (p + 0x114, .ADDI .x10 .x10 (-1)),
  (p + 0x118, .BNE .x10 .x0 (-20)),
  (p + 0x104, .LD .x11 .x6 (0)),
  (p + 0x108, .SD .x7 .x11 (0)),
  (p + 0x10c, .ADDI .x6 .x6 (8)),
  (p + 0x110, .ADDI .x7 .x7 (8)),
  (p + 0x114, .ADDI .x10 .x10 (-1)),
  (p + 0x118, .BNE .x10 .x0 (-20)),
  (p + 0x11c, .LUI .x6 133),
  (p + 0x120, .ADDI .x6 .x6 (8)),
  (p + 0x124, .ADDI .x7 .x0 (64)),
  (p + 0x128, .ADDI .x10 .x0 (4)),
  (p + 0x12c, .LD .x11 .x6 (0)),
  (p + 0x130, .SD .x7 .x11 (0)),
  (p + 0x134, .ADDI .x6 .x6 (8)),
  (p + 0x138, .ADDI .x7 .x7 (8)),
  (p + 0x13c, .ADDI .x10 .x10 (-1)),
  (p + 0x140, .BNE .x10 .x0 (-20)),
  (p + 0x12c, .LD .x11 .x6 (0)),
  (p + 0x130, .SD .x7 .x11 (0)),
  (p + 0x134, .ADDI .x6 .x6 (8)),
  (p + 0x138, .ADDI .x7 .x7 (8)),
  (p + 0x13c, .ADDI .x10 .x10 (-1)),
  (p + 0x140, .BNE .x10 .x0 (-20)),
  (p + 0x12c, .LD .x11 .x6 (0)),
  (p + 0x130, .SD .x7 .x11 (0)),
  (p + 0x134, .ADDI .x6 .x6 (8)),
  (p + 0x138, .ADDI .x7 .x7 (8)),
  (p + 0x13c, .ADDI .x10 .x10 (-1)),
  (p + 0x140, .BNE .x10 .x0 (-20)),
  (p + 0x12c, .LD .x11 .x6 (0)),
  (p + 0x130, .SD .x7 .x11 (0)),
  (p + 0x134, .ADDI .x6 .x6 (8)),
  (p + 0x138, .ADDI .x7 .x7 (8)),
  (p + 0x13c, .ADDI .x10 .x10 (-1)),
  (p + 0x140, .BNE .x10 .x0 (-20)),
  (p + 0x144, .ADDI .x10 .x0 (24)),
  (p + 0x148, .LUI .x11 256),
  (p + 0x14c, .ADDI .x11 .x11 (416)),
  (p + 0x150, .LUI .x12 132),
  (p + 0x154, .ADDI .x12 .x12 (0)),
  (p + 0x158, .ADDI .x5 .x0 (1))]

def prepare (p : Word) (s : MachineState) := runSchedule (prepareSchedule p) s

theorem prepare_checked (p : Word) (s : MachineState) (pc : s.pc = p + 0x0) :
    Checked (prepareSchedule p) s := by
  simp [prepareSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc,BitVec.add_assoc]

theorem prepare_pc (p : Word) (s : MachineState) (pc : s.pc = p + 0x0) :
    (prepare p s).pc = p + 0x15c := by
  simp [prepare,runSchedule,prepareSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc,BitVec.add_assoc]

def restoreSchedule (p : Word) : List (Word × Instr) := [
  (p + 0x160, .LUI .x6 133),
  (p + 0x164, .ADDI .x6 .x6 (0)),
  (p + 0x168, .ADDI .x7 .x0 (24)),
  (p + 0x16c, .ADDI .x10 .x0 (9)),
  (p + 0x170, .LD .x11 .x6 (0)),
  (p + 0x174, .SD .x7 .x11 (0)),
  (p + 0x178, .ADDI .x6 .x6 (8)),
  (p + 0x17c, .ADDI .x7 .x7 (8)),
  (p + 0x180, .ADDI .x10 .x10 (-1)),
  (p + 0x184, .BNE .x10 .x0 (-20)),
  (p + 0x170, .LD .x11 .x6 (0)),
  (p + 0x174, .SD .x7 .x11 (0)),
  (p + 0x178, .ADDI .x6 .x6 (8)),
  (p + 0x17c, .ADDI .x7 .x7 (8)),
  (p + 0x180, .ADDI .x10 .x10 (-1)),
  (p + 0x184, .BNE .x10 .x0 (-20)),
  (p + 0x170, .LD .x11 .x6 (0)),
  (p + 0x174, .SD .x7 .x11 (0)),
  (p + 0x178, .ADDI .x6 .x6 (8)),
  (p + 0x17c, .ADDI .x7 .x7 (8)),
  (p + 0x180, .ADDI .x10 .x10 (-1)),
  (p + 0x184, .BNE .x10 .x0 (-20)),
  (p + 0x170, .LD .x11 .x6 (0)),
  (p + 0x174, .SD .x7 .x11 (0)),
  (p + 0x178, .ADDI .x6 .x6 (8)),
  (p + 0x17c, .ADDI .x7 .x7 (8)),
  (p + 0x180, .ADDI .x10 .x10 (-1)),
  (p + 0x184, .BNE .x10 .x0 (-20)),
  (p + 0x170, .LD .x11 .x6 (0)),
  (p + 0x174, .SD .x7 .x11 (0)),
  (p + 0x178, .ADDI .x6 .x6 (8)),
  (p + 0x17c, .ADDI .x7 .x7 (8)),
  (p + 0x180, .ADDI .x10 .x10 (-1)),
  (p + 0x184, .BNE .x10 .x0 (-20)),
  (p + 0x170, .LD .x11 .x6 (0)),
  (p + 0x174, .SD .x7 .x11 (0)),
  (p + 0x178, .ADDI .x6 .x6 (8)),
  (p + 0x17c, .ADDI .x7 .x7 (8)),
  (p + 0x180, .ADDI .x10 .x10 (-1)),
  (p + 0x184, .BNE .x10 .x0 (-20)),
  (p + 0x170, .LD .x11 .x6 (0)),
  (p + 0x174, .SD .x7 .x11 (0)),
  (p + 0x178, .ADDI .x6 .x6 (8)),
  (p + 0x17c, .ADDI .x7 .x7 (8)),
  (p + 0x180, .ADDI .x10 .x10 (-1)),
  (p + 0x184, .BNE .x10 .x0 (-20)),
  (p + 0x170, .LD .x11 .x6 (0)),
  (p + 0x174, .SD .x7 .x11 (0)),
  (p + 0x178, .ADDI .x6 .x6 (8)),
  (p + 0x17c, .ADDI .x7 .x7 (8)),
  (p + 0x180, .ADDI .x10 .x10 (-1)),
  (p + 0x184, .BNE .x10 .x0 (-20)),
  (p + 0x170, .LD .x11 .x6 (0)),
  (p + 0x174, .SD .x7 .x11 (0)),
  (p + 0x178, .ADDI .x6 .x6 (8)),
  (p + 0x17c, .ADDI .x7 .x7 (8)),
  (p + 0x180, .ADDI .x10 .x10 (-1)),
  (p + 0x184, .BNE .x10 .x0 (-20))]

def restore (p : Word) (s : MachineState) := runSchedule (restoreSchedule p) s

theorem restore_checked (p : Word) (s : MachineState) (pc : s.pc = p + 0x160) :
    Checked (restoreSchedule p) s := by
  simp [restoreSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc,BitVec.add_assoc]

theorem restore_pc (p : Word) (s : MachineState) (pc : s.pc = p + 0x160) :
    (restore p s).pc = p + 0x188 := by
  simp [restore,runSchedule,restoreSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc,BitVec.add_assoc]

structure Code (image : Image) (p : Word) : Prop where
  prepare : ∀ e ∈ prepareSchedule p, instructionAt image e.1 = some (.base e.2)
  hash : instructionAt image (p + 0x15c) = some (.base .ECALL)
  restore : ∀ e ∈ restoreSchedule p, instructionAt image e.1 = some (.base e.2)

theorem keygen_code : Code SphincsMaskedImages.keygen 0x1c48 := by
  constructor <;> decide

theorem sign_code : Code SphincsMaskedImages.sign 0x1144 := by
  constructor <;> decide

theorem prepare_registers (p : Word) (s : MachineState) :
    (prepare p s).getReg .x10 = 0x18 ∧ (prepare p s).getReg .x11 = 1048992 ∧
      (prepare p s).getReg .x12 = 0x84000 ∧ (prepare p s).getReg .x5 = 1 := by
  simp [prepare,runSchedule,prepareSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

def answer (hash : Hash) (p : Word) (s : MachineState) :=
  writeHash (prepare p s) (hash (hashInput (prepare p s)))

def result (hash : Hash) (p : Word) (s : MachineState) := restore p (answer hash p s)

theorem trace (hash : Hash) (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) :
    Trace hash image s 236 16627 1 2049 (result hash p s) ∧ (result hash p s).pc = p + 0x188 := by
  have initial : s.pc = p + 0 := by simpa using pc
  have first : OrdinarySteps image s 177 (prepare p s) :=
    checked_sound image (prepareSchedule p) code.prepare s (prepare_checked p s initial)
  obtain ⟨src,bits,dst,service⟩ := prepare_registers p s
  have fetch : fetch image (prepare p s) = some (.base .ECALL) := by
    rw [fetch_at,prepare_pc p s initial];exact code.hash
  have valid : hashArgumentsValid (prepare p s) = true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (prepare p s)).1 = 1048992 := by simp [hashInput,bits]
  have h := Trace.hash (hash := hash) (image := image) (prepare p s) _ 0 0 0 0 fetch service valid (Trace.refl _)
  have hs : Trace hash image (prepare p s) 1 16392 1 2049 (answer hash p s) := by
    simp only [len] at h;exact h
  have apc : (answer hash p s).pc = p + 0x160 := by
    simp [answer,writeHash,prepare_pc p s initial,BitVec.add_assoc]
  have last : OrdinarySteps image (answer hash p s) 58 (result hash p s) :=
    checked_sound image (restoreSchedule p) code.restore _ (restore_checked p _ apc)
  exact ⟨first.trace.trans (hs.trans last.trace),restore_pc p _ apc⟩

/-- info: 'SigGolfCandidate.SphincsMaskedMacTrace.trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trace

end SigGolfCandidate.SphincsMaskedMacTrace
