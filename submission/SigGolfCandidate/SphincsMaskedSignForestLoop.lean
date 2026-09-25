import SigGolfCandidate.SphincsMaskedChainDomain

/-! Exact masked signer FORS leaf suffix and reusable leaf-loop induction.
The local trace starts after the tag-8 HASH at PC 0x1e4c; it finishes
at PC 0x1d54 for another leaf, or PC 0x1fe8 after leaf 255.
The whole-loop semantic result is explicitly conditional on LeafContract.
-/

namespace SigGolfCandidate.SphincsMaskedSignForestLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsVerifierCopy SphincsVerifierCopyMemory
open SphincsMaskedChainEndpoints
open SphincsVerifierCopy20DataGeneral SphincsVerifierFtsRootCopy
open SphincsVerifierFtsCopyAccess SphincsVerifierMessageCopy SphincsVerifierFtsPriorRoots
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def payloadSchedule : List (Word × Instr) := [
  (0x1e4c, .LUI .x6 66),
  (0x1e50, .ADDI .x6 .x6 0),
  (0x1e54, .LUI .x7 69),
  (0x1e58, .ADDI .x7 .x7 (-1280)),
  (0x1e5c, .LWU .x13 .x6 0),
  (0x1e60, .SW .x7 .x13 0),
  (0x1e64, .LWU .x13 .x6 4),
  (0x1e68, .SW .x7 .x13 4),
  (0x1e6c, .LWU .x13 .x6 8),
  (0x1e70, .SW .x7 .x13 8),
  (0x1e74, .LWU .x13 .x6 12),
  (0x1e78, .SW .x7 .x13 12),
  (0x1e7c, .LWU .x13 .x6 16),
  (0x1e80, .SW .x7 .x13 16),
  (0x1e84, .LUI .x6 69),
  (0x1e88, .ADDI .x6 .x6 (-1280)),
  (0x1e8c, .LUI .x7 64),
  (0x1e90, .ADDI .x7 .x7 40),
  (0x1e94, .LWU .x13 .x6 0),
  (0x1e98, .SW .x7 .x13 0),
  (0x1e9c, .LWU .x13 .x6 4),
  (0x1ea0, .SW .x7 .x13 4),
  (0x1ea4, .LWU .x13 .x6 8),
  (0x1ea8, .SW .x7 .x13 8),
  (0x1eac, .LWU .x13 .x6 12),
  (0x1eb0, .SW .x7 .x13 12),
  (0x1eb4, .LWU .x13 .x6 16),
  (0x1eb8, .SW .x7 .x13 16)]

def payload (s : MachineState) : MachineState := runSchedule payloadSchedule s

theorem payload_code : ∀ e ∈ payloadSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem payload_checked (s : MachineState) (pc : s.pc = 0x1e4c) :
    Checked payloadSchedule s := by
  simp [payloadSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem payload_block (s : MachineState) (pc : s.pc = 0x1e4c) :
    OrdinarySteps SphincsMaskedImages.sign s 28 (payload s) :=
  checked_sound _ payloadSchedule payload_code s (payload_checked s pc)

theorem payload_pc (s : MachineState) (pc : s.pc = 0x1e4c) :
    (payload s).pc = 0x1ebc := by
  simp [payload, runSchedule, payloadSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def headerSchedule : List (Word × Instr) := [
  (0x1ebc, .LUI .x6 1),
  (0x1ec0, .ADDI .x6 .x6 (-1791)),
  (0x1ec4, .LUI .x28 67),
  (0x1ec8, .ADDI .x28 .x28 0),
  (0x1ecc, .LD .x7 .x28 0),
  (0x1ed0, .SLLI .x7 .x7 16),
  (0x1ed4, .ADD .x6 .x6 .x7),
  (0x1ed8, .LUI .x7 64),
  (0x1edc, .ADDI .x7 .x7 0),
  (0x1ee0, .SW .x7 .x6 0),
  (0x1ee4, .LUI .x28 67),
  (0x1ee8, .ADDI .x28 .x28 16),
  (0x1eec, .LD .x6 .x28 0),
  (0x1ef0, .SW .x7 .x6 4),
  (0x1ef4, .LUI .x28 67),
  (0x1ef8, .ADDI .x28 .x28 8),
  (0x1efc, .LD .x6 .x28 0),
  (0x1f00, .SD .x7 .x6 8),
  (0x1f04, .LUI .x28 67),
  (0x1f08, .ADDI .x28 .x28 24),
  (0x1f0c, .LD .x6 .x28 0),
  (0x1f10, .SW .x7 .x6 16),
  (0x1f14, .ADDI .x6 .x0 116),
  (0x1f18, .LUI .x7 64),
  (0x1f1c, .ADDI .x7 .x7 20),
  (0x1f20, .LWU .x13 .x6 0),
  (0x1f24, .SW .x7 .x13 0),
  (0x1f28, .LWU .x13 .x6 4),
  (0x1f2c, .SW .x7 .x13 4),
  (0x1f30, .LWU .x13 .x6 8),
  (0x1f34, .SW .x7 .x13 8),
  (0x1f38, .LWU .x13 .x6 12),
  (0x1f3c, .SW .x7 .x13 12),
  (0x1f40, .LWU .x13 .x6 16),
  (0x1f44, .SW .x7 .x13 16),
  (0x1f48, .LUI .x10 64),
  (0x1f4c, .ADDI .x10 .x10 0),
  (0x1f50, .ADDI .x11 .x0 480),
  (0x1f54, .LUI .x12 66),
  (0x1f58, .ADDI .x12 .x12 0),
  (0x1f5c, .ADDI .x5 .x0 1)]

def header (s : MachineState) : MachineState := runSchedule headerSchedule s

theorem header_code : ∀ e ∈ headerSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem header_checked (s : MachineState) (pc : s.pc = 0x1ebc) :
    Checked headerSchedule s := by
  simp [headerSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem header_block (s : MachineState) (pc : s.pc = 0x1ebc) :
    OrdinarySteps SphincsMaskedImages.sign s 41 (header s) :=
  checked_sound _ headerSchedule header_code s (header_checked s pc)

theorem header_pc (s : MachineState) (pc : s.pc = 0x1ebc) :
    (header s).pc = 0x1f60 := by
  simp [header, runSchedule, headerSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def storeSetupSchedule : List (Word × Instr) := [
  (0x1f64, .LUI .x6 80),
  (0x1f68, .ADDI .x6 .x6 0),
  (0x1f6c, .LUI .x28 67),
  (0x1f70, .ADDI .x28 .x28 32),
  (0x1f74, .LD .x7 .x28 0),
  (0x1f78, .SLLI .x10 .x7 2),
  (0x1f7c, .SLLI .x11 .x7 4),
  (0x1f80, .ADD .x10 .x10 .x11),
  (0x1f84, .ADD .x7 .x6 .x10),
  (0x1f88, .LUI .x6 66),
  (0x1f8c, .ADDI .x6 .x6 0)]

def storeSetup (s : MachineState) : MachineState := runSchedule storeSetupSchedule s

theorem storeSetup_code : ∀ e ∈ storeSetupSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem storeSetup_checked (s : MachineState) (pc : s.pc = 0x1f64) :
    Checked storeSetupSchedule s := by
  simp [storeSetupSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem storeSetup_block (s : MachineState) (pc : s.pc = 0x1f64) :
    OrdinarySteps SphincsMaskedImages.sign s 11 (storeSetup s) :=
  checked_sound _ storeSetupSchedule storeSetup_code s (storeSetup_checked s pc)

theorem storeSetup_pc (s : MachineState) (pc : s.pc = 0x1f64) :
    (storeSetup s).pc = 0x1f90 := by
  simp [storeSetup, runSchedule, storeSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def finishSchedule : List (Word × Instr) := [
  (0x1fb8, .LUI .x28 67),
  (0x1fbc, .ADDI .x28 .x28 32),
  (0x1fc0, .LD .x6 .x28 0),
  (0x1fc4, .ADDI .x6 .x6 1),
  (0x1fc8, .LUI .x28 67),
  (0x1fcc, .ADDI .x28 .x28 32),
  (0x1fd0, .SD .x28 .x6 0),
  (0x1fd4, .LUI .x28 67),
  (0x1fd8, .ADDI .x28 .x28 32),
  (0x1fdc, .LD .x6 .x28 0),
  (0x1fe0, .ADDI .x7 .x0 256),
  (0x1fe4, .BNE .x6 .x7 (-656))]

def finish (s : MachineState) : MachineState := runSchedule finishSchedule s

theorem finish_code : ∀ e ∈ finishSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem finish_checked (s : MachineState) (pc : s.pc = 0x1fb8) :
    Checked finishSchedule s := by
  simp [finishSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, pc]

theorem finish_block (s : MachineState) (pc : s.pc = 0x1fb8) :
    OrdinarySteps SphincsMaskedImages.sign s 12 (finish s) :=
  checked_sound _ finishSchedule finish_code s (finish_checked s pc)

theorem header_registers (s : MachineState) :
    (header s).getReg .x10 = 0x40000 ∧ (header s).getReg .x11 = 480 ∧
    (header s).getReg .x12 = 0x42000 ∧ (header s).getReg .x5 = 1 := by
  simp [header, runSchedule, headerSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def answer (hash : Hash) (s : MachineState) : MachineState :=
  writeHash (header (payload s)) (hash (hashInput (header (payload s))))

theorem answer_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x1e4c) :
    Trace hash SphincsMaskedImages.sign s 70 77 1 1 (answer hash s) := by
  obtain ⟨src,bits,dst,service⟩ := header_registers (payload s)
  have fetched : fetch SphincsMaskedImages.sign (header (payload s)) = some (.base .ECALL) := by
    rw [fetch_at, header_pc _ (payload_pc s pc)]; decide
  have valid : hashArgumentsValid (header (payload s)) = true := by
    simp [hashArgumentsValid, src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (header (payload s))).1 = 480 := by simp [hashInput,bits]
  have step := Trace.hash (hash := hash) (image := SphincsMaskedImages.sign)
    (header (payload s)) _ 0 0 0 0 fetched service valid (Trace.refl _)
  simp only [len] at step
  exact ((payload_block s pc).trace.trans (header_block _ (payload_pc s pc)).trace).trans step

theorem answer_pc (hash : Hash) (s : MachineState) (pc : s.pc = 0x1e4c) :
    (answer hash s).pc = 0x1f64 := by
  simp [answer,writeHash,header_pc _ (payload_pc s pc)]

theorem storeSetup_registers (s : MachineState) (leaf : Nat)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf) :
    (storeSetup s).getReg .x6 = 0x42000 ∧
    (storeSetup s).getReg .x7 = BitVec.ofNat 64 (0x50000 + 20 * leaf) := by
  change s.getMem 0x43020#64 = BitVec.ofNat 64 leaf at counter
  simp [storeSetup, runSchedule, storeSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,counter]
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 0x50000 + (BitVec.ofNat 64 leaf * BitVec.ofNat 64 4 +
    BitVec.ofNat 64 leaf * BitVec.ofNat 64 16) = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1; omega

theorem store_code : Copy20Code SphincsMaskedImages.sign 996 := by
  constructor <;> intro i <;> fin_cases i <;> decide

def stored (s : MachineState) := copyRootState (storeSetup s)
def nextLeaf (s : MachineState) := finish (stored s)

theorem stored_pc (s : MachineState) (pc : s.pc = 0x1f64) : (stored s).pc = 0x1fb8 := by
  simp [stored,copyRootState,copyWordState,execInstrBr,storeSetup_pc s pc]

theorem store_block (s : MachineState) (leaf : Fin 256) (pc : s.pc = 0x1f64)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) :
    OrdinarySteps SphincsMaskedImages.sign s 33 (nextLeaf s) := by
  have regs := storeSetup_registers s leaf.val counter
  have copied := copy20_block_general SphincsMaskedImages.sign 996 store_code
    (storeSetup s) 0x42000 (0x50000 + 20 * leaf.val) (storeSetup_pc s pc) regs.1 regs.2
    (by decide) (by decide) (by omega) (by dsimp [MEMORY_BYTES]; omega) (by decide)
  exact ordinary_trans _ _ _ _ 11 22 (storeSetup_block s pc)
    (ordinary_trans _ _ _ _ 10 12 copied (finish_block _ (stored_pc s pc)))

theorem stored_leaf (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) :
    (stored s).getMem 0x43020 = s.getMem 0x43020 := by
  change (copyRootState (storeSetup s)).getMem 0x43020 = _
  rw [copyRoot_mem_frame]
  · simp [storeSetup,runSchedule,storeSetupSchedule,execInstrBr]
  · intro i
    rw [(storeSetup_registers s leaf.val counter).2]
    have address : BitVec.ofNat 64 (0x50000 + 20 * leaf.val) +
        signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
          BitVec.ofNat 64 (0x50000 + 20 * leaf.val + 4 * i.val) := by
      fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [address]
    intro eq
    have bound : 0x43020 < (alignToDword
        (BitVec.ofNat 64 (0x50000 + 20 * leaf.val + 4 * i.val))).toNat := by
      have ha : (BitVec.ofNat 64 0x50000).toNat % 8 = 0 := by decide
      have hover : (BitVec.ofNat 64 0x50000).toNat + (20 * leaf.val + 4 * i.val) < 2^64 := by
        change 0x50000 + (20 * leaf.val + 4 * i.val) < 2^64; omega
      have aligned := alignToDword_add_ofNat_of_aligned ha hover
      rw [← BitVec.ofNat_add] at aligned
      rw [show 0x50000 + 20 * leaf.val + 4 * i.val = 0x50000 + (20 * leaf.val + 4 * i.val) by omega,
        aligned, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [← eq] at bound
    contradiction

theorem finish_leaf (s : MachineState) : (finish s).getMem 0x43020 = s.getMem 0x43020 + 1 := by
  simp [finish,runSchedule,finishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem finish_pc (s : MachineState) (pc : s.pc = 0x1fb8) :
    (finish s).pc = if s.getMem 0x43020 + 1 = 256 then 0x1fe8 else 0x1d54 := by
  simp [finish,runSchedule,finishSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]




theorem payload_frame (s : MachineState) (a : Word)
    (outside : a ≠ 0x44b00#64 ∧ a ≠ 0x44b08#64 ∧ a ≠ 0x44b10#64 ∧
      a ≠ 0x40028#64 ∧ a ≠ 0x40030#64 ∧ a ≠ 0x40038#64) :
    (payload s).getMem a = s.getMem a := by
  obtain ⟨a0,a1,a2,a3,a4,a5⟩ := outside
  simp [payload,runSchedule,payloadSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,a0,a1,a2,a3,a4,a5]

theorem header_frame (s : MachineState) (a : Word)
    (outside : a ≠ 0x40000#64 ∧ a ≠ 0x40008#64 ∧ a ≠ 0x40010#64 ∧
      a ≠ 0x40018#64 ∧ a ≠ 0x40020#64) :
    (header s).getMem a = s.getMem a := by
  obtain ⟨a0,a1,a2,a3,a4⟩ := outside
  simp [header,runSchedule,headerSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,a0,a1,a2,a3,a4]

theorem answer_leaf (hash : Hash) (s : MachineState) :
    (answer hash s).getMem 0x43020 = s.getMem 0x43020 := by
  have dst := (header_registers (payload s)).2.2.1
  simp [answer,writeHash,dst,MachineState.writeWords]
  exact (header_frame (payload s) 0x43020 (by decide)).trans (payload_frame s 0x43020 (by decide))


theorem payload_word (s : MachineState) (i : Fin 5) :
    (payload s).getWord32 (BitVec.ofNat 64 (0x40028 + 4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4*i.val)) := by
  fin_cases i <;>
    simp [payload,runSchedule,payloadSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,
      SphincsMaskedChainStep.extract_replace_low,
      SphincsMaskedChainStep.extract_replace_high,
      SphincsMaskedChainStep.extract_replace_low_other,
      SphincsMaskedChainStep.extract_replace_high_other]

theorem header_payload_word (s : MachineState) (i : Fin 5) :
    (header s).getWord32 (BitVec.ofNat 64 (0x40028 + 4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x40028 + 4*i.val)) := by
  fin_cases i <;>
    simp [header,runSchedule,headerSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

/-- The second HASH payload is exactly the 160-bit secret derivation answer. -/
theorem answer_payload_word (s : MachineState) (i : Fin 5) :
    (header (payload s)).getWord32 (BitVec.ofNat 64 (0x40028 + 4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4*i.val)) :=
  (header_payload_word _ i).trans (payload_word s i)

private def CopyInvariant (original : MachineState) (c : Fin 256) (count : Nat)
    (s : MachineState) : Prop :=
  s.getReg .x6 = 0x42000 ∧ s.getReg .x7 = BitVec.ofNat 64 (0x50000 + 20 * c.val) ∧
  (∀ i : Fin 5, s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
    original.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val))) ∧
  (∀ i : Fin 5, i.val < count → s.getWord32 (BitVec.ofNat 64 (0x50000 + 20 * c.val + 4 * i.val)) =
    original.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)))

private theorem copyStep (original s : MachineState) (c : Fin 256) (slot : Fin 5)
    (inv : CopyInvariant original c slot.val s) :
    CopyInvariant original c (slot.val + 1) (copyWordState slot s) := by
  obtain ⟨src, dst, source, copied⟩ := inv
  obtain ⟨srcAfter, dstAfter⟩ := copyWord_pointers slot s
  refine ⟨srcAfter.trans src, dstAfter.trans dst, ?_, ?_⟩
  · intro i
    rw [copyWord_lane_frame s (0x50000 + 20 * c.val) (0x42000 + 4 * i.val) slot dst
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact source i
  · intro i hi
    by_cases same : slot = i
    · subst i
      rw [copyWord_data_general slot s 0x42000 (0x50000 + 20 * c.val) src dst]
      exact source slot
    · have ne : slot.val ≠ i.val := fun h => same (Fin.ext h)
      rw [copyWord_lane_frame s (0x50000 + 20 * c.val) (0x50000 + 20 * c.val + 4 * i.val) slot dst
        (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact copied i (by omega)

theorem copy_data (s : MachineState) (c : Fin 256)
    (src : s.getReg .x6 = 0x42000)
    (dst : s.getReg .x7 = BitVec.ofNat 64 (0x50000 + 20 * c.val)) (i : Fin 5) :
    (copyRootState s).getWord32 (BitVec.ofNat 64 (0x50000 + 20 * c.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) := by
  have initial : CopyInvariant s c 0 s := ⟨src, dst, fun _ => rfl, by intro _ h; omega⟩
  have s0 := copyStep s s c 0 initial
  have s1 := copyStep s (copyWordState 0 s) c 1 s0
  have s2 := copyStep s (copyWordState 1 (copyWordState 0 s)) c 2 s1
  have s3 := copyStep s (copyWordState 2 (copyWordState 1 (copyWordState 0 s))) c 3 s2
  have s4 := copyStep s (copyWordState 3 (copyWordState 2 (copyWordState 1 (copyWordState 0 s)))) c 4 s3
  exact s4.2.2.2 i (by omega)


theorem storeSetup_frame (s : MachineState) (a : Word) : (storeSetup s).getMem a = s.getMem a := by
  simp [storeSetup,runSchedule,storeSetupSchedule,execInstrBr]

theorem stored_data (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) (i : Fin 5) :
    (stored s).getWord32 (BitVec.ofNat 64 (0x50000 + 20 * leaf.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) := by
  have regs := storeSetup_registers s leaf.val counter
  rw [stored,copy_data _ leaf regs.1 regs.2 i]
  simp only [MachineState.getWord32,storeSetup_frame]

theorem finish_frame (s : MachineState) (a : Word) (outside : a ≠ 0x43020#64) :
    (finish s).getMem a = s.getMem a := by
  simp [finish,runSchedule,finishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,outside]

theorem cache_cell_lower (leaf : Fin 256) (i : Fin 5) :
    0x50000 ≤ (alignToDword (BitVec.ofNat 64 (0x50000 + 20 * leaf.val + 4 * i.val))).toNat := by
  have ha : (BitVec.ofNat 64 0x50000).toNat % 8 = 0 := by decide
  have hover : (BitVec.ofNat 64 0x50000).toNat + (20 * leaf.val + 4 * i.val) < 2^64 := by
    change 0x50000 + (20 * leaf.val + 4 * i.val) < 2^64; omega
  have aligned := alignToDword_add_ofNat_of_aligned ha hover
  rw [← BitVec.ofNat_add] at aligned
  rw [show 0x50000 + 20 * leaf.val + 4 * i.val = 0x50000 + (20 * leaf.val + 4 * i.val) by omega,
    aligned, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem finish_cache_word (s : MachineState) (leaf : Fin 256) (i : Fin 5) :
    (finish s).getWord32 (BitVec.ofNat 64 (0x50000 + 20 * leaf.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x50000 + 20 * leaf.val + 4 * i.val)) := by
  simp only [MachineState.getWord32]
  rw [finish_frame]
  intro eq
  have bound := cache_cell_lower leaf i
  rw [eq] at bound
  contradiction

theorem nextLeaf_data (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) (i : Fin 5) :
    (nextLeaf s).getWord32 (BitVec.ofNat 64 (0x50000 + 20 * leaf.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) := by
  rw [nextLeaf,finish_cache_word,stored_data s leaf counter i]

theorem nextLeaf_other (s : MachineState) (leaf other : Fin 256) (ne : leaf ≠ other)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) (i : Fin 5) :
    (nextLeaf s).getWord32 (BitVec.ofNat 64 (0x50000 + 20 * other.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x50000 + 20 * other.val + 4 * i.val)) := by
  rw [nextLeaf,finish_cache_word]
  change (copyRootState (storeSetup s)).getWord32 _ = _
  rw [copyRoot_word_frame]
  · simp only [MachineState.getWord32,storeSetup_frame]
  · intro j
    have address : (storeSetup s).getReg .x7 + signExtend12 (4#12 * BitVec.ofNat 12 j.val) =
        BitVec.ofNat 64 (0x50000 + 20 * leaf.val + 4 * j.val) := by
      rw [(storeSetup_registers s leaf.val counter).2]
      fin_cases j <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [address]
    have hn : leaf.val ≠ other.val := fun h => ne (Fin.ext h)
    exact wordLaneDistinct _ _ (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Exact cost and loop control after the secret HASH. -/
theorem leaf_suffix (hash : Hash) (s : MachineState) (leaf : Fin 256)
    (pc : s.pc = 0x1e4c) (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) :
    Trace hash SphincsMaskedImages.sign s 103 110 1 1 (nextLeaf (answer hash s)) ∧
    (nextLeaf (answer hash s)).getMem 0x43020 = BitVec.ofNat 64 (leaf.val + 1) ∧
    (nextLeaf (answer hash s)).pc = if leaf.val + 1 = 256 then 0x1fe8 else 0x1d54 := by
  have acounter := (answer_leaf hash s).trans counter
  have apc := answer_pc hash s pc
  refine ⟨(answer_trace hash s pc).trans (store_block _ leaf apc acounter).trace, ?_, ?_⟩
  · rw [nextLeaf,finish_leaf,stored_leaf _ leaf acounter,acounter]
    exact (BitVec.ofNat_add _ _).symm
  · rw [nextLeaf,finish_pc _ (stored_pc _ apc),stored_leaf _ leaf acounter,acounter]
    have eq : BitVec.ofNat 64 leaf.val + 1 = (256#64) ↔ leaf.val + 1 = 256 := by
      change BitVec.ofNat 64 leaf.val + BitVec.ofNat 64 1 = BitVec.ofNat 64 256 ↔ _
      rw [← BitVec.ofNat_add]
      constructor
      · intro h;have ht := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at ht
        omega
      · intro h;rw [h]
    change (if BitVec.ofNat 64 leaf.val + 1 = (256#64) then (0x1fe8 : Word) else 0x1d54) = _
    by_cases h : leaf.val + 1 = 256
    · rw [if_pos (eq.mpr h),if_pos h]
    · rw [if_neg (fun e => h (eq.mp e)),if_neg h]


def headerWord (s : MachineState) (i : Fin 10) : BitVec 32 :=
  if i.val = 0 then (2305#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val = 1 then (s.getMem 0x43010).setWidth 32
  else if i.val = 2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val = 3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val = 4 then (s.getMem 0x43018).setWidth 32
  else s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * (i.val - 5)))

/-- Domain separator 9, the live FORS tree/index fields, and all parameter words. -/
theorem header_word (s : MachineState) (i : Fin 10) :
    (header s).getWord32 (BitVec.ofNat 64 (0x40000 + 4*i.val)) = headerWord s i := by
  fin_cases i <;>
    simp [header,runSchedule,headerSchedule,headerWord,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,
      SphincsMaskedChainStep.extract_replace_low,
      SphincsMaskedChainStep.extract_replace_high,
      SphincsMaskedChainStep.extract_replace_low_other,
      SphincsMaskedChainStep.extract_replace_high_other]

theorem answer_words (hash : Hash) (s : MachineState) (i : Fin 5) :
    (answer hash s).getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) =
      (hash (hashInput (header (payload s)))).extractLsb' (32*i.val) 32 := by
  have dst := (header_registers (payload s)).2.2.1
  fin_cases i <;>
    simp [answer,writeHash,dst,MachineState.writeWords,
      MachineState.getWord32,alignToDword,byteOffset,extractWord32]
  all_goals ext j hj; interval_cases j <;> simp

/-- The stored endpoint is the low 160 bits of the actual second oracle answer. -/
theorem leaf_suffix_value (hash : Hash) (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) :
    SphincsMaskedChainDomain.Words20 (nextLeaf (answer hash s))
      (0x50000 + 20*leaf.val)
      ((hash (hashInput (header (payload s)))).extractLsb' 0 160) := by
  intro i
  rw [nextLeaf_data _ leaf ((answer_leaf hash s).trans counter),answer_words]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

/-- Scratch-independent memory retained by the second HASH. -/
theorem answer_frame (hash : Hash) (s : MachineState) (a : Word)
    (outside : a.toNat < 0x40000 ∨
      (0x43000 ≤ a.toNat ∧ a.toNat < 0x44b00) ∨ 0x44b18 ≤ a.toNat) :
    (answer hash s).getMem a = s.getMem a := by
  have ne (b : Word) (hb : b = 0x40000#64 ∨ b = 0x40008#64 ∨ b = 0x40010#64 ∨
      b = 0x40018#64 ∨ b = 0x40020#64 ∨ b = 0x40028#64 ∨ b = 0x40030#64 ∨
      b = 0x40038#64 ∨ b = 0x42000#64 ∨ b = 0x42008#64 ∨ b = 0x42010#64 ∨
      b = 0x42018#64 ∨ b = 0x44b00#64 ∨ b = 0x44b08#64 ∨ b = 0x44b10#64) : a ≠ b := by
    intro eq;subst b
    rcases hb with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst a <;> norm_num at outside
  have dst := (header_registers (payload s)).2.2.1
  simp only [answer,writeHash,dst,MachineState.writeWords,MachineState.getMem_setPC]
  norm_num only [BitVec.reduceAdd]
  rw [MachineState.getMem_setMem_ne (ne _ (by simp)),
    MachineState.getMem_setMem_ne (ne _ (by simp)),
    MachineState.getMem_setMem_ne (ne _ (by simp)),
    MachineState.getMem_setMem_ne (ne _ (by simp))]
  exact (header_frame _ _ ⟨ne _ (by simp),ne _ (by simp),ne _ (by simp),ne _ (by simp),ne _ (by simp)⟩).trans
    (payload_frame _ _ ⟨ne _ (by simp),ne _ (by simp),ne _ (by simp),ne _ (by simp),ne _ (by simp),ne _ (by simp)⟩)

theorem stored_low_frame (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val)
    (a : Word) (low : a.toNat < 0x50000) :
    (stored s).getMem a = s.getMem a := by
  change (copyRootState (storeSetup s)).getMem a = _
  rw [copyRoot_mem_frame]
  · exact storeSetup_frame s a
  · intro i
    rw [(storeSetup_registers s leaf.val counter).2]
    have address : BitVec.ofNat 64 (0x50000 + 20*leaf.val) +
        signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
        BitVec.ofNat 64 (0x50000 + 20*leaf.val + 4*i.val) := by
      fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [address]
    intro eq
    have lower := cache_cell_lower leaf i
    rw [← eq] at lower
    omega

/-- Key/parameter/signature memory and all live FORS controls except LEAF
    survive the suffix. The leaf counter itself is advanced by leaf_suffix. -/
theorem leaf_suffix_frame (hash : Hash) (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) (a : Word)
    (retained : a.toNat < 0x40000 ∨
      (0x43000 ≤ a.toNat ∧ a.toNat < 0x44b00 ∧ a ≠ 0x43020#64)) :
    (nextLeaf (answer hash s)).getMem a = s.getMem a := by
  have ne : a ≠ 0x43020#64 := by
    rcases retained with low | high
    · intro eq;subst a;norm_num at low
    · exact high.2.2
  have low : a.toNat < 0x50000 := by rcases retained with low|high <;> omega
  rw [nextLeaf,finish_frame _ a ne,stored_low_frame _ leaf ((answer_leaf hash s).trans counter) a low]
  apply answer_frame hash s a
  rcases retained with low | high
  · exact Or.inl low
  · exact Or.inr (Or.inl ⟨high.1,high.2.1⟩)

/-- Earlier cache slots survive the entire suffix, not only the store block. -/
theorem leaf_suffix_prior (hash : Hash) (s : MachineState) (leaf prior : Fin 256)
    (different : leaf ≠ prior)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) (i : Fin 5) :
    (nextLeaf (answer hash s)).getWord32 (BitVec.ofNat 64 (0x50000+20*prior.val+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x50000+20*prior.val+4*i.val)) := by
  rw [nextLeaf_other _ leaf prior different ((answer_leaf hash s).trans counter) i]
  simp only [MachineState.getWord32]
  rw [answer_frame hash s _ (Or.inr (Or.inr (by have := cache_cell_lower prior i;omega)))]

/-- The abstract payload already derived for each leaf of one FORS tree. -/
def LeafValue (values : Fin 256 → BitVec 160) (s : MachineState) (leaf : Fin 256) : Prop :=
  SphincsMaskedChainDomain.Words20 s (0x50000 + 20*leaf.val) (values leaf)

/-- Invariant retained across all leaf iterations, including the exit state.
    `context` may retain the secret, public parameter, message index, tree
    selector, signature pointer, and any previously emitted signature bytes. -/
def LeafInvariant (context : MachineState → Prop) (values : Fin 256 → BitVec 160)
    (n : Nat) (s : MachineState) : Prop :=
  context s ∧ s.pc = (if n = 256 then 0x1fe8 else 0x1d54) ∧
  s.getMem 0x43020 = BitVec.ofNat 64 n ∧
  ∀ leaf : Fin 256, leaf.val < n → LeafValue values s leaf

/-- One reusable local proof obligation for a complete tag-8/tag-9 iteration.
    Earlier endpoints are retained as words, allowing adjacent 20-byte slots
    to share a 64-bit memory cell without a false disjoint-cell assumption. -/
def LeafContract (hash : Hash) (context : MachineState → Prop)
    (values : Fin 256 → BitVec 160) : Prop :=
  ∀ (leaf : Fin 256) (s : MachineState), context s → s.pc = 0x1d54 →
    s.getMem 0x43020 = BitVec.ofNat 64 leaf.val →
    ∃ t, Trace hash SphincsMaskedImages.sign s 183 205 2 3 t ∧
      context t ∧ t.pc = (if leaf.val+1 = 256 then 0x1fe8 else 0x1d54) ∧
      t.getMem 0x43020 = BitVec.ofNat 64 (leaf.val+1) ∧
      LeafValue values t leaf ∧
      ∀ prior : Fin 256, prior.val < leaf.val →
        LeafValue values s prior → LeafValue values t prior

/-- The induction step is independent of the concrete oracle values. -/
theorem leafInvariant_step (hash : Hash) (context : MachineState → Prop)
    (values : Fin 256 → BitVec 160) (contract : LeafContract hash context values)
    (n : Nat) (bound : n < 256) (s : MachineState)
    (inv : LeafInvariant context values n s) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 183 205 2 3 t ∧
      LeafInvariant context values (n+1) t := by
  obtain ⟨ctx,pc,counter,prior⟩ := inv
  have here : s.pc = 0x1d54 := by simpa [show n ≠ 256 by omega] using pc
  obtain ⟨t,run,nextCtx,nextPc,nextCounter,written,preserved⟩ :=
    contract ⟨n,bound⟩ s ctx here counter
  refine ⟨t,run,nextCtx,nextPc,nextCounter,?_⟩
  intro leaf hleaf
  by_cases eq : leaf.val = n
  · have e : leaf = (⟨n,bound⟩ : Fin 256) := Fin.ext eq
    simpa only [e] using written
  · exact preserved leaf (show leaf.val < n by omega) (prior leaf (by omega))

/-- Every prefix of the leaf loop has an exact, linear resource count. -/
theorem leaves_prefix (hash : Hash) (context : MachineState → Prop)
    (values : Fin 256 → BitVec 160) (contract : LeafContract hash context values)
    (s : MachineState) (initial : LeafInvariant context values 0 s) :
    ∀ n, n ≤ 256 → ∃ t,
      Trace hash SphincsMaskedImages.sign s (183*n) (205*n) (2*n) (3*n) t ∧
      LeafInvariant context values n t := by
  intro n
  induction n with
  | zero =>
    intro bound
    exact ⟨s,Trace.refl s,initial⟩
  | succ n ih =>
    intro bound
    obtain ⟨middle,run,inv⟩ := ih (by omega)
    obtain ⟨final,step,done⟩ := leafInvariant_step hash context values contract n (by omega) middle inv
    refine ⟨final,?_,done⟩
    simpa only [Nat.mul_add,Nat.mul_one] using run.trans step

/-- The whole 256-leaf loop terminates at parent-tree setup and stores every
    abstract leaf. The only hypothesis remaining is the local semantic body
    contract, not a termination or global-resource assumption. -/
theorem leaves_complete (hash : Hash) (context : MachineState → Prop)
    (values : Fin 256 → BitVec 160) (contract : LeafContract hash context values)
    (s : MachineState) (ctx : context s) (pc : s.pc = 0x1d54)
    (counter : s.getMem 0x43020 = 0) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 46848 52480 512 768 t ∧
      context t ∧ t.pc = 0x1fe8 ∧ t.getMem 0x43020 = 256 ∧
      ∀ leaf, LeafValue values t leaf := by
  have initial : LeafInvariant context values 0 s := ⟨ctx,pc,counter,by intro leaf h;omega⟩
  obtain ⟨t,run,done⟩ := leaves_prefix hash context values contract s initial 256 (by decide)
  refine ⟨t,run,done.1,?_,done.2.2.1,fun leaf => done.2.2.2 leaf leaf.isLt⟩
  simpa using done.2.1

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLoop.answer_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms answer_trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLoop.answer_payload_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms answer_payload_word

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLoop.header_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms header_word

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLoop.leaf_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_suffix

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLoop.leaf_suffix_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_suffix_value

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLoop.leaf_suffix_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_suffix_frame

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLoop.leaf_suffix_prior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_suffix_prior

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLoop.leafInvariant_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leafInvariant_step

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLoop.leaves_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaves_prefix

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLoop.leaves_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaves_complete


end SigGolfCandidate.SphincsMaskedSignForestLoop
