import SigGolfCandidate.SphincsMaskedChainFrame

namespace SigGolfCandidate.SphincsMaskedLeafLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedChainLoop SphincsMaskedChainFrame
open SphincsVerifierFtsRootCopy SphincsVerifierCopyMemory SphincsVerifierCopy
open SphincsVerifierMessageCopy SphincsVerifierFtsCopyAccess
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def entrySchedule : List (Word × Instr) := [
  (0x111c, .ADDI .x6 .x0 (0)),
  (0x1120, .LUI .x28 67),
  (0x1124, .ADDI .x28 .x28 (80)),
  (0x1128, .SD .x28 .x6 (0))]

def entry (s : MachineState) : MachineState := runSchedule entrySchedule s

theorem entry_code : ∀ e ∈ entrySchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem entry_checked (s : MachineState) (pc : s.pc = 0x111c) : Checked entrySchedule s := by
  simp [entrySchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc]

theorem entry_block (s : MachineState) (pc : s.pc = 0x111c) :
    OrdinarySteps SphincsMaskedImages.keygen s 4 (entry s) :=
  checked_sound _ entrySchedule entry_code s (entry_checked s pc)

theorem entry_pc (s : MachineState) (pc : s.pc = 0x111c) :
    (entry s).pc = 0x112c := by
  simp [entry, runSchedule, entrySchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc]

def copySetupSchedule : List (Word × Instr) := [
  (0x1464, .ADDI .x6 .x0 (0)),
  (0x1468, .LUI .x28 67),
  (0x146c, .ADDI .x28 .x28 (16)),
  (0x1470, .SD .x28 .x6 (0)),
  (0x1474, .LUI .x6 68),
  (0x1478, .ADDI .x6 .x6 (768)),
  (0x147c, .LUI .x7 64),
  (0x1480, .ADDI .x7 .x7 (40)),
  (0x1484, .ADDI .x10 .x0 (130))]

def copySetup (s : MachineState) : MachineState := runSchedule copySetupSchedule s

theorem copySetup_code : ∀ e ∈ copySetupSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem copySetup_checked (s : MachineState) (pc : s.pc = 0x1464) : Checked copySetupSchedule s := by
  simp [copySetupSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc]

theorem copySetup_block (s : MachineState) (pc : s.pc = 0x1464) :
    OrdinarySteps SphincsMaskedImages.keygen s 9 (copySetup s) :=
  checked_sound _ copySetupSchedule copySetup_code s (copySetup_checked s pc)

theorem copySetup_pc (s : MachineState) (pc : s.pc = 0x1464) :
    (copySetup s).pc = 0x1488 := by
  simp [copySetup, runSchedule, copySetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc]

def hashPrepareSchedule : List (Word × Instr) := [
  (0x14a0, .ADDI .x6 .x0 (513)),
  (0x14a4, .LUI .x28 67),
  (0x14a8, .ADDI .x28 .x28 (0)),
  (0x14ac, .LD .x7 .x28 (0)),
  (0x14b0, .SLLI .x7 .x7 (16)),
  (0x14b4, .ADD .x6 .x6 .x7),
  (0x14b8, .LUI .x7 64),
  (0x14bc, .ADDI .x7 .x7 (0)),
  (0x14c0, .SW .x7 .x6 (0)),
  (0x14c4, .LUI .x28 67),
  (0x14c8, .ADDI .x28 .x28 (16)),
  (0x14cc, .LD .x6 .x28 (0)),
  (0x14d0, .SW .x7 .x6 (4)),
  (0x14d4, .LUI .x28 67),
  (0x14d8, .ADDI .x28 .x28 (8)),
  (0x14dc, .LD .x6 .x28 (0)),
  (0x14e0, .SD .x7 .x6 (8)),
  (0x14e4, .LUI .x28 67),
  (0x14e8, .ADDI .x28 .x28 (24)),
  (0x14ec, .LD .x6 .x28 (0)),
  (0x14f0, .SW .x7 .x6 (16)),
  (0x14f4, .ADDI .x6 .x0 (116)),
  (0x14f8, .LUI .x7 64),
  (0x14fc, .ADDI .x7 .x7 (20)),
  (0x1500, .LWU .x13 .x6 (0)),
  (0x1504, .SW .x7 .x13 (0)),
  (0x1508, .LWU .x13 .x6 (4)),
  (0x150c, .SW .x7 .x13 (4)),
  (0x1510, .LWU .x13 .x6 (8)),
  (0x1514, .SW .x7 .x13 (8)),
  (0x1518, .LWU .x13 .x6 (12)),
  (0x151c, .SW .x7 .x13 (12)),
  (0x1520, .LWU .x13 .x6 (16)),
  (0x1524, .SW .x7 .x13 (16)),
  (0x1528, .LUI .x10 64),
  (0x152c, .ADDI .x10 .x10 (0)),
  (0x1530, .LUI .x11 2),
  (0x1534, .ADDI .x11 .x11 (448)),
  (0x1538, .LUI .x12 66),
  (0x153c, .ADDI .x12 .x12 (0)),
  (0x1540, .ADDI .x5 .x0 (1))]

def hashPrepare (s : MachineState) : MachineState := runSchedule hashPrepareSchedule s

theorem hashPrepare_code : ∀ e ∈ hashPrepareSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem hashPrepare_checked (s : MachineState) (pc : s.pc = 0x14a0) : Checked hashPrepareSchedule s := by
  simp [hashPrepareSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

theorem hashPrepare_block (s : MachineState) (pc : s.pc = 0x14a0) :
    OrdinarySteps SphincsMaskedImages.keygen s 41 (hashPrepare s) :=
  checked_sound _ hashPrepareSchedule hashPrepare_code s (hashPrepare_checked s pc)

theorem hashPrepare_pc (s : MachineState) (pc : s.pc = 0x14a0) :
    (hashPrepare s).pc = 0x1544 := by
  simp [hashPrepare, runSchedule, hashPrepareSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

def storeSetupSchedule : List (Word × Instr) := [
  (0x1548, .ADDI .x6 .x0 (136)),
  (0x154c, .LUI .x28 67),
  (0x1550, .ADDI .x28 .x28 (32)),
  (0x1554, .LD .x7 .x28 (0)),
  (0x1558, .SLLI .x10 .x7 (2)),
  (0x155c, .SLLI .x11 .x7 (4)),
  (0x1560, .ADD .x10 .x10 .x11),
  (0x1564, .ADD .x7 .x6 .x10),
  (0x1568, .LUI .x6 66),
  (0x156c, .ADDI .x6 .x6 (0))]

def storeSetup (s : MachineState) : MachineState := runSchedule storeSetupSchedule s

theorem storeSetup_code : ∀ e ∈ storeSetupSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem storeSetup_checked (s : MachineState) (pc : s.pc = 0x1548) : Checked storeSetupSchedule s := by
  simp [storeSetupSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc]

theorem storeSetup_block (s : MachineState) (pc : s.pc = 0x1548) :
    OrdinarySteps SphincsMaskedImages.keygen s 10 (storeSetup s) :=
  checked_sound _ storeSetupSchedule storeSetup_code s (storeSetup_checked s pc)

theorem storeSetup_pc (s : MachineState) (pc : s.pc = 0x1548) :
    (storeSetup s).pc = 0x1570 := by
  simp [storeSetup, runSchedule, storeSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc]

def finishSchedule : List (Word × Instr) := [
  (0x1598, .LUI .x28 67),
  (0x159c, .ADDI .x28 .x28 (32)),
  (0x15a0, .LD .x6 .x28 (0)),
  (0x15a4, .ADDI .x6 .x6 (1)),
  (0x15a8, .LUI .x28 67),
  (0x15ac, .ADDI .x28 .x28 (32)),
  (0x15b0, .SD .x28 .x6 (0)),
  (0x15b4, .LUI .x28 67),
  (0x15b8, .ADDI .x28 .x28 (32)),
  (0x15bc, .LD .x6 .x28 (0)),
  (0x15c0, .LUI .x7 1),
  (0x15c4, .ADDI .x7 .x7 (-2048)),
  (0x15c8, .BNE .x6 .x7 (-1196))]

def finish (s : MachineState) : MachineState := runSchedule finishSchedule s

theorem finish_code : ∀ e ∈ finishSchedule,
    instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem finish_checked (s : MachineState) (pc : s.pc = 0x1598) : Checked finishSchedule s := by
  simp [finishSchedule, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc]

theorem finish_block (s : MachineState) (pc : s.pc = 0x1598) :
    OrdinarySteps SphincsMaskedImages.keygen s 13 (finish s) :=
  checked_sound _ finishSchedule finish_code s (finish_checked s pc)

theorem entry_counter (s : MachineState) : (entry s).getMem 0x43050 = 0 := by
  simp [entry, runSchedule, entrySchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem entry_leaf (s : MachineState) : (entry s).getMem 0x43020 = s.getMem 0x43020 := by
  simp [entry, runSchedule, entrySchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem copySetup_leaf (s : MachineState) : (copySetup s).getMem 0x43020 = s.getMem 0x43020 := by
  simp [copySetup, runSchedule, copySetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem hashPrepare_leaf (s : MachineState) : (hashPrepare s).getMem 0x43020 = s.getMem 0x43020 := by
  simp [hashPrepare, runSchedule, hashPrepareSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset]

theorem storeSetup_leaf (s : MachineState) : (storeSetup s).getMem 0x43020 = s.getMem 0x43020 := by
  simp [storeSetup, runSchedule, storeSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem copySetup_registers (s : MachineState) :
    (copySetup s).getReg .x6 = 0x44300 ∧ (copySetup s).getReg .x7 = 0x40028 ∧
      (copySetup s).getReg .x10 = 130 := by
  simp [copySetup, runSchedule, copySetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem payload_copy_code : CopyCode SphincsMaskedImages.keygen 0x1488 := by decide

theorem payload_copy (s : MachineState) (pc : s.pc = 0x1464) :
    ∃ t, OrdinarySteps SphincsMaskedImages.keygen s 789 t ∧ t.pc = 0x14a0 ∧
      t.getMem 0x43020 = s.getMem 0x43020 ∧
      (∀ i, i < 130 → t.getMem (wordAddress 0x40028 i) = s.getMem (wordAddress 0x44300 i)) := by
  have regs := copySetup_registers s
  have inv : CopyInvariant 0x1488 0x44300 0x40028 130 130 (copySetup s) := by
    refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
    · exact copySetup_pc s pc
    · exact regs.1
    · exact regs.2.1
    · exact regs.2.2
  obtain ⟨t, trace, done, copied, frame⟩ := copy_all SphincsMaskedImages.keygen 0x1488
    payload_copy_code 0x44300 0x40028 130 (copySetup s) inv
    (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))
  refine ⟨t, ordinary_trans _ _ _ _ 9 780 (copySetup_block s pc) trace, done.2.2.1, ?_, ?_⟩
  · rw [frame, copySetup_leaf]
    intro i hi eq
    have h := congrArg BitVec.toNat eq
    change 0x43020 = (0x40028 + 8 * i) % 2 ^ 64 at h
    omega
  · intro i hi
    rw [copied i hi]
    simp [copySetup, runSchedule, copySetupSchedule, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, wordAddress]
    have ne : BitVec.ofNat 64 (0x44300 + 8 * i) ≠ 0x43010#64 := by
      intro h; have h := congrArg BitVec.toNat h
      change (0x44300 + 8 * i) % 2 ^ 64 = 0x43010 at h
      omega
    simp [ne]

theorem hashPrepare_registers (s : MachineState) :
    (hashPrepare s).getReg .x10 = 0x40000 ∧ (hashPrepare s).getReg .x11 = 8640 ∧
    (hashPrepare s).getReg .x12 = 0x42000 ∧ (hashPrepare s).getReg .x5 = 1 := by
  simp [hashPrepare, runSchedule, hashPrepareSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset]

def answerState (hash : Hash) (s : MachineState) : MachineState :=
  writeHash (hashPrepare s) (hash (hashInput (hashPrepare s)))

theorem hash_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x14a0) :
    Trace hash SphincsMaskedImages.keygen s 42 177 1 17 (answerState hash s) := by
  obtain ⟨src,bits,dst,service⟩ := hashPrepare_registers s
  have fetch : fetch SphincsMaskedImages.keygen (hashPrepare s) = some (.base .ECALL) := by
    rw [fetch_at, hashPrepare_pc s pc]; decide
  have valid : hashArgumentsValid (hashPrepare s) = true := by
    simp [hashArgumentsValid, src,bits,dst, accessValid, rangeValid, MEMORY_BYTES]
  have len : (hashInput (hashPrepare s)).1 = 8640 := by simp [hashInput,bits]
  have step := Trace.hash (hash := hash) (image := SphincsMaskedImages.keygen)
    (hashPrepare s) _ 0 0 0 0 fetch service valid (Trace.refl _)
  have hashStep : Trace hash SphincsMaskedImages.keygen (hashPrepare s) 1 136 1 17
      (answerState hash s) := by simp only [len] at step; exact step
  exact (hashPrepare_block s pc).trace.trans hashStep

theorem answer_pc (hash : Hash) (s : MachineState) (pc : s.pc = 0x14a0) :
    (answerState hash s).pc = 0x1548 := by
  simp [answerState,writeHash,hashPrepare_pc s pc]

theorem answer_leaf (hash : Hash) (s : MachineState) :
    (answerState hash s).getMem 0x43020 = s.getMem 0x43020 := by
  have dst := (hashPrepare_registers s).2.2.1
  simp [answerState,writeHash,dst,MachineState.writeWords]
  exact hashPrepare_leaf s

theorem storeSetup_registers (s : MachineState) (leaf : Nat)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf) :
    (storeSetup s).getReg .x6 = 0x42000 ∧
    (storeSetup s).getReg .x7 = BitVec.ofNat 64 (0x88 + 20 * leaf) := by
  change s.getMem 0x43020#64 = BitVec.ofNat 64 leaf at counter
  simp [storeSetup, runSchedule, storeSetupSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,counter]
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 0x88 + (BitVec.ofNat 64 leaf * BitVec.ofNat 64 4 +
    BitVec.ofNat 64 leaf * BitVec.ofNat 64 16) = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1; omega

theorem store_code : Copy20Code SphincsMaskedImages.keygen 348 := by
  constructor <;> intro i <;> fin_cases i <;> decide

def stored (s : MachineState) := copyRootState (storeSetup s)
def nextLeaf (s : MachineState) := finish (stored s)

theorem stored_pc (s : MachineState) (pc : s.pc = 0x1548) : (stored s).pc = 0x1598 := by
  simp [stored,copyRootState,copyWordState,execInstrBr,storeSetup_pc s pc]

theorem store_block (s : MachineState) (leaf : Fin 2048) (pc : s.pc = 0x1548)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) :
    OrdinarySteps SphincsMaskedImages.keygen s 33 (nextLeaf s) := by
  have regs := storeSetup_registers s leaf.val counter
  have copied := copy20_block_general SphincsMaskedImages.keygen 348 store_code
    (storeSetup s) 0x42000 (0x88 + 20 * leaf.val) (storeSetup_pc s pc) regs.1 regs.2
    (by decide) (by decide) (by omega) (by dsimp [MEMORY_BYTES]; omega) (by decide)
  exact ordinary_trans _ _ _ _ 10 23 (storeSetup_block s pc)
    (ordinary_trans _ _ _ _ 10 13 copied (finish_block _ (stored_pc s pc)))

theorem stored_leaf (s : MachineState) (leaf : Fin 2048)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) :
    (stored s).getMem 0x43020 = s.getMem 0x43020 := by
  change (copyRootState (storeSetup s)).getMem 0x43020 = _
  rw [copyRoot_mem_frame]
  · exact storeSetup_leaf s
  · intro i
    rw [(storeSetup_registers s leaf.val counter).2]
    have address : BitVec.ofNat 64 (0x88 + 20 * leaf.val) +
        signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
          BitVec.ofNat 64 (0x88 + 20 * leaf.val + 4 * i.val) := by
      fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [address]
    intro eq
    have bound : (alignToDword (BitVec.ofNat 64 (0x88 + 20 * leaf.val + 4 * i.val))).toNat < 0x40000 := by
      unfold alignToDword
      rw [BitVec.toNat_and]
      apply lt_of_le_of_lt Nat.and_le_left
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [← eq] at bound
    contradiction

theorem finish_leaf (s : MachineState) : (finish s).getMem 0x43020 = s.getMem 0x43020 + 1 := by
  simp [finish,runSchedule,finishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem finish_pc (s : MachineState) (pc : s.pc = 0x1598) :
    (finish s).pc = if s.getMem 0x43020 + 1 = 2048 then 0x15cc else 0x111c := by
  simp [finish,runSchedule,finishSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]


/-- A complete leaf iteration, from resetting the chain counter through cache storage. -/
theorem leaf_trace (hash : Hash) (s : MachineState) (leaf : Fin 2048)
    (pc : s.pc = 0x111c) (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) :
    ∃ final, Trace hash SphincsMaskedImages.keygen s 41220 44683 417 485 final ∧
      final.getMem 0x43020 = BitVec.ofNat 64 (leaf.val + 1) ∧
      final.pc = if leaf.val + 1 = 2048 then 0x15cc else 0x111c := by
  let endpoints := chains hash 52 (entry s)
  have epc := entry_pc s pc
  obtain ⟨chainTrace, _, chainPc⟩ := fifty_two_chains hash (entry s) epc (entry_counter s)
  have ecounter : endpoints.getMem 0x43020 = BitVec.ofNat 64 leaf.val := by
    exact (chains_frame hash (entry s) epc (entry_counter s) 52 (by decide)
      0x43020 (Or.inr rfl)).trans ((entry_leaf s).trans counter)
  obtain ⟨copied,copyTrace,copyPc,copyCounter,_⟩ := payload_copy endpoints chainPc
  have answerCount : (answerState hash copied).getMem 0x43020 = BitVec.ofNat 64 leaf.val :=
    (answer_leaf hash copied).trans (copyCounter.trans ecounter)
  have apc := answer_pc hash copied copyPc
  let final := nextLeaf (answerState hash copied)
  refine ⟨final, ?_, ?_, ?_⟩
  · exact (entry_block s pc).trace.trans (chainTrace.trans (copyTrace.trace.trans
      ((hash_trace hash copied copyPc).trans (store_block _ leaf apc answerCount).trace)))
  · change (finish (stored (answerState hash copied))).getMem _ = _
    rw [finish_leaf,stored_leaf _ leaf answerCount,answerCount]
    exact (BitVec.ofNat_add _ _).symm
  · change (finish (stored (answerState hash copied))).pc = _
    rw [finish_pc _ (stored_pc _ apc),stored_leaf _ leaf answerCount,answerCount]
    have next : BitVec.ofNat 64 leaf.val + 1 = BitVec.ofNat 64 (leaf.val + 1) := (BitVec.ofNat_add _ _).symm
    rw [next]
    have eq : (BitVec.ofNat 64 (leaf.val + 1) : Word) = 2048 ↔ leaf.val + 1 = 2048 := by
      constructor
      · intro h
        have hh := congrArg BitVec.toNat h
        change (leaf.val + 1) % 2 ^ 64 = 2048 at hh
        rw [Nat.mod_eq_of_lt (by omega)] at hh
        exact hh
      · intro h; rw [h]; rfl
    simp only [eq]

/-- Parametric composition of the actual leaf loop without unrolling 2,048 executions. -/
theorem leaves_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x111c)
    (counter : s.getMem 0x43020 = 0) (n : Nat) (hn : n ≤ 2048) :
    ∃ final, Trace hash SphincsMaskedImages.keygen s (41220 * n) (44683 * n)
      (417 * n) (485 * n) final ∧ final.getMem 0x43020 = BitVec.ofNat 64 n ∧
      final.pc = if n = 2048 then 0x15cc else 0x111c := by
  induction n with
  | zero => exact ⟨s, Trace.refl _,counter,pc⟩
  | succ n ih =>
    obtain ⟨mid,first,count,loc⟩ := ih (by omega)
    have npc : mid.pc = 0x111c := by rw [loc,if_neg (by omega)]
    obtain ⟨final,last,nextCount,nextPc⟩ := leaf_trace hash mid ⟨n,by omega⟩ npc count
    refine ⟨final,?_,nextCount,nextPc⟩
    simpa only [Nat.mul_succ] using first.trans last

theorem all_leaves_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x111c)
    (counter : s.getMem 0x43020 = 0) :
    ∃ final, Trace hash SphincsMaskedImages.keygen s 84418560 91510784 854016 993280 final ∧
      final.getMem 0x43020 = 2048 ∧ final.pc = 0x15cc := by
  simpa using leaves_trace hash s pc counter 2048 (by decide)

/-- info: 'SigGolfCandidate.SphincsMaskedLeafLoop.payload_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms payload_copy

/-- info: 'SigGolfCandidate.SphincsMaskedLeafLoop.leaf_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_trace

/-- info: 'SigGolfCandidate.SphincsMaskedLeafLoop.all_leaves_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms all_leaves_trace

end SigGolfCandidate.SphincsMaskedLeafLoop
