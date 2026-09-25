import SigGolfCandidate.SphincsMaskedSignRootValue

namespace SigGolfCandidate.SphincsMaskedSignForestEntry
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
open SphincsSecurity SphincsBridge SphincsVerifierFtsGenericBytes
open SphincsMaskedChainDomain
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- The fixed bridge from a successful nonce search to the first FORS leaf. -/
def entrySchedule : List (Word × Instr) := [
  (0x1cc8, .ADDI .x6 .x0 0),
  (0x1ccc, .LUI .x28 67),
  (0x1cd0, .ADDI .x28 .x28 64),
  (0x1cd4, .SD .x28 .x6 0),
  (0x1cd8, .LUI .x6 32),
  (0x1cdc, .ADDI .x6 .x6 156),
  (0x1ce0, .LUI .x28 67),
  (0x1ce4, .ADDI .x28 .x28 160),
  (0x1ce8, .SD .x28 .x6 0),
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

def entryState (s : MachineState) : MachineState := runSchedule entrySchedule s

theorem schedule_code : ∀ e ∈ entrySchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by
  decide

theorem schedule_checked (s : MachineState) (pc : s.pc = 0x1cc8) :
    Checked entrySchedule s := by
  simp [Checked, entrySchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc]

theorem entry_block (s : MachineState) (pc : s.pc = 0x1cc8) :
    OrdinarySteps SphincsMaskedImages.sign s 35 (entryState s) := by
  exact checked_sound _ entrySchedule schedule_code s (schedule_checked s pc)

theorem entry_pc (s : MachineState) (pc : s.pc = 0x1cc8) :
    (entryState s).pc = 0x1d54 := by
  simp [entryState, runSchedule, entrySchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc]

theorem entry_tree (s : MachineState) :
    (entryState s).getMem 0x43008 = s.getMem 0x43078 := by
  simp [entryState, runSchedule, entrySchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem entry_counters (s : MachineState) :
    (entryState s).getMem 0x43040 = 0 ∧
    (entryState s).getMem 0x43000 = 0 ∧
    (entryState s).getMem 0x43020 = 0 ∧
    (entryState s).getMem 0x430a0 = 0x2009c := by
  simp [entryState, runSchedule, entrySchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem entry_leafByte (s : MachineState) :
    (entryState s).getByte 0x44800 = s.getByte 0x44800 := by
  simp [MachineState.getByte, entryState, runSchedule, entrySchedule,
    execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, alignToDword, byteOffset]

theorem entry_selected (s : MachineState) :
    (entryState s).getMem 0x430a8 =
      (s.getByte 0x44800).zeroExtend 64 := by
  simp [entryState, runSchedule, entrySchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, MachineState.getByte,
    alignToDword, byteOffset]

/-- Initialize the first FORS leaf and the four-word secret-key copy. -/
def leafSetupSchedule : List (Word × Instr) := [
  (0x1d54, .ADDI .x6 .x0 0),
  (0x1d58, .LUI .x28 67),
  (0x1d5c, .ADDI .x28 .x28 16),
  (0x1d60, .SD .x28 .x6 0),
  (0x1d64, .LUI .x28 67),
  (0x1d68, .ADDI .x28 .x28 32),
  (0x1d6c, .LD .x6 .x28 0),
  (0x1d70, .LUI .x28 67),
  (0x1d74, .ADDI .x28 .x28 24),
  (0x1d78, .SD .x28 .x6 0),
  (0x1d7c, .ADDI .x6 .x0 32),
  (0x1d80, .LUI .x7 64),
  (0x1d84, .ADDI .x7 .x7 40),
  (0x1d88, .ADDI .x10 .x0 4)]

def leafSetup (s : MachineState) : MachineState :=
  runSchedule leafSetupSchedule s

theorem leafSetup_code : ∀ e ∈ leafSetupSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by
  decide

theorem leafSetup_checked (s : MachineState) (pc : s.pc = 0x1d54) :
    Checked leafSetupSchedule s := by
  simp [Checked, leafSetupSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc]

theorem leafSetup_block (s : MachineState) (pc : s.pc = 0x1d54) :
    OrdinarySteps SphincsMaskedImages.sign s 14 (leafSetup s) := by
  exact checked_sound _ leafSetupSchedule leafSetup_code s
    (leafSetup_checked s pc)

theorem leafSetup_copyInvariant (s : MachineState)
    (pc : s.pc = 0x1d54) :
    CopyInvariant 0x1d8c 0x20 0x40028 4 4 (leafSetup s) := by
  simp [CopyInvariant, leafSetup, runSchedule, leafSetupSchedule,
    execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc]

theorem leafSetup_secretWord (s : MachineState) (i : Fin 4) :
    (leafSetup s).getMem (wordAddress 0x20 i.val) =
      s.getMem (wordAddress 0x20 i.val) := by
  fin_cases i <;>
    simp [leafSetup, runSchedule, leafSetupSchedule, wordAddress,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

theorem leafCopy_code : CopyCode SphincsMaskedImages.sign 0x1d8c := by
  decide

theorem leafSecretCopy (s : MachineState) (pc : s.pc = 0x1d54) :
    ∃ final, OrdinarySteps SphincsMaskedImages.sign s 38 final ∧
      final.pc = 0x1da4 ∧
      (∀ i, i < 4 → final.getMem (wordAddress 0x40028 i) =
        s.getMem (wordAddress 0x20 i)) := by
  let prepared := leafSetup s
  have first := leafSetup_block s pc
  obtain ⟨final, copied, done, data, _⟩ :=
    copy_all SphincsMaskedImages.sign 0x1d8c leafCopy_code
      0x20 0x40028 4 prepared
      (leafSetup_copyInvariant s pc)
      (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide))
  refine ⟨final, ?_, ?_, ?_⟩
  · simpa using ordinary_trans _ s prepared final 14 24 first copied
  · simpa [CopyInvariant] using done.2.2.1
  · intro i hi
    rw [data i hi, leafSetup_secretWord s ⟨i, hi⟩]

/-- Prepare the 72-byte FORS secret derivation query. -/
def leafHashSchedule : List (Word × Instr) := [
  (0x1da4, .LUI .x6 1),
  (0x1da8, .ADDI .x6 .x6 (-2047)),
  (0x1dac, .LUI .x28 67),
  (0x1db0, .ADDI .x28 .x28 0),
  (0x1db4, .LD .x7 .x28 0),
  (0x1db8, .SLLI .x7 .x7 16),
  (0x1dbc, .ADD .x6 .x6 .x7),
  (0x1dc0, .LUI .x7 64),
  (0x1dc4, .ADDI .x7 .x7 0),
  (0x1dc8, .SW .x7 .x6 0),
  (0x1dcc, .LUI .x28 67),
  (0x1dd0, .ADDI .x28 .x28 16),
  (0x1dd4, .LD .x6 .x28 0),
  (0x1dd8, .SW .x7 .x6 4),
  (0x1ddc, .LUI .x28 67),
  (0x1de0, .ADDI .x28 .x28 8),
  (0x1de4, .LD .x6 .x28 0),
  (0x1de8, .SD .x7 .x6 8),
  (0x1dec, .LUI .x28 67),
  (0x1df0, .ADDI .x28 .x28 24),
  (0x1df4, .LD .x6 .x28 0),
  (0x1df8, .SW .x7 .x6 16),
  (0x1dfc, .ADDI .x6 .x0 116),
  (0x1e00, .LUI .x7 64),
  (0x1e04, .ADDI .x7 .x7 20),
  (0x1e08, .LWU .x13 .x6 0),
  (0x1e0c, .SW .x7 .x13 0),
  (0x1e10, .LWU .x13 .x6 4),
  (0x1e14, .SW .x7 .x13 4),
  (0x1e18, .LWU .x13 .x6 8),
  (0x1e1c, .SW .x7 .x13 8),
  (0x1e20, .LWU .x13 .x6 12),
  (0x1e24, .SW .x7 .x13 12),
  (0x1e28, .LWU .x13 .x6 16),
  (0x1e2c, .SW .x7 .x13 16),
  (0x1e30, .LUI .x10 64),
  (0x1e34, .ADDI .x10 .x10 0),
  (0x1e38, .ADDI .x11 .x0 576),
  (0x1e3c, .LUI .x12 66),
  (0x1e40, .ADDI .x12 .x12 0),
  (0x1e44, .ADDI .x5 .x0 1)]

def leafHashReady (s : MachineState) : MachineState :=
  runSchedule leafHashSchedule s

theorem leafHash_code : ∀ e ∈ leafHashSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by
  decide

theorem leafHash_checked (s : MachineState) (pc : s.pc = 0x1da4) :
    Checked leafHashSchedule s := by
  simp [Checked, leafHashSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, MachineState.setWord32,
    MachineState.getWord32, alignToDword, byteOffset, pc]

theorem leafHash_block (s : MachineState) (pc : s.pc = 0x1da4) :
    OrdinarySteps SphincsMaskedImages.sign s 41 (leafHashReady s) := by
  exact checked_sound _ leafHashSchedule leafHash_code s
    (leafHash_checked s pc)

theorem leafHash_pc (s : MachineState) (pc : s.pc = 0x1da4) :
    (leafHashReady s).pc = 0x1e48 := by
  simp [leafHashReady, runSchedule, leafHashSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc]

theorem leafHash_registers (s : MachineState) :
    (leafHashReady s).getReg .x10 = 0x40000 ∧
    (leafHashReady s).getReg .x11 = 576 ∧
    (leafHashReady s).getReg .x12 = 0x42000 ∧
    (leafHashReady s).getReg .x5 = 1 := by
  simp [leafHashReady, runSchedule, leafHashSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

def leafHeaderWord (s : MachineState) (i : Fin 10) : BitVec 32 :=
  if i.val = 0 then (2049#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val = 1 then (s.getMem 0x43010).setWidth 32
  else if i.val = 2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val = 3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val = 4 then (s.getMem 0x43018).setWidth 32
  else s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * (i.val - 5)))

theorem leafHash_headerWord (s : MachineState) (i : Fin 10) :
    (leafHashReady s).getWord32
      (BitVec.ofNat 64 (0x40000 + 4 * i.val)) = leafHeaderWord s i := by
  fin_cases i <;>
    simp [leafHashReady, runSchedule, leafHashSchedule, leafHeaderWord,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, MachineState.setWord32,
      MachineState.getWord32, alignToDword, byteOffset,
      SphincsMaskedChainStep.extract_replace_low,
      SphincsMaskedChainStep.extract_replace_high,
      SphincsMaskedChainStep.extract_replace_low_other,
      SphincsMaskedChainStep.extract_replace_high_other]

theorem leafHash_seedWord (s : MachineState) (i : Fin 4) :
    (leafHashReady s).getMem (wordAddress 0x40028 i.val) =
      s.getMem (wordAddress 0x40028 i.val) := by
  fin_cases i <;>
    simp [leafHashReady, runSchedule, leafHashSchedule, wordAddress,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, MachineState.setWord32,
      MachineState.getWord32, alignToDword, byteOffset]

theorem leafHash_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1da4) :
    Trace hash SphincsMaskedImages.sign s 42 57 1 2
      (writeHash (leafHashReady s) (hash (hashInput (leafHashReady s)))) := by
  obtain ⟨src, bits, dst, service⟩ := leafHash_registers s
  have hfetch : fetch SphincsMaskedImages.sign (leafHashReady s) =
      some (.base .ECALL) := by
    rw [fetch_at, leafHash_pc s pc]
    decide
  have valid : hashArgumentsValid (leafHashReady s) = true := by
    simp [hashArgumentsValid, src, bits, dst, accessValid, rangeValid,
      MEMORY_BYTES]
  have len : (hashInput (leafHashReady s)).1 = 576 := by
    simp [hashInput, bits]
  have step := Trace.hash (hash := hash)
    (image := SphincsMaskedImages.sign)
    (leafHashReady s) _ 0 0 0 0 hfetch service valid (Trace.refl _)
  simp only [len] at step
  exact (leafHash_block s pc).trace.trans step

/-- The first FORS secret derivation reaches a valid HASH with a 72-byte input. -/
theorem firstForestHash (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1cc8) :
    ∃ final, Trace hash SphincsMaskedImages.sign s 115 130 1 2 final := by
  let entered := entryState s
  obtain ⟨copied, copyTrace, copiedPC, _⟩ :=
    leafSecretCopy entered (entry_pc s pc)
  let final := writeHash (leafHashReady copied)
    (hash (hashInput (leafHashReady copied)))
  refine ⟨final, ?_⟩
  have first := (entry_block s pc).trace (hash := hash)
  have middle := copyTrace.trace (hash := hash)
  have last := leafHash_trace hash copied copiedPC
  simpa [final, Execution.charge] using (first.trans middle).trans last

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.entry_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_block

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.entry_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_tree

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.entry_counters' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_counters

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.entry_leafByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_leafByte

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.entry_selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_selected

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.leafSecretCopy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leafSecretCopy

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.leafHash_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leafHash_block

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.leafHash_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leafHash_trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.leafHash_headerWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leafHash_headerWord

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.leafHash_seedWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leafHash_seedWord

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestEntry.firstForestHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstForestHash

end SigGolfCandidate.SphincsMaskedSignForestEntry
