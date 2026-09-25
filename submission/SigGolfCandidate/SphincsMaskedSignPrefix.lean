import SigGolfCandidate.SphincsMaskedKeygenPrefix

namespace SigGolfCandidate.SphincsMaskedSignPrefix
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The signer's first HASH setup is the keygen setup shifted past its
    four-instruction entry/reject block. -/
def prefixSchedule : List (Word × Instr) :=
  SphincsMaskedKeygenPrefix.prefixSchedule.map fun entry =>
    (entry.1 + 16, entry.2)

def firstHashState (s : MachineState) : MachineState :=
  runSchedule prefixSchedule s

theorem schedule_code : ∀ entry ∈ prefixSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign entry.1 =
      some (.base entry.2) := by
  decide

theorem prefix_checked (s : MachineState) (pc : s.pc = 0x1010) :
    Checked prefixSchedule s := by
  simp [Checked, prefixSchedule, SphincsMaskedKeygenPrefix.prefixSchedule,
    execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

theorem prefix_block (s : MachineState) (pc : s.pc = 0x1010) :
    OrdinarySteps SphincsMaskedImages.sign s 71 (firstHashState s) := by
  exact checked_sound _ prefixSchedule schedule_code s (prefix_checked s pc)

theorem firstHash_pc (s : MachineState) (pc : s.pc = 0x1010) :
    (firstHashState s).pc = 0x10e4 := by
  simp [firstHashState, runSchedule, prefixSchedule,
    SphincsMaskedKeygenPrefix.prefixSchedule, execInstrBr, signExtend12,
    signExtend13, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, MachineState.setWord32,
    alignToDword, byteOffset, pc]

theorem firstHash_registers (s : MachineState) :
    (firstHashState s).getReg .x10 = 0x40000 ∧
    (firstHashState s).getReg .x11 = 576 ∧
    (firstHashState s).getReg .x12 = 0x42000 ∧
    (firstHashState s).getReg .x5 = 1 := by
  simp [firstHashState, runSchedule, prefixSchedule,
    SphincsMaskedKeygenPrefix.prefixSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32]

theorem firstHash_words (s : MachineState)
    (zero : ∀ i : Fin 3,
      s.getMem (BitVec.ofNat 64 (0x40010 + 8 * i.val)) = 0)
    (i : Fin 9) :
    (firstHashState s).getMem (BitVec.ofNat 64 (0x40000 + 8 * i.val)) =
      SphincsMaskedKeygenPrefix.inputWord s i := by
  have z0 := zero 0
  have z1 := zero 1
  have z2 := zero 2
  norm_num at z0 z1 z2
  fin_cases i <;>
    simp [firstHashState, runSchedule, prefixSchedule,
      SphincsMaskedKeygenPrefix.prefixSchedule,
      SphincsMaskedKeygenPrefix.inputWord,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      MachineState.setWord32, alignToDword, byteOffset, replaceWord32,
      z0, z1, z2]
  all_goals
    ext j hj
    interval_cases j <;> simp

open SphincsSecurity SigGolfCandidate.SphincsBridge

theorem firstHash_parameterWords (s : MachineState) (seed : MasterSeed)
    (zero : ∀ i : Fin 3,
      s.getMem (BitVec.ofNat 64 (0x40010 + 8 * i.val)) = 0)
    (key : ∀ i : Fin 4,
      s.getMem (BitVec.ofNat 64 (0x20 + 8 * i.val)) =
        seed.extractLsb' (64 * i.val) 64) (i : Fin 9) :
    (firstHashState s).getMem (BitVec.ofNat 64 (0x40000 + 8 * i.val)) =
      SphincsMaskedKeygenPrefix.parameterWord seed i := by
  rw [firstHash_words s zero i]
  unfold SphincsMaskedKeygenPrefix.inputWord
    SphincsMaskedKeygenPrefix.parameterWord
  split_ifs
  · rfl
  · rfl
  · exact key ⟨i.val - 5, by omega⟩

/-- Exact first oracle input of the active masked-cache signer. -/
theorem firstHash_input (s : MachineState) (seed : MasterSeed)
    (zero : ∀ i : Fin 3,
      s.getMem (BitVec.ofNat 64 (0x40010 + 8 * i.val)) = 0)
    (key : ∀ i : Fin 4,
      s.getMem (BitVec.ofNat 64 (0x20 + 8 * i.val)) =
        seed.extractLsb' (64 * i.val) 64) :
    hashInput (firstHashState s) =
      toQuery (keygenHashInput 0 .parameter seed) := by
  apply Serialization.hashInput_of_list (firstHashState s) 0x40000
    (SphincsMaskedKeygenPrefix.parameterPayload seed)
  · exact (firstHash_registers s).1
  · rw [SphincsMaskedKeygenPrefix.parameterPayload_length,
        (firstHash_registers s).2.1]
    rfl
  · intro i hi
    have bound : i < 72 := by
      simpa [SphincsMaskedKeygenPrefix.parameterPayload_length] using hi
    rw [SphincsVerifierFtsRootCopyBytes.getByte_word _ 0x40000 i
      (by decide) (by omega)]
    change extractByte ((firstHashState s).getMem
      (BitVec.ofNat 64 (0x40000 + 8 * (i / 8)))) (i % 8) = _
    rw [firstHash_parameterWords s seed zero key ⟨i / 8, by omega⟩]
    exact SphincsMaskedKeygenPrefix.parameterPayload_byte seed ⟨i, bound⟩

def afterHashState (hash : SigGolf.Hash) (s : MachineState)
    (seed : MasterSeed) : MachineState :=
  writeHash (firstHashState s)
    (hash (toQuery (keygenHashInput 0 .parameter seed)))

theorem firstHash_trace (hash : SigGolf.Hash) (s : MachineState)
    (seed : MasterSeed) (pc : s.pc = 0x1010)
    (zero : ∀ i : Fin 3,
      s.getMem (BitVec.ofNat 64 (0x40010 + 8 * i.val)) = 0)
    (key : ∀ i : Fin 4,
      s.getMem (BitVec.ofNat 64 (0x20 + 8 * i.val)) =
        seed.extractLsb' (64 * i.val) 64) :
    Trace hash SphincsMaskedImages.sign s 72 87 1 2
      (afterHashState hash s seed) := by
  obtain ⟨src, bits, dst, service⟩ := firstHash_registers s
  have hfetch : fetch SphincsMaskedImages.sign (firstHashState s) =
      some (.base .ECALL) := by
    rw [SphincsVerifierFtsRootCopy.fetch_at, firstHash_pc s pc]
    decide
  have valid : hashArgumentsValid (firstHashState s) = true := by
    simp [hashArgumentsValid, src, bits, dst, accessValid, rangeValid,
      MEMORY_BYTES]
  have len : (hashInput (firstHashState s)).1 = 576 := by
    simp [hashInput, bits]
  have oneStep := Trace.hash (hash := hash)
    (image := SphincsMaskedImages.sign)
    (firstHashState s) _ 0 0 0 0 hfetch service valid (Trace.refl _)
  have hashStep : Trace hash SphincsMaskedImages.sign
      (firstHashState s) 1 16 1 2 (afterHashState hash s seed) := by
    simp only [len] at oneStep
    change Trace hash SphincsMaskedImages.sign (firstHashState s)
      1 16 1 2
      (writeHash (firstHashState s)
        (hash (hashInput (firstHashState s)))) at oneStep
    rw [firstHash_input s seed zero key] at oneStep
    exact oneStep
  exact (prefix_block s pc).trace.trans hashStep

/-- info: 'SigGolfCandidate.SphincsMaskedSignPrefix.prefix_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefix_block

/-- info: 'SigGolfCandidate.SphincsMaskedSignPrefix.firstHash_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstHash_trace

end SigGolfCandidate.SphincsMaskedSignPrefix
