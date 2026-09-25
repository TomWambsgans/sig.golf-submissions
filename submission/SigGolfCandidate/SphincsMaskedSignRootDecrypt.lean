import SigGolfCandidate.SphincsMaskedSignRootPadDomain
import SigGolfCandidate.SphincsVerifierCopyMemory

namespace SigGolfCandidate.SphincsMaskedSignRootDecrypt
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy SphincsVerifierCopyMemory
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Load masked root and pad, then XOR five 32-bit lanes into scratch. -/
def decryptSchedule : List (Word × Instr) := [
  (0x1440, .ADDI .x6 .x0 96),
  (0x1444, .LUI .x7 83),
  (0x1448, .ADDI .x7 .x7 32),
  (0x144c, .LUI .x12 66),
  (0x1450, .ADDI .x12 .x12 0),
  (0x1454, .LWU .x13 .x6 0),
  (0x1458, .LWU .x14 .x12 0),
  (0x145c, .XOR .x15 .x13 .x14),
  (0x1460, .SW .x7 .x15 0),
  (0x1464, .LWU .x13 .x6 4),
  (0x1468, .LWU .x14 .x12 4),
  (0x146c, .XOR .x15 .x13 .x14),
  (0x1470, .SW .x7 .x15 4),
  (0x1474, .LWU .x13 .x6 8),
  (0x1478, .LWU .x14 .x12 8),
  (0x147c, .XOR .x15 .x13 .x14),
  (0x1480, .SW .x7 .x15 8),
  (0x1484, .LWU .x13 .x6 12),
  (0x1488, .LWU .x14 .x12 12),
  (0x148c, .XOR .x15 .x13 .x14),
  (0x1490, .SW .x7 .x15 12),
  (0x1494, .LWU .x13 .x6 16),
  (0x1498, .LWU .x14 .x12 16),
  (0x149c, .XOR .x15 .x13 .x14),
  (0x14a0, .SW .x7 .x15 16)]

def decrypted (s : MachineState) : MachineState := runSchedule decryptSchedule s

theorem schedule_code : ∀ e ∈ decryptSchedule,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide

theorem schedule_checked (s : MachineState) (pc : s.pc = 0x1440) :
    Checked decryptSchedule s := by
  simp [Checked,decryptSchedule,execInstrBr,ordinaryStep,
    memoryArgumentsValid,accessValid,rangeValid,MEMORY_BYTES,
    signExtend12,signExtend13,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.setWord32,
    MachineState.getWord32,alignToDword,byteOffset,pc]

theorem decrypt_block (s : MachineState) (pc : s.pc = 0x1440) :
    OrdinarySteps SphincsMaskedImages.sign s 25 (decrypted s) :=
  checked_sound _ decryptSchedule schedule_code s (schedule_checked s pc)

theorem decrypt_pc (s : MachineState) (pc : s.pc = 0x1440) :
    (decrypted s).pc = 0x14a4 := by
  simp [decrypted,runSchedule,decryptSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,
    byteOffset,pc]

/-- Each scratch word is ciphertext XOR the root pad. -/
theorem decrypted_words (s : MachineState) (i : Fin 5) :
    (decrypted s).getWord32 (BitVec.ofNat 64 (0x53020 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) ^^^
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) := by
  fin_cases i <;>
    simp [decrypted,runSchedule,decryptSchedule,execInstrBr,
      signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,MachineState.setWord32,
      MachineState.getWord32,alignToDword,byteOffset,
      getWord32_setWord32_same]

/-- The accepting signer reaches the decrypted-root scratch after one pad HASH. -/
theorem root_unmask_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x132c) :
    Trace hash SphincsMaskedImages.sign s 112 127 1 2
      (decrypted (SphincsMaskedSignRootPad.padAnswer hash
        (SphincsMaskedSignRootPad.init s))) := by
  have first := SphincsMaskedSignRootPad.init_pad_trace hash s pc
  have nextpc : (SphincsMaskedSignRootPad.padAnswer hash
      (SphincsMaskedSignRootPad.init s)).pc = 0x1440 := by
    simp [SphincsMaskedSignRootPad.padAnswer,writeHash,
      SphincsMaskedSignRootPad.pad_pc,
      SphincsMaskedSignRootPad.init_pc s pc]
  exact first.trans (decrypt_block _ nextpc).trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootDecrypt.root_unmask_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms root_unmask_trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootDecrypt.decrypted_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypted_words

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootDecrypt.decrypt_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypt_block

end SigGolfCandidate.SphincsMaskedSignRootDecrypt
