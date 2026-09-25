import SigGolfCandidate.SphincsMaskedSignRootDecrypt
import SigGolfCandidate.SphincsMaskedMaskSemantics

namespace SigGolfCandidate.SphincsMaskedSignRootValue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
open SphincsMaskedSignRootPad SphincsMaskedSignRootPadDomain
open SphincsMaskedSignRootDecrypt
open SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsSecurity SphincsMaskedMaskSemantics
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Selecting the pad's top-tree address leaves the masked root untouched. -/
theorem init_root_word (s : MachineState) (i : Fin 5) :
    (init s).getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) := by
  fin_cases i <;>
    simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,
      MachineState.getWord32,alignToDword,byteOffset]

/-- The root-pad query preparation does not modify the masked root in the cache. -/
theorem padPrepare_root_word (s : MachineState) (i : Fin 5) :
    (padPrepare s).getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) := by
  fin_cases i <;>
    simp [padPrepare,runSchedule,padSchedule,
      SphincsMaskedMaskCode.prepareSchedule,execInstrBr,signExtend12,
      signExtend13,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,MachineState.setWord32,
      MachineState.getWord32,alignToDword,byteOffset]

theorem padAnswer_root_word (hash : Hash) (s : MachineState) (i : Fin 5) :
    (padAnswer hash s).getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) := by
  have dst := (pad_registers s).2.2.1
  have frame := padPrepare_root_word s i
  fin_cases i <;>
    simpa [padAnswer,writeHash,dst,MachineState.writeWords,
      MachineState.getWord32,alignToDword,byteOffset] using frame

theorem root_pad_masked_word (hash : Hash) (s : MachineState) (i : Fin 5) :
    (padAnswer hash (init s)).getWord32
      (BitVec.ofNat 64 (0x60 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) := by
  rw [padAnswer_root_word,init_root_word]

/-- Honest root ciphertext decrypts back to the keygen top-tree root. -/
theorem decrypted_root_words (hash : Hash) (s : MachineState)
    (parameter : BitVec 160) (seed : MasterSeed) (root : Digest)
    (par : Words20 s 0x74 parameter) (key : Words32 s seed)
    (masked : Words20 s 0x60
      (root ^^^ padValue hash parameter seed 4094)) (i : Fin 5) :
    (decrypted (padAnswer hash (init s))).getWord32
      (BitVec.ofNat 64 (0x53020 + 4 * i.val)) =
      root.extractLsb' (32 * i.val) 32 := by
  rw [decrypted_words,root_pad_masked_word,masked i,
    pad_answer_words32 hash s parameter seed par key i]
  have padEq :
      (padValue hash parameter seed 4094).extractLsb' (32 * i.val) 32 =
      (hash (SphincsBridge.toQuery
        (SphincsCacheSecretDomains.padInput parameter seed 4094))).extractLsb'
          (32 * i.val) 32 := by
    unfold padValue truncateHash
    exact BitVec.extractLsb'_extractLsb'_of_le (by simp [digestBits]; omega)
  rw [BitVec.extractLsb'_xor, padEq]
  simp only [BitVec.xor_assoc,BitVec.xor_self,BitVec.xor_zero]

/-- Copy the decrypted top root and public parameter to the compact signature. -/
def signaturePrefixSchedule : List (Word × Instr) := [
  (0x14a4, .LUI .x6 83),
  (0x14a8, .ADDI .x6 .x6 32),
  (0x14ac, .LUI .x7 32),
  (0x14b0, .ADDI .x7 .x7 96),
  (0x14b4, .LWU .x13 .x6 0),
  (0x14b8, .SW .x7 .x13 0),
  (0x14bc, .LWU .x13 .x6 4),
  (0x14c0, .SW .x7 .x13 4),
  (0x14c4, .LWU .x13 .x6 8),
  (0x14c8, .SW .x7 .x13 8),
  (0x14cc, .LWU .x13 .x6 12),
  (0x14d0, .SW .x7 .x13 12),
  (0x14d4, .LWU .x13 .x6 16),
  (0x14d8, .SW .x7 .x13 16),
  (0x14dc, .ADDI .x6 .x0 116),
  (0x14e0, .LUI .x7 32),
  (0x14e4, .ADDI .x7 .x7 116),
  (0x14e8, .LWU .x13 .x6 0),
  (0x14ec, .SW .x7 .x13 0),
  (0x14f0, .LWU .x13 .x6 4),
  (0x14f4, .SW .x7 .x13 4),
  (0x14f8, .LWU .x13 .x6 8),
  (0x14fc, .SW .x7 .x13 8),
  (0x1500, .LWU .x13 .x6 12),
  (0x1504, .SW .x7 .x13 12),
  (0x1508, .LWU .x13 .x6 16),
  (0x150c, .SW .x7 .x13 16)]

def signaturePrefix (s : MachineState) : MachineState :=
  runSchedule signaturePrefixSchedule s

theorem signaturePrefix_code : ∀ e ∈ signaturePrefixSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 =
      some (.base e.2) := by decide

theorem signaturePrefix_checked (s : MachineState) (pc : s.pc = 0x14a4) :
    Checked signaturePrefixSchedule s := by
  simp [Checked,signaturePrefixSchedule,execInstrBr,ordinaryStep,
    memoryArgumentsValid,accessValid,rangeValid,MEMORY_BYTES,
    signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.setWord32,
    MachineState.getWord32,alignToDword,byteOffset,pc]

theorem signaturePrefix_trace (s : MachineState) (pc : s.pc = 0x14a4) :
    OrdinarySteps SphincsMaskedImages.sign s 27 (signaturePrefix s) :=
  checked_sound _ signaturePrefixSchedule
    signaturePrefix_code s (signaturePrefix_checked s pc)

theorem signaturePrefix_pc (s : MachineState) (pc : s.pc = 0x14a4) :
    (signaturePrefix s).pc = 0x1510 := by
  simp [signaturePrefix,runSchedule,signaturePrefixSchedule,
    execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.setWord32,
    MachineState.getWord32,alignToDword,byteOffset,pc]

theorem signaturePrefix_root_word (s : MachineState) (i : Fin 5) :
    (signaturePrefix s).getWord32
      (BitVec.ofNat 64 (0x20060 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x53020 + 4 * i.val)) := by
  fin_cases i <;>
    simp [signaturePrefix,runSchedule,signaturePrefixSchedule,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,MachineState.setWord32,
      MachineState.getWord32,alignToDword,byteOffset]

theorem signaturePrefix_parameter_word (s : MachineState) (i : Fin 5) :
    (signaturePrefix s).getWord32
      (BitVec.ofNat 64 (0x20074 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val)) := by
  fin_cases i <;>
    simp [signaturePrefix,runSchedule,signaturePrefixSchedule,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,MachineState.setWord32,
      MachineState.getWord32,alignToDword,byteOffset]

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootValue.decrypted_root_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypted_root_words

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootValue.root_pad_masked_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms root_pad_masked_word

end SigGolfCandidate.SphincsMaskedSignRootValue
