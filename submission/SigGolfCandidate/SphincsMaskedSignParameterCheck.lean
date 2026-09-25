import SigGolfCandidate.SphincsMaskedSignPrefix
import SigGolfCandidate.SphincsMaskedMacTrace

namespace SigGolfCandidate.SphincsMaskedSignParameterCheck
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The successful answer/cache-parameter comparison immediately after the
    signer's first HASH. The rejection jumps are skipped. -/
def compareSchedule : List (Word × Instr) := [
  (0x10e8, .LUI .x6 66),
  (0x10ec, .ADDI .x6 .x6 0),
  (0x10f0, .ADDI .x7 .x0 116),
  (0x10f4, .LWU .x10 .x6 0),
  (0x10f8, .LWU .x11 .x7 0),
  (0x10fc, .BEQ .x10 .x11 8),
  (0x1104, .LWU .x10 .x6 4),
  (0x1108, .LWU .x11 .x7 4),
  (0x110c, .BEQ .x10 .x11 8),
  (0x1114, .LWU .x10 .x6 8),
  (0x1118, .LWU .x11 .x7 8),
  (0x111c, .BEQ .x10 .x11 8),
  (0x1124, .LWU .x10 .x6 12),
  (0x1128, .LWU .x11 .x7 12),
  (0x112c, .BEQ .x10 .x11 8),
  (0x1134, .LWU .x10 .x6 16),
  (0x1138, .LWU .x11 .x7 16),
  (0x113c, .BEQ .x10 .x11 8)]

def afterComparison (s : MachineState) : MachineState :=
  runSchedule compareSchedule s

theorem schedule_code : ∀ entry ∈ compareSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign entry.1 =
      some (.base entry.2) := by
  decide

theorem comparison_checked (s : MachineState) (pc : s.pc = 0x10e8)
    (equal : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val))) :
    Checked compareSchedule s := by
  have h0 := equal 0
  have h1 := equal 1
  have h2 := equal 2
  have h3 := equal 3
  have h4 := equal 4
  norm_num at h0 h1 h2 h3 h4
  simp [Checked, compareSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, signExtend13, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc, h0, h1, h2, h3, h4]

theorem comparison_trace (s : MachineState) (pc : s.pc = 0x10e8)
    (equal : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val))) :
    OrdinarySteps SphincsMaskedImages.sign s 18 (afterComparison s) := by
  exact checked_sound _ compareSchedule schedule_code s
    (comparison_checked s pc equal)

theorem comparison_pc (s : MachineState) (pc : s.pc = 0x10e8)
    (equal : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val))) :
    (afterComparison s).pc = 0x1144 := by
  have h0 := equal 0
  have h1 := equal 1
  have h2 := equal 2
  have h3 := equal 3
  have h4 := equal 4
  norm_num at h0 h1 h2 h3 h4
  simp [afterComparison, runSchedule, compareSchedule, execInstrBr,
    signExtend12, signExtend13, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc, h0, h1, h2, h3, h4]


theorem comparison_mem (s : MachineState) (address : Word) :
    (afterComparison s).getMem address = s.getMem address := by
  simp [afterComparison, runSchedule, compareSchedule, execInstrBr]

/-- The parameter check has no HASH service and costs only its 18 ordinary
    instructions on the success path. -/
theorem comparison_trace_hash (hash : SigGolf.Hash) (s : MachineState)
    (pc : s.pc = 0x10e8)
    (equal : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val))) :
    Trace hash SphincsMaskedImages.sign s 18 18 0 0
      (afterComparison s) :=
  (comparison_trace s pc equal).trace

/-- The parameter HASH answer is the five low 32-bit lanes of the oracle
    output used by the abstract key derivation. -/
theorem afterHash_words32 (hash : SigGolf.Hash) (s : MachineState)
    (seed : SphincsSecurity.MasterSeed) (i : Fin 5) :
    (SphincsMaskedSignPrefix.afterHashState hash s seed).getWord32
      (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
      (hash (SphincsBridge.toQuery
        (SphincsSecurity.keygenHashInput 0 .parameter seed))).extractLsb'
          (32 * i.val) 32 := by
  have dst := (SphincsMaskedSignPrefix.firstHash_registers s).2.2.1
  fin_cases i <;>
    simp [SphincsMaskedSignPrefix.afterHashState, writeHash, dst,
      MachineState.writeWords, MachineState.getWord32,
      alignToDword, byteOffset, extractWord32]
  all_goals ext j hj; interval_cases j <;> simp

/-- Conditional exact trace of loader, parameter HASH, and successful cache
    parameter check. A later keygen/sign refinement supplies the equality. -/
theorem loaded_comparison_trace (hash : SigGolf.Hash)
    (secretKey : SigGolf.SecretKey) (cache : SigGolf.Cache)
    (message : SigGolf.Message)
    (equal : ∀ i : Fin 5,
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val))) :
    Trace hash SphincsMaskedImages.sign
      (SphincsMaskedSignPrefix.entryState secretKey cache message)
      91 106 1 2
      (afterComparison
        (SphincsMaskedSignPrefix.afterHashState hash
          (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
          secretKey)) := by
  let s := SphincsMaskedSignPrefix.afterHashState hash
    (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
    secretKey
  have first := SphincsMaskedSignPrefix.loaded_firstHash_trace hash secretKey cache message
  have pc : s.pc = 0x10e8 := by
    simp [s, SphincsMaskedSignPrefix.afterHashState,
      writeHash, SphincsMaskedSignPrefix.firstHash_pc,
      SphincsMaskedSignPrefix.afterJump_pc]
  exact first.trans (comparison_trace_hash hash s pc equal)

/-- Conditional exact signer prefix through the authenticated-cache HASH. -/
theorem loaded_mac_trace (hash : SigGolf.Hash)
    (secretKey : SigGolf.SecretKey) (cache : SigGolf.Cache)
    (message : SigGolf.Message)
    (equal : ∀ i : Fin 5,
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val))) :
    Trace hash SphincsMaskedImages.sign
      (SphincsMaskedSignPrefix.entryState secretKey cache message)
      327 16733 2 2051
      (SphincsMaskedMacTrace.result hash 0x1144
        (afterComparison
          (SphincsMaskedSignPrefix.afterHashState hash
            (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
            secretKey))) := by
  let s := SphincsMaskedSignPrefix.afterHashState hash
    (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
    secretKey
  have first := loaded_comparison_trace hash secretKey cache message equal
  have spc : s.pc = 0x10e8 := by
    simp [s, SphincsMaskedSignPrefix.afterHashState,
      writeHash, SphincsMaskedSignPrefix.firstHash_pc,
      SphincsMaskedSignPrefix.afterJump_pc]
  have pc : (afterComparison s).pc = 0x1144 := comparison_pc s spc equal
  have mac := (SphincsMaskedMacTrace.trace hash SphincsMaskedImages.sign
    0x1144 SphincsMaskedMacTrace.sign_code (afterComparison s) pc).1
  exact first.trans mac

/-- info: 'SigGolfCandidate.SphincsMaskedSignParameterCheck.loaded_mac_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_mac_trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignParameterCheck.afterHash_words32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms afterHash_words32

/-- info: 'SigGolfCandidate.SphincsMaskedSignParameterCheck.loaded_comparison_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_comparison_trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignParameterCheck.comparison_trace_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms comparison_trace_hash

end SigGolfCandidate.SphincsMaskedSignParameterCheck
