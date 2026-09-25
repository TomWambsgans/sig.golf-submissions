import SigGolfCandidate.SphincsMaskedSignParameterCheck

namespace SigGolfCandidate.SphincsMaskedSignTagCheck
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Successful cache-MAC tag comparison. Rejection jumps are skipped. -/
def compareSchedule : List (Word × Instr) := [
  (0x12cc, .LUI .x6 132),
  (0x12d0, .ADDI .x6 .x6 0),
  (0x12d4, .LUI .x7 32),
  (0x12d8, .ADDI .x7 .x7 76),
  (0x12dc, .LWU .x10 .x6 0),
  (0x12e0, .LWU .x11 .x7 0),
  (0x12e4, .BEQ .x10 .x11 8),
  (0x12ec, .LWU .x10 .x6 4),
  (0x12f0, .LWU .x11 .x7 4),
  (0x12f4, .BEQ .x10 .x11 8),
  (0x12fc, .LWU .x10 .x6 8),
  (0x1300, .LWU .x11 .x7 8),
  (0x1304, .BEQ .x10 .x11 8),
  (0x130c, .LWU .x10 .x6 12),
  (0x1310, .LWU .x11 .x7 12),
  (0x1314, .BEQ .x10 .x11 8),
  (0x131c, .LWU .x10 .x6 16),
  (0x1320, .LWU .x11 .x7 16),
  (0x1324, .BEQ .x10 .x11 8)]

def afterComparison (s : MachineState) : MachineState :=
  runSchedule compareSchedule s

theorem schedule_code : ∀ entry ∈ compareSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign entry.1 =
      some (.base entry.2) := by
  decide

theorem comparison_checked (s : MachineState) (pc : s.pc = 0x12cc)
    (equal : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val))) :
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

theorem comparison_trace (s : MachineState) (pc : s.pc = 0x12cc)
    (equal : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val))) :
    OrdinarySteps SphincsMaskedImages.sign s 19 (afterComparison s) := by
  exact checked_sound _ compareSchedule schedule_code s
    (comparison_checked s pc equal)

theorem comparison_pc (s : MachineState) (pc : s.pc = 0x12cc)
    (equal : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val))) :
    (afterComparison s).pc = 0x132c := by
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

theorem comparison_trace_hash (hash : SigGolf.Hash) (s : MachineState)
    (pc : s.pc = 0x12cc)
    (equal : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val))) :
    Trace hash SphincsMaskedImages.sign s 19 19 0 0
      (afterComparison s) :=
  (comparison_trace s pc equal).trace

/-- The signer reaches the first post-authentication instruction whenever
    both its parameter and cache-tag checks succeed. -/
theorem loaded_authenticated_trace (hash : SigGolf.Hash)
    (secretKey : SigGolf.SecretKey) (cache : SigGolf.Cache)
    (message : SigGolf.Message)
    (parameterEqual : ∀ i : Fin 5,
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val)))
    (tagEqual : ∀ i : Fin 5,
      (SphincsMaskedMacTrace.result hash 0x1144
        (SphincsMaskedSignParameterCheck.afterComparison
          (SphincsMaskedSignPrefix.afterHashState hash
            (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
            secretKey))).getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)) =
      (SphincsMaskedMacTrace.result hash 0x1144
        (SphincsMaskedSignParameterCheck.afterComparison
          (SphincsMaskedSignPrefix.afterHashState hash
            (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
            secretKey))).getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val))) :
    Trace hash SphincsMaskedImages.sign
      (SphincsMaskedSignPrefix.entryState secretKey cache message)
      346 16752 2 2051
      (afterComparison
        (SphincsMaskedMacTrace.result hash 0x1144
          (SphincsMaskedSignParameterCheck.afterComparison
            (SphincsMaskedSignPrefix.afterHashState hash
              (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
              secretKey)))) := by
  let s := SphincsMaskedSignPrefix.afterHashState hash
    (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
    secretKey
  let checked := SphincsMaskedSignParameterCheck.afterComparison s
  let authenticated := SphincsMaskedMacTrace.result hash 0x1144 checked
  have first := SphincsMaskedSignParameterCheck.loaded_mac_trace hash secretKey cache message parameterEqual
  have spc : s.pc = 0x10e8 := by
    simp [s, SphincsMaskedSignPrefix.afterHashState,
      writeHash, SphincsMaskedSignPrefix.firstHash_pc,
      SphincsMaskedSignPrefix.afterJump_pc]
  have cpc : checked.pc = 0x1144 :=
    SphincsMaskedSignParameterCheck.comparison_pc s spc parameterEqual
  have apc : authenticated.pc = 0x12cc := by
    have h := (SphincsMaskedMacTrace.trace hash SphincsMaskedImages.sign
      0x1144 SphincsMaskedMacTrace.sign_code checked cpc).2
    simpa [authenticated] using h
  exact first.trans (comparison_trace_hash hash authenticated apc tagEqual)

/-- info: 'SigGolfCandidate.SphincsMaskedSignTagCheck.loaded_authenticated_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_authenticated_trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignTagCheck.comparison_trace_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms comparison_trace_hash

end SigGolfCandidate.SphincsMaskedSignTagCheck
