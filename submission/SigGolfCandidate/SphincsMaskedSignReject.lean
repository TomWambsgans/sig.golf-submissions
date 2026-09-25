import SigGolfCandidate.SphincsMaskedSignTagCheck

namespace SigGolfCandidate.SphincsMaskedSignReject
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Execute all comparisons through the first differing MAC lane, then take
    its jump to the signer's common rejection block. -/
def rejectSchedule (i : Fin 5) : List (Word × Instr) :=
  SphincsMaskedSignTagCheck.compareSchedule.take (7 + 3 * i.val) ++
    [(BitVec.ofNat 64 (0x12e8 + 16 * i.val), .JAL .x0 (-(740 + 16 * i.val)))]

def afterRejectJump (i : Fin 5) (s : MachineState) : MachineState :=
  runSchedule (rejectSchedule i) s

theorem rejectSchedule_code (i : Fin 5) : ∀ entry ∈ rejectSchedule i,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign entry.1 =
      some (.base entry.2) := by
  fin_cases i <;> decide

private theorem widened_eq_iff (a b : BitVec 32) :
    (a.setWidth 64 = b.setWidth 64) ↔ a = b := by
  constructor
  · intro h
    have q := congrArg (fun x : BitVec 64 => x.setWidth 32) h
    simpa using q
  · intro h
    rw [h]

theorem reject_checked (i : Fin 5) (s : MachineState)
    (pc : s.pc = 0x12cc)
    (prior : ∀ j : Fin 5, j.val < i.val →
      s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * j.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * j.val)))
    (different : s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)) ≠
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val))) :
    Checked (rejectSchedule i) s := by
  fin_cases i
  · norm_num at different
    simp [Checked, rejectSchedule, SphincsMaskedSignTagCheck.compareSchedule,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid, rangeValid,
      MEMORY_BYTES, signExtend12, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc, different]
  · have h0 := prior 0 (by decide)
    norm_num at h0 different
    simp [Checked, rejectSchedule, SphincsMaskedSignTagCheck.compareSchedule,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid, rangeValid,
      MEMORY_BYTES, signExtend12, signExtend13, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc, h0, different]
  · have h0 := prior 0 (by decide)
    have h1 := prior 1 (by decide)
    norm_num at h0 h1 different
    simp [Checked, rejectSchedule, SphincsMaskedSignTagCheck.compareSchedule,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid, rangeValid,
      MEMORY_BYTES, signExtend12, signExtend13, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc, h0, h1, different]
  · have h0 := prior 0 (by decide)
    have h1 := prior 1 (by decide)
    have h2 := prior 2 (by decide)
    norm_num at h0 h1 h2 different
    simp [Checked, rejectSchedule, SphincsMaskedSignTagCheck.compareSchedule,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid, rangeValid,
      MEMORY_BYTES, signExtend12, signExtend13, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc, h0, h1, h2, different]
  · have h0 := prior 0 (by decide)
    have h1 := prior 1 (by decide)
    have h2 := prior 2 (by decide)
    have h3 := prior 3 (by decide)
    norm_num at h0 h1 h2 h3 different
    simp [Checked, rejectSchedule, SphincsMaskedSignTagCheck.compareSchedule,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid, rangeValid,
      MEMORY_BYTES, signExtend12, signExtend13, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc, h0, h1, h2, h3, different]

private theorem checked_last_jump_pc (pre : List (Word × Instr))
    (last : Word × Instr) (s : MachineState)
    (checked : Checked (pre ++ [last]) s)
    (jump : ∀ t : MachineState, t.pc = last.1 →
      (execInstrBr t last.2).pc = 0x1004) :
    (runSchedule (pre ++ [last]) s).pc = 0x1004 := by
  induction pre generalizing s with
  | nil =>
    obtain ⟨atPc, _, _⟩ := checked
    simpa [runSchedule] using jump s atPc
  | cons entry rest ih =>
    obtain ⟨_, _, tail⟩ := checked
    simpa [runSchedule] using ih (execInstrBr s entry.2) tail

theorem reject_pc (i : Fin 5) (s : MachineState)
    (pc : s.pc = 0x12cc)
    (prior : ∀ j : Fin 5, j.val < i.val →
      s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * j.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * j.val)))
    (different : s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)) ≠
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val))) :
    (afterRejectJump i s).pc = 0x1004 := by
  have checked := reject_checked i s pc prior different
  apply checked_last_jump_pc
    (SphincsMaskedSignTagCheck.compareSchedule.take (7 + 3 * i.val))
    (BitVec.ofNat 64 (0x12e8 + 16 * i.val), .JAL .x0 (-(740 + 16 * i.val))) s
  · exact checked
  · intro t tpc
    fin_cases i <;> simp [execInstrBr, signExtend21, tpc]

theorem reject_trace (hash : SigGolf.Hash) (i : Fin 5) (s : MachineState)
    (pc : s.pc = 0x12cc)
    (prior : ∀ j : Fin 5, j.val < i.val →
      s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * j.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * j.val)))
    (different : s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)) ≠
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val))) :
    Trace hash SphincsMaskedImages.sign s (8 + 3 * i.val)
      (8 + 3 * i.val) 0 0 (afterRejectJump i s) := by
  have h := checked_sound _ (rejectSchedule i) (rejectSchedule_code i) s
    (reject_checked i s pc prior different)
  have length : (rejectSchedule i).length = 8 + 3 * i.val := by
    fin_cases i <;> decide
  rw [length] at h
  exact h.trace

def failureSchedule : List (Word × Instr) := [
  (0x1004, .ADDI .x5 .x0 0),
  (0x1008, .ADDI .x10 .x0 0)]

def afterFailureSetup (s : MachineState) : MachineState :=
  runSchedule failureSchedule s

theorem failureSchedule_code : ∀ entry ∈ failureSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign entry.1 =
      some (.base entry.2) := by
  decide

theorem failure_checked (s : MachineState) (pc : s.pc = 0x1004) :
    Checked failureSchedule s := by
  simp [Checked, failureSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, pc]

theorem failure_setup (s : MachineState) (pc : s.pc = 0x1004) :
    OrdinarySteps SphincsMaskedImages.sign s 2 (afterFailureSetup s) := by
  exact checked_sound _ failureSchedule failureSchedule_code s
    (failure_checked s pc)

theorem failure_registers (s : MachineState) (pc : s.pc = 0x1004) :
    (afterFailureSetup s).pc = 0x100c ∧
    (afterFailureSetup s).getReg .x5 = 0 ∧
    (afterFailureSetup s).getReg .x10 = 0 := by
  simp [afterFailureSetup, runSchedule, failureSchedule,
    execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc]

theorem failure_executes (hash : SigGolf.Hash) (s : MachineState)
    (pc : s.pc = 0x1004) :
    Executes hash SphincsMaskedImages.sign s 3
      ⟨.failure, afterFailureSetup s, 3, 0, 0⟩ := by
  obtain ⟨finalPc, service, status⟩ := failure_registers s pc
  have hf : fetch SphincsMaskedImages.sign (afterFailureSetup s) =
      some (.base .ECALL) := by
    rw [SphincsVerifierFtsRootCopy.fetch_at, finalPc]
    decide
  have terminal := Executes.halt (hash := hash)
    (image := SphincsMaskedImages.sign) (afterFailureSetup s) hf service
  have whole := (failure_setup s pc).then_executes terminal
  simpa [status, Execution.charge] using whole

theorem tag_mismatch_rejects (hash : SigGolf.Hash) (i : Fin 5)
    (s : MachineState) (pc : s.pc = 0x12cc)
    (prior : ∀ j : Fin 5, j.val < i.val →
      s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * j.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * j.val)))
    (different : s.getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)) ≠
      s.getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val))) :
    Executes hash SphincsMaskedImages.sign s (11 + 3 * i.val)
      ⟨.failure, afterFailureSetup (afterRejectJump i s),
        11 + 3 * i.val, 0, 0⟩ := by
  have path := reject_trace hash i s pc prior different
  have suffix := failure_executes hash (afterRejectJump i s)
    (reject_pc i s pc prior different)
  have whole := path.then_executes suffix
  convert whole using 1
  · omega
  · simp [Execution.charge]
    omega

/-- The first differing public-parameter lane also jumps to the common
    failure block, before the cache MAC is queried. -/
def parameterRejectSchedule (i : Fin 5) : List (Word × Instr) :=
  SphincsMaskedSignParameterCheck.compareSchedule.take (6 + 3 * i.val) ++
    [(BitVec.ofNat 64 (0x1100 + 16 * i.val), .JAL .x0 (-(252 + 16 * i.val)))]

def afterParameterReject (i : Fin 5) (s : MachineState) : MachineState :=
  runSchedule (parameterRejectSchedule i) s

theorem parameterRejectSchedule_code (i : Fin 5) :
    ∀ entry ∈ parameterRejectSchedule i,
      SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign entry.1 =
        some (.base entry.2) := by
  fin_cases i <;> decide

theorem parameterReject_checked (i : Fin 5) (s : MachineState)
    (pc : s.pc = 0x10e8)
    (prior : ∀ j : Fin 5, j.val < i.val →
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * j.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * j.val)))
    (different : s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) ≠
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val))) :
    Checked (parameterRejectSchedule i) s := by
  fin_cases i
  · norm_num at different
    simp [Checked, parameterRejectSchedule,
      SphincsMaskedSignParameterCheck.compareSchedule,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid, rangeValid,
      MEMORY_BYTES, signExtend12, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc, different]
  · have h0 := prior 0 (by decide)
    norm_num at h0 different
    simp [Checked, parameterRejectSchedule,
      SphincsMaskedSignParameterCheck.compareSchedule,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid, rangeValid,
      MEMORY_BYTES, signExtend12, signExtend13, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc, h0, different]
  · have h0 := prior 0 (by decide)
    have h1 := prior 1 (by decide)
    norm_num at h0 h1 different
    simp [Checked, parameterRejectSchedule,
      SphincsMaskedSignParameterCheck.compareSchedule,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid, rangeValid,
      MEMORY_BYTES, signExtend12, signExtend13, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc, h0, h1, different]
  · have h0 := prior 0 (by decide)
    have h1 := prior 1 (by decide)
    have h2 := prior 2 (by decide)
    norm_num at h0 h1 h2 different
    simp [Checked, parameterRejectSchedule,
      SphincsMaskedSignParameterCheck.compareSchedule,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid, rangeValid,
      MEMORY_BYTES, signExtend12, signExtend13, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc, h0, h1, h2, different]
  · have h0 := prior 0 (by decide)
    have h1 := prior 1 (by decide)
    have h2 := prior 2 (by decide)
    have h3 := prior 3 (by decide)
    norm_num at h0 h1 h2 h3 different
    simp [Checked, parameterRejectSchedule,
      SphincsMaskedSignParameterCheck.compareSchedule,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid, rangeValid,
      MEMORY_BYTES, signExtend12, signExtend13, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc, h0, h1, h2, h3, different]

theorem parameterReject_pc (i : Fin 5) (s : MachineState)
    (pc : s.pc = 0x10e8)
    (prior : ∀ j : Fin 5, j.val < i.val →
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * j.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * j.val)))
    (different : s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) ≠
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val))) :
    (afterParameterReject i s).pc = 0x1004 := by
  have checked := parameterReject_checked i s pc prior different
  apply checked_last_jump_pc
    (SphincsMaskedSignParameterCheck.compareSchedule.take (6 + 3 * i.val))
    (BitVec.ofNat 64 (0x1100 + 16 * i.val), .JAL .x0 (-(252 + 16 * i.val))) s
  · exact checked
  · intro t tpc
    fin_cases i <;> simp [execInstrBr, signExtend21, tpc]

theorem parameter_mismatch_rejects (hash : SigGolf.Hash) (i : Fin 5)
    (s : MachineState) (pc : s.pc = 0x10e8)
    (prior : ∀ j : Fin 5, j.val < i.val →
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * j.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * j.val)))
    (different : s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) ≠
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val))) :
    Executes hash SphincsMaskedImages.sign s (10 + 3 * i.val)
      ⟨.failure, afterFailureSetup (afterParameterReject i s),
        10 + 3 * i.val, 0, 0⟩ := by
  have path : OrdinarySteps SphincsMaskedImages.sign s
      (6 + 3 * i.val + 1) (afterParameterReject i s) := by
    have h := checked_sound _ (parameterRejectSchedule i)
      (parameterRejectSchedule_code i) s
      (parameterReject_checked i s pc prior different)
    have length : (parameterRejectSchedule i).length = 6 + 3 * i.val + 1 := by
      fin_cases i <;> decide
    rw [length] at h
    exact h
  have suffix := failure_executes hash (afterParameterReject i s)
    (parameterReject_pc i s pc prior different)
  have whole := path.trace.then_executes suffix
  convert whole using 1
  · omega
  · simp [Execution.charge]
    omega

/-- A public-parameter mismatch is a complete failed execution from the
    actual sign loader, not merely a local branch fact. -/
theorem loaded_parameter_mismatch_rejects (hash : SigGolf.Hash)
    (secretKey : SigGolf.SecretKey) (cache : SigGolf.Cache)
    (message : SigGolf.Message) (i : Fin 5)
    (prior : ∀ j : Fin 5, j.val < i.val →
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x42000 + 4 * j.val)) =
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x74 + 4 * j.val)))
    (different :
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) ≠
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val))) :
    Executes hash SphincsMaskedImages.sign
      (SphincsMaskedSignPrefix.entryState secretKey cache message)
      (83 + 3 * i.val)
      ⟨.failure,
        afterFailureSetup (afterParameterReject i
          (SphincsMaskedSignPrefix.afterHashState hash
            (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
            secretKey)),
        98 + 3 * i.val, 1, 2⟩ := by
  let s := SphincsMaskedSignPrefix.afterHashState hash
    (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
    secretKey
  have spc : s.pc = 0x10e8 := by
    simp [s, SphincsMaskedSignPrefix.afterHashState, writeHash,
      SphincsMaskedSignPrefix.firstHash_pc,
      SphincsMaskedSignPrefix.afterJump_pc]
  have suffix := parameter_mismatch_rejects hash i s spc prior different
  have whole := (SphincsMaskedSignPrefix.loaded_firstHash_trace hash
    secretKey cache message).then_executes suffix
  convert whole using 1
  · omega
  · simp [Execution.charge, s]
    omega

/-- A failed tag comparison rejects from the actual sign loader after its
    first two HASH calls; arbitrary later signing code is not entered. -/
theorem loaded_tag_mismatch_rejects (hash : SigGolf.Hash)
    (secretKey : SigGolf.SecretKey) (cache : SigGolf.Cache)
    (message : SigGolf.Message) (i : Fin 5)
    (parameterEqual : ∀ j : Fin 5,
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x42000 + 4 * j.val)) =
      (SphincsMaskedSignPrefix.afterHashState hash
        (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
        secretKey).getWord32 (BitVec.ofNat 64 (0x74 + 4 * j.val)))
    (prior : ∀ j : Fin 5, j.val < i.val →
      (SphincsMaskedMacTrace.result hash 0x1144
        (SphincsMaskedSignParameterCheck.afterComparison
          (SphincsMaskedSignPrefix.afterHashState hash
            (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
            secretKey))).getWord32 (BitVec.ofNat 64 (0x84000 + 4 * j.val)) =
      (SphincsMaskedMacTrace.result hash 0x1144
        (SphincsMaskedSignParameterCheck.afterComparison
          (SphincsMaskedSignPrefix.afterHashState hash
            (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
            secretKey))).getWord32 (BitVec.ofNat 64 (0x2004c + 4 * j.val)))
    (different :
      (SphincsMaskedMacTrace.result hash 0x1144
        (SphincsMaskedSignParameterCheck.afterComparison
          (SphincsMaskedSignPrefix.afterHashState hash
            (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
            secretKey))).getWord32 (BitVec.ofNat 64 (0x84000 + 4 * i.val)) ≠
      (SphincsMaskedMacTrace.result hash 0x1144
        (SphincsMaskedSignParameterCheck.afterComparison
          (SphincsMaskedSignPrefix.afterHashState hash
            (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
            secretKey))).getWord32 (BitVec.ofNat 64 (0x2004c + 4 * i.val))) :
    Executes hash SphincsMaskedImages.sign
      (SphincsMaskedSignPrefix.entryState secretKey cache message)
      (338 + 3 * i.val)
      ⟨.failure,
        afterFailureSetup (afterRejectJump i
          (SphincsMaskedMacTrace.result hash 0x1144
            (SphincsMaskedSignParameterCheck.afterComparison
              (SphincsMaskedSignPrefix.afterHashState hash
                (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
                secretKey)))),
        16744 + 3 * i.val, 2, 2051⟩ := by
  let s := SphincsMaskedSignPrefix.afterHashState hash
    (SphincsMaskedSignPrefix.afterJumpState secretKey cache message)
    secretKey
  let checked := SphincsMaskedSignParameterCheck.afterComparison s
  let authenticated := SphincsMaskedMacTrace.result hash 0x1144 checked
  have spc : s.pc = 0x10e8 := by
    simp [s, SphincsMaskedSignPrefix.afterHashState, writeHash,
      SphincsMaskedSignPrefix.firstHash_pc,
      SphincsMaskedSignPrefix.afterJump_pc]
  have cpc : checked.pc = 0x1144 :=
    SphincsMaskedSignParameterCheck.comparison_pc s spc parameterEqual
  have apc : authenticated.pc = 0x12cc := by
    have h := (SphincsMaskedMacTrace.trace hash SphincsMaskedImages.sign
      0x1144 SphincsMaskedMacTrace.sign_code checked cpc).2
    simpa [authenticated] using h
  have suffix := tag_mismatch_rejects hash i authenticated apc prior different
  have whole := (SphincsMaskedSignParameterCheck.loaded_mac_trace hash
    secretKey cache message parameterEqual).then_executes suffix
  convert whole using 1
  · omega
  · simp [Execution.charge, s, checked, authenticated]
    omega

/-- info: 'SigGolfCandidate.SphincsMaskedSignReject.reject_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reject_trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignReject.tag_mismatch_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tag_mismatch_rejects

/-- info: 'SigGolfCandidate.SphincsMaskedSignReject.parameter_mismatch_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parameter_mismatch_rejects

/-- info: 'SigGolfCandidate.SphincsMaskedSignReject.loaded_parameter_mismatch_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_parameter_mismatch_rejects

/-- info: 'SigGolfCandidate.SphincsMaskedSignReject.loaded_tag_mismatch_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_tag_mismatch_rejects

end SigGolfCandidate.SphincsMaskedSignReject
