import SigGolfCandidate.SphincsMaskedSignOtsPathValue

namespace SigGolfCandidate.SphincsMaskedSignOtsPathValue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedSignOtsParents SphincsMaskedSignOtsTree SphincsMaskedSignOtsPath
open SphincsMaskedSignOtsPathSetup SphincsMaskedSignOtsPathSibling SphincsMaskedSignOtsPathFinish
open SphincsMaskedSignOtsShift SphincsMaskedKeygenPrefix
open SphincsSecurity SphincsBridge SphincsVerifierCopy SphincsVerifierFtsRootCopy SphincsMaskedChainDomain
open SphincsVerifierWotsDecode SphincsVerifierWotsDecodeData SphincsVerifierMessageCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- A failed WOTS checksum resumes after the counter reset. -/
def retryPreludeCode : List (Word × Instr) := otsPreludeCode.drop 10

def retryPreludeState (s : MachineState) : MachineState := runSchedule retryPreludeCode s

def retryPrelude (location : Fin 5) (s : MachineState) : MachineState :=
  shift (delta location) (retryPreludeState (s.setPC 0x1a78))

theorem retryPrelude_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (670 + offset location) retryPreludeCode := by
  fin_cases location <;> rfl

theorem retryPrelude_encoded (location : Fin 5) :
    ∀ e ∈ retryPreludeCode,
      instructionAt SphincsMaskedImages.sign (e.1 + delta location) = some (.base e.2) := by
  apply encoded_of_block _ (670 + offset location) _ _ (retryPrelude_image location)
  · have h := SphincsMaskedSignOtsParents.offset_bound location
    change 670 + offset location + 10 ≤ 11000
    omega
  · intro i
    have h : ∀ i : Fin retryPreludeCode.length,
        retryPreludeCode[i.val].1 = BitVec.ofNat 64 (0x1a78 + 4 * i.val) := by
      intro j
      fin_cases j <;> rfl
    rw [h i, delta, ← BitVec.ofNat_add]
    congr 1
    omega

theorem retryPrelude_supported : ∀ e ∈ retryPreludeCode, Supported e.2 := by decide

theorem retryPrelude_checked (s : MachineState) (pc : s.pc = 0x1a78) :
    Checked retryPreludeCode s := by
  simp [retryPreludeCode, otsPreludeCode, Checked, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

theorem retryPrelude_block (location : Fin 5) (s : MachineState)
    (pc : s.pc = 0x1a78 + delta location) :
    OrdinarySteps SphincsMaskedImages.sign s 10 (retryPrelude location s) := by
  have trace := block_shift SphincsMaskedImages.sign (delta location) retryPreludeCode
    retryPrelude_supported (retryPrelude_encoded location) (s.setPC 0x1a78)
    (retryPrelude_checked (s.setPC 0x1a78) rfl)
  rw [SphincsMaskedSignOtsDomain.rebase_eq _ _ s pc] at trace
  have len : retryPreludeCode.length = 10 := rfl
  simpa only [retryPrelude, retryPreludeState, len] using trace

theorem retryPrelude_pc (location : Fin 5) (s : MachineState) :
    (retryPrelude location s).pc = 0x1aa0 + delta location := by
  simp [retryPrelude, retryPreludeState, retryPreludeCode, otsPreludeCode,
    runSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem retryPrelude_counter (location : Fin 5) (s : MachineState) :
    (retryPrelude location s).getMem 0x430b8 = s.getMem 0x430b8 := by
  simp [retryPrelude, retryPreludeState, retryPreludeCode, otsPreludeCode,
    runSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.retryPrelude_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms retryPrelude_block

theorem retry_encoding_hash (location : Fin 5) (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1a78 + delta location) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 71 78 1 1 t ∧
      t.pc = 0x1b94 + delta location ∧
      t.getMem 0x430b8 = s.getMem 0x430b8 := by
  let mid := retryPrelude location s
  let prep := otsHashPrep location mid
  let t := writeHash prep (hash (hashInput prep))
  refine ⟨t, ?_, ?_, ?_⟩
  · have first := (retryPrelude_block location s pc).trace (hash := hash)
    have second := (otsHashPrep_block location mid (retryPrelude_pc location s)).trace (hash := hash)
    have third := otsHashPrep_hash_step location hash mid
    simpa only [mid, prep, t, Nat.reduceAdd] using first.trans (second.trans third)
  · simp [t, prep, writeHash, otsHashPrep_pc]
    bv_omega
  · have frame := SphincsVerifierFtsLevelInit.writeHash_mem_frame prep
      (hash (hashInput prep)) (otsHashPrep_registers location mid).2.2.1
      0x430b8 (by decide) (by decide) (by decide) (by decide)
    rw [frame, otsHashPrep_frame location mid 0x430b8 (by decide),
      retryPrelude_counter]

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.retry_encoding_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms retry_encoding_hash

/-- A completed failed-checksum branch enters the next tag-4 HASH, retaining
    the incremented retry counter and exact cycle count. -/
theorem retry_encoding_followup (location : Fin 5) (hash : Hash)
    (s mid : MachineState)
    (first : OrdinarySteps SphincsMaskedImages.sign s 513 mid)
    (midPc : mid.pc = 0x1a78 + delta location)
    (counter : mid.getMem 0x430b8 = s.getMem 0x430b8 + 1) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 584 591 1 1 t ∧
      t.pc = 0x1b94 + delta location ∧
      t.getMem 0x430b8 = s.getMem 0x430b8 + 1 := by
  obtain ⟨t, second, finalPc, retained⟩ :=
    retry_encoding_hash location hash mid midPc
  exact ⟨t, by simpa only [Nat.reduceAdd] using first.trace.trans second,
    finalPc, retained.trans counter⟩

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.retry_encoding_followup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms retry_encoding_followup

/-- A checksum failure with valid digest padding takes the complete retry loop:
    both padding tests, digit decoding, counter advance, and the next HASH. -/
theorem retry_full_failed_attempt (location : Fin 5) (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1b94 + delta location)
    (padding1 : (otsPaddingFirst location s).getReg .x10 = 0)
    (padding2 : (otsPaddingSecond location (otsPaddingFirst location s)).getReg .x10 = 0)
    (bad : answerSum 52 (sumInit (otsPaddingSecond location (otsPaddingFirst location s))) ≠ 194)
    (under : s.getMem 0x430b8 + 1 ≠ (2 ^ 20 : Word)) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 594 601 1 1 t ∧
      t.pc = 0x1b94 + delta location ∧
      t.getMem 0x430b8 = s.getMem 0x430b8 + 1 := by
  let first := otsPaddingFirst location s
  let second := otsPaddingSecond location first
  let retry := retryDecision (retryCounter location
    (sumFailureJump (sumTest (signerDecoderRun 52 (sumInit second)))))
  have firstTrace := (otsPaddingFirst_block location s pc).trace (hash := hash)
  have firstPc : first.pc = 0x1bac + delta location :=
    otsPaddingFirst_good_pc location s padding1
  have secondTrace := (otsPaddingSecond_block location first firstPc).trace (hash := hash)
  have secondPc : second.pc = 0x1bc4 + delta location :=
    otsPaddingSecond_good_pc location first padding2
  have counter : second.getMem 0x430b8 = s.getMem 0x430b8 := by
    simp [second, first, otsPaddingSecond, otsPaddingSecondState,
      otsPaddingSecondCode, otsPaddingFirst, otsPaddingFirstState,
      otsPaddingFirstCode, runSchedule, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  have under' : second.getMem 0x430b8 + 1 ≠ (2 ^ 20 : Word) := by
    rw [counter]
    exact under
  obtain ⟨retryTrace, retryPc⟩ :=
    signer_encoding_retry location second secondPc bad under'
  obtain ⟨t, finalTrace, finalPc, finalCounter⟩ :=
    retry_encoding_hash location hash retry retryPc
  refine ⟨t, ?_, finalPc, ?_⟩
  · simpa only [first, second, retry, Nat.reduceAdd] using
      (firstTrace.trans (secondTrace.trans (retryTrace.trace (hash := hash)))).trans finalTrace
  · rw [finalCounter, signer_encoding_retry_counter, counter]

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.retry_full_failed_attempt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms retry_full_failed_attempt

/-- The concrete state reached by the next encoding HASH. -/
def retryHashState (location : Fin 5) (hash : Hash) (s : MachineState) : MachineState :=
  let prep := otsHashPrep location (retryPrelude location s)
  writeHash prep (hash (hashInput prep))

theorem retry_encoding_hash_exact (location : Fin 5) (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1a78 + delta location) :
    Trace hash SphincsMaskedImages.sign s 71 78 1 1 (retryHashState location hash s) ∧
      (retryHashState location hash s).pc = 0x1b94 + delta location ∧
      (retryHashState location hash s).getMem 0x430b8 = s.getMem 0x430b8 := by
  let mid := retryPrelude location s
  let prep := otsHashPrep location mid
  have first := (retryPrelude_block location s pc).trace (hash := hash)
  have second := (otsHashPrep_block location mid (retryPrelude_pc location s)).trace (hash := hash)
  have third := otsHashPrep_hash_step location hash mid
  refine ⟨?_, ?_, ?_⟩
  · simpa only [retryHashState, mid, prep, Nat.reduceAdd] using first.trans (second.trans third)
  · simp [retryHashState, prep, writeHash, otsHashPrep_pc]
    bv_omega
  · have frame := SphincsVerifierFtsLevelInit.writeHash_mem_frame prep
        (hash (hashInput prep)) (otsHashPrep_registers location mid).2.2.1
        0x430b8 (by decide) (by decide) (by decide) (by decide)
    simpa only [retryHashState, mid, prep] using
      (frame.trans ((otsHashPrep_frame location mid 0x430b8 (by decide)).trans
        (retryPrelude_counter location s)))

def retryChecksumState (location : Fin 5) (s : MachineState) : MachineState :=
  let second := otsPaddingSecond location (otsPaddingFirst location s)
  retryDecision (retryCounter location
    (sumFailureJump (sumTest (signerDecoderRun 52 (sumInit second)))))

def fullRetryState (location : Fin 5) (hash : Hash) (s : MachineState) : MachineState :=
  retryHashState location hash (retryChecksumState location s)

theorem retry_full_failed_attempt_exact (location : Fin 5) (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1b94 + delta location)
    (padding1 : (otsPaddingFirst location s).getReg .x10 = 0)
    (padding2 : (otsPaddingSecond location (otsPaddingFirst location s)).getReg .x10 = 0)
    (bad : answerSum 52 (sumInit (otsPaddingSecond location (otsPaddingFirst location s))) ≠ 194)
    (under : s.getMem 0x430b8 + 1 ≠ (2 ^ 20 : Word)) :
    Trace hash SphincsMaskedImages.sign s 594 601 1 1 (fullRetryState location hash s) ∧
      (fullRetryState location hash s).pc = 0x1b94 + delta location ∧
      (fullRetryState location hash s).getMem 0x430b8 = s.getMem 0x430b8 + 1 := by
  let first := otsPaddingFirst location s
  let second := otsPaddingSecond location first
  let retry := retryChecksumState location s
  have firstTrace := (otsPaddingFirst_block location s pc).trace (hash := hash)
  have firstPc : first.pc = 0x1bac + delta location :=
    otsPaddingFirst_good_pc location s padding1
  have secondTrace := (otsPaddingSecond_block location first firstPc).trace (hash := hash)
  have secondPc : second.pc = 0x1bc4 + delta location :=
    otsPaddingSecond_good_pc location first padding2
  have counter : second.getMem 0x430b8 = s.getMem 0x430b8 := by
    simp [second, first, otsPaddingSecond, otsPaddingSecondState,
      otsPaddingSecondCode, otsPaddingFirst, otsPaddingFirstState,
      otsPaddingFirstCode, runSchedule, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  have under' : second.getMem 0x430b8 + 1 ≠ (2 ^ 20 : Word) := by
    rw [counter]
    exact under
  obtain ⟨retryTrace, retryPc⟩ :=
    signer_encoding_retry location second secondPc bad under'
  have retryPc' : retry.pc = 0x1a78 + delta location := by
    exact retryPc
  obtain ⟨finalTrace, finalPc, finalCounter⟩ :=
    retry_encoding_hash_exact location hash retry retryPc'
  refine ⟨?_, finalPc, ?_⟩
  · simpa only [first, second, retry, retryChecksumState, fullRetryState, Nat.reduceAdd]
      using (firstTrace.trans (secondTrace.trans (retryTrace.trace (hash := hash)))).trans finalTrace
  · have retryCounter : retry.getMem 0x430b8 = s.getMem 0x430b8 + 1 := by
      change (retryDecision (retryCounter location
        (sumFailureJump (sumTest (signerDecoderRun 52 (sumInit second)))))).getMem
          0x430b8 = s.getMem 0x430b8 + 1
      rw [signer_encoding_retry_counter, counter]
    exact finalCounter.trans retryCounter

def fullRetryStates (location : Fin 5) (hash : Hash) (s : MachineState) : Nat → MachineState
  | 0 => s
  | n + 1 => fullRetryState location hash (fullRetryStates location hash s n)

/-- A bounded run of failed WOTS encodings has exact resource accounting. The
    premises describe the actual oracle answers at each deterministic retry state. -/
theorem retry_full_failed_attempts (location : Fin 5) (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1b94 + delta location) :
    ∀ n,
      (∀ j, j < n →
        let st := fullRetryStates location hash s j
        (otsPaddingFirst location st).getReg .x10 = 0 ∧
        (otsPaddingSecond location (otsPaddingFirst location st)).getReg .x10 = 0 ∧
        answerSum 52 (sumInit (otsPaddingSecond location (otsPaddingFirst location st))) ≠ 194 ∧
        st.getMem 0x430b8 + 1 ≠ (2 ^ 20 : Word)) →
      Trace hash SphincsMaskedImages.sign s (594 * n) (601 * n) n n
        (fullRetryStates location hash s n) ∧
      (fullRetryStates location hash s n).pc = 0x1b94 + delta location ∧
      (fullRetryStates location hash s n).getMem 0x430b8 = s.getMem 0x430b8 + (n : Word) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨Trace.refl s, pc, by simp [fullRetryStates]⟩
  | succ n ih =>
      intro failed
      obtain ⟨prior, priorPc, priorCounter⟩ := ih (fun j hj => failed j (by omega))
      obtain ⟨padding1, padding2, bad, under⟩ := failed n (by omega)
      obtain ⟨step, nextPc, nextCounter⟩ :=
        retry_full_failed_attempt_exact location hash (fullRetryStates location hash s n)
          priorPc padding1 padding2 bad under
      refine ⟨?_, nextPc, ?_⟩
      · simpa only [fullRetryStates, Nat.mul_add, Nat.reduceMul, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc] using prior.trans step
      · change (fullRetryState location hash (fullRetryStates location hash s n)).getMem
          0x430b8 = s.getMem 0x430b8 + ((n + 1 : Nat) : Word)
        rw [nextCounter, priorCounter]
        simp [add_assoc]

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.retry_full_failed_attempts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms retry_full_failed_attempts

end SigGolfCandidate.SphincsMaskedSignOtsPathValue
