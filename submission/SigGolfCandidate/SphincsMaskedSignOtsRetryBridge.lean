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

/-- The state after an accepted checksum, at the WOTS chain-signing entry. -/
def encodingSuccessState (location : Fin 5) (s : MachineState) : MachineState :=
  let second := otsPaddingSecond location (otsPaddingFirst location s)
  sumTest (signerDecoderRun 52 (sumInit second))

private theorem sumTest_byte (s : MachineState) (address : Word) :
    (sumTest s).getByte address = s.getByte address := by
  simp [MachineState.getByte, sumTest, execInstrBr]

/-- Every accepted encoding leaves its 52 decoded digits in the cells read by
    WOTS chain signing. -/
theorem encoding_success_digit (location : Fin 5) (s : MachineState)
    (chain : Fin 52) :
    (encodingSuccessState location s).getByte
      (BitVec.ofNat 64 (0x44000 + chain.val)) =
      answerDigit chain
        (sumInit (otsPaddingSecond location (otsPaddingFirst location s))) := by
  rw [encodingSuccessState, sumTest_byte]
  exact signer_run_digit 52 _ (by decide) chain chain.isLt

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.encoding_success_digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encoding_success_digit

private theorem digest_digit_mask (digest : Digest) (start : Nat) :
    BitVec.ofNat 8 ((digest.extractLsb' start 3).toNat) =
      (digest >>> start).setWidth 8 &&& 7#8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat,
    BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  rw [show 7 % 256 = 2^3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem answerDigit_digestEncoding (s : MachineState) (digest : Digest)
    (bytes : ∀ j : Fin 20,
      s.getByte (BitVec.ofNat 64 (0x42000 + j.val)) =
        digest.extractLsb' (8 * j.val) 8) (i : ChainIndex) :
    answerDigit i s =
      BitVec.ofNat 8 ((TargetSum.digestEncoding digest i).val) := by
  change answerDigit i s =
    BitVec.ofNat 8 ((digest.extractLsb' (TargetSum.digitOffset i) 3).toNat)
  rw [digest_digit_mask]
  have h0 := bytes ⟨0, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h0
  have h1 := bytes ⟨1, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h1
  have h2 := bytes ⟨2, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h2
  have h3 := bytes ⟨3, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h3
  have h4 := bytes ⟨4, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h4
  have h5 := bytes ⟨5, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h5
  have h6 := bytes ⟨6, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h6
  have h7 := bytes ⟨7, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h7
  have h8 := bytes ⟨8, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h8
  have h9 := bytes ⟨9, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h9
  have h10 := bytes ⟨10, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h10
  have h11 := bytes ⟨11, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h11
  have h12 := bytes ⟨12, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h12
  have h13 := bytes ⟨13, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h13
  have h14 := bytes ⟨14, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h14
  have h15 := bytes ⟨15, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h15
  have h16 := bytes ⟨16, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h16
  have h17 := bytes ⟨17, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h17
  have h18 := bytes ⟨18, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h18
  have h19 := bytes ⟨19, by decide⟩
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb] at h19
  simp at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
  fin_cases i <;>
    simp [answerDigit, answerWord, digitBit, TargetSum.digitOffset,
      TargetSum.digitsPerHalf, winternitzBits, numChains] <;>
    (repeat first | rw [h0] | rw [h1] | rw [h2] | rw [h3] | rw [h4] | rw [h5] | rw [h6] | rw [h7] | rw [h8] | rw [h9] | rw [h10] | rw [h11] | rw [h12] | rw [h13] | rw [h14] | rw [h15] | rw [h16] | rw [h17] | rw [h18] | rw [h19]) <;>
    apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_add] <;>
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq] at * <;>
    norm_num at * <;>
    simp only [show (7 : Nat) = 2^3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod] <;>
    omega

/-- The accepted concrete digit cells are the abstract WOTS encoding digits
    when the HASH answer bytes encode the abstract digest. -/
theorem encoding_success_abstract_digit (location : Fin 5) (s : MachineState)
    (digest : Digest) (encoding : Encoding)
    (answerBytes : ∀ j : Fin 20,
      (sumInit (otsPaddingSecond location (otsPaddingFirst location s))).getByte
        (BitVec.ofNat 64 (0x42000 + j.val)) = digest.extractLsb' (8 * j.val) 8)
    (decoded : TargetSum.decodeDigest digest = some encoding)
    (chain : ChainIndex) :
    (encodingSuccessState location s).getByte
      (BitVec.ofNat 64 (0x44000 + chain.val)) =
      BitVec.ofNat 8 (encoding chain).val := by
  have eqEncoding : encoding = TargetSum.digestEncoding digest := by
    unfold TargetSum.decodeDigest at decoded
    split at decoded <;> simp_all
  subst encoding
  exact (encoding_success_digit location s chain).trans
    (answerDigit_digestEncoding _ digest answerBytes chain)

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.answerDigit_digestEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms answerDigit_digestEncoding

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.encoding_success_abstract_digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encoding_success_abstract_digit

/-- The successful post-HASH encoding path checks both padding bytes, emits all
    52 WOTS digits, and exits the checksum branch with no further HASH calls. -/
theorem encoding_success_after_hash (location : Fin 5) (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1b94 + delta location)
    (padding1 : (otsPaddingFirst location s).getReg .x10 = 0)
    (padding2 : (otsPaddingSecond location (otsPaddingFirst location s)).getReg .x10 = 0)
    (good : answerSum 52
      (sumInit (otsPaddingSecond location (otsPaddingFirst location s))) = 194) :
    Trace hash SphincsMaskedImages.sign s 509 509 0 0 (encodingSuccessState location s) ∧
      (encodingSuccessState location s).pc = 0x23cc + delta location := by
  let first := otsPaddingFirst location s
  let second := otsPaddingSecond location first
  have firstTrace := (otsPaddingFirst_block location s pc).trace (hash := hash)
  have firstPc : first.pc = 0x1bac + delta location :=
    otsPaddingFirst_good_pc location s padding1
  have secondTrace := (otsPaddingSecond_block location first firstPc).trace (hash := hash)
  have secondPc : second.pc = 0x1bc4 + delta location :=
    otsPaddingSecond_good_pc location first padding2
  obtain ⟨goodTrace, goodPc⟩ := signer_encoding_good location second secondPc good
  refine ⟨?_, ?_⟩
  · simpa only [first, second, encodingSuccessState, Nat.reduceAdd] using
      firstTrace.trans (secondTrace.trans (goodTrace.trace (hash := hash)))
  · exact goodPc

/-- After any bounded sequence of failed encodings, an accepted checksum reaches
    WOTS chain signing with exact cumulative costs. -/
theorem encoding_success_after_retries (location : Fin 5) (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1b94 + delta location) (n : Nat)
    (failed : ∀ j, j < n →
      let st := fullRetryStates location hash s j
      (otsPaddingFirst location st).getReg .x10 = 0 ∧
      (otsPaddingSecond location (otsPaddingFirst location st)).getReg .x10 = 0 ∧
      answerSum 52 (sumInit (otsPaddingSecond location (otsPaddingFirst location st))) ≠ 194 ∧
      st.getMem 0x430b8 + 1 ≠ (2 ^ 20 : Word))
    (padding1 : (otsPaddingFirst location (fullRetryStates location hash s n)).getReg .x10 = 0)
    (padding2 : (otsPaddingSecond location
      (otsPaddingFirst location (fullRetryStates location hash s n))).getReg .x10 = 0)
    (good : answerSum 52 (sumInit (otsPaddingSecond location
      (otsPaddingFirst location (fullRetryStates location hash s n)))) = 194) :
    Trace hash SphincsMaskedImages.sign s (594 * n + 509) (601 * n + 509) n n
      (encodingSuccessState location (fullRetryStates location hash s n)) ∧
      (encodingSuccessState location (fullRetryStates location hash s n)).pc =
        0x23cc + delta location := by
  obtain ⟨retries, endPc, _⟩ := retry_full_failed_attempts location hash s pc n failed
  obtain ⟨finish, successPc⟩ := encoding_success_after_hash location hash _
    endPc padding1 padding2 good
  exact ⟨by simpa only [Nat.add_zero] using retries.trans finish, successPc⟩

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.encoding_success_after_retries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encoding_success_after_retries

/-- Concrete state after the first encoding HASH at the WOTS entry. -/
def initialEncodingState (location : Fin 5) (hash : Hash) (s : MachineState) : MachineState :=
  let prep := otsHashPrep location (otsPrelude location s)
  writeHash prep (hash (hashInput prep))

theorem initial_encoding_hash_exact (location : Fin 5) (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1a50 + delta location) :
    Trace hash SphincsMaskedImages.sign s 81 88 1 1 (initialEncodingState location hash s) ∧
      (initialEncodingState location hash s).pc = 0x1b94 + delta location := by
  let mid := otsPrelude location s
  let prep := otsHashPrep location mid
  have first := (otsPrelude_block location s pc).trace (hash := hash)
  have second := (otsHashPrep_block location mid (otsPrelude_pc location s)).trace (hash := hash)
  have third := otsHashPrep_hash_step location hash mid
  refine ⟨?_, ?_⟩
  · simpa only [initialEncodingState, mid, prep, Nat.reduceAdd] using
      first.trans (second.trans third)
  · simp [initialEncodingState, prep, writeHash, otsHashPrep_pc]
    bv_omega

/-- The full accepted encoding, including its first HASH and all bounded
    retries, reaches the WOTS signing entry with exact costs. -/
theorem encoding_success_from_entry (location : Fin 5) (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1a50 + delta location) (n : Nat)
    (failed : ∀ j, j < n →
      let st := fullRetryStates location hash (initialEncodingState location hash s) j
      (otsPaddingFirst location st).getReg .x10 = 0 ∧
      (otsPaddingSecond location (otsPaddingFirst location st)).getReg .x10 = 0 ∧
      answerSum 52 (sumInit (otsPaddingSecond location (otsPaddingFirst location st))) ≠ 194 ∧
      st.getMem 0x430b8 + 1 ≠ (2 ^ 20 : Word))
    (padding1 : (otsPaddingFirst location
      (fullRetryStates location hash (initialEncodingState location hash s) n)).getReg .x10 = 0)
    (padding2 : (otsPaddingSecond location (otsPaddingFirst location
      (fullRetryStates location hash (initialEncodingState location hash s) n))).getReg .x10 = 0)
    (good : answerSum 52 (sumInit (otsPaddingSecond location (otsPaddingFirst location
      (fullRetryStates location hash (initialEncodingState location hash s) n)))) = 194) :
    Trace hash SphincsMaskedImages.sign s (594 * n + 590) (601 * n + 597) (n + 1) (n + 1)
      (encodingSuccessState location
        (fullRetryStates location hash (initialEncodingState location hash s) n)) ∧
      (encodingSuccessState location
        (fullRetryStates location hash (initialEncodingState location hash s) n)).pc =
          0x23cc + delta location := by
  obtain ⟨first, firstPc⟩ := initial_encoding_hash_exact location hash s pc
  obtain ⟨rest, endPc⟩ := encoding_success_after_retries location hash
    (initialEncodingState location hash s) firstPc n failed padding1 padding2 good
  have combined := first.trans rest
  have stepsEq : 81 + (594 * n + 509) = 594 * n + 590 := by omega
  have cyclesEq : 88 + (601 * n + 509) = 601 * n + 597 := by omega
  have callsEq : 1 + n = n + 1 := by omega
  rw [stepsEq, cyclesEq, callsEq] at combined
  exact ⟨combined, endPc⟩

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.encoding_success_from_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encoding_success_from_entry

set_option backward.isDefEq.respectTransparency false

/-- The first concrete WOTS encoding HASH result carries the abstract digest
    whenever its prepared query is the abstract encoding query. -/
theorem initial_encoding_digest_words (location : Fin 5) (hash : Hash)
    (s : MachineState) (parameter : PublicParameter) (lay : Layer)
    (treeIdx : TreeIndex) (leaf : LeafIndex) (message : Digest) (counter : Counter)
    (query : hashInput (otsHashPrep location (otsPrelude location s)) =
      toQuery (tweakableHashInput parameter (.encoding lay treeIdx leaf)
        (bytesLE 20 message ++ bytesLE 4 (BitVec.ofNat 32 counter.toNat)))) :
    Words20 (initialEncodingState location hash s) 0x42000
      (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Concrete.tweakableHash parameter (.encoding lay treeIdx leaf)
          (bytesLE 20 message ++ bytesLE 4 (BitVec.ofNat 32 counter.toNat)) :
          OracleComp SphincsSecurity.HashSpec Digest)) := by
  have answer_words (i : Fin 5) :
      (initialEncodingState location hash s).getWord32
        (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
        (hash (hashInput (otsHashPrep location (otsPrelude location s)))).extractLsb'
          (32 * i.val) 32 := by
    have dst := (otsHashPrep_registers location (otsPrelude location s)).2.2.1
    fin_cases i <;>
      simp [initialEncodingState, writeHash, dst, MachineState.writeWords,
        MachineState.getWord32, alignToDword, byteOffset, extractWord32]
    all_goals ext j hj; interval_cases j <;> simp
  have value := SphincsMaskedChainDomain.eval_hash hash parameter
    (.encoding lay treeIdx leaf)
    (bytesLE 20 message ++ bytesLE 4 (BitVec.ofNat 32 counter.toNat))
  rw [value]
  intro i
  rw [answer_words, query]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.initial_encoding_digest_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initial_encoding_digest_words

def encodingQueryWord (s : MachineState) (i : Fin 16) : BitVec 32 :=
  if i.val = 0 then (0x401#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val = 1 then (s.getMem 0x43010).setWidth 32
  else if i.val = 2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val = 3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val = 4 then (s.getMem 0x43018).setWidth 32
  else if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x74 + 4*(i.val-5)))
  else if i.val < 15 then s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4*(i.val-10)))
  else extractWord32 (s.getMem 0x430b8) 0

theorem encoding_prepared_word (location : Fin 5) (s : MachineState) (i : Fin 16) :
    (otsHashPrep location s).getWord32 (BitVec.ofNat 64 (0x40000 + 4*i.val)) =
      encodingQueryWord s i := by
  fin_cases i <;>
    simp [otsHashPrep, otsHashPrepState, otsHashPrepCode, runSchedule,
      encodingQueryWord, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset,
      SphincsMaskedChainStep.extract_replace_low,
      SphincsMaskedChainStep.extract_replace_high,
      SphincsMaskedChainStep.extract_replace_high_other]


def EncodingContext (s : MachineState) (parameter message : Digest)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (counter : Counter) : Prop :=
  s.getMem 0x43000 = BitVec.ofNat 64 lay.val ∧
  s.getMem 0x43010 = 0 ∧
  s.getMem 0x43008 = BitVec.ofNat 64 treeIdx.val ∧
  s.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
  s.getMem 0x430b8 = BitVec.ofNat 64 counter.toNat ∧
  Words20 s 0x74 parameter ∧ Words20 s 0x44a00 message

def encodingPayload (parameter message : Digest) (lay : Layer)
    (treeIdx : TreeIndex) (leaf : LeafIndex) (counter : Counter) : List Byte :=
  (tweakableHashInput parameter (.encoding lay treeIdx leaf)
    (bytesLE 20 message ++ bytesLE 4 (BitVec.ofNat 32 counter.toNat))).map UInt8.toBitVec

theorem encodingPayload_length (parameter message : Digest) (lay : Layer)
    (treeIdx : TreeIndex) (leaf : LeafIndex) (counter : Counter) :
    (encodingPayload parameter message lay treeIdx leaf counter).length = 64 := by
  simp [encodingPayload, tweakableHashInput, tweakBytes, hashDomainFields,
    tweakFields, fieldBytes, bytesLE]

theorem encoding_prepared_byte (location : Fin 5) (s : MachineState) (i : Fin 64) :
    (otsHashPrep location s).getByte (BitVec.ofNat 64 (0x40000+i.val)) =
      (encodingQueryWord s ⟨i.val / 4, by omega⟩).extractLsb' (8*(i.val%4)) 8 := by
  have h := SphincsVerifierFtsGenericBytes.variableWord_byte (otsHashPrep location s)
    (0x40000 + 4*(i.val/4)) (by omega) (by omega)
    0 ⟨i.val%4, Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at h
  rw [show 0x40000 + 4*(i.val/4) + i.val%4 = 0x40000 + i.val by omega] at h
  rw [h, encoding_prepared_word location s ⟨i.val/4, by omega⟩]

private theorem ofNat_width_byte (n start : Nat) (h : start + 8 ≤ 32) :
    (BitVec.ofNat 32 n).extractLsb' start 8 =
      (BitVec.ofNat 64 n).extractLsb' start 8 := by
  rw [← BitVec.setWidth_ofNat_of_le (show 32 ≤ 64 by decide) n]
  exact BitVec.extractLsb'_setWidth_of_le h

theorem encoding_context_byte (s : MachineState) (parameter message : Digest)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (counter : Counter)
    (ctx : EncodingContext s parameter message lay treeIdx leaf counter) (i : Fin 64) :
    (encodingQueryWord s ⟨i.val/4, by omega⟩).extractLsb' (8*(i.val%4)) 8 =
      (encodingPayload parameter message lay treeIdx leaf counter)[i.val]'(by
        rw [encodingPayload_length]; exact i.isLt) := by
  obtain ⟨layer,zero,tree,index,ctr,par,msg⟩ := ctx
  have p0 := par 0
  have p1 := par 1
  have p2 := par 2
  have p3 := par 3
  have p4 := par 4
  have m0 := msg 0
  have m1 := msg 1
  have m2 := msg 2
  have m3 := msg 3
  have m4 := msg 4
  norm_num at p0 p1 p2 p3 p4 m0 m1 m2 m3 m4
  unfold encodingQueryWord
  simp only [layer, zero, tree, index, ctr]
  fin_cases i <;>
    simp [p0, p1, p2, p3, p4, m0, m1, m2, m3, m4,
      encodingPayload, tweakableHashInput, tweakBytes, hashDomainFields,
      tweakFields, fieldBytes, bytesLE, protocolDomainSep, extractWord32,
      BitVec.setWidth_ushiftRight_eq_extractLsb,
      SphincsMaskedSignForestDomain.nested_extract]


  case «8» => exact ofNat_width_byte treeIdx.val 0 (by decide)
  case «9» => exact ofNat_width_byte treeIdx.val 8 (by decide)
  case «10» => exact ofNat_width_byte treeIdx.val 16 (by decide)
  case «11» => exact ofNat_width_byte treeIdx.val 24 (by decide)
  case «0» => fin_cases lay <;> decide
  case «1» => fin_cases lay <;> decide
  case «2» => fin_cases lay <;> decide
  case «3» => fin_cases lay <;> decide


theorem encoding_context_query (location : Fin 5) (s : MachineState)
    (parameter message : Digest) (lay : Layer) (treeIdx : TreeIndex)
    (leaf : LeafIndex) (counter : Counter)
    (ctx : EncodingContext s parameter message lay treeIdx leaf counter) :
    hashInput (otsHashPrep location s) =
      toQuery (tweakableHashInput parameter (.encoding lay treeIdx leaf)
        (bytesLE 20 message ++ bytesLE 4 (BitVec.ofNat 32 counter.toNat))) := by
  apply Serialization.hashInput_of_list (otsHashPrep location s) 0x40000
    (encodingPayload parameter message lay treeIdx leaf counter)
  · exact (otsHashPrep_registers location s).1
  · rw [encodingPayload_length, (otsHashPrep_registers location s).2.1]
    rfl
  · intro i hi
    have bound : i < 64 := by simpa only [encodingPayload_length] using hi
    rw [encoding_prepared_byte location s ⟨i, bound⟩]
    exact encoding_context_byte s parameter message lay treeIdx leaf counter ctx ⟨i, bound⟩


theorem encoding_entry_context (location : Fin 5) (s : MachineState)
    (parameter message : Digest) (lay : Layer) (treeIdx : TreeIndex)
    (leaf : LeafIndex)
    (layer : s.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (tree : s.getMem 0x43008 = BitVec.ofNat 64 treeIdx.val)
    (selected : s.getMem 0x430a8 = BitVec.ofNat 64 leaf.val)
    (par : Words20 s 0x74 parameter)
    (msg : Words20 s 0x44a00 message) :
    EncodingContext (otsPrelude location s) parameter message lay treeIdx leaf (0 : Counter) := by
  have controls := otsPrelude_controls location s leaf.val selected
  refine ⟨?_, controls.2.2.1, ?_, controls.2.2.2, ?_, ?_, ?_⟩
  · rw [otsPrelude_frame location s 0x43000 (by decide)]
    exact layer
  · rw [otsPrelude_frame location s 0x43008 (by decide)]
    exact tree
  · simpa using controls.2.1
  · intro i
    rw [otsPrelude_low_word location s (0x74+4*i.val) (by omega)]
    exact par i
  · intro i
    have frame : (otsPrelude location s).getWord32
        (BitVec.ofNat 64 (0x44a00 + 4*i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4*i.val)) := by
      fin_cases i <;>
        simp [MachineState.getWord32, otsPrelude_frame, otsPreludeWrites,
          alignToDword, byteOffset]
    rw [frame]
    exact msg i


/-- The live WOTS entry fields determine the first encoding HASH query. -/
theorem encoding_entry_query (location : Fin 5) (s : MachineState)
    (parameter message : Digest) (lay : Layer) (treeIdx : TreeIndex)
    (leaf : LeafIndex)
    (layer : s.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (tree : s.getMem 0x43008 = BitVec.ofNat 64 treeIdx.val)
    (selected : s.getMem 0x430a8 = BitVec.ofNat 64 leaf.val)
    (par : Words20 s 0x74 parameter)
    (msg : Words20 s 0x44a00 message) :
    hashInput (otsHashPrep location (otsPrelude location s)) =
      toQuery (tweakableHashInput parameter (.encoding lay treeIdx leaf)
        (bytesLE 20 message ++ bytesLE 4 (BitVec.ofNat 32 (0 : Counter).toNat))) := by
  exact encoding_context_query location (otsPrelude location s) parameter message lay
    treeIdx leaf 0 (encoding_entry_context location s parameter message lay treeIdx leaf
      layer tree selected par msg)


/-- The first concrete HASH result equals the abstract encoding digest under the live entry fields. -/
theorem initial_encoding_digest_words_from_entry (location : Fin 5) (hash : Hash)
    (s : MachineState) (parameter : PublicParameter) (lay : Layer)
    (treeIdx : TreeIndex) (leaf : LeafIndex) (message : Digest)
    (layer : s.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (tree : s.getMem 0x43008 = BitVec.ofNat 64 treeIdx.val)
    (selected : s.getMem 0x430a8 = BitVec.ofNat 64 leaf.val)
    (par : Words20 s 0x74 parameter)
    (msg : Words20 s 0x44a00 message) :
    Words20 (initialEncodingState location hash s) 0x42000
      (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Concrete.tweakableHash parameter (.encoding lay treeIdx leaf)
          (bytesLE 20 message ++ bytesLE 4 (BitVec.ofNat 32 (0 : Counter).toNat)) :
          OracleComp SphincsSecurity.HashSpec Digest)) := by
  exact initial_encoding_digest_words location hash s parameter lay treeIdx leaf message 0
    (encoding_entry_query location s parameter message lay treeIdx leaf
      layer tree selected par msg)

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.encoding_entry_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encoding_entry_query

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.initial_encoding_digest_words_from_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initial_encoding_digest_words_from_entry

end SigGolfCandidate.SphincsMaskedSignOtsPathValue
