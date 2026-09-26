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

end SigGolfCandidate.SphincsMaskedSignOtsPathValue
