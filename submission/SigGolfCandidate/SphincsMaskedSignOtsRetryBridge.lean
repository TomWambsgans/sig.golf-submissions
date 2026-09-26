import SigGolfCandidate.SphincsMaskedSignOtsPathValue
import SigGolfCandidate.SphincsMaskedSignForestSemantics

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

/-- A path sibling copy does not touch the low parameter memory. -/
theorem pathNext_low_frame (location : Fin 5) (s : MachineState)
    (level bit pointer : Nat) (ctrl : PathControls location s level bit pointer)
    (lower : 0x100 ≤ pointer) (upper : pointer + 20 ≤ 0x40000)
    (a : Word) (low : a.toNat < 0x100) :
    (pathNext location s).getMem a = s.getMem a := by
  have outside : a ∉ controlWrites := by
    simp only [controlWrites, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, and_true]
    repeat' constructor
    all_goals
      intro h
      have hnat := congrArg BitVec.toNat h
      norm_num at hnat
      omega
  rw [pathNext, finish_frame location _ a outside]
  have regs := setup_regs location s level bit pointer ctrl
  rw [SphincsMaskedSignForestTail.copy_memory_frame _ pointer 0x100 0x40000
    regs.2 (by decide) lower upper (by decide) a (Or.inl low)]
  exact setup_frame location s a

/-- The finite path loop retains every low parameter cell. -/
theorem paths_execution_low_frame (location : Fin 5) (s : MachineState)
    (selected pointer : Nat)
    (pc : s.pc = 0x1938 + delta location)
    (ctrl : PathControls location s 0 selected pointer)
    (selectedBound : selected < Levels.width location 0)
    (pointerBound : pointer + 20 * Levels.height location ≤ 0x40000)
    (aligned : pointer % 4 = 0)
    (pointerLow : 0x100 ≤ pointer)
    (n : Nat) (bound : n ≤ Levels.height location) :
    ∃ t, OrdinarySteps SphincsMaskedImages.sign s (70*n) t ∧
      PathControls location t n (selected/2^n) (pointer+20*n) ∧
      t.pc=(if n=Levels.height location then 0x1a50+delta location
        else 0x1938+delta location) ∧
      ∀ a : Word, a.toNat < 0x100 → t.getMem a = s.getMem a := by
  induction n with
  | zero =>
      have positive : 0 < Levels.height location := by fin_cases location <;> decide
      refine ⟨s, OrdinarySteps.refl _, ?_, ?_, ?_⟩
      · simpa using ctrl
      · simpa only [if_neg (show 0 ≠ Levels.height location by omega)] using pc
      · intro _ _; rfl
  | succ n ih =>
      obtain ⟨mid, first, midCtrl, midPc, frame⟩ := ih (by omega)
      have here : mid.pc = 0x1938 + delta location := by
        simpa only [if_neg (show n ≠ Levels.height location by omega)] using midPc
      let level : Fin (Levels.height location) := ⟨n,by omega⟩
      have bitBound := divided_selector_bound location selected selectedBound level
      obtain ⟨step, done, loc⟩ := path_step location mid level (selected/2^n)
        (pointer+20*n) here midCtrl bitBound (by omega) (by omega)
      refine ⟨pathNext location mid, ?_, ?_, loc, ?_⟩
      · simpa only [Nat.mul_add,Nat.mul_one,Nat.add_comm] using first.append step
      · convert done using 1
        · simp [Nat.pow_succ,Nat.div_div_eq_div_mul]
        · omega
      · intro a low
        rw [pathNext_low_frame location mid n (selected/2^n) (pointer+20*n)
          midCtrl (by omega) (by omega) a low, frame a low]


private theorem ordinary_unique {image : Image}
    {start left right : MachineState} {n : Nat}
    (first : OrdinarySteps image start n left)
    (second : OrdinarySteps image start n right) : left = right := by
  induction first generalizing right with
  | refl state => cases second; rfl
  | step state next final instruction steps hf hs tail ih =>
      cases second with
      | step _ other _ otherInstruction _ hf' hs' tail' =>
          have instrEq := Option.some.inj (hf.symm.trans hf')
          subst otherInstruction
          have nextEq := Option.some.inj (hs.symm.trans hs')
          subst other
          exact ih tail'

/-- The exact path-data witness also retains low parameter cells. -/
theorem paths_execution_data_low_frame (location : Fin 5) (s : MachineState)
    (selected pointer : Nat)
    (pc : s.pc = 0x1938 + delta location)
    (ctrl : PathControls location s 0 selected pointer)
    (selectedBound : selected < Levels.width location 0)
    (pointerBound : pointer + 20 * Levels.height location ≤ 0x40000)
    (aligned : pointer % 4 = 0)
    (pointerLow : 0x100 ≤ pointer)
    (n : Nat) (bound : n ≤ Levels.height location) :
    ∃ t, OrdinarySteps SphincsMaskedImages.sign s (70*n) t ∧
      PathControls location t n (selected/2^n) (pointer+20*n) ∧
      t.pc=(if n=Levels.height location then 0x1a50+delta location
        else 0x1938+delta location) ∧
      (∀ a : Word, a.toNat < 0x100 → t.getMem a = s.getMem a) ∧
      (∀ a, OtsPathRetained a → t.getMem a = s.getMem a) ∧
      (∀ j : Fin n, ∀ i : Fin 5,
        t.getWord32 (BitVec.ofNat 64 (pointer+20*j.val+4*i.val)) =
        s.getWord32 (BitVec.ofNat 64
          (Levels.cacheBase location j.val+20*((selected/2^j.val) ^^^ 1)+4*i.val))) := by
  obtain ⟨t, run, controls, endPc, high, data⟩ :=
    paths_execution_data location s selected pointer pc ctrl selectedBound pointerBound
      aligned n bound
  obtain ⟨u, runLow, _, _, low⟩ :=
    paths_execution_low_frame location s selected pointer pc ctrl selectedBound
      pointerBound aligned pointerLow n bound
  have same : u = t := ordinary_unique runLow run
  subst u
  exact ⟨t, run, controls, endPc, low, high, data⟩


/-- The completed concrete path retains the signer query inputs. -/
theorem path_complete_input_frame (location : Fin 5) (hash : Hash)
    (s : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (treeIdx : TreeIndex) (selected : LeafIndex)
    (pc : s.pc = 0x18d8 + delta location)
    (selectedMem : s.getMem 0x430a8 = BitVec.ofNat 64 selected.val)
    (selectedBound : selected.val < Levels.width location 0)
    (cache : ∀ l, l ≤ Levels.height location → ∀ node,
      node < Levels.width location l →
      Words20 s (Levels.cacheBase location l+20*node)
        (treeValue hash parameter seed (signerLayer location) treeIdx l node)) :
    ∃ t, OrdinarySteps SphincsMaskedImages.sign s
      (24+70*Levels.height location) t ∧
      t.pc = 0x1a50+delta location ∧
      (∀ j : Fin (Levels.height location),
        let pathLevel : Fin (layerHeight (signerLayer location)) :=
          ⟨j.val,by rw [← signerLayer_height]; exact j.isLt⟩
        Words20 t (pathPointer location+20*j.val)
          (evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
            (Seeded.treePath parameter (signerLayer location) treeIdx seed selected :
              OracleComp SphincsSecurity.HashSpec
                (Fin (layerHeight (signerLayer location)) → Digest)) pathLevel)) ∧
      (∀ a : Word, a.toNat < 0x100 → t.getMem a = s.getMem a) ∧
      (∀ a, OtsPathRetained a → t.getMem a = s.getMem a) := by
  obtain ⟨t, run, done, values⟩ := path_complete location hash s parameter seed treeIdx
    selected pc selectedMem selectedBound cache
  have first : OrdinarySteps SphincsMaskedImages.sign s 24 (entryState location s) :=
    init_block location s pc
  have ctrl := entry_controls location s selected.val selectedMem
  have ptrLow : 0x100 ≤ pathPointer location := by fin_cases location <;> decide
  obtain ⟨u, rest, _, _, low, high, _⟩ := paths_execution_data_low_frame location
    (entryState location s) selected.val (pathPointer location)
    (entry_pc location s) ctrl selectedBound (pointer_height_bound location)
    (pointer_bound location).1 ptrLow (Levels.height location) (le_refl _)
  have same : u = t := ordinary_unique (first.append rest) run
  subst u
  refine ⟨t, run, done, values, ?_, ?_⟩
  · intro a ha
    rw [low a ha]
    simp only [entryState, shift_mem]
    rw [initialized_frame location _ a]
    · rfl
    · simp only [controlWrites,List.mem_cons,List.not_mem_nil,
        not_or,not_false_eq_true,and_true]
      repeat' constructor
      all_goals
        intro h
        have hnat := congrArg BitVec.toNat h
        norm_num at hnat
        omega
  · intro a ha
    rw [high a ha]
    simp only [entryState, shift_mem]
    rw [initialized_frame location _ a ha.2]
    rfl


/-- Subtree and path execution deliver the five live encoding-entry fields. -/
theorem subtree_root_path_encoding_entry (location : Fin 5) (hash : Hash)
    (s : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (treeIdx : TreeIndex) (selected : LeafIndex) (message : Digest)
    (pc : s.pc = 0x111c+chainDelta location)
    (counter : s.getMem 0x43020 = 0)
    (ctx : SphincsMaskedSignOtsParents.KeyContext s parameter seed
      (signerLayer location) treeIdx)
    (selectedMem : s.getMem 0x430a8 = BitVec.ofNat 64 selected.val)
    (selectedBound : selected.val < Levels.width location 0)
    (msg : Words20 s 0x44a00 message) :
    ∃ t, Trace hash SphincsMaskedImages.sign s
      (41220*SphincsMaskedSignOtsTree.Finish.width location+33+39*Levels.height location+
        124*Levels.totalNodes location (Levels.height location)+
        (24+70*Levels.height location))
      (44683*SphincsMaskedSignOtsTree.Finish.width location+33+39*Levels.height location+
        139*Levels.totalNodes location (Levels.height location)+
        (24+70*Levels.height location))
      (417*SphincsMaskedSignOtsTree.Finish.width location+
        Levels.totalNodes location (Levels.height location))
      (485*SphincsMaskedSignOtsTree.Finish.width location+
        2*Levels.totalNodes location (Levels.height location)) t ∧
      t.pc = 0x1a50+delta location ∧
      t.getMem 0x43000 = BitVec.ofNat 64 (signerLayer location).val ∧
      t.getMem 0x43008 = BitVec.ofNat 64 treeIdx.val ∧
      t.getMem 0x430a8 = BitVec.ofNat 64 selected.val ∧
      Words20 t 0x74 parameter ∧ Words20 t 0x44a00 message := by
  obtain ⟨mid, rootRun, midPc, midCtx, _, cache, retained⟩ :=
    subtree_root location hash s parameter seed treeIdx pc counter ctx
  have midSelected : mid.getMem 0x430a8 = BitVec.ofNat 64 selected.val := by
    rw [retained 0x430a8 (by simp [SphincsMaskedSignOtsTree.Frame.Retained,
      SphincsMaskedSignOtsTree.Frame.controls]) (by decide) (by decide) (by decide)]
    exact selectedMem
  have midMessage : Words20 mid 0x44a00 message := by
    intro i
    have saved := msg i
    simp only [MachineState.getWord32] at saved ⊢
    rw [retained _ (by fin_cases i <;> simp [SphincsMaskedSignOtsTree.Frame.Retained,
      SphincsMaskedSignOtsTree.Frame.controls, alignToDword]) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact saved
  obtain ⟨t, pathRun, done, _, low, high⟩ :=
    path_complete_input_frame location hash mid parameter seed treeIdx selected
      midPc midSelected selectedBound cache
  have header (a : Word) (ret : OtsPathRetained a) : t.getMem a = mid.getMem a :=
    high a ret
  have wordLow (i : Fin 5) :
      t.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) =
        mid.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) := by
    simp only [MachineState.getWord32]
    rw [low _ (by fin_cases i <;> decide)]
  have wordHigh (i : Fin 5) :
      t.getWord32 (BitVec.ofNat 64 (0x44a00+4*i.val)) =
        mid.getWord32 (BitVec.ofNat 64 (0x44a00+4*i.val)) := by
    simp only [MachineState.getWord32]
    rw [high _ (by fin_cases i <;> decide)]
  refine ⟨t, ?_, done, ?_, ?_, ?_, ?_, ?_⟩
  · exact rootRun.trans pathRun.trace
  · exact (header _ (by simp [OtsPathRetained, controlWrites])).trans midCtx.1
  · exact (header _ (by simp [OtsPathRetained, controlWrites])).trans midCtx.2.1
  · exact (header _ (by simp [OtsPathRetained, controlWrites])).trans midSelected
  · intro i
    rw [wordLow i]
    exact midCtx.2.2.1 i
  · intro i
    rw [wordHigh i]
    exact midMessage i


/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.paths_execution_data_low_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paths_execution_data_low_frame

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.subtree_root_path_encoding_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms subtree_root_path_encoding_entry

def forestToOtsCode : List (Word × Instr) := [
  (0x2764, .ADDI .x6 .x0 0x005#12),
  (0x2768, .LUI .x28 0x00043#20),
  (0x276c, .ADDI .x28 .x28 0x000#12),
  (0x2770, .SD .x28 .x6 0x000#12),
  (0x2774, .LUI .x28 0x00043#20),
  (0x2778, .ADDI .x28 .x28 0x078#12),
  (0x277c, .LD .x6 .x28 0x000#12),
  (0x2780, .SRLI .x6 .x6 0x04#6),
  (0x2784, .LUI .x28 0x00043#20),
  (0x2788, .ADDI .x28 .x28 0x008#12),
  (0x278c, .SD .x28 .x6 0x000#12),
  (0x2790, .LUI .x28 0x00043#20),
  (0x2794, .ADDI .x28 .x28 0x078#12),
  (0x2798, .LD .x6 .x28 0x000#12),
  (0x279c, .SRLI .x6 .x6 0x00#6),
  (0x27a0, .ANDI .x6 .x6 0x00f#12),
  (0x27a4, .LUI .x28 0x00043#20),
  (0x27a8, .ADDI .x28 .x28 0x020#12),
  (0x27ac, .SD .x28 .x6 0x000#12),
  (0x27b0, .LUI .x28 0x00043#20),
  (0x27b4, .ADDI .x28 .x28 0x020#12),
  (0x27b8, .LD .x6 .x28 0x000#12),
  (0x27bc, .LUI .x28 0x00043#20),
  (0x27c0, .ADDI .x28 .x28 0x0a8#12),
  (0x27c4, .SD .x28 .x6 0x000#12),
  (0x27c8, .ADDI .x6 .x0 0x000#12),
  (0x27cc, .LUI .x28 0x00043#20),
  (0x27d0, .ADDI .x28 .x28 0x020#12),
  (0x27d4, .SD .x28 .x6 0x000#12)]

def forestToOtsState (s : MachineState) : MachineState := runSchedule forestToOtsCode s

private def code0 := forestToOtsCode.take 5
private def code1 := (forestToOtsCode.drop 5).take 5
private def code2 := (forestToOtsCode.drop 10).take 5
private def code3 := (forestToOtsCode.drop 15).take 5
private def code4 := (forestToOtsCode.drop 20).take 5
private def code5 := forestToOtsCode.drop 25

private theorem image0 : DecodedBlock SphincsMaskedImages.sign 1497 code0 := by rfl
private theorem image1 : DecodedBlock SphincsMaskedImages.sign 1502 code1 := by rfl
private theorem image2 : DecodedBlock SphincsMaskedImages.sign 1507 code2 := by rfl
private theorem image3 : DecodedBlock SphincsMaskedImages.sign 1512 code3 := by rfl
private theorem image4 : DecodedBlock SphincsMaskedImages.sign 1517 code4 := by rfl
private theorem image5 : DecodedBlock SphincsMaskedImages.sign 1522 code5 := by rfl

private theorem encoded0 : ∀ e ∈ code0,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by
  have h := encoded_of_block _ 1497 _ 0 image0 (by decide)
    (by intro i; fin_cases i <;> decide)
  intro e he
  simpa [add_zero] using h e he

private theorem encoded1 : ∀ e ∈ code1,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by
  have h := encoded_of_block _ 1502 _ 0 image1 (by decide)
    (by intro i; fin_cases i <;> decide)
  intro e he
  simpa [add_zero] using h e he

private theorem encoded2 : ∀ e ∈ code2,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by
  have h := encoded_of_block _ 1507 _ 0 image2 (by decide)
    (by intro i; fin_cases i <;> decide)
  intro e he
  simpa [add_zero] using h e he

private theorem encoded3 : ∀ e ∈ code3,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by
  have h := encoded_of_block _ 1512 _ 0 image3 (by decide)
    (by intro i; fin_cases i <;> decide)
  intro e he
  simpa [add_zero] using h e he

private theorem encoded4 : ∀ e ∈ code4,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by
  have h := encoded_of_block _ 1517 _ 0 image4 (by decide)
    (by intro i; fin_cases i <;> decide)
  intro e he
  simpa [add_zero] using h e he

private theorem encoded5 : ∀ e ∈ code5,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by
  have h := encoded_of_block _ 1522 _ 0 image5 (by decide)
    (by intro i; fin_cases i <;> decide)
  intro e he
  simpa [add_zero] using h e he

theorem forestToOts_encoded : ∀ e ∈ forestToOtsCode,
    instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by
  have split : forestToOtsCode =
      code0 ++ code1 ++ code2 ++ code3 ++ code4 ++ code5 := by rfl
  intro e he
  rw [split] at he
  simp only [List.mem_append] at he
  rcases he with (((((h0 | h1) | h2) | h3) | h4) | h5)
  · exact encoded0 e h0
  · exact encoded1 e h1
  · exact encoded2 e h2
  · exact encoded3 e h3
  · exact encoded4 e h4
  · exact encoded5 e h5

theorem forestToOts_supported : ∀ e ∈ forestToOtsCode, Supported e.2 := by decide

theorem forestToOts_checked (s : MachineState) (pc : s.pc = 0x2764) :
    Checked forestToOtsCode s := by
  simp [forestToOtsCode, Checked, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

private theorem shift_zero (s : MachineState) : shift 0 s = s := by
  cases s
  simp [shift, MachineState.setPC]

theorem forestToOts_block (s : MachineState) (pc : s.pc = 0x2764) :
    OrdinarySteps SphincsMaskedImages.sign s 29 (forestToOtsState s) := by
  have block := block_shift SphincsMaskedImages.sign 0 forestToOtsCode
    forestToOts_supported
    (by intro e he; simpa [add_zero] using forestToOts_encoded e he)
    s (forestToOts_checked s pc)
  have length : forestToOtsCode.length = 29 := by decide
  simpa only [shift_zero, forestToOtsState, length] using block

theorem forestToOts_layer (s : MachineState) :
    (forestToOtsState s).getMem 0x43000 = 5 := by
  simp [forestToOtsState, forestToOtsCode, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem forestToOts_tree (s : MachineState) :
    (forestToOtsState s).getMem 0x43008 = s.getMem 0x43078 >>> 4 := by
  simp [forestToOtsState, forestToOtsCode, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem forestToOts_selected (s : MachineState) :
    (forestToOtsState s).getMem 0x430a8 = s.getMem 0x43078 &&& 15 := by
  simp [forestToOtsState, forestToOtsCode, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem forestToOts_counter (s : MachineState) :
    (forestToOtsState s).getMem 0x43020 = 0 := by
  simp [forestToOtsState, forestToOtsCode, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem forestToOts_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x43000#64) (h1 : a ≠ 0x43008#64)
    (h2 : a ≠ 0x43020#64) (h3 : a ≠ 0x430a8#64) :
    (forestToOtsState s).getMem a = s.getMem a := by
  simp [forestToOtsState, forestToOtsCode, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    h0, h1, h2, h3]

private theorem bottom_tree_val (index : Index) :
    (Concrete.treeIndexAt index bottomLayer).val = index.val / 16 := by
  have h : totalHeight - heightAbove bottomLayer = 4 := by decide
  simp [Concrete.treeIndexAt, h]

private theorem bottom_leaf_val (index : Index) :
    (Concrete.leafIndexAt index bottomLayer).val = index.val % 16 := by
  have h : heightBelow bottomLayer = 0 := by decide
  have h4 : layerHeight bottomLayer = 4 := by decide
  simp [Concrete.leafIndexAt, h, h4]

private theorem indexSmall (index : Index) : index.val < 2^64 := by
  have h := index.isLt
  norm_num [totalHeight] at h ⊢
  omega

theorem forestToOts_tree_index (s : MachineState) (index : Index)
    (hi : s.getMem 0x43078 = BitVec.ofNat 64 index.val) :
    (forestToOtsState s).getMem 0x43008 =
      BitVec.ofNat 64 (Concrete.treeIndexAt index bottomLayer).val := by
  rw [forestToOts_tree, hi, bottom_tree_val]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (indexSmall index)]
  rw [Nat.mod_eq_of_lt (by have hsmall := indexSmall index; omega)]

theorem forestToOts_leaf_index (s : MachineState) (index : Index)
    (hi : s.getMem 0x43078 = BitVec.ofNat 64 index.val) :
    (forestToOtsState s).getMem 0x430a8 =
      BitVec.ofNat 64 (Concrete.leafIndexAt index bottomLayer).val := by
  rw [forestToOts_selected, hi, bottom_leaf_val]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  change index.val % 2^64 &&& 15 = index.val % 16 % 2^64
  have hsmall := indexSmall index
  have hmod : index.val % 16 < 2^64 := by
    have h := Nat.mod_lt index.val (by decide : 0 < 16)
    omega
  have hand : index.val &&& 15 = index.val % 16 := by
    simpa using (Nat.and_two_pow_sub_one_eq_mod index.val 4)
  rw [Nat.mod_eq_of_lt hsmall, hand, Nat.mod_eq_of_lt hmod]

theorem forestToOts_pc (s : MachineState) (pc : s.pc = 0x2764) :
    (forestToOtsState s).pc = 0x27d8 := by
  simp [forestToOtsState, forestToOtsCode, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

theorem forestToOts_context (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (index : Index)
    (message : Digest)
    (ctx : SphincsMaskedSignForestSemantics.Context s parameter seed index)
    (msg : Words20 s 0x44a00 message) :
    SphincsMaskedSignOtsParents.KeyContext (forestToOtsState s) parameter seed
      bottomLayer (Concrete.treeIndexAt index bottomLayer) ∧
    (forestToOtsState s).getMem 0x43020 = 0 ∧
    (forestToOtsState s).getMem 0x430a8 =
      BitVec.ofNat 64 (Concrete.leafIndexAt index bottomLayer).val ∧
    Words20 (forestToOtsState s) 0x44a00 message := by
  obtain ⟨par,key,idx⟩ := ctx
  refine ⟨⟨?_,?_,?_,?_⟩,forestToOts_counter s,forestToOts_leaf_index s index idx,?_⟩
  · change (forestToOtsState s).getMem 0x43000 = (5#64)
    exact forestToOts_layer s
  · exact forestToOts_tree_index s index idx
  · intro i
    have saved := par i
    simp only [MachineState.getWord32] at saved ⊢
    rw [forestToOts_frame s _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)]
    exact saved
  · intro i
    have saved := key i
    simp only [MachineState.getWord32] at saved ⊢
    rw [forestToOts_frame s _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)]
    exact saved
  · intro i
    have saved := msg i
    simp only [MachineState.getWord32] at saved ⊢
    rw [forestToOts_frame s _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)]
    exact saved


/-- The forest digest reaches the first bottom-layer subtree entry. -/
theorem forest_complete_to_bottom_entry (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (index : Index)
    (pc : s.pc = 0x1cc8)
    (ctx : SphincsMaskedSignForestSemantics.Context s parameter seed index) :
    ∃ t, Trace hash SphincsMaskedImages.sign s
      (1915509+29) (2142908+29) 18433 30729 t ∧
      t.pc = 0x27d8 ∧
      SphincsMaskedSignOtsParents.KeyContext t parameter seed bottomLayer
        (Concrete.treeIndexAt index bottomLayer) ∧
      t.getMem 0x43020 = 0 ∧
      t.getMem 0x430a8 =
        BitVec.ofNat 64 (Concrete.leafIndexAt index bottomLayer).val ∧
      Words20 t 0x44a00
        (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
          (Seeded.ftsKey parameter index seed)) := by
  obtain ⟨mid, first, midPc, midCtx, _, message⟩ :=
    SphincsMaskedSignForestSemantics.forest_complete hash s parameter seed index pc ctx
  have next := forestToOts_block mid midPc
  have fields := forestToOts_context mid parameter seed index _ midCtx message
  refine ⟨forestToOtsState mid, ?_, forestToOts_pc mid midPc,
    fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩
  exact first.trans next.trace

/-- The actual forest completion reaches a certified bottom-layer encoding entry. -/
theorem forest_complete_to_bottom_encoding_entry (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (index : Index)
    (pc : s.pc = 0x1cc8)
    (ctx : SphincsMaskedSignForestSemantics.Context s parameter seed index) :
    ∃ t, Trace hash SphincsMaskedImages.sign s
      ((1915509+29)+
        (41220*SphincsMaskedSignOtsTree.Finish.width (4 : Fin 5)+33+
          39*Levels.height (4 : Fin 5)+
          124*Levels.totalNodes (4 : Fin 5) (Levels.height (4 : Fin 5))+
          (24+70*Levels.height (4 : Fin 5))))
      ((2142908+29)+
        (44683*SphincsMaskedSignOtsTree.Finish.width (4 : Fin 5)+33+
          39*Levels.height (4 : Fin 5)+
          139*Levels.totalNodes (4 : Fin 5) (Levels.height (4 : Fin 5))+
          (24+70*Levels.height (4 : Fin 5))))
      (18433 + (417*SphincsMaskedSignOtsTree.Finish.width (4 : Fin 5)+
        Levels.totalNodes (4 : Fin 5) (Levels.height (4 : Fin 5))))
      (30729 + (485*SphincsMaskedSignOtsTree.Finish.width (4 : Fin 5)+
        2*Levels.totalNodes (4 : Fin 5) (Levels.height (4 : Fin 5)))) t ∧
      t.pc = 0x1a50+delta (4 : Fin 5) ∧
      t.getMem 0x43000 = BitVec.ofNat 64 bottomLayer.val ∧
      t.getMem 0x43008 = BitVec.ofNat 64 (Concrete.treeIndexAt index bottomLayer).val ∧
      t.getMem 0x430a8 = BitVec.ofNat 64 (Concrete.leafIndexAt index bottomLayer).val ∧
      Words20 t 0x74 parameter ∧
      Words20 t 0x44a00
        (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
          (Seeded.ftsKey parameter index seed)) := by
  obtain ⟨mid, first, midPc, midCtx, midCounter, midSelected, midMsg⟩ :=
    forest_complete_to_bottom_entry hash s parameter seed index pc ctx
  have pc' : mid.pc = 0x111c + chainDelta (4 : Fin 5) := by
    simpa [chainDelta] using midPc
  have layerEq : signerLayer (4 : Fin 5) = bottomLayer := by
    apply Fin.ext
    decide
  have ctx' : SphincsMaskedSignOtsParents.KeyContext mid parameter seed
      (signerLayer (4 : Fin 5)) (Concrete.treeIndexAt index bottomLayer) := by
    rw [layerEq]
    exact midCtx
  have leafBound : (Concrete.leafIndexAt index bottomLayer).val <
      Levels.width (4 : Fin 5) 0 := by
    rw [bottom_leaf_val]
    change index.val % 16 < 16
    exact Nat.mod_lt _ (by decide)
  obtain ⟨t, second, done, lay, tree, selected, par, msg⟩ :=
    subtree_root_path_encoding_entry (4 : Fin 5) hash mid parameter seed
      (Concrete.treeIndexAt index bottomLayer)
      (Concrete.leafIndexAt index bottomLayer) _ pc' midCounter ctx' midSelected
      leafBound midMsg
  refine ⟨t, ?_, done, ?_, tree, selected, par, msg⟩
  · exact first.trans second
  · rw [← layerEq]
    exact lay

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.forestToOts_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forestToOts_block

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.forest_complete_to_bottom_encoding_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forest_complete_to_bottom_encoding_entry

/-- The forest key becomes the exact first bottom-layer WOTS encoding HASH digest. -/
theorem forest_complete_first_bottom_encoding_digest (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (index : Index)
    (pc : s.pc = 0x1cc8)
    (ctx : SphincsMaskedSignForestSemantics.Context s parameter seed index) :
    ∃ t, (∃ steps cycles calls blocks,
      Trace hash SphincsMaskedImages.sign s steps cycles calls blocks t) ∧
      Trace hash SphincsMaskedImages.sign t 81 88 1 1
        (initialEncodingState (4 : Fin 5) hash t) ∧
      Words20 (initialEncodingState (4 : Fin 5) hash t) 0x42000
        (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
          (Concrete.tweakableHash parameter
            (.encoding bottomLayer (Concrete.treeIndexAt index bottomLayer)
              (Concrete.leafIndexAt index bottomLayer))
            (bytesLE 20 (evalWithAnswerFn (spec := SphincsSecurity.HashSpec)
              (adaptOracle hash) (Seeded.ftsKey parameter index seed)) ++
              bytesLE 4 (BitVec.ofNat 32 (0 : Counter).toNat)) :
            OracleComp SphincsSecurity.HashSpec Digest)) := by
  obtain ⟨t, run, done, layer, tree, selected, par, msg⟩ :=
    forest_complete_to_bottom_encoding_entry hash s parameter seed index pc ctx
  have first := (initial_encoding_hash_exact (4 : Fin 5) hash t done).1
  have digest := initial_encoding_digest_words_from_entry (4 : Fin 5) hash t
    parameter bottomLayer (Concrete.treeIndexAt index bottomLayer)
    (Concrete.leafIndexAt index bottomLayer)
    (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
      (Seeded.ftsKey parameter index seed)) layer tree selected par msg
  exact ⟨t, ⟨_, _, _, _, run⟩, first, digest⟩

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.forest_complete_first_bottom_encoding_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forest_complete_first_bottom_encoding_digest


/-- A decodable abstract encoding digest clears the first concrete WOTS padding test. -/
private theorem digest_first_padding_clear (digest : Digest) (encoding : Encoding)
    (decoded : TargetSum.decodeDigest digest = some encoding) :
    (((digest.extractLsb' 72 8).setWidth 64) &&& (0xc0 : Word)) = 0 := by
  unfold TargetSum.decodeDigest at decoded
  split at decoded
  · rename_i h
    rcases h with ⟨h₁, h₂, h₃, h₄, hv⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [h₁, h₂]
  · simp at decoded

/-- The first concrete WOTS retry check accepts a decodable HASH digest. -/
theorem first_encoding_padding_of_decode (location : Fin 5) (s : MachineState)
    (digest : Digest) (encoding : Encoding)
    (words : Words20 s 0x42000 digest)
    (decoded : TargetSum.decodeDigest digest = some encoding) :
    (otsPaddingFirst location s).getReg .x10 = 0 := by
  rw [otsPaddingFirst_register]
  have byte := SphincsMaskedPublicKeyDomain.words20_byte s 0x42000 digest
    (by omega) (by decide) words ⟨9, by decide⟩
  have addr : (0x42000 + (9 : Nat)) = 0x42009 := by omega
  simp only [addr] at byte
  have b : s.getByte 0x42009 = digest.extractLsb' 72 8 := by
    convert byte using 1 <;> rfl
  rw [b]
  exact digest_first_padding_clear digest encoding decoded

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.first_encoding_padding_of_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_encoding_padding_of_decode


/-- The first padding test reads the digest without changing any memory byte. -/
private theorem otsPaddingFirst_byte (location : Fin 5) (s : MachineState)
    (address : Word) :
    (otsPaddingFirst location s).getByte address = s.getByte address := by
  simp [otsPaddingFirst, otsPaddingFirstState, otsPaddingFirstCode,
    runSchedule, execInstrBr, MachineState.getByte]

/-- A decodable abstract encoding digest clears the second concrete padding test. -/
private theorem digest_second_padding_clear (digest : Digest) (encoding : Encoding)
    (decoded : TargetSum.decodeDigest digest = some encoding) :
    (((digest.extractLsb' 152 8).setWidth 64) &&& (0xc0 : Word)) = 0 := by
  unfold TargetSum.decodeDigest at decoded
  split at decoded
  · rename_i h
    rcases h with ⟨h₁, h₂, h₃, h₄, hv⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [h₃, h₄]
  · simp at decoded

/-- The second concrete WOTS retry check accepts a decodable HASH digest. -/
theorem second_encoding_padding_of_decode (location : Fin 5) (s : MachineState)
    (digest : Digest) (encoding : Encoding)
    (words : Words20 s 0x42000 digest)
    (decoded : TargetSum.decodeDigest digest = some encoding) :
    (otsPaddingSecond location (otsPaddingFirst location s)).getReg .x10 = 0 := by
  rw [otsPaddingSecond_register]
  rw [otsPaddingFirst_byte]
  have byte := SphincsMaskedPublicKeyDomain.words20_byte s 0x42000 digest
    (by omega) (by decide) words ⟨19, by decide⟩
  have addr : (0x42000 + (19 : Nat)) = 0x42013 := by omega
  simp only [addr] at byte
  have b : s.getByte 0x42013 = digest.extractLsb' 152 8 := by
    convert byte using 1 <;> rfl
  rw [b]
  exact digest_second_padding_clear digest encoding decoded

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.second_encoding_padding_of_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms second_encoding_padding_of_decode

private theorem answerSum_as_nat_sum (n : Nat) (s : MachineState) :
    answerSum n s = BitVec.ofNat 64
      (∑ j ∈ Finset.range n,
        (answerWord ⟨j % 52, Nat.mod_lt _ (by decide)⟩ s &&& 7#64).toNat) := by
  induction n with
  | zero => simp [answerSum]
  | succ n ih =>
    simp only [answerSum, Finset.sum_range_succ, ih]
    rw [BitVec.ofNat_add]
    simp

private theorem answer_digit_value_of_digest (s : MachineState) (digest : Digest)
    (bytes : ∀ j : Fin 20,
      s.getByte (BitVec.ofNat 64 (0x42000 + j.val)) =
        digest.extractLsb' (8 * j.val) 8) (i : ChainIndex) :
    (answerWord i s &&& 7#64).toNat =
      (TargetSum.digestEncoding digest i).val := by
  have h := congrArg BitVec.toNat (answerDigit_digestEncoding s digest bytes i)
  have small : (answerWord i s &&& 7#64).toNat < 8 := by
    simp only [BitVec.toNat_and]
    exact Nat.lt_succ_of_le Nat.and_le_right
  change (answerWord i s &&& 7#64).toNat % 256 =
    (TargetSum.digestEncoding digest i).val % 256 at h
  rw [Nat.mod_eq_of_lt (by omega : (answerWord i s &&& 7#64).toNat < 256)] at h
  have digitSmall : (TargetSum.digestEncoding digest i).val < 256 := by
    have bound : (TargetSum.digestEncoding digest i).val < 8 := by
      simpa [SphincsSecurity.chainLength, SphincsSecurity.winternitzBits] using
        (TargetSum.digestEncoding digest i).isLt
    omega
  rw [Nat.mod_eq_of_lt digitSmall] at h
  exact h

private theorem answerSum_of_valid_digest (s : MachineState) (digest : Digest)
    (bytes : ∀ j : Fin 20,
      s.getByte (BitVec.ofNat 64 (0x42000 + j.val)) =
        digest.extractLsb' (8 * j.val) 8)
    (valid : TargetSum.Valid (TargetSum.digestEncoding digest)) :
    answerSum 52 s = 194 := by
  rw [answerSum_as_nat_sum]
  have hsum : (∑ j ∈ Finset.range 52,
      (answerWord ⟨j % 52, Nat.mod_lt _ (by decide)⟩ s &&& 7#64).toNat) =
      TargetSum.sum (TargetSum.digestEncoding digest) := by
    rw [TargetSum.sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have small : j.val < 52 := j.isLt
    simpa [Nat.mod_eq_of_lt small] using
      answer_digit_value_of_digest s digest bytes j
  rw [hsum]
  simp [TargetSum.Valid, targetSum] at valid
  simp [valid]

private theorem otsPaddingSecond_byte (location : Fin 5) (s : MachineState) (address : Word) :
    (otsPaddingSecond location s).getByte address = s.getByte address := by
  simp [otsPaddingSecond, otsPaddingSecondState, otsPaddingSecondCode,
    runSchedule, execInstrBr, MachineState.getByte]

private theorem sumInit_byte (s : MachineState) (address : Word) :
    (sumInit s).getByte address = s.getByte address := by
  simp [sumInit, execInstrBr, MachineState.getByte]

/-- A decodable abstract WOTS HASH digest passes the concrete 52-digit checksum. -/
theorem encoding_checksum_of_decode (location : Fin 5) (s : MachineState)
    (digest : Digest) (encoding : Encoding)
    (words : Words20 s 0x42000 digest)
    (decoded : TargetSum.decodeDigest digest = some encoding) :
    answerSum 52 (sumInit (otsPaddingSecond location (otsPaddingFirst location s))) = 194 := by
  have bytes : ∀ j : Fin 20,
      (sumInit (otsPaddingSecond location (otsPaddingFirst location s))).getByte
        (BitVec.ofNat 64 (0x42000 + j.val)) =
        digest.extractLsb' (8 * j.val) 8 := by
    intro j
    rw [sumInit_byte, otsPaddingSecond_byte, otsPaddingFirst_byte]
    exact SphincsMaskedPublicKeyDomain.words20_byte s 0x42000 digest
      (by omega) (by decide) words j
  have valid : TargetSum.Valid (TargetSum.digestEncoding digest) := by
    unfold TargetSum.decodeDigest at decoded
    split at decoded
    · rename_i h
      exact h.2.2.2.2
    · simp at decoded
  exact answerSum_of_valid_digest _ _ bytes valid

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.encoding_checksum_of_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encoding_checksum_of_decode

def bottomEncodingDigest (hash : Hash) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) : Digest :=
  evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
    (Concrete.tweakableHash parameter
      (.encoding bottomLayer (Concrete.treeIndexAt index bottomLayer)
        (Concrete.leafIndexAt index bottomLayer))
      (bytesLE 20 (evalWithAnswerFn (spec := SphincsSecurity.HashSpec)
        (adaptOracle hash) (Seeded.ftsKey parameter index seed)) ++
        bytesLE 4 (BitVec.ofNat 32 (0 : Counter).toNat)) :
      OracleComp SphincsSecurity.HashSpec Digest)

theorem forest_complete_first_bottom_encoding_accepted (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (index : Index)
    (encoding : Encoding) (pc : s.pc = 0x1cc8)
    (ctx : SphincsMaskedSignForestSemantics.Context s parameter seed index)
    (decoded : TargetSum.decodeDigest
      (bottomEncodingDigest hash parameter seed index) = some encoding) :
    ∃ t u, (∃ steps cycles calls blocks,
      Trace hash SphincsMaskedImages.sign s steps cycles calls blocks t) ∧
      Trace hash SphincsMaskedImages.sign t 590 597 1 1 u ∧
      u.pc = 0x23cc + delta (4 : Fin 5) ∧
      u.getByte (BitVec.ofNat 64 0x44000) =
        BitVec.ofNat 8 (encoding (⟨0, by decide⟩ : ChainIndex)).val := by
  obtain ⟨t, run, done, layer, tree, selected, par, msg⟩ :=
    forest_complete_to_bottom_encoding_entry hash s parameter seed index pc ctx
  have words : Words20 (initialEncodingState (4 : Fin 5) hash t) 0x42000
      (bottomEncodingDigest hash parameter seed index) := by
    exact initial_encoding_digest_words_from_entry (4 : Fin 5) hash t
      parameter bottomLayer (Concrete.treeIndexAt index bottomLayer)
      (Concrete.leafIndexAt index bottomLayer)
      (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.ftsKey parameter index seed)) layer tree selected par msg
  have p1 := first_encoding_padding_of_decode (4 : Fin 5)
    (initialEncodingState (4 : Fin 5) hash t)
    (bottomEncodingDigest hash parameter seed index) encoding words decoded
  have p2 := second_encoding_padding_of_decode (4 : Fin 5)
    (initialEncodingState (4 : Fin 5) hash t)
    (bottomEncodingDigest hash parameter seed index) encoding words decoded
  have good := encoding_checksum_of_decode (4 : Fin 5)
    (initialEncodingState (4 : Fin 5) hash t)
    (bottomEncodingDigest hash parameter seed index) encoding words decoded
  have failed : ∀ j, j < 0 →
      let st := fullRetryStates (4 : Fin 5) hash
        (initialEncodingState (4 : Fin 5) hash t) j
      (otsPaddingFirst (4 : Fin 5) st).getReg .x10 = 0 ∧
      (otsPaddingSecond (4 : Fin 5) (otsPaddingFirst (4 : Fin 5) st)).getReg .x10 = 0 ∧
      answerSum 52 (sumInit (otsPaddingSecond (4 : Fin 5)
        (otsPaddingFirst (4 : Fin 5) st))) ≠ 194 ∧
      st.getMem 0x430b8 + 1 ≠ (2 ^ 20 : Word) := by
    intro j hj
    omega
  obtain ⟨accepted, endPc⟩ := encoding_success_from_entry
    (4 : Fin 5) hash t done 0 failed
    (by simpa [fullRetryStates] using p1)
    (by simpa [fullRetryStates] using p2)
    (by simpa [fullRetryStates] using good)
  have bytes : ∀ j : Fin 20,
      (sumInit (otsPaddingSecond (4 : Fin 5)
        (otsPaddingFirst (4 : Fin 5)
          (initialEncodingState (4 : Fin 5) hash t)))).getByte
        (BitVec.ofNat 64 (0x42000 + j.val)) =
        (bottomEncodingDigest hash parameter seed index).extractLsb' (8 * j.val) 8 := by
    intro j
    rw [sumInit_byte, otsPaddingSecond_byte, otsPaddingFirst_byte]
    exact SphincsMaskedPublicKeyDomain.words20_byte _ 0x42000 _
      (by omega) (by decide) words j
  have digit := encoding_success_abstract_digit (4 : Fin 5)
    (initialEncodingState (4 : Fin 5) hash t)
    (bottomEncodingDigest hash parameter seed index) encoding bytes decoded
    (⟨0, by decide⟩ : ChainIndex)
  refine ⟨t, encodingSuccessState (4 : Fin 5)
    (initialEncodingState (4 : Fin 5) hash t),
    ⟨_, _, _, _, run⟩, ?_, ?_, ?_⟩
  · simpa [fullRetryStates] using accepted
  · simpa [fullRetryStates] using endPc
  · simpa using digit


/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.forest_complete_first_bottom_encoding_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forest_complete_first_bottom_encoding_accepted

/-- The first bottom-layer signer seed-copy loop is the protected six-instruction
    word-copy idiom, repeated four times for the 32-byte secret key. -/
theorem first_bottom_secret_copy_code :
    CopyCode SphincsMaskedImages.sign 0x3b08 := by decide

theorem first_bottom_secret_copy (s : MachineState)
    (pc : s.pc = 0x3b08)
    (source : s.getReg .x6 = 0x20)
    (destination : s.getReg .x7 = 0x40028)
    (count : s.getReg .x10 = 4) :
    ∃ t, OrdinarySteps SphincsMaskedImages.sign s 24 t ∧
      t.pc = 0x3b20 ∧
      (∀ i, i < 4 → t.getMem (wordAddress 0x40028 i) =
        s.getMem (wordAddress 0x20 i)) := by
  have inv : CopyInvariant 0x3b08 0x20 0x40028 4 4 s := by
    exact ⟨by decide, by decide, by simpa using pc,
      by simpa using source, by simpa using destination, by simpa using count⟩
  obtain ⟨t, copied, done, values, _⟩ := copy_all
    SphincsMaskedImages.sign 0x3b08 first_bottom_secret_copy_code
    0x20 0x40028 4 s inv (by decide) (by decide) (by decide) (by decide)
    (Or.inl (by decide))
  exact ⟨t, by simpa using copied, by simpa [CopyInvariant] using done.2.2.1, values⟩

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.first_bottom_secret_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_bottom_secret_copy

end SigGolfCandidate.SphincsMaskedSignOtsPathValue
