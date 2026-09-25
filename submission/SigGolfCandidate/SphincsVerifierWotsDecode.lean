import SigGolfCandidate.SphincsVerifierMessageCopy

namespace SigGolfCandidate.SphincsVerifierWotsDecode
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def digitBit (i : Nat) : Nat := 3 * i + if i < 26 then 0 else 2

def digitWords (i : Nat) : Nat :=
  if digitBit i % 8 = 0 then 8
  else if digitBit i % 8 < 6 then 9 else 12

def digitStart (i : Nat) : Nat :=
  968 + ((List.range i).map digitWords).sum

def suffixStart (i : Nat) : Nat := digitStart i + digitWords i - 5

/-- All 52 statically unrolled decoders start by loading the SHA answer and
    extracting the byte containing their three-bit WOTS digit. -/
theorem decoder_prefix_code (i : Fin 52) :
    (SphincsImages.verify.code[digitStart i.val]?).bind decodeInstruction =
      some (.base (.LUI .x6 0x42)) ∧
    (SphincsImages.verify.code[digitStart i.val + 1]?).bind decodeInstruction =
      some (.base (.ADDI .x6 .x6 0)) ∧
    (SphincsImages.verify.code[digitStart i.val + 2]?).bind decodeInstruction =
      some (.base (.LBU .x10 .x6 (BitVec.ofNat 12 (digitBit i.val / 8)))) := by
  fin_cases i <;> decide

theorem decoder_suffix_code (i : Fin 52) :
    (SphincsImages.verify.code[suffixStart i.val]?).bind decodeInstruction =
      some (.base (.ANDI .x10 .x10 7)) ∧
    (SphincsImages.verify.code[suffixStart i.val + 1]?).bind decodeInstruction =
      some (.base (.ADD .x15 .x15 .x10)) ∧
    (SphincsImages.verify.code[suffixStart i.val + 2]?).bind decodeInstruction =
      some (.base (.LUI .x6 0x44)) ∧
    (SphincsImages.verify.code[suffixStart i.val + 3]?).bind decodeInstruction =
      some (.base (.ADDI .x6 .x6 (i.val))) ∧
    (SphincsImages.verify.code[suffixStart i.val + 4]?).bind decodeInstruction =
      some (.base (.SB .x6 .x10 0)) := by
  fin_cases i <;> decide

theorem decoder_shift_code (i : Fin 52) :
    (digitBit i.val % 8 ≠ 0 →
      (SphincsImages.verify.code[digitStart i.val + 3]?).bind decodeInstruction =
        some (.base (.SRLI .x10 .x10 (BitVec.ofNat 6 (digitBit i.val % 8))))) ∧
    (digitBit i.val % 8 > 5 →
      (SphincsImages.verify.code[digitStart i.val + 4]?).bind decodeInstruction =
        some (.base (.LBU .x11 .x6 (BitVec.ofNat 12 (digitBit i.val / 8 + 1)))) ∧
      (SphincsImages.verify.code[digitStart i.val + 5]?).bind decodeInstruction =
        some (.base (.SLLI .x11 .x11 (BitVec.ofNat 6 (8 - digitBit i.val % 8)))) ∧
      (SphincsImages.verify.code[digitStart i.val + 6]?).bind decodeInstruction =
        some (.base (.ADD .x10 .x10 .x11))) := by
  fin_cases i <;> decide

def decoderPrefixState (i : Fin 52) (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x42)
  let state := execInstrBr state (.ADDI .x6 .x6 0)
  execInstrBr state (.LBU .x10 .x6 (BitVec.ofNat 12 (digitBit i.val / 8)))

theorem decoder_prefix_block (i : Fin 52) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * digitStart i.val)) :
    OrdinarySteps SphincsImages.verify state 3
      (decoderPrefixState i state) ∧
    (decoderPrefixState i state).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (digitStart i.val + 3)) ∧
    (decoderPrefixState i state).getReg .x6 = 0x42000 := by
  let s1 := execInstrBr state (.LUI .x6 0x42)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LBU .x10 .x6 (BitVec.ofNat 12 (digitBit i.val / 8)))
  have hcode := decoder_prefix_code i
  have p1 : s1.pc = BitVec.ofNat 64
      (0x1000 + 4 * (digitStart i.val + 1)) := by
    simp [s1, execInstrBr, pc, ← BitVec.ofNat_add]
    congr 1
  have p2 : s2.pc = BitVec.ofNat 64
      (0x1000 + 4 * (digitStart i.val + 2)) := by
    simp [s2, execInstrBr, p1, ← BitVec.ofNat_add]
    congr 1
  have source : s2.getReg .x6 = 0x42000 := by
    simp [s2, s1, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have valid : memoryArgumentsValid s2
      (.LBU .x10 .x6 (BitVec.ofNat 12 (digitBit i.val / 8))) = true := by
    simp only [memoryArgumentsValid, source]
    fin_cases i <;> decide
  have trace : OrdinarySteps SphincsImages.verify state 3 s3 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x42)) 2
    · rw [fetch_index SphincsImages.verify state (digitStart i.val)
        (by fin_cases i <;> decide) pc]
      exact hcode.1
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 1
    · rw [fetch_index SphincsImages.verify s1 (digitStart i.val + 1)
        (by fin_cases i <;> decide) p1]
      exact hcode.2.1
    · rfl
    apply OrdinarySteps.step s2 s3 _
      (.base (.LBU .x10 .x6 (BitVec.ofNat 12 (digitBit i.val / 8)))) 0
    · rw [fetch_index SphincsImages.verify s2 (digitStart i.val + 2)
        (by fin_cases i <;> decide) p2]
      exact hcode.2.2
    · simp [s3, ordinaryStep, valid]
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [decoderPrefixState] using trace, ?_, ?_⟩
  · change s3.pc = _
    simp [s3, execInstrBr, p2, ← BitVec.ofNat_add]
    congr 1
  · change s3.getReg .x6 = _
    simpa [s3, execInstrBr, MachineState.getReg_setReg_ne] using source

def decoderSuffixState (i : Fin 52) (state : MachineState) : MachineState :=
  let state := execInstrBr state (.ANDI .x10 .x10 7)
  let state := execInstrBr state (.ADD .x15 .x15 .x10)
  let state := execInstrBr state (.LUI .x6 0x44)
  let state := execInstrBr state (.ADDI .x6 .x6 i.val)
  execInstrBr state (.SB .x6 .x10 0)

theorem decoder_suffix_block (i : Fin 52) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * suffixStart i.val)) :
    OrdinarySteps SphincsImages.verify state 5
      (decoderSuffixState i state) ∧
    (decoderSuffixState i state).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (suffixStart i.val + 5)) := by
  let s1 := execInstrBr state (.ANDI .x10 .x10 7)
  let s2 := execInstrBr s1 (.ADD .x15 .x15 .x10)
  let s3 := execInstrBr s2 (.LUI .x6 0x44)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 i.val)
  let s5 := execInstrBr s4 (.SB .x6 .x10 0)
  have hcode := decoder_suffix_code i
  have p1 : s1.pc = BitVec.ofNat 64
      (0x1000 + 4 * (suffixStart i.val + 1)) := by
    simp [s1, execInstrBr, pc, ← BitVec.ofNat_add]
    congr 1
  have p2 : s2.pc = BitVec.ofNat 64
      (0x1000 + 4 * (suffixStart i.val + 2)) := by
    simp [s2, execInstrBr, p1, ← BitVec.ofNat_add]
    congr 1
  have p3 : s3.pc = BitVec.ofNat 64
      (0x1000 + 4 * (suffixStart i.val + 3)) := by
    simp [s3, execInstrBr, p2, ← BitVec.ofNat_add]
    congr 1
  have p4 : s4.pc = BitVec.ofNat 64
      (0x1000 + 4 * (suffixStart i.val + 4)) := by
    simp [s4, execInstrBr, p3, ← BitVec.ofNat_add]
    congr 1
  have destination : s4.getReg .x6 = BitVec.ofNat 64 (0x44000 + i.val) := by
    fin_cases i <;> simp [s4, s3, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have valid : memoryArgumentsValid s4 (.SB .x6 .x10 0) = true := by
    simp only [memoryArgumentsValid, destination]
    fin_cases i <;> decide
  have trace : OrdinarySteps SphincsImages.verify state 5 s5 := by
    apply OrdinarySteps.step state s1 _ (.base (.ANDI .x10 .x10 7)) 4
    · rw [fetch_index SphincsImages.verify state (suffixStart i.val)
        (by fin_cases i <;> decide) pc]
      exact hcode.1
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADD .x15 .x15 .x10)) 3
    · rw [fetch_index SphincsImages.verify s1 (suffixStart i.val + 1)
        (by fin_cases i <;> decide) p1]
      exact hcode.2.1
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x6 0x44)) 2
    · rw [fetch_index SphincsImages.verify s2 (suffixStart i.val + 2)
        (by fin_cases i <;> decide) p2]
      exact hcode.2.2.1
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 i.val)) 1
    · rw [fetch_index SphincsImages.verify s3 (suffixStart i.val + 3)
        (by fin_cases i <;> decide) p3]
      exact hcode.2.2.2.1
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.SB .x6 .x10 0)) 0
    · rw [fetch_index SphincsImages.verify s4 (suffixStart i.val + 4)
        (by fin_cases i <;> decide) p4]
      exact hcode.2.2.2.2
    · simp [s5, ordinaryStep, memoryArgumentsValid, destination,
        signExtend12, accessValid, rangeValid, MEMORY_BYTES]
      fin_cases i <;> decide
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [decoderSuffixState] using trace, ?_⟩
  change s5.pc = _
  simp [s5, execInstrBr, p4, ← BitVec.ofNat_add]
  congr 1

def decoderMiddleState (i : Fin 52) (state : MachineState) : MachineState :=
  let shift := digitBit i.val % 8
  if shift = 0 then state
  else
    let state := execInstrBr state (.SRLI .x10 .x10 (BitVec.ofNat 6 shift))
    if shift ≤ 5 then state
    else
      let state := execInstrBr state
        (.LBU .x11 .x6 (BitVec.ofNat 12 (digitBit i.val / 8 + 1)))
      let state := execInstrBr state (.SLLI .x11 .x11 (BitVec.ofNat 6 (8 - shift)))
      execInstrBr state (.ADD .x10 .x10 .x11)

theorem decoder_middle_block (i : Fin 52) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (digitStart i.val + 3)))
    (source : state.getReg .x6 = 0x42000) :
    OrdinarySteps SphincsImages.verify state (digitWords i.val - 8)
      (decoderMiddleState i state) ∧
    (decoderMiddleState i state).pc =
      BitVec.ofNat 64 (0x1000 + 4 * suffixStart i.val) ∧
    (decoderMiddleState i state).getReg .x6 = 0x42000 := by
  let shift := digitBit i.val % 8
  by_cases hz : shift = 0
  · have words : digitWords i.val = 8 := by simp [digitWords, shift, hz]
    have start : suffixStart i.val = digitStart i.val + 3 := by
      simp [suffixStart, words]
    simp [decoderMiddleState, shift, hz, words, start, pc, source,
      OrdinarySteps.refl]
  · let s1 := execInstrBr state (.SRLI .x10 .x10 (BitVec.ofNat 6 shift))
    have code1 := (decoder_shift_code i).1 hz
    have p1 : s1.pc = BitVec.ofNat 64
        (0x1000 + 4 * (digitStart i.val + 4)) := by
      simp [s1, execInstrBr, pc, ← BitVec.ofNat_add]
      congr 1
    have source1 : s1.getReg .x6 = 0x42000 := by
      simpa [s1, execInstrBr, MachineState.getReg_setReg_ne] using source
    have first : OrdinarySteps SphincsImages.verify state 1 s1 := by
      apply OrdinarySteps.step state s1 _
        (.base (.SRLI .x10 .x10 (BitVec.ofNat 6 shift))) 0
      · rw [fetch_index SphincsImages.verify state (digitStart i.val + 3)
          (by fin_cases i <;> decide) pc]
        exact code1
      · rfl
      exact OrdinarySteps.refl _
    by_cases hsmall : shift ≤ 5
    · have words : digitWords i.val = 9 := by
        simp [digitWords, shift, hz]
        omega
      have start : suffixStart i.val = digitStart i.val + 4 := by
        simp [suffixStart, words]
      refine ⟨?_, ?_, ?_⟩
      · simpa [decoderMiddleState, shift, hz, hsmall, words] using first
      · simpa [decoderMiddleState, shift, hz, hsmall, start] using p1
      · simpa [decoderMiddleState, shift, hz, hsmall] using source1
    · have hlarge : shift > 5 := by omega
      have words : digitWords i.val = 12 := by
        simp [digitWords, shift, hz]
        omega
      have start : suffixStart i.val = digitStart i.val + 7 := by
        simp [suffixStart, words]
      let s2 := execInstrBr s1
        (.LBU .x11 .x6 (BitVec.ofNat 12 (digitBit i.val / 8 + 1)))
      let s3 := execInstrBr s2 (.SLLI .x11 .x11 (BitVec.ofNat 6 (8 - shift)))
      let s4 := execInstrBr s3 (.ADD .x10 .x10 .x11)
      have code := (decoder_shift_code i).2 hlarge
      have p2 : s2.pc = BitVec.ofNat 64
          (0x1000 + 4 * (digitStart i.val + 5)) := by
        simp [s2, execInstrBr, p1, ← BitVec.ofNat_add]
        congr 1
      have p3 : s3.pc = BitVec.ofNat 64
          (0x1000 + 4 * (digitStart i.val + 6)) := by
        simp [s3, execInstrBr, p2, ← BitVec.ofNat_add]
        congr 1
      have p4 : s4.pc = BitVec.ofNat 64
          (0x1000 + 4 * (digitStart i.val + 7)) := by
        simp [s4, execInstrBr, p3, ← BitVec.ofNat_add]
        congr 1
      have valid : memoryArgumentsValid s1
          (.LBU .x11 .x6 (BitVec.ofNat 12 (digitBit i.val / 8 + 1))) = true := by
        simp only [memoryArgumentsValid, source1]
        fin_cases i <;> decide
      have rest : OrdinarySteps SphincsImages.verify s1 3 s4 := by
        apply OrdinarySteps.step s1 s2 _
          (.base (.LBU .x11 .x6 (BitVec.ofNat 12 (digitBit i.val / 8 + 1)))) 2
        · rw [fetch_index SphincsImages.verify s1 (digitStart i.val + 4)
            (by fin_cases i <;> decide) p1]
          exact code.1
        · simp [s2, ordinaryStep, valid]
        apply OrdinarySteps.step s2 s3 _
          (.base (.SLLI .x11 .x11 (BitVec.ofNat 6 (8 - shift)))) 1
        · rw [fetch_index SphincsImages.verify s2 (digitStart i.val + 5)
            (by fin_cases i <;> decide) p2]
          exact code.2.1
        · rfl
        apply OrdinarySteps.step s3 s4 _
          (.base (.ADD .x10 .x10 .x11)) 0
        · rw [fetch_index SphincsImages.verify s3 (digitStart i.val + 6)
            (by fin_cases i <;> decide) p3]
          exact code.2.2
        · rfl
        exact OrdinarySteps.refl _
      refine ⟨?_, ?_, ?_⟩
      · simpa [decoderMiddleState, shift, hz, hsmall, words] using first.append rest
      · simpa [decoderMiddleState, shift, hz, hsmall, start] using p4
      · have source4 : s4.getReg .x6 = 0x42000 := by
          simpa [s4, s3, s2, execInstrBr,
            MachineState.getReg_setReg_ne] using source1
        simpa [decoderMiddleState, shift, hz, hsmall] using source4

def decoderState (i : Fin 52) (state : MachineState) : MachineState :=
  decoderSuffixState i (decoderMiddleState i (decoderPrefixState i state))

theorem decoder_block (i : Fin 52) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * digitStart i.val)) :
    OrdinarySteps SphincsImages.verify state (digitWords i.val)
      (decoderState i state) ∧
    (decoderState i state).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (digitStart i.val + digitWords i.val)) := by
  have first := decoder_prefix_block i state pc
  have middle := decoder_middle_block i (decoderPrefixState i state)
    first.2.1 first.2.2
  have suffix := decoder_suffix_block i
    (decoderMiddleState i (decoderPrefixState i state)) middle.2.1
  have width : 8 ≤ digitWords i.val := by fin_cases i <;> decide
  have count : 3 + (digitWords i.val - 8) + 5 = digitWords i.val := by
    omega
  have finish : suffixStart i.val + 5 =
      digitStart i.val + digitWords i.val := by
    simp [suffixStart]
    omega
  refine ⟨?_, ?_⟩
  · simpa only [decoderState, count] using
      (first.1.append middle.1).append suffix.1
  · simpa only [decoderState, finish] using suffix.2

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecode.decoder_prefix_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_prefix_code

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecode.decoder_suffix_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_suffix_code

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecode.decoder_shift_code' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_shift_code

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecode.decoder_prefix_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_prefix_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecode.decoder_suffix_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_suffix_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecode.decoder_middle_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_middle_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecode.decoder_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decoder_block

end SigGolfCandidate.SphincsVerifierWotsDecode
