import SigGolfCandidate.SphincsVerifierWotsDecode
import SigGolfCandidate.SphincsVerifierLeaf0

namespace SigGolfCandidate.SphincsVerifierWotsDecodeData
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsDecode
open SigGolfCandidate.SphincsVerifierLeaf0
set_option maxRecDepth 16384
set_option maxHeartbeats 0

@[simp] private theorem getByte_setPC (s : MachineState) (pc a : Word) :
    (s.setPC pc).getByte a = s.getByte a := by
  simp [MachineState.getByte]

@[simp] private theorem getReg_setByte (s : MachineState) (a : Word)
    (b : Byte) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by
  simp [MachineState.setByte]

@[simp] private theorem getByte_setReg (s : MachineState) (r : Reg)
    (v a : Word) :
    (s.setReg r v).getByte a = s.getByte a := by
  simp [MachineState.getByte]

theorem decoder_suffix_byte (i : Fin 52) (state : MachineState) :
    (decoderSuffixState i state).getByte
      (BitVec.ofNat 64 (0x44000 + i.val)) =
      ((state.getReg .x10 &&& 7#64).truncate 8) := by
  fin_cases i <;>
    simp [decoderSuffixState, execInstrBr, signExtend12,
      getByte_setByte,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem decoder_suffix_sum (i : Fin 52) (state : MachineState) :
    (decoderSuffixState i state).getReg .x15 =
      state.getReg .x15 + (state.getReg .x10 &&& 7#64) := by
  simp [decoderSuffixState, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem decoder_prefix_value (i : Fin 52) (state : MachineState) :
    (decoderPrefixState i state).getReg .x10 =
      (state.getByte (BitVec.ofNat 64 (0x42000 + digitBit i.val / 8))).zeroExtend 64 := by
  fin_cases i <;>
    simp [decoderPrefixState, digitBit, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq,
      MachineState.getByte]

theorem decoder_prefix_memory (i : Fin 52) (state : MachineState)
    (address : Word) :
    (decoderPrefixState i state).getByte address = state.getByte address := by
  simp [decoderPrefixState, execInstrBr, MachineState.getByte]

theorem decoder_middle_memory (i : Fin 52) (state : MachineState)
    (address : Word) :
    (decoderMiddleState i state).getByte address = state.getByte address := by
  simp [decoderMiddleState, execInstrBr, MachineState.getByte]

theorem decoder_suffix_memory (i : Fin 52) (state : MachineState)
    (address : Word) :
    (decoderSuffixState i state).getByte address =
      if address = BitVec.ofNat 64 (0x44000 + i.val) then
        ((state.getReg .x10 &&& 7#64).truncate 8)
      else state.getByte address := by
  fin_cases i <;>
    simp [decoderSuffixState, execInstrBr, signExtend12,
      getByte_setByte, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

def middleValue (i : Fin 52) (state : MachineState) : Word :=
  let shift := digitBit i.val % 8
  if shift = 0 then state.getReg .x10
  else if shift ≤ 5 then state.getReg .x10 >>> shift
  else
    (state.getReg .x10 >>> shift) +
      ((state.getByte
        (BitVec.ofNat 64 (0x42000 + digitBit i.val / 8 + 1))).zeroExtend 64 <<<
        (8 - shift))

theorem decoder_middle_value (i : Fin 52) (state : MachineState)
    (source : state.getReg .x6 = 0x42000) :
    (decoderMiddleState i state).getReg .x10 = middleValue i state := by
  fin_cases i <;>
    simp [decoderMiddleState, middleValue, digitBit, execInstrBr,
      signExtend12, source, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, MachineState.getByte]

def answerWord (i : Fin 52) (state : MachineState) : Word :=
  let shift := digitBit i.val % 8
  let low := (state.getByte
    (BitVec.ofNat 64 (0x42000 + digitBit i.val / 8))).zeroExtend 64
  if shift = 0 then low
  else if shift ≤ 5 then low >>> shift
  else
    (low >>> shift) +
      ((state.getByte
        (BitVec.ofNat 64 (0x42000 + digitBit i.val / 8 + 1))).zeroExtend 64 <<<
        (8 - shift))

def answerDigit (i : Fin 52) (state : MachineState) : Byte :=
  (answerWord i state &&& 7#64).truncate 8

theorem decoder_prefix_source (i : Fin 52) (state : MachineState) :
    (decoderPrefixState i state).getReg .x6 = 0x42000 := by
  simp [decoderPrefixState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem decoder_word (i : Fin 52) (state : MachineState) :
    (decoderMiddleState i (decoderPrefixState i state)).getReg .x10 =
      answerWord i state := by
  rw [decoder_middle_value i (decoderPrefixState i state)
    (decoder_prefix_source i state)]
  simp [middleValue, answerWord, decoder_prefix_value,
    decoder_prefix_memory]

theorem decoder_digit (i : Fin 52) (state : MachineState) :
    (decoderState i state).getByte
      (BitVec.ofNat 64 (0x44000 + i.val)) = answerDigit i state := by
  change (decoderSuffixState i
    (decoderMiddleState i (decoderPrefixState i state))).getByte _ = _
  rw [decoder_suffix_byte, decoder_word]
  rfl

theorem decoder_prefix_checksum (i : Fin 52) (state : MachineState) :
    (decoderPrefixState i state).getReg .x15 = state.getReg .x15 := by
  simp [decoderPrefixState, execInstrBr,
    MachineState.getReg_setReg_ne]

theorem decoder_middle_checksum (i : Fin 52) (state : MachineState) :
    (decoderMiddleState i state).getReg .x15 = state.getReg .x15 := by
  simp [decoderMiddleState, execInstrBr,
    MachineState.getReg_setReg_ne]

theorem decoder_checksum (i : Fin 52) (state : MachineState) :
    (decoderState i state).getReg .x15 =
      state.getReg .x15 + (answerWord i state &&& 7#64) := by
  change (decoderSuffixState i
    (decoderMiddleState i (decoderPrefixState i state))).getReg .x15 = _
  rw [decoder_suffix_sum, decoder_word, decoder_middle_checksum,
    decoder_prefix_checksum]

theorem decoder_memory (i : Fin 52) (state : MachineState)
    (address : Word) :
    (decoderState i state).getByte address =
      if address = BitVec.ofNat 64 (0x44000 + i.val) then
        answerDigit i state
      else state.getByte address := by
  change (decoderSuffixState i
    (decoderMiddleState i (decoderPrefixState i state))).getByte address = _
  rw [decoder_suffix_memory]
  by_cases same : address = BitVec.ofNat 64 (0x44000 + i.val)
  · simp [same, answerDigit, decoder_word]
  · simp [same, decoder_middle_memory, decoder_prefix_memory]

def digitCost (count : Nat) : Nat :=
  ((List.range count).map digitWords).sum

theorem digitStart_eq (count : Nat) :
    digitStart count = 968 + digitCost count := rfl

theorem digitCost_succ (count : Nat) :
    digitCost (count + 1) = digitCost count + digitWords count := by
  simp [digitCost, List.range_succ, List.map_append, List.sum_append]

theorem digitStart_succ (count : Nat) :
    digitStart (count + 1) = digitStart count + digitWords count := by
  simp [digitStart_eq, digitCost_succ, Nat.add_assoc]

def decoderRun : Nat → MachineState → MachineState
  | 0, state => state
  | count + 1, state =>
      decoderState ⟨count % 52, Nat.mod_lt _ (by decide)⟩
        (decoderRun count state)

theorem decoder_run_block (count : Nat) (state : MachineState)
    (within : count ≤ 52) (pc : state.pc = 0x1f20) :
    OrdinarySteps SphincsImages.verify state (digitCost count)
      (decoderRun count state) ∧
    (decoderRun count state).pc =
      BitVec.ofNat 64 (0x1000 + 4 * digitStart count) := by
  induction count with
  | zero =>
      constructor
      · simpa [digitCost, decoderRun] using
          OrdinarySteps.refl (image := SphincsImages.verify) state
      · simpa [decoderRun, digitStart] using pc
  | succ count ih =>
      have small : count < 52 := by omega
      obtain ⟨pre, prePc⟩ := ih (by omega)
      let i : Fin 52 := ⟨count, small⟩
      have step := decoder_block i (decoderRun count state)
        (by simpa [i] using prePc)
      have result : decoderRun (count + 1) state =
          decoderState i (decoderRun count state) := by
        simp [decoderRun, i, Nat.mod_eq_of_lt small]
      refine ⟨?_, ?_⟩
      · simpa [result, digitCost_succ, i] using pre.append step.1
      · simpa [result, digitStart_succ, i] using step.2

theorem decoder_run_all (state : MachineState) (pc : state.pc = 0x1f20) :
    OrdinarySteps SphincsImages.verify state 496
      (decoderRun 52 state) ∧
    (decoderRun 52 state).pc = 0x26e0 := by
  have all := decoder_run_block 52 state (by decide) pc
  have cost : digitCost 52 = 496 := by decide
  have finish : BitVec.ofNat 64 (0x1000 + 4 * digitStart 52) = 0x26e0 := by
    decide
  simpa [cost, finish] using all

theorem decoder_run_answer_byte (count : Nat) (state : MachineState)
    (within : count ≤ 52) (index : Fin 32) :
    (decoderRun count state).getByte
      (BitVec.ofNat 64 (0x42000 + index.val)) =
      state.getByte (BitVec.ofNat 64 (0x42000 + index.val)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have small : count < 52 := by omega
      let i : Fin 52 := ⟨count, small⟩
      have different :
          BitVec.ofNat 64 (0x42000 + index.val) ≠
            BitVec.ofNat 64 (0x44000 + i.val) := by
        intro eq
        have h := congrArg BitVec.toNat eq
        have leftSmall : 0x42000 + index.val < 2^64 := by omega
        have rightSmall : 0x44000 + i.val < 2^64 := by
          have := i.isLt
          omega
        simp only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt leftSmall, Nat.mod_eq_of_lt rightSmall] at h
        have := index.isLt
        have := i.isLt
        omega
      have stepEq : decoderRun (count + 1) state =
          decoderState i (decoderRun count state) := by
        simp [decoderRun, i, Nat.mod_eq_of_lt small]
      rw [stepEq]
      rw [decoder_memory]
      simp only [if_neg different]
      exact ih (by omega)

theorem answerWord_run (count : Nat) (state : MachineState)
    (within : count ≤ 52) (i : Fin 52) :
    answerWord i (decoderRun count state) = answerWord i state := by
  let lowIndex : Fin 32 := ⟨digitBit i.val / 8, by fin_cases i <;> decide⟩
  let highIndex : Fin 32 := ⟨digitBit i.val / 8 + 1, by fin_cases i <;> decide⟩
  have low := decoder_run_answer_byte count state within lowIndex
  have high := decoder_run_answer_byte count state within highIndex
  have high' : (decoderRun count state).getByte
      (BitVec.ofNat 64 (0x42000 + digitBit i.val / 8 + 1)) =
      state.getByte (BitVec.ofNat 64 (0x42000 + digitBit i.val / 8 + 1)) := by
    simpa [highIndex, Nat.add_assoc] using high
  simp [answerWord, lowIndex, low, high']

theorem answerDigit_run (count : Nat) (state : MachineState)
    (within : count ≤ 52) (i : Fin 52) :
    answerDigit i (decoderRun count state) = answerDigit i state := by
  simp [answerDigit, answerWord_run count state within i]

theorem decoder_run_digit (count : Nat) (state : MachineState)
    (within : count ≤ 52) (i : Fin 52) (inside : i.val < count) :
    (decoderRun count state).getByte
      (BitVec.ofNat 64 (0x44000 + i.val)) = answerDigit i state := by
  induction count with
  | zero => omega
  | succ count ih =>
      have small : count < 52 := by omega
      let last : Fin 52 := ⟨count, small⟩
      have stepEq : decoderRun (count + 1) state =
          decoderState last (decoderRun count state) := by
        simp [decoderRun, last, Nat.mod_eq_of_lt small]
      rw [stepEq]
      by_cases same : i.val = count
      · have equality : i = last := Fin.ext (by simpa [last] using same)
        subst i
        rw [decoder_digit]
        exact answerDigit_run count state (by omega) last
      · have different :
            BitVec.ofNat 64 (0x44000 + i.val) ≠
              BitVec.ofNat 64 (0x44000 + last.val) := by
          intro eq
          have h := congrArg BitVec.toNat eq
          have ismall : 0x44000 + i.val < 2^64 := by
            have := i.isLt
            omega
          have lsmall : 0x44000 + last.val < 2^64 := by
            have := last.isLt
            omega
          simp only [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt ismall, Nat.mod_eq_of_lt lsmall] at h
          have : last.val = count := rfl
          omega
        rw [decoder_memory]
        simp only [if_neg different]
        exact ih (by omega) (by omega)

def answerSum : Nat → MachineState → Word
  | 0, _ => 0
  | count + 1, state =>
      answerSum count state +
        (answerWord ⟨count % 52, Nat.mod_lt _ (by decide)⟩ state &&& 7#64)

theorem decoder_run_checksum (count : Nat) (state : MachineState)
    (within : count ≤ 52) :
    (decoderRun count state).getReg .x15 =
      state.getReg .x15 + answerSum count state := by
  induction count with
  | zero => simp [decoderRun, answerSum]
  | succ count ih =>
      have small : count < 52 := by omega
      let last : Fin 52 := ⟨count, small⟩
      have stepEq : decoderRun (count + 1) state =
          decoderState last (decoderRun count state) := by
        simp [decoderRun, last, Nat.mod_eq_of_lt small]
      rw [stepEq, decoder_checksum, ih (by omega),
        answerWord_run count state (by omega) last]
      simp [answerSum, last, Nat.mod_eq_of_lt small, BitVec.add_assoc]

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_suffix_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_suffix_byte

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_suffix_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_suffix_sum

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_prefix_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_prefix_value

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_middle_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decoder_middle_memory

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_suffix_memory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_suffix_memory

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_middle_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_middle_value

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_digit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_digit

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_checksum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_checksum

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_memory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_memory

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_run_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_run_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_run_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_run_all

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_run_answer_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_run_answer_byte

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.answerDigit_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms answerDigit_run

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_run_digit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_run_digit

/-- info: 'SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_run_checksum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_run_checksum

end SigGolfCandidate.SphincsVerifierWotsDecodeData
