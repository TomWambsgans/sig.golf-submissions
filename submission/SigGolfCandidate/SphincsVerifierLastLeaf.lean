import SigGolfCandidate.SphincsVerifierLeavesTrace

/-!
# Final digest selector

The last digest group is a rejection check, not an FTS tree. The verifier
continues only when the selector is zero, matching the abstract admissibility
condition.
-/

namespace SigGolfCandidate.SphincsVerifierLastLeaf
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolfCandidate.SphincsVerifierLeafCode
open SigGolfCandidate.SphincsVerifierDigestDecode
open SigGolfCandidate.SphincsVerifierLeavesFrame
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierMessageHash
set_option maxRecDepth 16384

def lastTailState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x42)
  let state := execInstrBr state (.ADDI .x6 .x6 0)
  let state := execInstrBr state (.LBU .x10 .x6 28)
  let state := execInstrBr state (.LBU .x11 .x6 29)
  let state := execInstrBr state (.SRLI .x10 .x10 2)
  let state := execInstrBr state (.SLLI .x11 .x11 6)
  let state := execInstrBr state (.ADD .x10 .x10 .x11)
  execInstrBr state (.ANDI .x10 .x10 255)

theorem lastTail_block (state : MachineState) (pc : state.pc = 0x16f0) :
    OrdinarySteps SphincsImages.verify state 8 (lastTailState state) := by
  let s1 := execInstrBr state (.LUI .x6 0x42)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LBU .x10 .x6 28)
  let s4 := execInstrBr s3 (.LBU .x11 .x6 29)
  let s5 := execInstrBr s4 (.SRLI .x10 .x10 2)
  let s6 := execInstrBr s5 (.SLLI .x11 .x11 6)
  let s7 := execInstrBr s6 (.ADD .x10 .x10 .x11)
  let s8 := execInstrBr s7 (.ANDI .x10 .x10 255)
  have p1 : s1.pc = 0x16f4 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x16f8 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x16fc := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1700 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1704 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1708 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x170c := by simp [s7, execInstrBr, p6]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x42)) 7
  · rw [fetch_index SphincsImages.verify state 444 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 6
  · rw [fetch_index SphincsImages.verify s1 445 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LBU .x10 .x6 28)) 5
  · rw [fetch_index SphincsImages.verify s2 446 (by decide) (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LBU .x11 .x6 29)) 4
  · rw [fetch_index SphincsImages.verify s3 447 (by decide) (by simpa using p3)]
    decide
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SRLI .x10 .x10 2)) 3
  · rw [fetch_index SphincsImages.verify s4 448 (by decide) (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SLLI .x11 .x11 6)) 2
  · rw [fetch_index SphincsImages.verify s5 449 (by decide) (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x10 .x10 .x11)) 1
  · rw [fetch_index SphincsImages.verify s6 450 (by decide) (by simpa using p6)]
    decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ANDI .x10 .x10 255)) 0
  · rw [fetch_index SphincsImages.verify s7 451 (by decide) (by simpa using p7)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem lastTail_pc (state : MachineState) (pc : state.pc = 0x16f0) :
    (lastTailState state).pc = 0x1710 := by
  simp [lastTailState, execInstrBr, pc]

theorem lastTail_value (state : MachineState) :
    (lastTailState state).getReg .x10 =
      (((state.getByte 0x4201c).zeroExtend 64 >>> 2) +
        ((state.getByte 0x4201d).zeroExtend 64 <<< 6)) &&& 255#64 := by
  simp [lastTailState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getByte, MachineState.getMem_setPC,
    MachineState.getMem_setReg]

theorem lastTail_value_nat (state : MachineState) :
    ((lastTailState state).getReg .x10).toNat =
      ((state.getByte 0x4201c).toNat / 4 +
        (state.getByte 0x4201d).toNat * 64) % 256 := by
  rw [lastTail_value]
  simp only [BitVec.toNat_and, BitVec.toNat_add,
    BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [show (255#64).toNat = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  norm_num
  omega

theorem lastTail_digest (state : MachineState) (answer : BitVec 256)
    (bytes : AnswerBytes state answer) :
    ((lastTailState state).getReg .x10).toNat =
      (SphincsSecurity.Concrete.digestLeaves
        (SphincsSecurity.truncateMessageDigest answer)
        SphincsSecurity.Concrete.lastIndexGroup).val := by
  rw [lastTail_value_nat]
  have first := bytes ⟨28, by decide⟩
  have second := bytes ⟨29, by decide⟩
  rw [show 0x42000 + (28 : Nat) = 0x4201c by decide] at first
  rw [show 0x42000 + (29 : Nat) = 0x4201d by decide] at second
  calc
    _ = (((answer.extractLsb' (8 * 28) 8).toNat / 4 +
          (answer.extractLsb' (8 * 29) 8).toNat * 64) % 256) := by
      exact congrArg₂
        (fun a b : BitVec 8 => (a.toNat / 4 + b.toNat * 64) % 256)
        first second
    _ = _ := by
      simpa [SphincsSecurity.Concrete.lastIndexGroup,
        SphincsSecurity.ftsTrees] using
        leaf_from_answer_bytes_eq_digestLeaves answer
          SphincsSecurity.Concrete.lastIndexGroup

def lastAcceptState (state : MachineState) : MachineState :=
  execInstrBr (lastTailState state) (.BEQ .x10 .x0 8)

theorem lastAccept_block (state : MachineState)
    (pc : state.pc = 0x16f0) :
    OrdinarySteps SphincsImages.verify state 9 (lastAcceptState state) := by
  have front := lastTail_block state pc
  have middlePc := lastTail_pc state pc
  have back : OrdinarySteps SphincsImages.verify
      (lastTailState state) 1 (lastAcceptState state) := by
    apply OrdinarySteps.step _ _ _ (.base (.BEQ .x10 .x0 8)) 0
    · rw [fetch_index SphincsImages.verify (lastTailState state) 452
        (by decide) (by simpa using middlePc)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  simpa [lastAcceptState] using front.append back

theorem lastAccept_pc (state : MachineState)
    (pc : state.pc = 0x16f0)
    (zero : (lastTailState state).getReg .x10 = 0) :
    (lastAcceptState state).pc = 0x1718 := by
  have middlePc := lastTail_pc state pc
  simp [lastAcceptState, execInstrBr, zero, middlePc]
  decide

theorem admissible_lastTail_zero (state : MachineState)
    (answer : BitVec 256) (bytes : AnswerBytes state answer)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer)) :
    (lastTailState state).getReg .x10 = 0 := by
  have value := lastTail_digest state answer bytes
  change SphincsSecurity.Concrete.digestLeaves
    (SphincsSecurity.truncateMessageDigest answer)
    SphincsSecurity.Concrete.lastIndexGroup = 0 at admissible
  rw [admissible] at value
  apply BitVec.eq_of_toNat_eq
  simpa using value

private theorem getByte_setPC (state : MachineState) (pc address : Word) :
    (state.setPC pc).getByte address = state.getByte address := by
  simp [MachineState.getByte]

private theorem getByte_execBEQ (state : MachineState) (address : Word) :
    (execInstrBr state (.BEQ .x10 .x0 8)).getByte address =
      state.getByte address := by
  simp [execInstrBr]
  split_ifs <;> simp [getByte_setPC]

private theorem getMem_execBEQ (state : MachineState) (address : Word) :
    (execInstrBr state (.BEQ .x10 .x0 8)).getMem address =
      state.getMem address := by
  simp [execInstrBr]

theorem lastAccept_byte (state : MachineState) (address : Word) :
    (lastAcceptState state).getByte address = state.getByte address := by
  rw [show lastAcceptState state =
    execInstrBr (lastTailState state) (.BEQ .x10 .x0 8) by rfl,
    getByte_execBEQ]
  simp [lastTailState, execInstrBr,
    Memory.getByte_setReg, getByte_setPC]

theorem lastAccept_mem (state : MachineState) (address : Word) :
    (lastAcceptState state).getMem address = state.getMem address := by
  rw [show lastAcceptState state =
    execInstrBr (lastTailState state) (.BEQ .x10 .x0 8) by rfl,
    getMem_execBEQ]
  simp [lastTailState, execInstrBr]

theorem messageReady_admissible_leaves (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer)) :
    let initial := indexStoredState (indexValueState (writeHash state answer))
    let selectors := leafStates initial 24 (by decide)
    let final := lastAcceptState selectors
    OrdinarySteps SphincsImages.verify (writeHash state answer) 284 final ∧
      final.pc = 0x1718 ∧
      ∀ tree : Fin 24,
        (final.getByte (BitVec.ofNat 64 (0x44800 + tree.val))).toNat =
          abstractLeaf answer tree := by
  obtain ⟨front, selectorPc, selectors⟩ :=
    messageReady_leaves state pk message randomness ready pc answer
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selected := leafStates initial 24 (by decide)
  have initialBytes : AnswerBytes initial answer := by
    intro index
    exact messageReady_indexStored_answerBytes
      state pk message randomness ready answer index
  have selectedBytes : AnswerBytes selected answer :=
    leafStates_answer initial answer initialBytes 24 (by decide)
  have zero := admissible_lastTail_zero selected answer selectedBytes admissible
  have back := lastAccept_block selected selectorPc
  have endPc := lastAccept_pc selected selectorPc zero
  exact ⟨by simpa [initial, selected] using front.append back,
    endPc,
    by intro tree
       rw [lastAccept_byte]
       exact selectors tree⟩

/-- info: 'SigGolfCandidate.SphincsVerifierLastLeaf.messageReady_admissible_leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_admissible_leaves

end SigGolfCandidate.SphincsVerifierLastLeaf
