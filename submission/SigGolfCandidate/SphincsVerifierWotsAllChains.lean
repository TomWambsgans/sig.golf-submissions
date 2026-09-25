import SigGolfCandidate.SphincsVerifierWotsChainPreserved
import SigGolfCandidate.SphincsVerifierWotsDecodeData
import SigGolfCandidate.SphincsVerifierWotsChainSetup

namespace SigGolfCandidate.SphincsVerifierWotsAllChains
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsChainPreserved
open SigGolfCandidate.SphincsVerifierWotsDigitFrame
open SigGolfCandidate.SphincsVerifierWotsLoop
open SigGolfCandidate.SphincsVerifierWotsDecodeData
open SigGolfCandidate.SphincsVerifierWotsChainSetup
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def DigitsValid (state : MachineState) : Prop :=
  ∀ j : Fin 52,
    (state.getByte (BitVec.ofNat 64 (0x44000 + j.val))).toNat < 8

theorem answerDigit_small (j : Fin 52) (state : MachineState) :
    (answerDigit j state).toNat < 8 := by
  simp only [answerDigit, BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  simp only [Nat.mod_eq_of_lt (by decide : 7 < 2 ^ 64)]
  have bound : (answerWord j state).toNat &&& 7 ≤ 7 := Nat.and_le_right
  omega

theorem digitByte_frame (before after : MachineState)
    (frame : ∀ address, DigitAddr address →
      after.getMem address = before.getMem address)
    (j : Fin 52) :
    after.getByte (BitVec.ofNat 64 (0x44000 + j.val)) =
      before.getByte (BitVec.ofNat 64 (0x44000 + j.val)) := by
  unfold MachineState.getByte
  rw [frame _ (digit_address j)]

theorem digitsValid_frame (before after : MachineState)
    (frame : ∀ address, DigitAddr address →
      after.getMem address = before.getMem address)
    (valid : DigitsValid before) : DigitsValid after := by
  intro j
  rw [digitByte_frame before after frame j]
  exact valid j

theorem chainSetup_digitFrame (state : MachineState)
    (address : Word) (inside : DigitAddr address) :
    (chainSetupState state).getMem address = state.getMem address := by
  have neCounter : address ≠ 0x43050 :=
    digit_ne address inside _ (Or.inl (by decide))
  have nePointer : address ≠ 0x43028 :=
    digit_ne address inside _ (Or.inl (by decide))
  simp [chainSetupState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  split_ifs with equal1 equal2
  · exact (nePointer equal1).elim
  · exact (neCounter equal2).elim
  · rfl

theorem decoder_to_chain_valid (state : MachineState) :
    DigitsValid (decodedChainState state) := by
  intro j
  have frame : ∀ address, DigitAddr address →
      (decodedChainState state).getMem address =
        (decoderRun 52 state).getMem address := by
    intro address inside
    exact chainSetup_digitFrame (decoderRun 52 state) address inside
  rw [digitByte_frame (decoderRun 52 state)
    (decodedChainState state) frame j,
    decoder_run_digit 52 state (by decide) j (by have := j.isLt; omega)]
  exact answerDigit_small j state

def LoopInv (initial : MachineState) (i : Nat)
    (current : MachineState) : Prop :=
  current.pc = (if i = 52 then 0x298c else 0x2710) ∧
  current.getMem 0x43050 = BitVec.ofNat 64 i ∧
  current.getMem 0x43028 = BitVec.ofNat 64 (0x2547c + 20 * i) ∧
  (∀ address, DigitAddr address →
    current.getMem address = initial.getMem address) ∧
  DigitsValid current

theorem all_chains (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x2710)
    (counter : state.getMem 0x43050 = 0)
    (pointer : state.getMem 0x43028 = 0x2547c)
    (valid : DigitsValid state) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc = 0x298c ∧
      final.getMem 0x43050 = 52 ∧
      final.getMem 0x43028 = 0x2547c + 20 * 52 ∧
      (∀ address, DigitAddr address →
        final.getMem address = state.getMem address) ∧
      steps ≤ 728 * 52 ∧
      cycles ≤ 777 * 52 ∧
      calls ≤ 7 * 52 ∧
      blocks ≤ 7 * 52 ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  have next (i : Nat) (current : MachineState)
      (small : i < 52) (inv : LoopInv state i current) :
      ∃ (following : MachineState) (steps cycles calls blocks : Nat),
        LoopInv state (i + 1) following ∧
        steps ≤ 728 ∧ cycles ≤ 777 ∧ calls ≤ 7 ∧ blocks ≤ 7 ∧
        ∀ (tailSteps : Nat) (result : Execution),
          Executes hash SphincsImages.verify following tailSteps result →
          Executes hash SphincsImages.verify current (tailSteps + steps)
            (result.charge cycles calls blocks) := by
    let chain : Fin 52 := ⟨i, small⟩
    let digit : Fin 8 := ⟨
      (current.getByte (BitVec.ofNat 64 (0x44000 + i))).toNat,
      inv.2.2.2.2 chain⟩
    have decoded : current.getByte
        (BitVec.ofNat 64 (0x44000 + chain.val)) =
        BitVec.ofNat 8 digit.val := by
      simp [chain, digit]
    obtain ⟨following, steps, cycles, calls, blocks,
        nextPc, nextCounter, nextPointer, digitFrame,
        stepBound, cycleBound, callBound, blockBound, run⟩ :=
      chainRound_preserved hash current chain digit
        (by have ne : i ≠ 52 := by omega
            simpa [LoopInv, ne] using inv.1)
        inv.2.1 inv.2.2.1 decoded
    refine ⟨following, steps, cycles, calls, blocks,
      ⟨?_, nextCounter, nextPointer, ?_, ?_⟩,
      by omega, by omega, by omega, by omega, run⟩
    · simpa [chain] using nextPc
    · intro address inside
      exact (digitFrame address inside).trans (inv.2.2.2.1 address inside)
    · exact digitsValid_frame current following digitFrame inv.2.2.2.2
  obtain ⟨final, steps, cycles, calls, blocks,
      inv, stepBound, cycleBound, callBound, blockBound, run⟩ :=
    bounded_loop hash SphincsImages.verify (LoopInv state) 52
      728 777 7 7 next 0 52 state (by decide)
      ⟨by simpa [LoopInv] using pc, by simpa using counter,
        by simpa using pointer, by intro address _; rfl, valid⟩
  refine ⟨final, steps, cycles, calls, blocks,
    by simpa [LoopInv] using inv.1,
    inv.2.1, inv.2.2.1, inv.2.2.2.1,
    stepBound, cycleBound, callBound, blockBound, run⟩

theorem decode_and_all_chains (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x1f20)
    (checksum : state.getReg .x15 + answerSum 52 state = 194) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc = 0x298c ∧
      final.getMem 0x43050 = 52 ∧
      final.getMem 0x43028 = 0x2547c + 20 * 52 ∧
      steps ≤ 507 + 728 * 52 ∧
      cycles ≤ 507 + 777 * 52 ∧
      calls ≤ 7 * 52 ∧
      blocks ≤ 7 * 52 ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  obtain ⟨decodeTrace, decodedPc, decodedCounter, decodedPointer⟩ :=
    decoder_to_chain state pc checksum
  obtain ⟨final, steps, cycles, calls, blocks,
      finalPc, finalCounter, finalPointer, _, stepBound,
      cycleBound, callBound, blockBound, run⟩ :=
    all_chains hash (decodedChainState state) decodedPc
      decodedCounter decodedPointer (decoder_to_chain_valid state)
  refine ⟨final, 507 + steps, 507 + cycles, calls, blocks,
    finalPc, finalCounter, finalPointer,
    by omega, by omega, callBound, blockBound, ?_⟩
  intro tailSteps result tail
  have after := run tailSteps result tail
  have before := decodeTrace.then_executes after
  simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using before

/-- info: 'SigGolfCandidate.SphincsVerifierWotsAllChains.all_chains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms all_chains

/-- info: 'SigGolfCandidate.SphincsVerifierWotsAllChains.decode_and_all_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decode_and_all_chains

end SigGolfCandidate.SphincsVerifierWotsAllChains
