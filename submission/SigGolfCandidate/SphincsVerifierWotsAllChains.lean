import SigGolfCandidate.SphincsVerifierWotsChainPreserved
import SigGolfCandidate.SphincsVerifierWotsDecodeData
import SigGolfCandidate.SphincsVerifierWotsChainSetup
import SigGolfCandidate.Hypertree.KeygenTrace

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

namespace SigGolfCandidate.SphincsVerifierWotsAllChainsGeneral
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsAllChains
open SigGolfCandidate.SphincsVerifierWotsChainPreservedGeneral
open SigGolfCandidate.SphincsVerifierWotsDigitFrame
open SigGolfCandidate.SphincsVerifierWotsLoop
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def LoopInvGeneral (initial : MachineState) (sourceBase : Nat) (i : Nat)
    (current : MachineState) : Prop :=
  current.pc = (if i = 52 then 0x298c else 0x2710) ∧
  current.getMem 0x43050 = BitVec.ofNat 64 i ∧
  current.getMem 0x43028 = BitVec.ofNat 64 (sourceBase + 20 * i) ∧
  (∀ address, DigitAddr address →
    current.getMem address = initial.getMem address) ∧
  DigitsValid current

theorem all_chains_general (hash : Hash) (state : MachineState)
    (sourceBase : Nat)
    (baseBound : sourceBase + 20 * 52 ≤ 0x40000)
    (baseAligned : sourceBase % 4 = 0)
    (pc : state.pc = 0x2710)
    (counter : state.getMem 0x43050 = 0)
    (pointer : state.getMem 0x43028 = BitVec.ofNat 64 sourceBase)
    (valid : DigitsValid state) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc = 0x298c ∧
      final.getMem 0x43050 = 52 ∧
      final.getMem 0x43028 = BitVec.ofNat 64 (sourceBase + 20 * 52) ∧
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
      (small : i < 52) (inv : LoopInvGeneral state sourceBase i current) :
      ∃ (following : MachineState) (steps cycles calls blocks : Nat),
        LoopInvGeneral state sourceBase (i + 1) following ∧
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
      chainRound_preserved_general hash current sourceBase
        baseBound baseAligned chain digit
        (by have ne : i ≠ 52 := by omega
            simpa [LoopInvGeneral, ne] using inv.1)
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
    bounded_loop hash SphincsImages.verify (LoopInvGeneral state sourceBase) 52
      728 777 7 7 next 0 52 state (by decide)
      ⟨by simpa [LoopInvGeneral] using pc, by simpa using counter,
        by simpa using pointer, by intro address _; rfl, valid⟩
  refine ⟨final, steps, cycles, calls, blocks,
    by simpa [LoopInvGeneral] using inv.1,
    inv.2.1, inv.2.2.1, inv.2.2.2.1,
    stepBound, cycleBound, callBound, blockBound, run⟩

/-- info: 'SigGolfCandidate.SphincsVerifierWotsAllChainsGeneral.all_chains_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms all_chains_general

end SigGolfCandidate.SphincsVerifierWotsAllChainsGeneral

namespace SigGolfCandidate.SphincsVerifierWotsStepTrace
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsStepIteration
open SigGolfCandidate.SphincsVerifierWotsStepBody
open SigGolfCandidate.SphincsVerifierWotsStepHashReady
open SigGolfCandidate.SphincsVerifierWotsStepHash
open SigGolfCandidate.SphincsVerifierWotsStepNext
open SigGolfCandidate.SphincsVerifierWotsStepCheck
open SigGolfCandidate.SphincsVerifierWotsFullChain
open SigGolfCandidate.SphincsVerifierWotsChainEntryGeneral
open SigGolfCandidate.SphincsVerifierWotsChainEntry
open SigGolfCandidate.SphincsVerifierWotsChainEndGeneral
open SigGolfCandidate.SphincsVerifierWotsChainRound
open SigGolfCandidate.SphincsVerifierWotsChainEnd
open SigGolfCandidate.SphincsVerifierWotsDigitFrame
open SigGolfCandidate.SphincsVerifierWotsAllChains
open SigGolfCandidate.SphincsVerifierWotsAllChainsGeneral
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem step_iteration_trace (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x2788) :
    Trace hash SphincsImages.verify state 89 96 1 1 (stepNext hash state) := by
  obtain ⟨pre, prePc⟩ := stepHashPrefix_block state pc
  obtain ⟨ready, readyPc, source, bits, destination, service⟩ :=
    stepHashReady_block (stepHashPrefixState state) prePc
  have hashPc : (stepAfterHash hash state).pc = 0x2894 := by
    simp [stepAfterHash, stepReady, writeHash, readyPc]
  obtain ⟨copy, copyPc⟩ :=
    stepAnswerCopy_block (stepAfterHash hash state) hashPc
  obtain ⟨advance, _⟩ :=
    stepReturn_block (stepAnswerCopyState (stepAfterHash hash state)) copyPc
  have hashStep : Trace hash SphincsImages.verify
      (stepReady state) 1 8 1 1 (stepAfterHash hash state) := by
    have args := step_hash_arguments (stepReady state) source bits destination
    simpa only [stepAfterHash, args.2] using
      (Trace.hash (stepReady state) (stepAfterHash hash state)
        0 0 0 0 (step_hash_site (stepReady state) readyPc)
        service args.1 (Trace.refl _))
  have before := (pre.append ready).trace (hash := hash)
  have after := (copy.append advance).trace (hash := hash)
  have combined := before.trans (hashStep.trans after)
  simpa [stepNext, stepReady, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using combined

theorem step_round_trace (hash : Hash) (state : MachineState)
    (digit : Fin 8) (pc : state.pc = 0x2774)
    (cell : state.getMem 0x43058 = BitVec.ofNat 64 digit.val)
    (small : digit.val < 7) :
    Trace hash SphincsImages.verify state 94 101 1 1
      (stepRound hash state) := by
  have checked := stepCheck_block state digit pc cell
  have checkedPc : (stepCheckState state).pc = 0x2788 := by
    simpa [show digit.val ≠ 7 by omega] using checked.2
  have rest := step_iteration_trace hash (stepCheckState state) checkedPc
  simpa [stepRound] using (checked.1.trace (hash := hash)).trans rest

theorem bounded_loop_trace (hash : Hash) (image : Image)
    (Inv : Nat → MachineState → Prop) (limit : Nat)
    (stepLimit cycleLimit callLimit blockLimit : Nat)
    (step : ∀ (i : Nat) (state : MachineState), i < limit → Inv i state →
      ∃ (next : MachineState) (steps cycles calls blocks : Nat),
        Inv (i + 1) next ∧ steps ≤ stepLimit ∧ cycles ≤ cycleLimit ∧
        calls ≤ callLimit ∧ blocks ≤ blockLimit ∧
        Trace hash image state steps cycles calls blocks next)
    (start count : Nat) (state : MachineState)
    (within : start + count ≤ limit) (initial : Inv start state) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      Inv (start + count) final ∧
      steps ≤ stepLimit * count ∧ cycles ≤ cycleLimit * count ∧
      calls ≤ callLimit * count ∧ blocks ≤ blockLimit * count ∧
      Trace hash image state steps cycles calls blocks final := by
  induction count generalizing start state with
  | zero =>
      exact ⟨state, 0, 0, 0, 0, by simpa using initial,
        by simp, by simp, by simp, by simp, Trace.refl _⟩
  | succ count ih =>
      have small : start < limit := by omega
      obtain ⟨next, a, b, c, d, nextInv, ha, hb, hc, hd, pre⟩ :=
        step start state small initial
      obtain ⟨final, e, f, g, h, finalInv, he, hf, hg, hh, suffix⟩ :=
        ih (start + 1) next (by omega) nextInv
      refine ⟨final, a + e, b + f, c + g, d + h,
        by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using finalInv, ?_, ?_, ?_, ?_, pre.trans suffix⟩
      · rw [Nat.mul_succ]; omega
      · rw [Nat.mul_succ]; omega
      · rw [Nat.mul_succ]; omega
      · rw [Nat.mul_succ]; omega

theorem step_loop_trace (hash : Hash) (start : Fin 8)
    (state : MachineState)
    (pc : state.pc = 0x2774)
    (cell : state.getMem 0x43058 = BitVec.ofNat 64 start.val) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc = 0x28ec ∧
      (∀ address, Preserved address →
        final.getMem address = state.getMem address) ∧
      steps ≤ 94 * (7 - start.val) + 5 ∧
      cycles ≤ 101 * (7 - start.val) + 5 ∧
      calls ≤ 7 - start.val ∧ blocks ≤ 7 - start.val ∧
      Trace hash SphincsImages.verify state steps cycles calls blocks final := by
  let Inv : Nat → MachineState → Prop := fun i current =>
    current.pc = 0x2774 ∧
    current.getMem 0x43058 = BitVec.ofNat 64 (start.val + i) ∧
    ∀ address, Preserved address →
      current.getMem address = state.getMem address
  have next (i : Nat) (current : MachineState)
      (bound : i < 7 - start.val) (inv : Inv i current) :
      ∃ (following : MachineState) (steps cycles calls blocks : Nat),
        Inv (i + 1) following ∧
        steps ≤ 94 ∧ cycles ≤ 101 ∧ calls ≤ 1 ∧ blocks ≤ 1 ∧
        Trace hash SphincsImages.verify current steps cycles calls blocks following := by
    let digit : Fin 8 := ⟨start.val + i, by have := start.isLt; omega⟩
    have small : digit.val < 7 := by dsimp [digit]; omega
    have currentCell : current.getMem 0x43058 =
        BitVec.ofNat 64 digit.val := inv.2.1
    refine ⟨stepRound hash current, 94, 101, 1, 1, ?_, by decide,
      by decide, by decide, by decide, ?_⟩
    · refine ⟨stepRound_pc hash current digit inv.1 currentCell small,
        ?_, ?_⟩
      · rw [stepRound_cell, currentCell]
        change BitVec.ofNat 64 (start.val + i) +
          BitVec.ofNat 64 1 =
          BitVec.ofNat 64 (start.val + (i + 1))
        rw [← BitVec.ofNat_add]
        congr 1
      · intro address preserved
        exact (preserved_round_frame hash current address preserved).trans
          (inv.2.2 address preserved)
    · exact step_round_trace hash current digit inv.1 currentCell small
  obtain ⟨seven, steps, cycles, calls, blocks, finalInv,
      stepBound, cycleBound, callBound, blockBound, run⟩ :=
    bounded_loop_trace hash SphincsImages.verify Inv (7 - start.val)
      94 101 1 1 next 0 (7 - start.val) state
      (by omega) ⟨pc, by simpa [Inv] using cell,
        by intro address _; rfl⟩
  have sevenCell : seven.getMem 0x43058 = 7 := by
    have sum : start.val + (7 - start.val) = 7 := by
      have := start.isLt
      omega
    simpa [Inv, sum] using finalInv.2.1
  have checked := stepCheck_block seven (⟨7, by decide⟩ : Fin 8)
    finalInv.1 (by simpa using sevenCell)
  refine ⟨stepCheckState seven, steps + 5, cycles + 5,
    calls, blocks, by simpa using checked.2, ?_,
    by omega, by omega, by simpa using callBound,
    by simpa using blockBound, ?_⟩
  · intro address preserved
    have frame : (stepCheckState seven).getMem address =
        seven.getMem address := by
      simp [stepCheckState, execInstrBr]
    exact frame.trans (finalInv.2.2 address preserved)
  · exact run.trans (checked.1.trace (hash := hash))

theorem chain_round_trace_general (hash : Hash) (state : MachineState)
    (sourceBase : Nat)
    (baseBound : sourceBase + 20 * 52 ≤ 0x40000)
    (baseAligned : sourceBase % 4 = 0)
    (chain : Fin 52) (digit : Fin 8)
    (pc : state.pc = 0x2710)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (sourceBase + 20 * chain.val))
    (decoded : state.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
      BitVec.ofNat 8 digit.val) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc =
        (if chain.val + 1 = 52 then 0x298c else 0x2710) ∧
      final.getMem 0x43050 = BitVec.ofNat 64 (chain.val + 1) ∧
      final.getMem 0x43028 =
        BitVec.ofNat 64 (sourceBase + 20 * (chain.val + 1)) ∧
      (∀ address, DigitAddr address →
        final.getMem address = state.getMem address) ∧
      steps ≤ 94 * (7 - digit.val) + 70 ∧
      cycles ≤ 101 * (7 - digit.val) + 70 ∧
      calls ≤ 7 - digit.val ∧ blocks ≤ 7 - digit.val ∧
      Trace hash SphincsImages.verify state steps cycles calls blocks final := by
  obtain ⟨entry, entryPc⟩ := chainEntry_block_general state chain
    (sourceBase + 20 * chain.val)
    (by have := chain.isLt; omega) (by omega) pc pointer counter
  have entryCell : (chainEntryState state).getMem 0x43058 =
      BitVec.ofNat 64 digit.val := by
    rw [chainEntry_step state chain counter, decoded]
    fin_cases digit <;> decide
  obtain ⟨middle, middleSteps, middleCycles, middleCalls, middleBlocks,
      middlePc, middleFrame, middleStepBound, middleCycleBound,
      middleCallBound, middleBlockBound, middleTrace⟩ :=
    step_loop_trace hash digit (chainEntryState state) entryPc entryCell
  have middleCounter : middle.getMem 0x43050 =
      BitVec.ofNat 64 chain.val := by
    rw [middleFrame 0x43050 (Or.inl (Or.inl rfl)),
      chainEntry_controlFrame state 0x43050 (Or.inl rfl), counter]
  have middlePointer : middle.getMem 0x43028 =
      BitVec.ofNat 64 (sourceBase + 20 * chain.val) := by
    rw [middleFrame 0x43028 (Or.inl (Or.inr rfl)),
      chainEntry_controlFrame state 0x43028 (Or.inr rfl), pointer]
  obtain ⟨endTrace, endPc, endCounter⟩ :=
    chainEnd_block middle chain middlePc middleCounter
  have endPointer := chainEnd_pointer_general middle chain sourceBase
    middleCounter middlePointer
  refine ⟨chainEndState middle, middleSteps + 65,
    middleCycles + 65, middleCalls, middleBlocks,
    endPc, endCounter, endPointer, ?_,
    by omega, by omega, middleCallBound, middleBlockBound, ?_⟩
  · intro address digitAddr
    exact (chainEnd_digitFrame middle chain middleCounter address
      digitAddr).trans ((middleFrame address (Or.inr digitAddr)).trans
        (chainEntry_digitFrame state address digitAddr))
  · have pre := (entry.trace (hash := hash)).trans middleTrace
    have whole := pre.trans (endTrace.trace (hash := hash))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using whole

theorem all_chains_trace_general (hash : Hash) (state : MachineState)
    (sourceBase : Nat)
    (baseBound : sourceBase + 20 * 52 ≤ 0x40000)
    (baseAligned : sourceBase % 4 = 0)
    (pc : state.pc = 0x2710)
    (counter : state.getMem 0x43050 = 0)
    (pointer : state.getMem 0x43028 = BitVec.ofNat 64 sourceBase)
    (valid : DigitsValid state) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc = 0x298c ∧
      final.getMem 0x43050 = 52 ∧
      final.getMem 0x43028 = BitVec.ofNat 64 (sourceBase + 20 * 52) ∧
      (∀ address, DigitAddr address →
        final.getMem address = state.getMem address) ∧
      steps ≤ 728 * 52 ∧
      cycles ≤ 777 * 52 ∧
      calls ≤ 7 * 52 ∧
      blocks ≤ 7 * 52 ∧
      Trace hash SphincsImages.verify state steps cycles calls blocks final := by
  have next (i : Nat) (current : MachineState)
      (small : i < 52) (inv : LoopInvGeneral state sourceBase i current) :
      ∃ (following : MachineState) (steps cycles calls blocks : Nat),
        LoopInvGeneral state sourceBase (i + 1) following ∧
        steps ≤ 728 ∧ cycles ≤ 777 ∧ calls ≤ 7 ∧ blocks ≤ 7 ∧
        Trace hash SphincsImages.verify current steps cycles calls blocks following := by
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
      chain_round_trace_general hash current sourceBase
        baseBound baseAligned chain digit
        (by have ne : i ≠ 52 := by omega
            simpa [LoopInvGeneral, ne] using inv.1)
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
    bounded_loop_trace hash SphincsImages.verify (LoopInvGeneral state sourceBase) 52
      728 777 7 7 next 0 52 state (by decide)
      ⟨by simpa [LoopInvGeneral] using pc, by simpa using counter,
        by simpa using pointer, by intro address _; rfl, valid⟩
  refine ⟨final, steps, cycles, calls, blocks,
    by simpa [LoopInvGeneral] using inv.1,
    inv.2.1, inv.2.2.1, inv.2.2.2.1,
    stepBound, cycleBound, callBound, blockBound, run⟩

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepTrace.step_iteration_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_iteration_trace

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepTrace.step_round_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_round_trace

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepTrace.bounded_loop_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bounded_loop_trace

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepTrace.step_loop_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_loop_trace

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepTrace.chain_round_trace_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chain_round_trace_general

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepTrace.all_chains_trace_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms all_chains_trace_general

end SigGolfCandidate.SphincsVerifierWotsStepTrace
