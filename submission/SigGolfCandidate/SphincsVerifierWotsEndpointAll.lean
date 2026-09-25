import SigGolfCandidate.SphincsVerifierWotsEndpointFrame

namespace SigGolfCandidate.SphincsVerifierWotsEndpointAll
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsEndpointFrame
open SigGolfCandidate.SphincsVerifierWotsEndpointCopy
open SigGolfCandidate.SphincsVerifierWotsAllChains
open SigGolfCandidate.SphincsVerifierWotsDigitFrame
open SigGolfCandidate.SphincsVerifierWotsLoop
open SigGolfCandidate.SphincsVerifierWotsChainSetup
open SigGolfCandidate.SphincsVerifierWotsDecodeData
set_option maxRecDepth 16384
set_option maxHeartbeats 0

private def History (initial : MachineState) (i : Nat)
    (current : MachineState) : Prop :=
  current.pc = (if i = 52 then 0x298c else 0x2710) ∧
  current.getMem 0x43050 = BitVec.ofNat 64 i ∧
  current.getMem 0x43028 = BitVec.ofNat 64 (0x2547c + 20 * i) ∧
  (∀ address, DigitAddr address →
    current.getMem address = initial.getMem address) ∧
  DigitsValid current ∧
  ∃ midpoint : Fin 52 → MachineState,
    ∀ (chain : Fin 52), chain.val < i →
      (midpoint chain).pc = 0x28ec ∧
      ∀ (index : Fin 5),
        current.getWord32 (word (0x44300 + 20 * chain.val) index) =
          (midpoint chain).getWord32 (word 0x44b00 index)

theorem all_chains_endpoints (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x2710)
    (counter : state.getMem 0x43050 = 0)
    (pointer : state.getMem 0x43028 = 0x2547c)
    (valid : DigitsValid state) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat)
      (midpoint : Fin 52 → MachineState),
      final.pc = 0x298c ∧
      final.getMem 0x43050 = 52 ∧
      final.getMem 0x43028 = 0x2547c + 20 * 52 ∧
      (∀ chain : Fin 52,
        (midpoint chain).pc = 0x28ec ∧
        ∀ index : Fin 5,
          final.getWord32
            (word (0x44300 + 20 * chain.val) index) =
            (midpoint chain).getWord32 (word 0x44b00 index)) ∧
      steps ≤ 728 * 52 ∧
      cycles ≤ 777 * 52 ∧
      calls ≤ 7 * 52 ∧
      blocks ≤ 7 * 52 ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  have next (i : Nat) (current : MachineState)
      (small : i < 52) (inv : History state i current) :
      ∃ (following : MachineState) (steps cycles calls blocks : Nat),
        History state (i + 1) following ∧
        steps ≤ 728 ∧ cycles ≤ 777 ∧ calls ≤ 7 ∧ blocks ≤ 7 ∧
        ∀ (tailSteps : Nat) (result : Execution),
          Executes hash SphincsImages.verify following tailSteps result →
          Executes hash SphincsImages.verify current (tailSteps + steps)
            (result.charge cycles calls blocks) := by
    obtain ⟨currentPc, currentCounter, currentPointer,
      digitFrame, digitValid, midpoint, history⟩ := inv
    let chain : Fin 52 := ⟨i, small⟩
    let digit : Fin 8 := ⟨
      (current.getByte (BitVec.ofNat 64 (0x44000 + i))).toNat,
      digitValid chain⟩
    have decoded : current.getByte
        (BitVec.ofNat 64 (0x44000 + chain.val)) =
        BitVec.ofNat 8 digit.val := by
      simp [chain, digit]
    obtain ⟨following, middle, steps, cycles, calls, blocks,
        nextPc, middlePc, nextCounter, nextPointer, currentValue,
        otherFrame, nextDigitFrame, stepBound, cycleBound,
        callBound, blockBound, run⟩ :=
      chainRound_otherWord hash current chain digit
        (by have ne : i ≠ 52 := by omega
            simpa [History, ne] using currentPc)
        currentCounter currentPointer decoded
    let newMidpoint : Fin 52 → MachineState :=
      fun j => if j.val = i then middle else midpoint j
    refine ⟨following, steps, cycles, calls, blocks,
      ⟨?_, nextCounter, nextPointer, ?_, ?_,
        newMidpoint, ?_⟩,
      by omega, by omega, by omega, by omega, run⟩
    · simpa [chain] using nextPc
    · intro address inside
      exact (nextDigitFrame address inside).trans
        (digitFrame address inside)
    · exact digitsValid_frame current following nextDigitFrame digitValid
    · intro j before
      by_cases same : j.val = i
      · have sameChain : j = chain := Fin.ext (by simpa [chain] using same)
        subst j
        refine ⟨by simp [newMidpoint, chain, middlePc], ?_⟩
        intro index
        simpa [newMidpoint, chain] using currentValue index
      · have old : j.val < i := by omega
        obtain ⟨oldPc, oldValue⟩ := history j old
        have different : chain ≠ j := by
          intro equality
          exact same (by simpa [chain] using congrArg Fin.val equality |>.symm)
        refine ⟨by simpa [newMidpoint, same] using oldPc, ?_⟩
        intro index
        simpa [newMidpoint, same] using
          (otherFrame j index different).trans (oldValue index)
  obtain ⟨final, steps, cycles, calls, blocks,
      inv, stepBound, cycleBound, callBound, blockBound, run⟩ :=
    bounded_loop hash SphincsImages.verify (History state) 52
      728 777 7 7 next 0 52 state (by decide)
      ⟨by simpa [History] using pc, by simpa using counter,
        by simpa using pointer, by intro address _; rfl,
        valid, fun _ => state, by intro j impossible; omega⟩
  obtain ⟨finalPc, finalCounter, finalPointer,
    _, _, midpoint, history⟩ := inv
  refine ⟨final, steps, cycles, calls, blocks, midpoint,
    by simpa [History] using finalPc,
    finalCounter, finalPointer, ?_,
    stepBound, cycleBound, callBound, blockBound, run⟩
  intro chain
  exact history chain (by have := chain.isLt; omega)

/-- info: 'SigGolfCandidate.SphincsVerifierWotsEndpointAll.all_chains_endpoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms all_chains_endpoints

end SigGolfCandidate.SphincsVerifierWotsEndpointAll
