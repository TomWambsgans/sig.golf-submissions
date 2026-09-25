import SigGolfCandidate.SphincsVerifierWotsDigitFrame

namespace SigGolfCandidate.SphincsVerifierWotsFullChain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsStepCheck
open SigGolfCandidate.SphincsVerifierWotsStepIteration
open SigGolfCandidate.SphincsVerifierWotsOuterFrame
open SigGolfCandidate.SphincsVerifierWotsDigitFrame
open SigGolfCandidate.SphincsVerifierWotsLoop
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def Preserved (address : Word) : Prop :=
  Control address ∨ DigitAddr address

theorem preserved_round_frame (hash : Hash) (state : MachineState)
    (address : Word) (preserved : Preserved address) :
    (stepRound hash state).getMem address = state.getMem address := by
  rcases preserved with control | digit
  · exact stepRound_controlFrame hash state address control
  · exact stepRound_digitFrame hash state address digit

theorem stepLoop_to_chain_end_preserved (hash : Hash) (start : Fin 8)
    (state : MachineState)
    (pc : state.pc = 0x2774)
    (cell : state.getMem 0x43058 = BitVec.ofNat 64 start.val) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc = 0x28ec ∧
      (∀ address, Preserved address →
        final.getMem address = state.getMem address) ∧
      steps ≤ 94 * (7 - start.val) + 5 ∧
      cycles ≤ 101 * (7 - start.val) + 5 ∧
      calls ≤ 7 - start.val ∧
      blocks ≤ 7 - start.val ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
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
        ∀ (tailSteps : Nat) (result : Execution),
          Executes hash SphincsImages.verify following tailSteps result →
          Executes hash SphincsImages.verify current (tailSteps + steps)
            (result.charge cycles calls blocks) := by
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
      · intro address control
        exact (preserved_round_frame hash current address control).trans
          (inv.2.2 address control)
    · intro tailSteps result tail
      exact stepRound_exec hash current digit inv.1 currentCell small
        tailSteps result tail
  obtain ⟨seven, steps, cycles, calls, blocks, finalInv,
      stepBound, cycleBound, callBound, blockBound, run⟩ :=
    bounded_loop hash SphincsImages.verify Inv (7 - start.val)
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
  · intro address control
    have frame : (stepCheckState seven).getMem address =
        seven.getMem address := by
      simp [stepCheckState, execInstrBr]
    exact frame.trans (finalInv.2.2 address control)
  · intro tailSteps result tail
    have after := checked.1.then_executes tail
    have before := run (tailSteps + 5) (result.charge 5 0 0) after
    simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using before

/-- info: 'SigGolfCandidate.SphincsVerifierWotsFullChain.stepLoop_to_chain_end_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepLoop_to_chain_end_preserved

end SigGolfCandidate.SphincsVerifierWotsFullChain
