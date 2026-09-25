import SigGolfCandidate.Execution

namespace SigGolfCandidate.SphincsVerifierWotsLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096

/-- A verifier loop can be certified one iteration at a time. The invariant may
    include the decoded WOTS chain values, current witness pointer, memory
    frame, and exact program counter. This combinator carries exact execution
    and four resource bounds through any number of iterations. -/
theorem bounded_loop (hash : Hash) (image : Image)
    (Inv : Nat → MachineState → Prop)
    (limit : Nat)
    (stepLimit cycleLimit callLimit blockLimit : Nat)
    (step : ∀ (i : Nat) (state : MachineState), i < limit → Inv i state →
      ∃ (next : MachineState) (steps cycles calls blocks : Nat),
        Inv (i + 1) next ∧
        steps ≤ stepLimit ∧ cycles ≤ cycleLimit ∧
        calls ≤ callLimit ∧ blocks ≤ blockLimit ∧
        ∀ (tailSteps : Nat) (result : Execution),
          Executes hash image next tailSteps result →
          Executes hash image state (tailSteps + steps)
            (result.charge cycles calls blocks))
    (start count : Nat) (state : MachineState)
    (within : start + count ≤ limit) (initial : Inv start state) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      Inv (start + count) final ∧
      steps ≤ stepLimit * count ∧ cycles ≤ cycleLimit * count ∧
      calls ≤ callLimit * count ∧ blocks ≤ blockLimit * count ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash image final tailSteps result →
        Executes hash image state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  induction count generalizing start state with
  | zero =>
      refine ⟨state, 0, 0, 0, 0, by simpa using initial,
        by simp, by simp, by simp, by simp, ?_⟩
      intro tailSteps result tail
      simpa [Execution.charge] using tail
  | succ count ih =>
      have small : start < limit := by omega
      obtain ⟨next, a, b, c, d, nextInv, ha, hb, hc, hd, pre⟩ :=
        step start state small initial
      obtain ⟨final, e, f, g, h, finalInv, he, hf, hg, hh, suffix⟩ :=
        ih (start + 1) next (by omega) nextInv
      refine ⟨final, a + e, b + f, c + g, d + h,
        by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalInv,
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [Nat.mul_succ]; omega
      · rw [Nat.mul_succ]; omega
      · rw [Nat.mul_succ]; omega
      · rw [Nat.mul_succ]; omega
      · intro tailSteps result tail
        have tailRun := suffix tailSteps result tail
        have full := pre (tailSteps + e) (result.charge f g h) tailRun
        simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using full

/-- info: 'SigGolfCandidate.SphincsVerifierWotsLoop.bounded_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bounded_loop

end SigGolfCandidate.SphincsVerifierWotsLoop
