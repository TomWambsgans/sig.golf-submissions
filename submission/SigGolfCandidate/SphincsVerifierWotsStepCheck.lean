import SigGolfCandidate.SphincsVerifierWotsChainEntry

namespace SigGolfCandidate.SphincsVerifierWotsStepCheck
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def stepCheckState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 88)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.ADDI .x7 .x0 7)
  execInstrBr state (.BEQ .x6 .x7 360)

theorem stepCheck_block (state : MachineState) (step : Fin 8)
    (pc : state.pc = 0x2774)
    (cell : state.getMem 0x43058 = BitVec.ofNat 64 step.val) :
    OrdinarySteps SphincsImages.verify state 5 (stepCheckState state) ∧
    (stepCheckState state).pc =
      (if step.val = 7 then 0x28ec else 0x2788) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 88)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 7)
  let s5 := execInstrBr s4 (.BEQ .x6 .x7 360)
  have p1 : s1.pc = 0x2778 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x277c := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x2780 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x2784 := by simp [s4, execInstrBr, p3]
  have trace : OrdinarySteps SphincsImages.verify state 5 s5 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 4
    · rw [fetch_index SphincsImages.verify state 1501 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 88)) 3
    · rw [fetch_index SphincsImages.verify s1 1502 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 2
    · rw [fetch_index SphincsImages.verify s2 1503 (by decide)
        (by simpa using p2)]
      decide
    · simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s2, s1,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x0 7)) 1
    · rw [fetch_index SphincsImages.verify s3 1504 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.BEQ .x6 .x7 360)) 0
    · rw [fetch_index SphincsImages.verify s4 1505 (by decide)
        (by simpa using p4)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [stepCheckState] using trace, ?_⟩
  have loaded : s4.getReg .x6 = BitVec.ofNat 64 step.val := by
    simpa [s4, s3, s2, s1, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using cell
  have seven : s4.getReg .x7 = 7 := by
    simp [s4, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  change s5.pc = _
  fin_cases step <;>
    simp [s5, execInstrBr, p4, loaded, seven,
      signExtend13]

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepCheck.stepCheck_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepCheck_block

end SigGolfCandidate.SphincsVerifierWotsStepCheck
