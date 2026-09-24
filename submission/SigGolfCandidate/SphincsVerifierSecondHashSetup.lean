import SigGolfCandidate.SphincsVerifierSecondHashParameter

/-!
# Second verifier HASH setup

The verifier selects the 112-byte input at `0x40000`, the output at `0x42000`,
and the HASH service. The next instruction is ECALL at PC `0x12a0`.
-/

namespace SigGolfCandidate.SphincsVerifierSecondHashSetup
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierSecondHashParameter

def hashRegistersState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x10 0x40)
  let state := execInstrBr state (.ADDI .x10 .x10 0)
  let state := execInstrBr state (.ADDI .x11 .x0 896)
  let state := execInstrBr state (.LUI .x12 0x42)
  let state := execInstrBr state (.ADDI .x12 .x12 0)
  execInstrBr state (.ADDI .x5 .x0 1)

theorem hashRegisters_block (state : MachineState) (pc : state.pc = 0x1288) :
    OrdinarySteps SphincsImages.verify state 6 (hashRegistersState state) := by
  let s1 := execInstrBr state (.LUI .x10 0x40)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 896)
  let s4 := execInstrBr s3 (.LUI .x12 0x42)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 0)
  let s6 := execInstrBr s5 (.ADDI .x5 .x0 1)
  have p1 : s1.pc = 0x128c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1290 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1294 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1298 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x129c := by simp [s5, execInstrBr, p4]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x10 0x40)) 5
  · rw [fetch_index SphincsImages.verify state 162 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 4
  · rw [fetch_index SphincsImages.verify s1 163 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 896)) 3
  · rw [fetch_index SphincsImages.verify s2 164 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x42)) 2
  · rw [fetch_index SphincsImages.verify s3 165 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 0)) 1
  · rw [fetch_index SphincsImages.verify s4 166 (by decide)
      (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x5 .x0 1)) 0
  · rw [fetch_index SphincsImages.verify s5 167 (by decide)
      (by simpa using p5)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem hashRegisters_pc (state : MachineState) (pc : state.pc = 0x1288) :
    (hashRegistersState state).pc = 0x12a0 := by
  simp [hashRegistersState, execInstrBr, pc]

theorem hashRegisters_ready (state : MachineState) :
    (hashRegistersState state).getReg .x10 = 0x40000 ∧
    (hashRegistersState state).getReg .x11 = 896 ∧
    (hashRegistersState state).getReg .x12 = 0x42000 ∧
    (hashRegistersState state).getReg .x5 = 1 := by
  simp [hashRegistersState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def secondHashReadyState (state : MachineState) : MachineState :=
  hashRegistersState (headerAndParameterState state)

theorem secondHashReady_block (state : MachineState) (pc : state.pc = 0x11f8) :
    OrdinarySteps SphincsImages.verify state 42 (secondHashReadyState state) := by
  have first := headerAndParameter_block state pc
  have headerPc := SphincsVerifierSecondHashTag.header_next_pc state pc
  have parameterPc := parameter_next_pc
    (SphincsVerifierSecondHashTag.headerState state) headerPc
  have second := hashRegisters_block (headerAndParameterState state)
    (by simpa [headerAndParameterState] using parameterPc)
  simpa [secondHashReadyState] using first.append second

theorem secondHashReady_pc (state : MachineState) (pc : state.pc = 0x11f8) :
    (secondHashReadyState state).pc = 0x12a0 := by
  have headerPc := SphincsVerifierSecondHashTag.header_next_pc state pc
  have parameterPc := parameter_next_pc
    (SphincsVerifierSecondHashTag.headerState state) headerPc
  exact hashRegisters_pc (headerAndParameterState state)
    (by simpa [headerAndParameterState] using parameterPc)

theorem secondHashReady_regs (state : MachineState) :
    (secondHashReadyState state).getReg .x10 = 0x40000 ∧
    (secondHashReadyState state).getReg .x11 = 896 ∧
    (secondHashReadyState state).getReg .x12 = 0x42000 ∧
    (secondHashReadyState state).getReg .x5 = 1 :=
  hashRegisters_ready _

/-- info: 'SigGolfCandidate.SphincsVerifierSecondHashSetup.secondHashReady_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms secondHashReady_block

end SigGolfCandidate.SphincsVerifierSecondHashSetup
