import SigGolfCandidate.SphincsVerifierFtsForestHeader

namespace SigGolfCandidate.SphincsVerifierFtsForestHashReady
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsForestHeader
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def forestParameterPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x23)
  let state := execInstrBr state (.ADDI .x6 .x6 (-844))
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 20)

theorem forestParameterPointers_regs (state : MachineState) :
    (forestParameterPointers state).getReg .x6 = 0x22cb4 ∧
    (forestParameterPointers state).getReg .x7 = 0x40014 := by
  simp [forestParameterPointers, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem forestParameterPointers_pc (state : MachineState) (pc : state.pc = 0x1ce4) :
    (forestParameterPointers state).pc = 0x1cf4 := by
  simp [forestParameterPointers, execInstrBr, pc]

theorem forestParameterPointers_block (state : MachineState) (pc : state.pc = 0x1ce4) :
    OrdinarySteps SphincsImages.verify state 4 (forestParameterPointers state) := by
  let s1 := execInstrBr state (.LUI .x6 0x23)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-844))
  let s3 := execInstrBr s2 (.LUI .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 20)
  have p1 : s1.pc = 0x1ce8 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1cec := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1cf0 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x23)) 3
  · rw [fetch_index SphincsImages.verify state 825 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-844))) 2
  · rw [fetch_index SphincsImages.verify s1 826 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x40)) 1
  · rw [fetch_index SphincsImages.verify s2 827 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 20)) 0
  · rw [fetch_index SphincsImages.verify s3 828 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

set_option maxHeartbeats 0 in
theorem forest_parameter_copy_code : Copy20Code SphincsImages.verify 829 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

def forestParameterState (state : MachineState) : MachineState :=
  copyRootState (forestParameterPointers state)

theorem forestParameter_block (state : MachineState) (pc : state.pc = 0x1ce4) :
    OrdinarySteps SphincsImages.verify state 14 (forestParameterState state) := by
  have pointers := forestParameterPointers_block state pc
  have copy := copy20_block SphincsImages.verify 829 forest_parameter_copy_code
    (forestParameterPointers state) (by simpa using forestParameterPointers_pc state pc)
    (Or.inr (Or.inr (forestParameterPointers_regs state).1))
    (Or.inr (Or.inr (forestParameterPointers_regs state).2)) (by decide)
  simpa [forestParameterState] using pointers.append copy

theorem forestParameter_next_pc (state : MachineState) (pc : state.pc = 0x1ce4) :
    (forestParameterState state).pc = 0x1d1c := by
  exact copy20_final_pc (forestParameterPointers state) 829
    (by simpa using forestParameterPointers_pc state pc)

def forestHashRegistersState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x10 0x40)
  let state := execInstrBr state (.ADDI .x10 .x10 0)
  let state := execInstrBr state (.LUI .x11 0x1)
  let state := execInstrBr state (.ADDI .x11 .x11 64)
  let state := execInstrBr state (.LUI .x12 0x42)
  let state := execInstrBr state (.ADDI .x12 .x12 0)
  execInstrBr state (.ADDI .x5 .x0 1)

theorem forestHashRegisters_block (state : MachineState)
    (pc : state.pc = 0x1d1c) :
    OrdinarySteps SphincsImages.verify state 7 (forestHashRegistersState state) := by
  let s1 := execInstrBr state (.LUI .x10 0x40)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.LUI .x11 0x1)
  let s4 := execInstrBr s3 (.ADDI .x11 .x11 64)
  let s5 := execInstrBr s4 (.LUI .x12 0x42)
  let s6 := execInstrBr s5 (.ADDI .x12 .x12 0)
  let s7 := execInstrBr s6 (.ADDI .x5 .x0 1)
  have p1 : s1.pc = 0x1d20 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1d24 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1d28 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1d2c := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1d30 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1d34 := by simp [s6, execInstrBr, p5]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x10 0x40)) 6
  · rw [fetch_index SphincsImages.verify state 839 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 5
  · rw [fetch_index SphincsImages.verify s1 840 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x11 0x1)) 4
  · rw [fetch_index SphincsImages.verify s2 841 (by decide) (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x11 .x11 64)) 3
  · rw [fetch_index SphincsImages.verify s3 842 (by decide) (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x12 0x42)) 2
  · rw [fetch_index SphincsImages.verify s4 843 (by decide) (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x12 .x12 0)) 1
  · rw [fetch_index SphincsImages.verify s5 844 (by decide) (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x5 .x0 1)) 0
  · rw [fetch_index SphincsImages.verify s6 845 (by decide) (by simpa using p6)]
    decide
  · rfl
  exact OrdinarySteps.refl _

def forestHashReadyState (state : MachineState) : MachineState :=
  forestHashRegistersState (forestParameterState (forestHeaderState state))

theorem forestHashReady_block (state : MachineState)
    (pc : state.pc = 0x1c8c) :
    OrdinarySteps SphincsImages.verify state 43 (forestHashReadyState state) ∧
    (forestHashReadyState state).pc = 0x1d38 ∧
    (forestHashReadyState state).getReg .x10 = 0x40000 ∧
    (forestHashReadyState state).getReg .x11 = 4160 ∧
    (forestHashReadyState state).getReg .x12 = 0x42000 ∧
    (forestHashReadyState state).getReg .x5 = 1 := by
  have header := forestHeader_block state pc
  have parameter := forestParameter_block (forestHeaderState state) header.2
  have parameterPc := forestParameter_next_pc (forestHeaderState state) header.2
  have registers := forestHashRegisters_block
    (forestParameterState (forestHeaderState state)) parameterPc
  have readyPc : (forestHashReadyState state).pc = 0x1d38 := by
    simp [forestHashReadyState, forestHashRegistersState, execInstrBr, parameterPc]
  have readyRegs :
      (forestHashReadyState state).getReg .x10 = 0x40000 ∧
      (forestHashReadyState state).getReg .x11 = 4160 ∧
      (forestHashReadyState state).getReg .x12 = 0x42000 ∧
      (forestHashReadyState state).getReg .x5 = 1 := by
    simp [forestHashReadyState, forestHashRegistersState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact ⟨by simpa only [forestHashReadyState, show 22 + 14 + 7 = 43 by decide]
    using (header.1.append parameter).append registers, readyPc,
    readyRegs.1, readyRegs.2.1, readyRegs.2.2.1, readyRegs.2.2.2⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestHashReady.forestHashReady_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestHashReady_block

end SigGolfCandidate.SphincsVerifierFtsForestHashReady
