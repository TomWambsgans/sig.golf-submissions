import SigGolfCandidate.SphincsVerifierFtsHeader

/-!
# First FORS HASH public-parameter copy

Four pointer instructions and five load/store pairs move the submitted public
parameter to bytes 20–39 of the first FORS HASH input.
-/

namespace SigGolfCandidate.SphincsVerifierFtsParameter
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
set_option maxRecDepth 16384

def parameterPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x23)
  let state := execInstrBr state (.ADDI .x6 .x6 (-844))
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 20)

theorem parameterPointers_regs (state : MachineState) :
    (parameterPointers state).getReg .x6 = 0x22cb4 ∧
    (parameterPointers state).getReg .x7 = 0x40014 := by
  simp [parameterPointers, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem parameterPointers_pc (state : MachineState) (pc : state.pc = 0x1878) :
    (parameterPointers state).pc = 0x1888 := by
  simp [parameterPointers, execInstrBr, pc]

theorem parameterPointers_block (state : MachineState) (pc : state.pc = 0x1878) :
    OrdinarySteps SphincsImages.verify state 4 (parameterPointers state) := by
  let s1 := execInstrBr state (.LUI .x6 0x23)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-844))
  let s3 := execInstrBr s2 (.LUI .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 20)
  have p1 : s1.pc = 0x187c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1880 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1884 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x23)) 3
  · rw [fetch_index SphincsImages.verify state 542 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-844))) 2
  · rw [fetch_index SphincsImages.verify s1 543 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x40)) 1
  · rw [fetch_index SphincsImages.verify s2 544 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 20)) 0
  · rw [fetch_index SphincsImages.verify s3 545 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

set_option maxHeartbeats 0 in
theorem parameter_copy_code : Copy20Code SphincsImages.verify 546 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

def parameterState (state : MachineState) : MachineState :=
  copyRootState (parameterPointers state)

theorem parameter_block (state : MachineState) (pc : state.pc = 0x1878) :
    OrdinarySteps SphincsImages.verify state 14 (parameterState state) := by
  have pointers := parameterPointers_block state pc
  have copy := copy20_block SphincsImages.verify 546 parameter_copy_code
    (parameterPointers state) (by simpa using parameterPointers_pc state pc)
    (Or.inr (Or.inr (parameterPointers_regs state).1))
    (Or.inr (Or.inr (parameterPointers_regs state).2)) (by decide)
  simpa [parameterState] using pointers.append copy

theorem parameter_next_pc (state : MachineState) (pc : state.pc = 0x1878) :
    (parameterState state).pc = 0x18b0 := by
  exact copy20_final_pc (parameterPointers state) 546
    (by simpa using parameterPointers_pc state pc)

def headerAndParameterState (state : MachineState) : MachineState :=
  parameterState (SphincsVerifierFtsHeader.headerState state)

theorem headerAndParameter_block (state : MachineState) (pc : state.pc = 0x1820) :
    OrdinarySteps SphincsImages.verify state 36 (headerAndParameterState state) := by
  have header := SphincsVerifierFtsHeader.header_block state pc
  have headerPc := SphincsVerifierFtsHeader.header_next_pc state pc
  have parameter := parameter_block
    (SphincsVerifierFtsHeader.headerState state) headerPc
  simpa [headerAndParameterState] using header.append parameter

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParameter.headerAndParameter_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms headerAndParameter_block

end SigGolfCandidate.SphincsVerifierFtsParameter
