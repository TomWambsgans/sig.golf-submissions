import SigGolfCandidate.SphincsVerifierFtsParentHeader
import SigGolfCandidate.SphincsVerifierFtsParameter

/-! Copy the public parameter into the first FORS parent HASH input. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentParameter
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

theorem parameterPointers_pc (state : MachineState) (pc : state.pc = 0x1ac8) :
    (parameterPointers state).pc = 0x1ad8 := by
  simp [parameterPointers, execInstrBr, pc]

theorem parameterPointers_block (state : MachineState) (pc : state.pc = 0x1ac8) :
    OrdinarySteps SphincsImages.verify state 4 (parameterPointers state) := by
  let s1 := execInstrBr state (.LUI .x6 0x23)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-844))
  let s3 := execInstrBr s2 (.LUI .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 20)
  have p1 : s1.pc = 0x1acc := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1ad0 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1ad4 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x23)) 3
  · rw [fetch_index SphincsImages.verify state 690 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-844))) 2
  · rw [fetch_index SphincsImages.verify s1 691 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x40)) 1
  · rw [fetch_index SphincsImages.verify s2 692 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 20)) 0
  · rw [fetch_index SphincsImages.verify s3 693 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

set_option maxHeartbeats 0 in
theorem parameter_copy_code : Copy20Code SphincsImages.verify 694 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

def parameterState (state : MachineState) : MachineState :=
  copyRootState (parameterPointers state)

theorem parameter_block (state : MachineState) (pc : state.pc = 0x1ac8) :
    OrdinarySteps SphincsImages.verify state 14 (parameterState state) := by
  have pointers := parameterPointers_block state pc
  have copy := copy20_block SphincsImages.verify 694 parameter_copy_code
    (parameterPointers state) (by simpa using parameterPointers_pc state pc)
    (Or.inr (Or.inr (parameterPointers_regs state).1))
    (Or.inr (Or.inr (parameterPointers_regs state).2)) (by decide)
  simpa [parameterState] using pointers.append copy

theorem parameter_next_pc (state : MachineState) (pc : state.pc = 0x1ac8) :
    (parameterState state).pc = 0x1b00 := by
  exact copy20_final_pc (parameterPointers state) 694
    (by simpa using parameterPointers_pc state pc)


def parentReadyState (state : MachineState) : MachineState :=
  parameterState (SphincsVerifierFtsParentHeader.parentHeaderState state)

theorem parentReady_block (state : MachineState) (pc : state.pc = 0x1a70) :
    OrdinarySteps SphincsImages.verify state 36 (parentReadyState state) ∧
      (parentReadyState state).pc = 0x1b00 := by
  have header := SphincsVerifierFtsParentHeader.parentHeader_block state pc
  have parameter := parameter_block
    (SphincsVerifierFtsParentHeader.parentHeaderState state) header.2
  exact ⟨header.1.append parameter,
    parameter_next_pc _ header.2⟩

end SigGolfCandidate.SphincsVerifierFtsParentParameter
