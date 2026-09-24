import SigGolfCandidate.SphincsVerifierFtsParentParameter

/-! Set the 80-byte first FORS parent HASH input and output registers. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsParentParameter
set_option maxRecDepth 16384

def hashRegistersState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x10 0x40)
  let state := execInstrBr state (.ADDI .x10 .x10 0)
  let state := execInstrBr state (.ADDI .x11 .x0 640)
  let state := execInstrBr state (.LUI .x12 0x42)
  let state := execInstrBr state (.ADDI .x12 .x12 0)
  execInstrBr state (.ADDI .x5 .x0 1)

theorem hashRegisters_block (state : MachineState) (pc : state.pc = 0x1b00) :
    OrdinarySteps SphincsImages.verify state 6 (hashRegistersState state) := by
  let s1 := execInstrBr state (.LUI .x10 0x40)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 640)
  let s4 := execInstrBr s3 (.LUI .x12 0x42)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 0)
  let s6 := execInstrBr s5 (.ADDI .x5 .x0 1)
  have p1 : s1.pc = 0x1b04 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1b08 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1b0c := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1b10 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1b14 := by simp [s5, execInstrBr, p4]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x10 0x40)) 5
  · rw [fetch_index SphincsImages.verify state 704 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 4
  · rw [fetch_index SphincsImages.verify s1 705 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 640)) 3
  · rw [fetch_index SphincsImages.verify s2 706 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x42)) 2
  · rw [fetch_index SphincsImages.verify s3 707 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 0)) 1
  · rw [fetch_index SphincsImages.verify s4 708 (by decide)
      (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x5 .x0 1)) 0
  · rw [fetch_index SphincsImages.verify s5 709 (by decide)
      (by simpa using p5)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem hashRegisters_pc (state : MachineState) (pc : state.pc = 0x1b00) :
    (hashRegistersState state).pc = 0x1b18 := by
  simp [hashRegistersState, execInstrBr, pc]

theorem hashRegisters_ready (state : MachineState) :
    (hashRegistersState state).getReg .x10 = 0x40000 ∧
    (hashRegistersState state).getReg .x11 = 640 ∧
    (hashRegistersState state).getReg .x12 = 0x42000 ∧
    (hashRegistersState state).getReg .x5 = 1 := by
  simp [hashRegistersState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]


def parentHashReadyState (state : MachineState) : MachineState :=
  hashRegistersState (parentReadyState state)

theorem parentHashReady_block (state : MachineState) (pc : state.pc = 0x1a70) :
    OrdinarySteps SphincsImages.verify state 42 (parentHashReadyState state) ∧
      (parentHashReadyState state).pc = 0x1b18 ∧
      (parentHashReadyState state).getReg .x10 = 0x40000 ∧
      (parentHashReadyState state).getReg .x11 = 640 ∧
      (parentHashReadyState state).getReg .x12 = 0x42000 ∧
      (parentHashReadyState state).getReg .x5 = 1 := by
  have first := parentReady_block state pc
  have second := hashRegisters_block (parentReadyState state) first.2
  have regs := hashRegisters_ready (parentReadyState state)
  exact ⟨first.1.append second,
    hashRegisters_pc _ first.2, regs.1, regs.2.1, regs.2.2.1,
    regs.2.2.2⟩

end SigGolfCandidate.SphincsVerifierFtsParentSetup
