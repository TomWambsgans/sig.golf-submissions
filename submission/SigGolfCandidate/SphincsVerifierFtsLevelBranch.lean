import SigGolfCandidate.SphincsVerifierFtsLevelInit

/-! Read the first FORS authentication-path selector and isolate its low bit. -/

namespace SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierFtsResult
set_option maxRecDepth 16384

def parityState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 112)
  let state := execInstrBr state (.LD .x6 .x28 0)
  execInstrBr state (.ANDI .x6 .x6 1)

theorem parity_pc (state : MachineState) (pc : state.pc = 0x1914) :
    (parityState state).pc = 0x1924 := by
  simp [parityState, execInstrBr, pc]

theorem parity_block (state : MachineState) (pc : state.pc = 0x1914) :
    OrdinarySteps SphincsImages.verify state 4 (parityState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 112)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ANDI .x6 .x6 1)
  have p1 : s1.pc = 0x1918 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x191c := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1920 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
  · rw [fetch_index SphincsImages.verify state 581 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 112)) 2
  · rw [fetch_index SphincsImages.verify s1 582 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
  · rw [fetch_index SphincsImages.verify s2 583 (by decide)
      (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ANDI .x6 .x6 1)) 0
  · rw [fetch_index SphincsImages.verify s3 584 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem parity_reg (state : MachineState) :
    (parityState state).getReg .x6 = state.getMem 0x43070 &&& 1 := by
  simp [parityState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem parity_mem (state : MachineState) (address : Word) :
    (parityState state).getMem address = state.getMem address := by
  simp [parityState, execInstrBr]

theorem parity_preserve_witness (state : MachineState)
    (signature : SphincsSecurity.Signature)
    (witness : SphincsVerifierFtsEarlyFrame.FtsWitness state signature) :
    SphincsVerifierFtsEarlyFrame.FtsWitness (parityState state)
      signature := by
  apply SphincsVerifierFtsEarlyFrame.FtsWitness.transport
    state _ signature witness
  intro i hi
  simp only [MachineState.getByte]
  rw [parity_mem]

set_option maxHeartbeats 0 in
theorem firstFtsLevelParity (state : MachineState)
    (signature : SphincsSecurity.Signature) (answer : BitVec 256)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (witness : SphincsVerifierFtsEarlyFrame.FtsWitness state signature) :
    let hashed := writeHash state answer
    let start := levelInitState (resultState hashed)
    let parity := parityState start
    OrdinarySteps SphincsImages.verify hashed 22 parity ∧
      parity.pc = 0x1924 ∧
      parity.getReg .x6 = start.getMem 0x43070 &&& 1 ∧
      SphincsVerifierFtsEarlyFrame.FtsWitness parity signature := by
  let hashed := writeHash state answer
  let start := levelInitState (resultState hashed)
  obtain ⟨trace, startPc, _, preserved, _⟩ :=
    firstFtsLevelStart state signature answer pc source bits destination witness
  exact ⟨trace.append (parity_block start startPc),
    parity_pc start startPc, parity_reg start,
    parity_preserve_witness start signature preserved⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLevelBranch.parity_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parity_block

end SigGolfCandidate.SphincsVerifierFtsLevelBranch
