import SigGolfCandidate.SphincsVerifierWotsDecodeData

namespace SigGolfCandidate.SphincsVerifierWotsChainSetup
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierWotsDecodeData
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def chainSetupState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.ADDI .x10 .x0 194)
  let state := execInstrBr state (.BEQ .x15 .x10 8)
  let state := execInstrBr state (.ADDI .x6 .x0 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 80)
  let state := execInstrBr state (.SD .x28 .x6 0)
  let state := execInstrBr state (.LUI .x6 0x25)
  let state := execInstrBr state (.ADDI .x6 .x6 1148)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  execInstrBr state (.SD .x28 .x6 0)

theorem chainSetup_block (state : MachineState)
    (pc : state.pc = 0x26e0) (checksum : state.getReg .x15 = 194) :
    OrdinarySteps SphincsImages.verify state 11 (chainSetupState state) ∧
    (chainSetupState state).pc = 0x2710 := by
  let s1 := execInstrBr state (.ADDI .x10 .x0 194)
  let s2 := execInstrBr s1 (.BEQ .x15 .x10 8)
  let s3 := execInstrBr s2 (.ADDI .x6 .x0 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x43)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 80)
  let s6 := execInstrBr s5 (.SD .x28 .x6 0)
  let s7 := execInstrBr s6 (.LUI .x6 0x25)
  let s8 := execInstrBr s7 (.ADDI .x6 .x6 1148)
  let s9 := execInstrBr s8 (.LUI .x28 0x43)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 40)
  let s11 := execInstrBr s10 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x26e4 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x26ec := by
    have equal : s1.getReg .x15 = s1.getReg .x10 := by
      simp [s1, execInstrBr, signExtend12, checksum,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    simp [s2, execInstrBr, p1, equal, signExtend13]
  have p3 : s3.pc = 0x26f0 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x26f4 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x26f8 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x26fc := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x2700 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x2704 := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x2708 := by simp [s9, execInstrBr, p8]
  have p10 : s10.pc = 0x270c := by simp [s10, execInstrBr, p9]
  have p11 : s11.pc = 0x2710 := by simp [s11, execInstrBr, p10]
  have trace : OrdinarySteps SphincsImages.verify state 11 s11 := by
    apply OrdinarySteps.step state s1 _ (.base (.ADDI .x10 .x0 194)) 10
    · rw [fetch_index SphincsImages.verify state 1464 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.BEQ .x15 .x10 8)) 9
    · rw [fetch_index SphincsImages.verify s1 1465 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x6 .x0 0)) 8
    · rw [fetch_index SphincsImages.verify s2 1467 (by decide)
        (by simpa using p2)]
      decide
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x43)) 7
    · rw [fetch_index SphincsImages.verify s3 1468 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 80)) 6
    · rw [fetch_index SphincsImages.verify s4 1469 (by decide)
        (by simpa using p4)]
      decide
    · rfl
    apply OrdinarySteps.step s5 s6 _ (.base (.SD .x28 .x6 0)) 5
    · rw [fetch_index SphincsImages.verify s5 1470 (by decide)
        (by simpa using p5)]
      decide
    · simp [s6, ordinaryStep, memoryArgumentsValid, execInstrBr,
        signExtend12, accessValid, rangeValid, MEMORY_BYTES,
        s5, s4, MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne]
    apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x6 0x25)) 4
    · rw [fetch_index SphincsImages.verify s6 1471 (by decide)
        (by simpa using p6)]
      decide
    · rfl
    apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x6 .x6 1148)) 3
    · rw [fetch_index SphincsImages.verify s7 1472 (by decide)
        (by simpa using p7)]
      decide
    · rfl
    apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 0x43)) 2
    · rw [fetch_index SphincsImages.verify s8 1473 (by decide)
        (by simpa using p8)]
      decide
    · rfl
    apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 40)) 1
    · rw [fetch_index SphincsImages.verify s9 1474 (by decide)
        (by simpa using p9)]
      decide
    · rfl
    apply OrdinarySteps.step s10 s11 _ (.base (.SD .x28 .x6 0)) 0
    · rw [fetch_index SphincsImages.verify s10 1475 (by decide)
        (by simpa using p10)]
      decide
    · simp [s11, ordinaryStep, memoryArgumentsValid, execInstrBr,
        signExtend12, accessValid, rangeValid, MEMORY_BYTES,
        s10, s9, s8, s7, MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne]
    exact OrdinarySteps.refl _
  exact ⟨by simpa only [chainSetupState] using trace,
    by simpa only [chainSetupState] using p11⟩

theorem chainSetup_cells (state : MachineState)
    (checksum : state.getReg .x15 = 194) :
    (chainSetupState state).getMem 0x43050 = 0 ∧
    (chainSetupState state).getMem 0x43028 = 0x2547c := by
  simp [chainSetupState, execInstrBr, signExtend12, signExtend13,
    checksum, MachineState.getMem_setMem_eq,
    MachineState.getMem_setMem_ne,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def decodedChainState (state : MachineState) : MachineState :=
  chainSetupState (decoderRun 52 state)

theorem decoder_to_chain (state : MachineState)
    (pc : state.pc = 0x1f20)
    (checksum : state.getReg .x15 + answerSum 52 state = 194) :
    OrdinarySteps SphincsImages.verify state 507
      (decodedChainState state) ∧
    (decodedChainState state).pc = 0x2710 ∧
    (decodedChainState state).getMem 0x43050 = 0 ∧
    (decodedChainState state).getMem 0x43028 = 0x2547c := by
  have decode := decoder_run_all state pc
  have sum : (decoderRun 52 state).getReg .x15 = 194 := by
    rw [decoder_run_checksum 52 state (by decide)]
    exact checksum
  have setup := chainSetup_block (decoderRun 52 state) decode.2 sum
  have cells := chainSetup_cells (decoderRun 52 state) sum
  refine ⟨?_, setup.2, cells.1, cells.2⟩
  simpa [decodedChainState] using decode.1.append setup.1

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainSetup.chainSetup_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainSetup_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainSetup.decoder_to_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decoder_to_chain

end SigGolfCandidate.SphincsVerifierWotsChainSetup
