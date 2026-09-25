import SigGolfCandidate.SphincsVerifierWotsAllChains
import SigGolfCandidate.SphincsVerifierFtsRootCopy

namespace SigGolfCandidate.SphincsVerifierWotsRootCopy
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsRootCopy
open SigGolfCandidate.SphincsVerifierMessageCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def rootCopySetupState (state : MachineState) : MachineState :=
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 16)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.LUI .x6 0x44)
  let s6 := execInstrBr s5 (.ADDI .x6 .x6 768)
  let s7 := execInstrBr s6 (.LUI .x7 0x40)
  let s8 := execInstrBr s7 (.ADDI .x7 .x7 40)
  let s9 := execInstrBr s8 (.ADDI .x10 .x0 130)
  s9

theorem rootCopySetup_block (state : MachineState)
    (pc : state.pc = 0x298c) :
    OrdinarySteps SphincsImages.verify state 9 (rootCopySetupState state) ∧
    (rootCopySetupState state).pc = 0x29b0 ∧
    (rootCopySetupState state).getReg .x6 = 0x44300 ∧
    (rootCopySetupState state).getReg .x7 = 0x40028 ∧
    (rootCopySetupState state).getReg .x10 = 130 := by
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 16)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.LUI .x6 0x44)
  let s6 := execInstrBr s5 (.ADDI .x6 .x6 768)
  let s7 := execInstrBr s6 (.LUI .x7 0x40)
  let s8 := execInstrBr s7 (.ADDI .x7 .x7 40)
  let s9 := execInstrBr s8 (.ADDI .x10 .x0 130)
  have p1 : s1.pc = 0x2990 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x2994 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x2998 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x299c := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x29a0 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x29a4 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x29a8 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x29ac := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x29b0 := by simp [s9, execInstrBr, p8]
  have trace : OrdinarySteps SphincsImages.verify state 9 s9 := by
    apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 0)) 8
    · rw [fetch_index SphincsImages.verify state 1635 (by decide) (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x43)) 7
    · rw [fetch_index SphincsImages.verify s1 1636 (by decide) (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 16)) 6
    · rw [fetch_index SphincsImages.verify s2 1637 (by decide) (by simpa using p2)]
      decide
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 5
    · rw [fetch_index SphincsImages.verify s3 1638 (by decide) (by simpa using p3)]
      decide
    · simp [s4, s3, s2, s1, ordinaryStep, memoryArgumentsValid, accessValid, rangeValid, execInstrBr, signExtend12, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x6 0x44)) 4
    · rw [fetch_index SphincsImages.verify s4 1639 (by decide) (by simpa using p4)]
      decide
    · rfl
    apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x6 .x6 768)) 3
    · rw [fetch_index SphincsImages.verify s5 1640 (by decide) (by simpa using p5)]
      decide
    · rfl
    apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x7 0x40)) 2
    · rw [fetch_index SphincsImages.verify s6 1641 (by decide) (by simpa using p6)]
      decide
    · rfl
    apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x7 .x7 40)) 1
    · rw [fetch_index SphincsImages.verify s7 1642 (by decide) (by simpa using p7)]
      decide
    · rfl
    apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x10 .x0 130)) 0
    · rw [fetch_index SphincsImages.verify s8 1643 (by decide) (by simpa using p8)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [rootCopySetupState] using trace, ?_, ?_, ?_, ?_⟩
  · simpa only [rootCopySetupState] using p9
  · simp [rootCopySetupState, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  · simp [rootCopySetupState, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  · simp [rootCopySetupState, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem rootCopy_code : CopyCode SphincsImages.verify 0x29b0 := by decide

theorem rootCopy_all (state : MachineState)
    (pc : state.pc = 0x29b0)
    (source : state.getReg .x6 = 0x44300)
    (destination : state.getReg .x7 = 0x40028)
    (count : state.getReg .x10 = 130) :
    ∃ final,
      OrdinarySteps SphincsImages.verify state 780 final ∧
      final.pc = 0x29c8 ∧
      (∀ i, i < 130 →
        final.getMem (BitVec.ofNat 64 (0x40028 + 8 * i)) =
          state.getMem (BitVec.ofNat 64 (0x44300 + 8 * i))) ∧
      (∀ address,
        (∀ i, i < 130 →
          address ≠ BitVec.ofNat 64 (0x40028 + 8 * i)) →
        final.getMem address = state.getMem address) := by
  have inv : CopyInvariant 0x29b0 0x44300 0x40028 130 130 state := by
    refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
    · simpa using pc
    · simpa using source
    · simpa using destination
    · simpa using count
  obtain ⟨final, trace, done, copied, frame⟩ :=
    copy_all SphincsImages.verify 0x29b0 rootCopy_code
      0x44300 0x40028 130 state inv
      (by decide) (by decide) (by decide) (by decide)
      (Or.inr (by decide))
  refine ⟨final, by simpa using trace, ?_, copied, frame⟩
  simpa [CopyInvariant] using done.2.2.1

theorem rootCopy_setup_and_all (state : MachineState)
    (pc : state.pc = 0x298c) :
    ∃ final,
      OrdinarySteps SphincsImages.verify state 789 final ∧
      final.pc = 0x29c8 ∧
      (∀ i, i < 130 →
        final.getMem (BitVec.ofNat 64 (0x40028 + 8 * i)) =
          (rootCopySetupState state).getMem
            (BitVec.ofNat 64 (0x44300 + 8 * i))) := by
  obtain ⟨setup, setupPc, source, destination, count⟩ :=
    rootCopySetup_block state pc
  obtain ⟨final, copied, finalPc, payload, _⟩ :=
    rootCopy_all (rootCopySetupState state) setupPc
      source destination count
  refine ⟨final, ?_, finalPc, payload⟩
  simpa using setup.append copied

theorem rootHash_site (state : MachineState) (pc : state.pc = 0x2a70) :
    fetch SphincsImages.verify state = some (.base .ECALL) := by
  rw [fetch_index SphincsImages.verify state 1692 (by decide)
    (by simpa using pc)]
  decide

theorem rootHash_arguments (state : MachineState)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 8640)
    (destination : state.getReg .x12 = 0x42000) :
    hashArgumentsValid state = true ∧
      compressions (hashInput state).1 = 17 := by
  constructor
  · simp [hashArgumentsValid, source, bits, destination,
      accessValid, rangeValid, MEMORY_BYTES]
  · simp [hashInput, source, bits, compressions]

theorem rootHash_step (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x2a70)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 8640)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash state (hash (hashInput state))) steps result) :
    Executes hash SphincsImages.verify state (steps + 1)
      (result.charge 136 1 17) := by
  have args := rootHash_arguments state source bits destination
  have step := Executes.hash state steps result (rootHash_site state pc)
    service args.1 tail
  simpa [args.2] using step

/-- info: 'SigGolfCandidate.SphincsVerifierWotsRootCopy.rootCopy_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootCopy_all

/-- info: 'SigGolfCandidate.SphincsVerifierWotsRootCopy.rootCopy_setup_and_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootCopy_setup_and_all

/-- info: 'SigGolfCandidate.SphincsVerifierWotsRootCopy.rootHash_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootHash_step

end SigGolfCandidate.SphincsVerifierWotsRootCopy
