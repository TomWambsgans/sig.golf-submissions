import SigGolfCandidate.SphincsVerifierIndexPrefix

/-!
# Verifier hypertree-index storage

Six instructions copy the 34-bit digest index to the shared index and
message-index cells used by the FORS and hypertree loops.
-/

namespace SigGolfCandidate.SphincsVerifierIndexStore
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierMessageHash

def indexStoredState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 24)
  let state := execInstrBr state (.SD .x28 .x10 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 120)
  execInstrBr state (.SD .x28 .x10 0)

theorem indexStore_block (state : MachineState)
    (pc : state.pc = 0x12b8) :
    OrdinarySteps SphincsImages.verify state 6 (indexStoredState state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 24)
  let s3 := execInstrBr s2 (.SD .x28 .x10 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x43)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 120)
  let s6 := execInstrBr s5 (.SD .x28 .x10 0)
  have p1 : s1.pc = 0x12bc := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x12c0 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x12c4 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x12c8 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x12cc := by simp [s5, execInstrBr, p4]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 5
  · rw [fetch_index SphincsImages.verify state 174 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 24)) 4
  · rw [fetch_index SphincsImages.verify s1 175 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x28 .x10 0)) 3
  · rw [fetch_index SphincsImages.verify s2 176 (by decide) (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s3 177 (by decide) (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 120)) 1
  · rw [fetch_index SphincsImages.verify s4 178 (by decide) (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SD .x28 .x10 0)) 0
  · rw [fetch_index SphincsImages.verify s5 179 (by decide) (by simpa using p5)]
    decide
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem indexStored_pc (state : MachineState) (pc : state.pc = 0x12b8) :
    (indexStoredState state).pc = 0x12d0 := by
  simp [indexStoredState, execInstrBr, pc]

theorem indexStored_data (state : MachineState) :
    (indexStoredState state).getMem 0x43018 = state.getReg .x10 ∧
    (indexStoredState state).getMem 0x43078 = state.getReg .x10 := by
  constructor <;>
    simp [indexStoredState, execInstrBr, signExtend12,
      MachineState.getMem_setMem_ne, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

theorem messageReady_indexStored (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256) :
    let final := indexStoredState (indexValueState (writeHash state answer))
    OrdinarySteps SphincsImages.verify (writeHash state answer) 11 final ∧
      final.pc = 0x12d0 ∧
      final.getMem 0x43018 = BitVec.ofNat 64
        (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest answer)).val ∧
      final.getMem 0x43078 = BitVec.ofNat 64
        (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest answer)).val := by
  obtain ⟨front, index⟩ :=
    messageReady_indexValue state pk message randomness ready pc answer
  have middlePc := indexValue_pc (writeHash state answer) (by
    simp [writeHash, pc])
  have suffix := indexStore_block
    (indexValueState (writeHash state answer)) middlePc
  have stored := indexStored_data (indexValueState (writeHash state answer))
  have indexWord : (indexValueState (writeHash state answer)).getReg .x10 =
      BitVec.ofNat 64 (SphincsSecurity.Concrete.digestIndex
        (SphincsSecurity.truncateMessageDigest answer)).val := by
    apply BitVec.eq_of_toNat_eq
    have bound : (SphincsSecurity.Concrete.digestIndex
        (SphincsSecurity.truncateMessageDigest answer)).val < 2 ^ 64 := by
      have h := (SphincsSecurity.Concrete.digestIndex
        (SphincsSecurity.truncateMessageDigest answer)).isLt
      simp [SphincsSecurity.totalHeight] at h
      omega
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using index
  exact ⟨by simpa using front.append suffix,
    indexStored_pc _ middlePc,
    stored.1.trans indexWord,
    stored.2.trans indexWord⟩

/-- info: 'SigGolfCandidate.SphincsVerifierIndexStore.indexStore_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms indexStore_block

/-- info: 'SigGolfCandidate.SphincsVerifierIndexStore.messageReady_indexStored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_indexStored

end SigGolfCandidate.SphincsVerifierIndexStore
