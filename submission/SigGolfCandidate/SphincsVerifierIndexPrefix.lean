import SigGolfCandidate.SphincsVerifierDigestDecode

/-!
# Verifier digest-index extraction prefix

The first five ordinary instructions after the message HASH answer load its
low word and keep exactly the 34 hypertree-index bits.
-/

namespace SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierMessageHash
open SigGolfCandidate.SphincsVerifierMessageAnswer

def indexValueState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x42)
  let state := execInstrBr state (.ADDI .x6 .x6 0)
  let state := execInstrBr state (.LD .x10 .x6 0)
  let state := execInstrBr state (.SLLI .x10 .x10 30)
  execInstrBr state (.SRLI .x10 .x10 30)

theorem indexValue_block (state : MachineState)
    (pc : state.pc = 0x12a4) :
    OrdinarySteps SphincsImages.verify state 5 (indexValueState state) := by
  let s1 := execInstrBr state (.LUI .x6 0x42)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LD .x10 .x6 0)
  let s4 := execInstrBr s3 (.SLLI .x10 .x10 30)
  let s5 := execInstrBr s4 (.SRLI .x10 .x10 30)
  have p1 : s1.pc = 0x12a8 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x12ac := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x12b0 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x12b4 := by simp [s4, execInstrBr, p3]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x42)) 4
  · rw [fetch_index SphincsImages.verify state 169 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 3
  · rw [fetch_index SphincsImages.verify s1 170 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x10 .x6 0)) 2
  · rw [fetch_index SphincsImages.verify s2 171 (by decide) (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x10 .x10 30)) 1
  · rw [fetch_index SphincsImages.verify s3 172 (by decide) (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SRLI .x10 .x10 30)) 0
  · rw [fetch_index SphincsImages.verify s4 173 (by decide) (by simpa using p4)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem indexValue_pc (state : MachineState) (pc : state.pc = 0x12a4) :
    (indexValueState state).pc = 0x12b8 := by
  simp [indexValueState, execInstrBr, pc]

theorem indexValue_data (state : MachineState) :
    (indexValueState state).getReg .x10 =
      ((state.getMem 0x42000 <<< 30) >>> 30) := by
  simp [indexValueState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

private theorem maskedIndex (answer : BitVec 256) :
    (((answer.extractLsb' 0 64) <<< 30) >>> 30).toNat =
      (answer.extractLsb' 0 34).toNat := by
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  simp only [Nat.pow_zero, Nat.div_one]
  have powers : 2 ^ 64 = 2 ^ 30 * 2 ^ 34 := by norm_num
  rw [powers]
  rw [Nat.mul_comm (answer.toNat % (2 ^ 30 * 2 ^ 34)) (2 ^ 30),
    Nat.mul_mod_mul_left]
  omega

theorem indexValue_eq_digestIndex (state : MachineState)
    (answer : BitVec 256)
    (word : state.getMem 0x42000 = answer.extractLsb' 0 64) :
    ((indexValueState state).getReg .x10).toNat =
      (SphincsSecurity.Concrete.digestIndex
        (SphincsSecurity.truncateMessageDigest answer)).val := by
  rw [indexValue_data, word, maskedIndex]
  change (answer.extractLsb' 0 34).toNat =
    ((answer.extractLsb' 0 SphincsSecurity.messageDigestBits).extractLsb'
      0 SphincsSecurity.totalHeight).toNat
  rw [BitVec.extractLsb'_extractLsb'_of_le (by
    simp [SphincsSecurity.totalHeight, SphincsSecurity.messageDigestBits,
      SphincsSecurity.ftsTrees, SphincsSecurity.ftsTreeHeight])]
  rfl

theorem messageReady_indexValue (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256) :
    OrdinarySteps SphincsImages.verify (writeHash state answer) 5
      (indexValueState (writeHash state answer)) ∧
    ((indexValueState (writeHash state answer)).getReg .x10).toNat =
      (SphincsSecurity.Concrete.digestIndex
        (SphincsSecurity.truncateMessageDigest answer)).val := by
  have nextPc : (writeHash state answer).pc = 0x12a4 := by
    simp [writeHash, pc]
  constructor
  · exact indexValue_block (writeHash state answer) nextPc
  · apply indexValue_eq_digestIndex
    simpa using messageReady_answer_word state pk message randomness
      ready answer 0

/-- info: 'SigGolfCandidate.SphincsVerifierIndexPrefix.indexValue_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms indexValue_block

/-- info: 'SigGolfCandidate.SphincsVerifierIndexPrefix.messageReady_indexValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_indexValue

end SigGolfCandidate.SphincsVerifierIndexPrefix
