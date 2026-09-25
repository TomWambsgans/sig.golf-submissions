import SigGolfCandidate.SphincsSignTopHashSite
import SigGolfCandidate.SphincsVerifierFtsResult

/-! The exact signer image copies a top-node HASH answer into CURRENT. -/

namespace SigGolfCandidate.SphincsSignTopHashResult
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierFtsResult

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

set_option maxHeartbeats 0 in
theorem sign_resultPointers_block (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 42608)) :
    OrdinarySteps SphincsImages.sign state 4 (resultPointers state) := by
  let s1 := execInstrBr state (.LUI .x6 0x42)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LUI .x7 0x45)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 (-1536))
  have p1 : s1.pc = BitVec.ofNat 64 (0x1000 + 42612) := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = BitVec.ofNat 64 (0x1000 + 42616) := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = BitVec.ofNat 64 (0x1000 + 42620) := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x42)) 3
  · rw [fetch_index SphincsImages.sign state (42608 / 4) (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 2
  · rw [fetch_index SphincsImages.sign s1 (42612 / 4) (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x45)) 1
  · rw [fetch_index SphincsImages.sign s2 (42616 / 4) (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 (-1536))) 0
  · rw [fetch_index SphincsImages.sign s3 (42620 / 4) (by decide)
      (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

set_option maxHeartbeats 0 in
theorem sign_resultCopy_code : Copy20Code SphincsImages.sign (42624 / 4) := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

theorem sign_result_block (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 42608)) :
    OrdinarySteps SphincsImages.sign state 14 (resultState state) := by
  have pointers := sign_resultPointers_block state pc
  have nextPc : (resultPointers state).pc =
      BitVec.ofNat 64 (0x1000 + 42624) := by
    simp [resultPointers, execInstrBr, pc]
  have copy := copy20_block_general SphincsImages.sign (42624 / 4)
    sign_resultCopy_code (resultPointers state) 0x42000 0x44a00
    (by simpa using nextPc)
    (resultPointers_regs state).1 (resultPointers_regs state).2
    (by decide) (by decide) (by decide) (by decide) (by decide)
  simpa [resultState] using pointers.append copy

theorem sign_result_pc (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 42608)) :
    (resultState state).pc = BitVec.ofNat 64 (0x1000 + 42664) := by
  have nextPc : (resultPointers state).pc =
      BitVec.ofNat 64 (0x1000 + 42624) := by
    simp [resultPointers, execInstrBr, pc]
  simpa [resultState] using copy20_final_pc (resultPointers state) (42624 / 4)
    (by simpa using nextPc)

theorem sign_top_hash_result (state : MachineState)
    (answer : BitVec 256)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 42604))
    (destination : state.getReg .x12 = 0x42000) :
    OrdinarySteps SphincsImages.sign (writeHash state answer) 14
      (resultState (writeHash state answer)) ∧
    (resultState (writeHash state answer)).pc =
      BitVec.ofNat 64 (0x1000 + 42664) ∧
    ∀ i, (hi : i < 20) →
      (resultState (writeHash state answer)).getByte
        (BitVec.ofNat 64 (0x44a00 + i)) =
          (truncateHash answer).extractLsb' (8 * i) 8 := by
  have hashedPc : (writeHash state answer).pc =
      BitVec.ofNat 64 (0x1000 + 42608) := by
    simp [writeHash, pc]
  exact ⟨sign_result_block _ hashedPc, sign_result_pc _ hashedPc,
    fun i hi => result_truncated_bytes state answer destination i hi⟩

/-- info: 'SigGolfCandidate.SphincsSignTopHashResult.sign_top_hash_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_top_hash_result

end SigGolfCandidate.SphincsSignTopHashResult
