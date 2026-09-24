import SigGolfCandidate.SphincsVerifierFtsParentExecution
import SigGolfCandidate.SphincsVerifierFtsResult

/-! Copy the first FORS parent HASH answer into the running-root buffer. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentResult
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierCopy20DataGeneral
set_option maxRecDepth 16384

def resultPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x42)
  let state := execInstrBr state (.ADDI .x6 .x6 0)
  let state := execInstrBr state (.LUI .x7 0x45)
  execInstrBr state (.ADDI .x7 .x7 (-1536))

theorem resultPointers_regs (state : MachineState) :
    (resultPointers state).getReg .x6 = 0x42000 ∧
    (resultPointers state).getReg .x7 = 0x44a00 := by
  simp [resultPointers, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem resultPointers_pc (state : MachineState)
    (pc : state.pc = 0x1b1c) :
    (resultPointers state).pc = 0x1b2c := by
  simp [resultPointers, execInstrBr, pc]

theorem resultPointers_block (state : MachineState)
    (pc : state.pc = 0x1b1c) :
    OrdinarySteps SphincsImages.verify state 4 (resultPointers state) := by
  let s1 := execInstrBr state (.LUI .x6 0x42)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LUI .x7 0x45)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 (-1536))
  have p1 : s1.pc = 0x1b20 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1b24 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1b28 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x42)) 3
  · rw [fetch_index SphincsImages.verify state 711 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 2
  · rw [fetch_index SphincsImages.verify s1 712 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x45)) 1
  · rw [fetch_index SphincsImages.verify s2 713 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 (-1536))) 0
  · rw [fetch_index SphincsImages.verify s3 714 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

set_option maxHeartbeats 0 in
theorem resultCopy_code : Copy20Code SphincsImages.verify 715 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

def resultState (state : MachineState) : MachineState :=
  copyRootState (resultPointers state)

theorem result_block (state : MachineState) (pc : state.pc = 0x1b1c) :
    OrdinarySteps SphincsImages.verify state 14 (resultState state) := by
  have pointers := resultPointers_block state pc
  have copy := copy20_block_general SphincsImages.verify 715
    resultCopy_code (resultPointers state) 0x42000 0x44a00
    (by simpa using resultPointers_pc state pc)
    (resultPointers_regs state).1 (resultPointers_regs state).2
    (by decide) (by decide) (by decide) (by decide) (by decide)
  simpa [resultState] using pointers.append copy

theorem result_pc (state : MachineState) (pc : state.pc = 0x1b1c) :
    (resultState state).pc = 0x1b54 := by
  exact copy20_final_pc (resultPointers state) 715
    (by simpa using resultPointers_pc state pc)

theorem parentHash_result (state : MachineState) (answer : BitVec 256)
    (pc : state.pc = 0x1b18)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 640)
    (destination : state.getReg .x12 = 0x42000) :
    hashArgumentsValid state = true ∧
      compressions (hashInput state).1 = 2 ∧
      OrdinarySteps SphincsImages.verify (writeHash state answer) 14
        (resultState (writeHash state answer)) ∧
      (resultState (writeHash state answer)).pc = 0x1b54 ∧
      ∀ i, (hi : i < 20) →
        (resultState (writeHash state answer)).getByte
          (BitVec.ofNat 64 (0x44a00 + i)) =
          (SphincsSecurity.truncateHash answer).extractLsb' (8 * i) 8 := by
  have hashedPc : (writeHash state answer).pc = 0x1b1c := by
    simp [writeHash, pc]
  have hashArgs := SphincsVerifierFtsParentHash.hash_arguments state
    source bits destination
  refine ⟨hashArgs.1, hashArgs.2,
    result_block _ hashedPc, result_pc _ hashedPc, ?_⟩
  intro i hi
  change (SphincsVerifierFtsResult.resultState (writeHash state answer)).getByte
    (BitVec.ofNat 64 (0x44a00 + i)) = _
  exact SphincsVerifierFtsResult.result_truncated_bytes state answer
    destination i hi

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentResult.parentHash_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentHash_result


end SigGolfCandidate.SphincsVerifierFtsParentResult
