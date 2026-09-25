import SigGolfCandidate.SphincsVerifierWotsLeafHeader
import SigGolfCandidate.SphincsVerifierWotsValue

namespace SigGolfCandidate.SphincsVerifierWotsLeafResult
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsMaskedKeygenPrefix
open SigGolfCandidate.SphincsVerifierWotsEndpointCopy
open SigGolfCandidate.SphincsVerifierWotsValue
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierWotsLeafHashReady
open SigGolfCandidate.SphincsVerifierWotsLeafQuery
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def leafAnswerCopySchedule : List (Word × Instr) := [
  (0x2a74, .LUI .x6 66), (0x2a78, .ADDI .x6 .x6 0),
  (0x2a7c, .LUI .x7 69), (0x2a80, .ADDI .x7 .x7 (-1536)),
  (0x2a84, .LWU .x13 .x6 0), (0x2a88, .SW .x7 .x13 0),
  (0x2a8c, .LWU .x13 .x6 4), (0x2a90, .SW .x7 .x13 4),
  (0x2a94, .LWU .x13 .x6 8), (0x2a98, .SW .x7 .x13 8),
  (0x2a9c, .LWU .x13 .x6 12), (0x2aa0, .SW .x7 .x13 12),
  (0x2aa4, .LWU .x13 .x6 16), (0x2aa8, .SW .x7 .x13 16)]

theorem leafAnswerCopy_code : ∀ entry ∈ leafAnswerCopySchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by decide

def leafAnswerCopyState (s : MachineState) : MachineState :=
  runSchedule leafAnswerCopySchedule s

theorem leafAnswerCopy_checked (s : MachineState) (pc : s.pc = 0x2a74) :
    Checked leafAnswerCopySchedule s := by
  simp [Checked, leafAnswerCopySchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, MachineState.setWord32,
    alignToDword, byteOffset, pc]

theorem leafAnswerCopy_block (s : MachineState) (pc : s.pc = 0x2a74) :
    OrdinarySteps SphincsImages.verify s 14 (leafAnswerCopyState s) := by
  simpa only [leafAnswerCopyState, show leafAnswerCopySchedule.length = 14 by decide]
    using checked_sound _ leafAnswerCopySchedule leafAnswerCopy_code s
      (leafAnswerCopy_checked s pc)

private def leafAnswerPointersSchedule : List (Word × Instr) :=
  leafAnswerCopySchedule.take 4
private def leafAnswerWordsSchedule : List (Word × Instr) :=
  leafAnswerCopySchedule.drop 4
private theorem leafAnswer_split : leafAnswerCopySchedule =
    leafAnswerPointersSchedule ++ leafAnswerWordsSchedule := by decide
private theorem runSchedule_append (xs ys : List (Word × Instr)) (s : MachineState) :
    runSchedule (xs ++ ys) s = runSchedule ys (runSchedule xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem leafAnswerWords_eq (s : MachineState) :
    runSchedule leafAnswerWordsSchedule s = copyRootState s := by rfl

private theorem copyWord_pc_general (slot : Fin 5) (s : MachineState) :
    (copyWordState slot s).pc = s.pc + 8 := by
  simp [copyWordState, execInstrBr]
  bv_decide

private theorem copyRoot_pc_general (s : MachineState) :
    (copyRootState s).pc = s.pc + 40 := by
  simp [copyRootState, copyWord_pc_general]
  bv_decide

theorem leafAnswerCopy_pc_general (s : MachineState) :
    (leafAnswerCopyState s).pc = s.pc + 56 := by
  have pointerPc : (runSchedule leafAnswerPointersSchedule s).pc = s.pc + 16 := by
    simp [leafAnswerPointersSchedule, leafAnswerCopySchedule,
      runSchedule, execInstrBr]
    bv_decide
  rw [leafAnswerCopyState, leafAnswer_split, runSchedule_append,
    leafAnswerWords_eq, copyRoot_pc_general, pointerPc]
  bv_decide

theorem leafAnswerCopy_pc (s : MachineState) (pc : s.pc = 0x2a74) :
    (leafAnswerCopyState s).pc = 0x2aac := by
  rw [leafAnswerCopy_pc_general, pc]
  decide

theorem leafAnswerCopy_word (s : MachineState) (slot : Fin 5) :
    (leafAnswerCopyState s).getWord32 (word 0x44a00 slot) =
      s.getWord32 (word 0x42000 slot) := by
  let pointers := runSchedule leafAnswerPointersSchedule s
  have source : pointers.getReg .x6 = 0x42000 := by
    simp [pointers, leafAnswerPointersSchedule, leafAnswerCopySchedule,
      runSchedule, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  have destination : pointers.getReg .x7 = 0x44a00 := by
    simp [pointers, leafAnswerPointersSchedule, leafAnswerCopySchedule,
    runSchedule, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have copied := copy20_data pointers 0x42000 0x44a00 source destination
    (by intro i j; fin_cases i <;> fin_cases j <;> decide)
    (by intro i j different
        fin_cases i <;> fin_cases j <;>
          first | exact (different rfl).elim | decide)
    slot
  have pointerFrame : pointers.getWord32 (word 0x42000 slot) =
      s.getWord32 (word 0x42000 slot) := by
    simp [pointers, leafAnswerPointersSchedule, leafAnswerCopySchedule,
      runSchedule, execInstrBr, MachineState.getWord32]
  rw [leafAnswerCopyState, leafAnswer_split, runSchedule_append,
    leafAnswerWords_eq]
  exact copied.trans pointerFrame

def leafHashNext (hash : Hash) (s : MachineState) : MachineState :=
  leafAnswerCopyState
    (writeHash (leafHashReadyState s) (hash (hashInput (leafHashReadyState s))))

theorem leafHashNext_word (hash : Hash) (s : MachineState) (slot : Fin 5) :
    (leafHashNext hash s).getWord32 (word 0x44a00 slot) =
      (hash (hashInput (leafHashReadyState s))).extractLsb'
        (32 * slot.val) 32 := by
  rw [leafHashNext, leafAnswerCopy_word]
  exact writeHash_word32 (leafHashReadyState s)
    (hash (hashInput (leafHashReadyState s)))
    (leafHashReady_regs s).2.2.1 slot

theorem leafHashNext_byte (hash : Hash) (s : MachineState)
    (i : Nat) (hi : i < 20) :
    (leafHashNext hash s).getByte (BitVec.ofNat 64 (0x44a00 + i)) =
      (hash (hashInput (leafHashReadyState s))).extractLsb' (8 * i) 8 := by
  let slot : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * slot.val + byte.val = i := by
    dsimp [slot, byte]
    omega
  rw [← split,
    show 0x44a00 + (4 * slot.val + byte.val) =
      0x44a00 + 4 * slot.val + byte.val by omega,
    variableWord_byte _ 0x44a00 (by decide) (by decide) slot byte]
  have value := leafHashNext_word hash s slot
  simp only [word] at value
  rw [value]
  ext bit (hbit : bit < 8)
  simp
  have hb : 8 * byte.val + bit < 32 := by have := byte.isLt; omega
  simp [hb, show 32 * slot.val + (8 * byte.val + bit) =
    8 * (4 * slot.val + byte.val) + bit by omega]

theorem leafHashNext_byte_of_query (hash : Hash) (s : MachineState)
    (input : HashInput)
    (query : hashInput (leafHashReadyState s) = toQuery input)
    (i : Nat) (hi : i < 20) :
    (leafHashNext hash s).getByte (BitVec.ofNat 64 (0x44a00 + i)) =
      (truncateHash (hash (toQuery input))).extractLsb' (8 * i) 8 := by
  rw [leafHashNext_byte hash s i hi, query]
  exact
    (BitVec.extractLsb'_extractLsb'_of_le
      (x := hash (toQuery input))
      (start := 8 * i) (len := 8) (len' := digestBits)
      (by unfold digestBits; omega)).symm

#print axioms leafAnswerCopy_block
#print axioms leafAnswerCopy_pc
#print axioms leafAnswerCopy_word
#print axioms leafHashNext_byte_of_query

end SigGolfCandidate.SphincsVerifierWotsLeafResult
