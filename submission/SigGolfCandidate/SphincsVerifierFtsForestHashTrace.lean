import SigGolfCandidate.SphincsVerifierFtsForestHash
import SigGolfCandidate.SphincsVerifierFtsCopyAccess
import SigGolfCandidate.SphincsVerifierFtsResult

namespace SigGolfCandidate.SphincsVerifierFtsForestHashTrace
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsPostForestCopy
open SigGolfCandidate.SphincsVerifierFtsForestHashReady
open SigGolfCandidate.SphincsVerifierFtsForestHash
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierFtsResult
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- The exact post-FORS path reaches the 520-byte HASH service after 430
    ordinary instructions. The call costs nine compressions and 72 cycles. -/
theorem forest_hash_trace (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x1c08) (steps : Nat) (result : Execution)
    (tail : ∀ copied,
      OrdinarySteps SphincsImages.verify state 387 copied →
      copied.pc = 0x1c8c →
      Executes hash SphincsImages.verify
        (writeHash (forestHashReadyState copied)
          (hash (hashInput (forestHashReadyState copied)))) steps result) :
    Executes hash SphincsImages.verify state (steps + 431)
      (result.charge 502 1 9) := by
  obtain ⟨copied, copiedTrace, copiedPc, _⟩ :=
    forestRootBytes_copied state pc
  have header := forestHashReady_block copied copiedPc
  have final := hash_step hash (forestHashReadyState copied)
    header.2.1 header.2.2.1 header.2.2.2.1
    header.2.2.2.2.1 header.2.2.2.2.2
    steps result (tail copied copiedTrace copiedPc)
  have ordinary := copiedTrace.append header.1
  have combined := ordinary.then_executes final
  simpa [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using combined

def forestAnswerPointersState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x42)
  let state := execInstrBr state (.ADDI .x6 .x6 0)
  let state := execInstrBr state (.LUI .x7 0x45)
  execInstrBr state (.ADDI .x7 .x7 (-1536))

theorem forestAnswerPointers_block (state : MachineState)
    (pc : state.pc = 0x1d3c) :
    OrdinarySteps SphincsImages.verify state 4
      (forestAnswerPointersState state) ∧
    (forestAnswerPointersState state).pc = 0x1d4c ∧
    (forestAnswerPointersState state).getReg .x6 = 0x42000 ∧
    (forestAnswerPointersState state).getReg .x7 = 0x44a00 := by
  let s1 := execInstrBr state (.LUI .x6 0x42)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LUI .x7 0x45)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 (-1536))
  have p1 : s1.pc = 0x1d40 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1d44 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1d48 := by simp [s3, execInstrBr, p2]
  have trace : OrdinarySteps SphincsImages.verify state 4 s4 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x42)) 3
    · rw [fetch_index SphincsImages.verify state 847 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 2
    · rw [fetch_index SphincsImages.verify s1 848 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x45)) 1
    · rw [fetch_index SphincsImages.verify s2 849 (by decide)
        (by simpa using p2)]
      decide
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 (-1536))) 0
    · rw [fetch_index SphincsImages.verify s3 850 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [forestAnswerPointersState] using trace, ?_, ?_, ?_⟩
  · simp [forestAnswerPointersState, execInstrBr, pc]
  · simp [forestAnswerPointersState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  · simp [forestAnswerPointersState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]

theorem forestAnswer_copy_code : Copy20Code SphincsImages.verify 851 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

def forestAnswerCopyState (state : MachineState) : MachineState :=
  copyRootState (forestAnswerPointersState state)

theorem forestAnswerCopy_block (state : MachineState)
    (pc : state.pc = 0x1d3c) :
    OrdinarySteps SphincsImages.verify state 14
      (forestAnswerCopyState state) ∧
    (forestAnswerCopyState state).pc = 0x1d74 := by
  obtain ⟨pointers, pointerPc, source, destination⟩ :=
    forestAnswerPointers_block state pc
  have copy := copy20_block_general SphincsImages.verify 851
    forestAnswer_copy_code (forestAnswerPointersState state)
    0x42000 0x44a00 (by simpa using pointerPc)
    (by simpa using source) (by simpa using destination)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨by simpa only [forestAnswerCopyState] using pointers.append copy,
    ?_⟩
  exact copy20_final_pc (forestAnswerPointersState state) 851
    (by simpa using pointerPc)

theorem forestAnswerCopy_byte (state : MachineState)
    (pc : state.pc = 0x1d3c)
    (i : Nat) (hi : i < 20) :
    (forestAnswerCopyState state).getByte
      (BitVec.ofNat 64 (0x44a00 + i)) =
      state.getByte (BitVec.ofNat 64 (0x42000 + i)) := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  have copied := copyResult_data (forestAnswerPointersState state)
    (forestAnswerPointers_block state pc).2.2.1
    (forestAnswerPointers_block state pc).2.2.2 index
  have pointersFrame : (forestAnswerPointersState state).getWord32
      (BitVec.ofNat 64 (0x42000 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * index.val)) := by
    simp [forestAnswerPointersState, execInstrBr, MachineState.getWord32]
  have destination := result_word_byte (forestAnswerCopyState state)
    0x44a00 (Or.inr rfl) index byte
  have source := result_word_byte state 0x42000 (Or.inl rfl) index byte
  simpa only [Nat.add_assoc, split] using
    destination.trans ((congrArg (fun value : BitVec 32 =>
      value.extractLsb' (8 * byte.val) 8)
        (copied.trans pointersFrame)).trans source.symm)

theorem forestAnswerCopy_hash_value (state : MachineState)
    (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000)
    (i : Nat) (hi : i < 20) :
    (forestAnswerCopyState (writeHash state answer)).getByte
      (BitVec.ofNat 64 (0x44a00 + i)) =
      (SphincsSecurity.truncateHash answer).extractLsb' (8 * i) 8 := by
  simpa only [forestAnswerCopyState, forestAnswerPointersState,
    resultState, resultPointers] using
      result_truncated_bytes state answer destination i hi

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestHashTrace.forestAnswerCopy_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestAnswerCopy_byte

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestHashTrace.forestAnswerCopy_hash_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestAnswerCopy_hash_value

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestHashTrace.forestAnswerCopy_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestAnswerCopy_block

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestHashTrace.forest_hash_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forest_hash_trace

end SigGolfCandidate.SphincsVerifierFtsForestHashTrace
