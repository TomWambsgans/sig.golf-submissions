import SigGolfCandidate.SphincsVerifierFtsEarlyFrame
import SigGolfCandidate.SphincsVerifierFtsCopyAccess
import SigGolfCandidate.SphincsVerifierCopy20DataGeneral
import SigGolfCandidate.SphincsVerifierMessageAnswer
import SigGolfCandidate.SphincsVerifierFtsHash

/-! The first FORS leaf HASH answer is copied into the verifier's current-root buffer. -/

namespace SigGolfCandidate.SphincsVerifierFtsResult
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopy20DataGeneral
open SigGolfCandidate.SphincsVerifierHashSetup
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
    (pc : state.pc = 0x18cc) :
    (resultPointers state).pc = 0x18dc := by
  simp [resultPointers, execInstrBr, pc]

theorem resultPointers_block (state : MachineState)
    (pc : state.pc = 0x18cc) :
    OrdinarySteps SphincsImages.verify state 4 (resultPointers state) := by
  let s1 := execInstrBr state (.LUI .x6 0x42)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LUI .x7 0x45)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 (-1536))
  have p1 : s1.pc = 0x18d0 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x18d4 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x18d8 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x42)) 3
  · rw [fetch_index SphincsImages.verify state 563 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 2
  · rw [fetch_index SphincsImages.verify s1 564 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x45)) 1
  · rw [fetch_index SphincsImages.verify s2 565 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 (-1536))) 0
  · rw [fetch_index SphincsImages.verify s3 566 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

set_option maxHeartbeats 0 in
theorem resultCopy_code : Copy20Code SphincsImages.verify 567 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

def resultState (state : MachineState) : MachineState :=
  copyRootState (resultPointers state)

theorem result_block (state : MachineState) (pc : state.pc = 0x18cc) :
    OrdinarySteps SphincsImages.verify state 14 (resultState state) := by
  have pointers := resultPointers_block state pc
  have copy := copy20_block_general SphincsImages.verify 567
    resultCopy_code (resultPointers state) 0x42000 0x44a00
    (by simpa using resultPointers_pc state pc)
    (resultPointers_regs state).1 (resultPointers_regs state).2
    (by decide) (by decide) (by decide) (by decide) (by decide)
  simpa [resultState] using pointers.append copy

theorem result_pc (state : MachineState) (pc : state.pc = 0x18cc) :
    (resultState state).pc = 0x1904 := by
  exact copy20_final_pc (resultPointers state) 567
    (by simpa using resultPointers_pc state pc)

theorem resultPointers_mem (state : MachineState) (address : Word) :
    (resultPointers state).getMem address = state.getMem address := by
  simp [resultPointers, execInstrBr]

theorem result_lowByte_frame (state : MachineState) (address : Word)
    (low : (alignToDword address).toNat < 0x40000) :
    (resultState state).getByte address = state.getByte address := by
  let pointers := resultPointers state
  have outside : ∀ offset : Fin 5,
      alignToDword address ≠ alignToDword
        (pointers.getReg .x7 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset equal
    have high : 0x40000 ≤
        (alignToDword
          (pointers.getReg .x7 + signExtend12
            (4#12 * BitVec.ofNat 12 offset.val))).toNat := by
      rw [(resultPointers_regs state).2]
      fin_cases offset <;> decide
    have values := congrArg BitVec.toNat equal
    omega
  simp only [MachineState.getByte]
  change extractByte ((copyRootState pointers).getMem
    (alignToDword address)) (byteOffset address) = _
  rw [copyRoot_mem_frame pointers (alignToDword address) outside,
    resultPointers_mem]

theorem result_allWitness_frame (state : MachineState) (i : Nat)
    (hi : i < SphincsWire.signatureBytes) :
    (resultState state).getByte (BitVec.ofNat 64 (0x22ca0 + i)) =
      state.getByte (BitVec.ofNat 64 (0x22ca0 + i)) := by
  let address : Word := BitVec.ofNat 64 (0x22ca0 + i)
  have low : (alignToDword address).toNat < 0x40000 := by
    have length := SphincsWire.signatureBytes_eq
    have small : 0x22ca0 + i < 2 ^ 64 := by omega
    have range : 0x22ca0 + i < 0x40000 := by omega
    have aligned : (alignToDword address).toNat ≤ address.toNat := by
      unfold alignToDword
      rw [BitVec.toNat_and]
      exact Nat.and_le_left
    have exactAddress : address.toNat = 0x22ca0 + i := by
      simp only [address, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt small
    omega
  exact result_lowByte_frame state address low

theorem result_preserve_FtsWitness (state : MachineState)
    (signature : SphincsSecurity.Signature)
    (witness : SphincsVerifierFtsEarlyFrame.FtsWitness state signature) :
    SphincsVerifierFtsEarlyFrame.FtsWitness (resultState state)
      signature := by
  apply SphincsVerifierFtsEarlyFrame.FtsWitness.transport
    state _ signature witness
  intro i hi
  exact result_allWitness_frame state i hi

theorem copyWord_source_result (written read : Fin 5)
    (state : MachineState) (destination : state.getReg .x7 = 0x44a00) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x42000 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

theorem copyWord_other_result (written read : Fin 5)
    (different : written ≠ read) (state : MachineState)
    (destination : state.getReg .x7 = 0x44a00) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x44a00 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

private def CopyResultInvariant (original : MachineState) (count : Nat)
    (state : MachineState) : Prop :=
  state.getReg .x6 = 0x42000 ∧
  state.getReg .x7 = 0x44a00 ∧
  (∀ index : Fin 5,
    state.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * index.val))) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * index.val)))

private theorem copyResultStep (original state : MachineState) (slot : Fin 5)
    (invariant : CopyResultInvariant original slot.val state) :
    CopyResultInvariant original (slot.val + 1)
      (copyWordState slot state) := by
  rcases invariant with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ := copyWord_pointers slot state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination, ?_, ?_⟩
  · intro index
    rw [copyWord_source_result slot index state destination]
    exact sourceWords index
  · intro index before
    by_cases same : slot = index
    · subst index
      rw [copyWord_data_general slot state 0x42000 0x44a00
        source destination]
      exact sourceWords slot
    · rw [copyWord_other_result slot index same state destination]
      have smaller : index.val < slot.val := by
        have unequal : slot.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact copiedWords index smaller

theorem copyResult_data (original : MachineState)
    (source : original.getReg .x6 = 0x42000)
    (destination : original.getReg .x7 = 0x44a00)
    (index : Fin 5) :
    (copyRootState original).getWord32
      (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * index.val)) := by
  have initial : CopyResultInvariant original 0 original := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro index impossible
    omega
  have after0 := copyResultStep original original 0 initial
  have after1 := copyResultStep original (copyWordState 0 original) 1 after0
  have after2 := copyResultStep original (copyWordState 1
    (copyWordState 0 original)) 2 after1
  have after3 := copyResultStep original (copyWordState 2
    (copyWordState 1 (copyWordState 0 original))) 3 after2
  have after4 := copyResultStep original (copyWordState 3
    (copyWordState 2 (copyWordState 1 (copyWordState 0 original)))) 4 after3
  exact after4.2.2.2 index (by have := index.isLt; omega)

theorem result_data (state : MachineState) (index : Fin 5) :
    (resultState state).getWord32
      (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * index.val)) := by
  change (copyRootState (resultPointers state)).getWord32 _ = _
  rw [copyResult_data _ (resultPointers_regs state).1
    (resultPointers_regs state).2]
  simp [MachineState.getWord32, resultPointers_mem]

theorem result_word_byte (state : MachineState) (base : Nat)
    (supported : base = 0x42000 ∨ base = 0x44a00)
    (index : Fin 5) (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64
      (base + 4 * index.val + byte.val)) =
      (state.getWord32 (BitVec.ofNat 64
        (base + 4 * index.val))).extractLsb' (8 * byte.val) 8 := by
  have split := SphincsVerifierSecondHashHeader.extractByte_from_word32
    (state.getMem (alignToDword
      (BitVec.ofNat 64 (base + 4 * index.val + byte.val))))
    ⟨(base + 4 * index.val + byte.val) % 8,
      Nat.mod_lt _ (by decide)⟩
  rcases supported with h | h <;> subst base <;>
    fin_cases index <;> fin_cases byte <;>
      simpa [MachineState.getByte, MachineState.getWord32,
        alignToDword, byteOffset] using split

theorem result_bytes (state : MachineState) (i : Nat) (hi : i < 20) :
    (resultState state).getByte (BitVec.ofNat 64 (0x44a00 + i)) =
      state.getByte (BitVec.ofNat 64 (0x42000 + i)) := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  calc
    (resultState state).getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        (resultState state).getByte (BitVec.ofNat 64
          (0x44a00 + 4 * index.val + byte.val)) := by
          simp only [Nat.add_assoc, split]
    _ = ((resultState state).getWord32
          (BitVec.ofNat 64 (0x44a00 + 4 * index.val))).extractLsb'
          (8 * byte.val) 8 :=
      result_word_byte (resultState state) 0x44a00 (Or.inr rfl) index byte
    _ = (state.getWord32 (BitVec.ofNat 64
          (0x42000 + 4 * index.val))).extractLsb'
          (8 * byte.val) 8 := by rw [result_data state index]
    _ = state.getByte (BitVec.ofNat 64 (0x42000 + i)) := by
      rw [← result_word_byte state 0x42000 (Or.inl rfl) index byte]
      simp only [Nat.add_assoc, split]

private theorem answer_word_byte (state : MachineState)
    (index : Fin 4) (byte : Fin 8) :
    state.getByte (BitVec.ofNat 64
      (0x42000 + 8 * index.val + byte.val)) =
      extractByte
        (state.getMem (BitVec.ofNat 64 (0x42000 + 8 * index.val)))
        byte.val := by
  fin_cases index <;> fin_cases byte <;>
    simp [MachineState.getByte, alignToDword, byteOffset]

theorem hashAnswer_byte (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000)
    (i : Nat) (hi : i < 32) :
    (writeHash state answer).getByte (BitVec.ofNat 64 (0x42000 + i)) =
      answer.extractLsb' (8 * i) 8 := by
  let index : Fin 4 := ⟨i / 8, by omega⟩
  let byte : Fin 8 := ⟨i % 8, Nat.mod_lt _ (by decide)⟩
  have split : 8 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  calc
    (writeHash state answer).getByte (BitVec.ofNat 64 (0x42000 + i)) =
        (writeHash state answer).getByte
          (BitVec.ofNat 64 (0x42000 + 8 * index.val + byte.val)) := by
            simp only [Nat.add_assoc, split]
    _ = extractByte ((writeHash state answer).getMem
          (BitVec.ofNat 64 (0x42000 + 8 * index.val))) byte.val :=
      answer_word_byte (writeHash state answer) index byte
    _ = extractByte (answer.extractLsb' (64 * index.val) 64)
          byte.val := by
            rw [SphincsVerifierMessageAnswer.writeHash_word state answer
              destination index]
    _ = answer.extractLsb' (8 * i) 8 := by
      simpa only [split] using
        SphincsVerifierSecondHashBytes.extractByte_extractLsb64
          answer index.val byte

theorem result_truncated_bytes (state : MachineState)
    (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000)
    (i : Nat) (hi : i < 20) :
    (resultState (writeHash state answer)).getByte
      (BitVec.ofNat 64 (0x44a00 + i)) =
      (SphincsSecurity.truncateHash answer).extractLsb' (8 * i) 8 := by
  rw [result_bytes _ i hi,
    hashAnswer_byte state answer destination i (by omega)]
  change answer.extractLsb' (8 * i) 8 =
    (answer.extractLsb' 0 SphincsSecurity.digestBits).extractLsb'
      (8 * i) 8
  rw [BitVec.extractLsb'_extractLsb'_of_le (by
    simp [SphincsSecurity.digestBits]
    omega)]

theorem firstFtsHash_result (state : MachineState)
    (signature : SphincsSecurity.Signature) (answer : BitVec 256)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (witness : SphincsVerifierFtsEarlyFrame.FtsWitness state signature) :
    let hashed := writeHash state answer
    let copied := resultState hashed
    hashArgumentsValid state = true ∧
      compressions (hashInput state).1 = 1 ∧
      OrdinarySteps SphincsImages.verify hashed 14 copied ∧
      copied.pc = 0x1904 ∧
      SphincsVerifierFtsEarlyFrame.FtsWitness copied signature ∧
      ∀ i, (hi : i < 20) →
        copied.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (SphincsSecurity.truncateHash answer).extractLsb' (8 * i) 8 := by
  let hashed := writeHash state answer
  let copied := resultState hashed
  have hashedPc : hashed.pc = 0x18cc := by
    simp [hashed, writeHash, pc]
  have hashCost := SphincsVerifierFtsHash.hash_arguments state
    source bits destination
  exact ⟨hashCost.1, hashCost.2, result_block hashed hashedPc,
    result_pc hashed hashedPc,
    result_preserve_FtsWitness hashed signature
      (SphincsVerifierFtsEarlyFrame.firstFtsHashAnswer_preserve_FtsWitness
        state answer signature destination witness),
    fun i hi => result_truncated_bytes state answer destination i hi⟩

/-- One HASH call, followed by the exact fourteen instructions that copy its first twenty answer bytes. -/
theorem firstFtsHash_then_result (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (resultState (writeHash state (hash (hashInput state)))) steps result) :
    Executes hash SphincsImages.verify state (steps + 15)
      ((result.charge 14 0 0).charge 8 1 1) := by
  let hashed := writeHash state (hash (hashInput state))
  have hashedPc : hashed.pc = 0x18cc := by
    simp [hashed, writeHash, pc]
  have block := result_block hashed hashedPc
  have afterCopy : Executes hash SphincsImages.verify hashed (steps + 14)
      (result.charge 14 0 0) := block.then_executes tail
  have step := SphincsVerifierFtsHash.hash_step hash state pc source bits
    destination service (steps + 14) (result.charge 14 0 0) afterCopy
  simpa only [Nat.add_assoc] using step

theorem loaded_honest_firstFts_leaf_result
    (hash : Hash) (publicKey : SigGolf.PublicKey)
    (message : SigGolf.Message)
    (inner : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (state : MachineState) (commitmentAnswer digestAnswer : BitVec 256)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire inner signature) =
        some state)
    (answerMatches : ∀ index : Fin 2,
      commitmentAnswer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest digestAnswer)) :
    ∃ ready final copied,
      OrdinarySteps SphincsImages.verify
        (writeHash (firstHashState state) commitmentAnswer) 107 ready ∧
      OrdinarySteps SphincsImages.verify
        (writeHash ready digestAnswer) 392 final ∧
      final.pc = 0x18c8 ∧
      hashInput final = SphincsBridge.toQuery
        (SphincsVerifierFtsQuery.firstFtsInput inner
          (SphincsSecurity.Concrete.digestIndex
            (SphincsSecurity.truncateMessageDigest digestAnswer))
          (SphincsSecurity.Concrete.digestLeaves
            (SphincsSecurity.truncateMessageDigest digestAnswer)
            ⟨0, by decide⟩)
          (signature.ftsSecret ⟨0, by decide⟩)) ∧
      OrdinarySteps SphincsImages.verify
        (writeHash final (hash (hashInput final))) 14 copied ∧
      copied.pc = 0x1904 ∧
      SphincsVerifierFtsEarlyFrame.FtsWitness copied signature ∧
      ∀ i, (hi : i < 20) →
        copied.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (SphincsSecurity.truncateHash
            (hash (SphincsBridge.toQuery
              (SphincsVerifierFtsQuery.firstFtsInput inner
                (SphincsSecurity.Concrete.digestIndex
                  (SphincsSecurity.truncateMessageDigest digestAnswer))
                (SphincsSecurity.Concrete.digestLeaves
                  (SphincsSecurity.truncateMessageDigest digestAnswer)
                  ⟨0, by decide⟩)
                (signature.ftsSecret ⟨0, by decide⟩))))).extractLsb'
                  (8 * i) 8 := by
  obtain ⟨ready, final, traceFirst, traceSecond, pc, source, bits,
    destination, _, query, witness, _⟩ :=
    SphincsVerifierFtsEarlyFrame.loaded_honest_firstFts_query
      publicKey message inner signature state commitmentAnswer digestAnswer
      loaded answerMatches admissible
  let answer := hash (hashInput final)
  let copied := resultState (writeHash final answer)
  obtain ⟨_, _, traceResult, copiedPc, copiedWitness, copiedBytes⟩ :=
    firstFtsHash_result final signature answer pc source bits destination witness
  refine ⟨ready, final, copied, traceFirst, traceSecond, pc, query,
    traceResult, copiedPc, copiedWitness, ?_⟩
  intro i hi
  rw [← query]
  exact copiedBytes i hi

/-- info: 'SigGolfCandidate.SphincsVerifierFtsResult.loaded_honest_firstFts_leaf_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_firstFts_leaf_result

/-- info: 'SigGolfCandidate.SphincsVerifierFtsResult.firstFtsHash_then_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstFtsHash_then_result

/-- info: 'SigGolfCandidate.SphincsVerifierFtsResult.result_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result_block

end SigGolfCandidate.SphincsVerifierFtsResult
