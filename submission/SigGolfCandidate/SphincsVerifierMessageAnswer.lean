import SigGolfCandidate.SphincsVerifierLoadedMessageHash

/-!
# The verifier's message-digest HASH answer

All four answer words are written to the verifier's fixed output buffer.
This is the starting invariant for decoding the index and FORS leaf choices.
-/

namespace SigGolfCandidate.SphincsVerifierMessageAnswer
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageHash
open SigGolfCandidate.SphincsVerifierSecondHashBytes

theorem writeHash_word (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) (index : Fin 4) :
    (writeHash state answer).getMem
      (BitVec.ofNat 64 (0x42000 + 8 * index.val)) =
      answer.extractLsb' (64 * index.val) 64 := by
  fin_cases index <;>
    simp [writeHash, MachineState.writeWords_cons, destination,
      MachineState.getMem_setMem_ne]

theorem messageReady_answer_word (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (answer : BitVec 256) (index : Fin 4) :
    (writeHash state answer).getMem
      (BitVec.ofNat 64 (0x42000 + 8 * index.val)) =
      answer.extractLsb' (64 * index.val) 64 :=
  writeHash_word state answer ready.destination index

private theorem answer_word_byte (state : MachineState)
    (index : Fin 4) (byte : Fin 8) :
    state.getByte (BitVec.ofNat 64
      (0x42000 + 8 * index.val + byte.val)) =
      extractByte
        (state.getMem (BitVec.ofNat 64 (0x42000 + 8 * index.val)))
        byte.val := by
  fin_cases index <;> fin_cases byte <;>
    simp [MachineState.getByte, alignToDword, byteOffset]

theorem messageReady_answer_byte (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (answer : BitVec 256) (i : Nat) (hi : i < 32) :
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
      simpa only [Nat.add_assoc, split]
    _ = extractByte ((writeHash state answer).getMem
          (BitVec.ofNat 64 (0x42000 + 8 * index.val))) byte.val :=
      answer_word_byte (writeHash state answer) index byte
    _ = extractByte (answer.extractLsb' (64 * index.val) 64)
          byte.val := by rw [messageReady_answer_word state pk message randomness ready answer index]
    _ = answer.extractLsb' (8 * i) 8 := by
      simpa only [split] using
        extractByte_extractLsb64 answer index.val byte

/-- info: 'SigGolfCandidate.SphincsVerifierMessageAnswer.messageReady_answer_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_answer_word

/-- info: 'SigGolfCandidate.SphincsVerifierMessageAnswer.messageReady_answer_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_answer_byte

end SigGolfCandidate.SphincsVerifierMessageAnswer
