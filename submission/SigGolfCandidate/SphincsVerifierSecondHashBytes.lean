import SigGolfCandidate.SphincsVerifierSecondHashPayload

/-!
# Word-to-byte facts for the second HASH input

These lemmas turn the verified 32-bit public-parameter, randomizer, and root
words into their exact 20-byte serialized fields.
-/

namespace SigGolfCandidate.SphincsVerifierSecondHashBytes
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierLoader

def FieldBase (base : Nat) : Prop :=
  base = 0x40014 ∨ base = 0x40028 ∨ base = 0x4003c ∨
    base = 0x22cb4

theorem word32_byte (state : MachineState) (base : Nat)
    (supported : FieldBase base) (index : Fin 5) (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64 (base + 4 * index.val + byte.val)) =
      (state.getWord32 (BitVec.ofNat 64 (base + 4 * index.val))).extractLsb'
        (8 * byte.val) 8 := by
  have split := SphincsVerifierSecondHashHeader.extractByte_from_word32
    (state.getMem (alignToDword
      (BitVec.ofNat 64 (base + 4 * index.val + byte.val))))
    ⟨(base + 4 * index.val + byte.val) % 8,
      Nat.mod_lt _ (by decide)⟩
  rcases supported with h | h | h | h <;> subst base <;>
    fin_cases index <;> fin_cases byte <;>
      simpa [MachineState.getByte, MachineState.getWord32,
        alignToDword, byteOffset] using split

theorem slice_byte {n : Nat} (value : BitVec n) (base byte : Nat)
    (small : byte < 4) :
    (value.extractLsb' (8 * base) 32).extractLsb' (8 * byte) 8 =
      value.extractLsb' (8 * (base + byte)) 8 := by
  ext bit bitBound
  simp [Nat.mul_add, Nat.add_assoc] <;> omega

theorem field_bytes_of_words {n : Nat} (state : MachineState)
    (base : Nat) (supported : FieldBase base) (value : BitVec n)
    (source : Nat)
    (words : ∀ index : Fin 5,
      state.getWord32 (BitVec.ofNat 64 (base + 4 * index.val)) =
        value.extractLsb' (8 * (source + 4 * index.val)) 32)
    (i : Nat) (hi : i < 20) :
    state.getByte (BitVec.ofNat 64 (base + i)) =
      value.extractLsb' (8 * (source + i)) 8 := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  calc
    state.getByte (BitVec.ofNat 64 (base + i)) =
        state.getByte
          (BitVec.ofNat 64 (base + 4 * index.val + byte.val)) := by
      simpa only [Nat.add_assoc, split]
    _ = (state.getWord32
          (BitVec.ofNat 64 (base + 4 * index.val))).extractLsb'
          (8 * byte.val) 8 := word32_byte state base supported index byte
    _ = (value.extractLsb' (8 * (source + 4 * index.val)) 32).extractLsb'
          (8 * byte.val) 8 := by rw [words index]
    _ = value.extractLsb' (8 * (source + i)) 8 := by
      simpa only [Nat.add_assoc, split] using slice_byte value (source + 4 * index.val)
        byte.val byte.isLt

theorem randomizer_bytes_of_words (state : MachineState)
    (witness : Bytes SphincsWire.signatureBytes)
    (randomness : SphincsSecurity.Randomness)
    (words : ∀ index : Fin 5,
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        witness.extractLsb' (8 * (40 + 4 * index.val)) 32)
    (encoded : ∀ i, (hi : i < 20) →
      witness.extractLsb' (8 * (40 + i)) 8 =
        randomness.extractLsb' (8 * i) 8)
    (i : Nat) (hi : i < 20) :
    state.getByte (BitVec.ofNat 64 (0x40028 + i)) =
      randomness.extractLsb' (8 * i) 8 := by
  exact (field_bytes_of_words state 0x40028 (Or.inr (Or.inl rfl))
    witness 40 words i hi).trans (encoded i hi)

theorem root_bytes_of_words (state : MachineState)
    (witness : Bytes SphincsWire.signatureBytes)
    (pk : SphincsSecurity.PublicKey)
    (words : ∀ index : Fin 5,
      state.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        witness.extractLsb' (8 * (4 * index.val)) 32)
    (encoded : EncodedWitness witness pk)
    (i : Nat) (hi : i < 20) :
    state.getByte (BitVec.ofNat 64 (0x4003c + i)) =
      pk.root.extractLsb' (8 * i) 8 := by
  have actual := field_bytes_of_words state 0x4003c
    (Or.inr (Or.inr (Or.inl rfl))) witness 0
    (by simpa using words) i hi
  have actual' : state.getByte (BitVec.ofNat 64 (0x4003c + i)) =
      witness.extractLsb' (8 * i) 8 := by simpa using actual
  exact actual'.trans (encoded.root i hi)

theorem parameter_bytes_of_words (ready original : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (words : ∀ index : Fin 5,
      ready.getWord32 (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
        original.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)))
    (encoded : WitnessPrefix original pk)
    (i : Nat) (hi : i < 20) :
    ready.getByte (BitVec.ofNat 64 (0x40014 + i)) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  have destination := word32_byte ready 0x40014 (Or.inl rfl) index byte
  have source := word32_byte original 0x22cb4
    (Or.inr (Or.inr (Or.inr rfl))) index byte
  have hbyte : ready.getByte (BitVec.ofNat 64 (0x40014 + i)) =
      original.getByte (BitVec.ofNat 64 (0x22cb4 + i)) := by
    calc
      ready.getByte (BitVec.ofNat 64 (0x40014 + i)) =
          ready.getByte
            (BitVec.ofNat 64 (0x40014 + 4 * index.val + byte.val)) := by
        simpa only [Nat.add_assoc, split]
      _ = (ready.getWord32
            (BitVec.ofNat 64 (0x40014 + 4 * index.val))).extractLsb'
            (8 * byte.val) 8 := destination
      _ = (original.getWord32
            (BitVec.ofNat 64 (0x22cb4 + 4 * index.val))).extractLsb'
            (8 * byte.val) 8 := by rw [words index]
      _ = original.getByte
            (BitVec.ofNat 64 (0x22cb4 + 4 * index.val + byte.val)) := source.symm
      _ = original.getByte (BitVec.ofNat 64 (0x22cb4 + i)) := by
        simpa only [Nat.add_assoc, split]
  exact hbyte.trans (encoded.parameter i hi)

private theorem extractByte_extractLsb64 {n : Nat} (value : BitVec n)
    (word : Nat) (byte : Fin 8) :
    extractByte (value.extractLsb' (64 * word) 64) byte.val =
      value.extractLsb' (8 * (8 * word + byte.val)) 8 := by
  ext bit bitBound
  simp [extractByte, BitVec.truncate_eq_setWidth, Nat.mul_add,
    Nat.add_assoc]
  have within : byte.val * 8 + bit < 64 := by
    have := byte.isLt
    omega
  simp only [within]
  simp only [decide_true, Bool.true_and]
  congr 1
  omega

private theorem message_word_byte (state : MachineState)
    (index : Fin 4) (byte : Fin 8) :
    state.getByte (BitVec.ofNat 64
      (0x40050 + 8 * index.val + byte.val)) =
      extractByte
        (state.getMem (BitVec.ofNat 64 (0x40050 + 8 * index.val)))
        byte.val := by
  fin_cases index <;> fin_cases byte <;>
    simp [MachineState.getByte, alignToDword, byteOffset]

theorem message_bytes_of_words (state : MachineState)
    (message : SigGolf.Message)
    (words : ∀ index : Fin 4,
      state.getMem (BitVec.ofNat 64 (0x40050 + 8 * index.val)) =
        message.extractLsb' (64 * index.val) 64)
    (i : Nat) (hi : i < 32) :
    state.getByte (BitVec.ofNat 64 (0x40050 + i)) =
      message.extractLsb' (8 * i) 8 := by
  let index : Fin 4 := ⟨i / 8, by omega⟩
  let byte : Fin 8 := ⟨i % 8, Nat.mod_lt _ (by decide)⟩
  have split : 8 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  calc
    state.getByte (BitVec.ofNat 64 (0x40050 + i)) =
        state.getByte
          (BitVec.ofNat 64 (0x40050 + 8 * index.val + byte.val)) := by
      simpa only [Nat.add_assoc, split]
    _ = extractByte
          (state.getMem (BitVec.ofNat 64 (0x40050 + 8 * index.val)))
          byte.val := message_word_byte state index byte
    _ = extractByte (message.extractLsb' (64 * index.val) 64)
          byte.val := by rw [words index]
    _ = message.extractLsb' (8 * i) 8 := by
      simpa only [split] using
        extractByte_extractLsb64 message index.val byte

/-- info: 'SigGolfCandidate.SphincsVerifierSecondHashBytes.field_bytes_of_words' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms field_bytes_of_words

end SigGolfCandidate.SphincsVerifierSecondHashBytes
