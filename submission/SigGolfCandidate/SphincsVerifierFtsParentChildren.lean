import SigGolfCandidate.SphincsVerifierFtsParentWitness

/-! Relate the FORS parent pair's two 20-byte fields to the running root and path. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentChildren
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsParentExecution
set_option maxRecDepth 16384

theorem pairWord_byte (state : MachineState) (base : Nat)
    (supported : base = 0x22cf0 ∨ base = 0x44a00 ∨
      base = 0x40028 ∨ base = 0x4003c)
    (index : Fin 5) (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64 (base + 4 * index.val + byte.val)) =
      (state.getWord32
        (BitVec.ofNat 64 (base + 4 * index.val))).extractLsb'
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

theorem positioned_pair_words (start : MachineState)
    (pc : start.pc = 0x1914)
    (pointer : start.getMem 0x43028 = 0x22cf0)
    (index : Fin 5) :
    let positioned := firstPositionedState start
    if (parityState start).getReg .x6 = 0 then
      positioned.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        start.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) ∧
      positioned.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        start.getWord32 (BitVec.ofNat 64 (0x22cf0 + 4 * index.val))
    else
      positioned.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        start.getWord32 (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)) ∧
      positioned.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        start.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  let pair := pairState start
  let advanced := advancePointerState pair
  let shifted := shiftIndexState advanced
  let positioned := levelPositionState shifted
  have pairWords := (pair_trace_and_data start (parity_pc start pc) pointer).2.2 index
  have positionWords := levelPosition_pair_data shifted index
  have shiftWords := shiftIndex_pair_data advanced index
  have advanceWords := advancePointer_pair_data pair index
  have first : positioned.getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        pair.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) :=
    (positionWords.1.trans shiftWords.1).trans advanceWords.1
  have second : positioned.getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        pair.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) :=
    (positionWords.2.trans shiftWords.2).trans advanceWords.2
  by_cases zero : (parityState start).getReg .x6 = 0
  · simp only [zero, if_true] at pairWords ⊢
    exact ⟨first.trans pairWords.1, second.trans pairWords.2⟩
  · simp only [zero, if_false] at pairWords ⊢
    exact ⟨first.trans pairWords.1, second.trans pairWords.2⟩

private theorem transfer_bytes (ready original : MachineState)
    (destination source : Nat)
    (destinationSupported : destination = 0x40028 ∨ destination = 0x4003c)
    (sourceSupported : source = 0x22cf0 ∨ source = 0x44a00)
    (words : ∀ index : Fin 5,
      ready.getWord32 (BitVec.ofNat 64 (destination + 4 * index.val)) =
        original.getWord32 (BitVec.ofNat 64 (source + 4 * index.val)))
    (i : Nat) (hi : i < 20) :
    ready.getByte (BitVec.ofNat 64 (destination + i)) =
      original.getByte (BitVec.ofNat 64 (source + i)) := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  have readyByte := pairWord_byte ready destination
    (destinationSupported.elim (fun h => Or.inr (Or.inr (Or.inl h)))
      (fun h => Or.inr (Or.inr (Or.inr h)))) index byte
  have originalByte := pairWord_byte original source
    (sourceSupported.elim Or.inl (fun h => Or.inr (Or.inl h))) index byte
  simpa only [Nat.add_assoc, split] using
    readyByte.trans ((congrArg (fun value : BitVec 32 =>
      value.extractLsb' (8 * byte.val) 8) (words index)).trans
        originalByte.symm)

theorem positioned_pair_bytes (start : MachineState)
    (pc : start.pc = 0x1914)
    (pointer : start.getMem 0x43028 = 0x22cf0)
    (i : Nat) (hi : i < 20) :
    let positioned := firstPositionedState start
    if (parityState start).getReg .x6 = 0 then
      positioned.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        start.getByte (BitVec.ofNat 64 (0x44a00 + i)) ∧
      positioned.getByte (BitVec.ofNat 64 (0x4003c + i)) =
        start.getByte (BitVec.ofNat 64 (0x22cf0 + i))
    else
      positioned.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        start.getByte (BitVec.ofNat 64 (0x22cf0 + i)) ∧
      positioned.getByte (BitVec.ofNat 64 (0x4003c + i)) =
        start.getByte (BitVec.ofNat 64 (0x44a00 + i)) := by
  by_cases zero : (parityState start).getReg .x6 = 0
  · simp only [zero, if_true]
    constructor
    · apply transfer_bytes _ _ 0x40028 0x44a00 (Or.inl rfl)
        (Or.inr rfl) _ i hi
      intro index
      have pair := positioned_pair_words start pc pointer index
      simp only [zero, if_true] at pair
      exact pair.1
    · apply transfer_bytes _ _ 0x4003c 0x22cf0 (Or.inr rfl)
        (Or.inl rfl) _ i hi
      intro index
      have pair := positioned_pair_words start pc pointer index
      simp only [zero, if_true] at pair
      exact pair.2
  · simp only [zero, if_false]
    constructor
    · apply transfer_bytes _ _ 0x40028 0x22cf0 (Or.inl rfl)
        (Or.inl rfl) _ i hi
      intro index
      have pair := positioned_pair_words start pc pointer index
      simp only [zero, if_false] at pair
      exact pair.1
    · apply transfer_bytes _ _ 0x4003c 0x44a00 (Or.inr rfl)
        (Or.inr rfl) _ i hi
      intro index
      have pair := positioned_pair_words start pc pointer index
      simp only [zero, if_false] at pair
      exact pair.2

theorem positioned_children_encoded (start : MachineState)
    (current sibling : SphincsSecurity.Digest)
    (pc : start.pc = 0x1914)
    (pointer : start.getMem 0x43028 = 0x22cf0)
    (currentEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        current.extractLsb' (8 * i) 8)
    (siblingEncoded : ∀ i, (hi : i < 20) →
      start.getByte (BitVec.ofNat 64 (0x22cf0 + i)) =
        sibling.extractLsb' (8 * i) 8)
    (i : Nat) (hi : i < 20) :
    let positioned := firstPositionedState start
    let zero := (parityState start).getReg .x6 = 0
    positioned.getByte (BitVec.ofNat 64 (0x40028 + i)) =
      (if zero then current else sibling).extractLsb' (8 * i) 8 ∧
    positioned.getByte (BitVec.ofNat 64 (0x4003c + i)) =
      (if zero then sibling else current).extractLsb' (8 * i) 8 := by
  have pair := positioned_pair_bytes start pc pointer i hi
  by_cases zero : (parityState start).getReg .x6 = 0
  · simp only [zero, if_true] at pair ⊢
    exact ⟨pair.1.trans (currentEncoded i hi),
      pair.2.trans (siblingEncoded i hi)⟩
  · simp only [zero, if_false] at pair ⊢
    exact ⟨pair.1.trans (siblingEncoded i hi),
      pair.2.trans (currentEncoded i hi)⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentChildren.positioned_children_encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms positioned_children_encoded

end SigGolfCandidate.SphincsVerifierFtsParentChildren
