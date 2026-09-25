import SigGolfCandidate.SphincsVerifierFtsGenericChildren

/-! Byte-level FORS authentication children at arbitrary witness offsets. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericBytes
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsGenericChildren
open SigGolfCandidate.SphincsVerifierFtsParentChildren
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsParentExecution
set_option maxRecDepth 16384

private theorem byteOffset_ofNat_mod (number : Nat)
    (small : number < 2 ^ 64) :
    byteOffset (BitVec.ofNat 64 number) = number % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  have cast : (BitVec.ofNat 64 number).toNat = number := by
    simp only [BitVec.toNat_ofNat]
    omega
  rw [cast]
  change number &&& (2 ^ 3 - 1) = number % 8
  exact Nat.and_two_pow_sub_one_eq_mod number 3

private theorem aligned_base_nat_split (address : Word) :
    (alignToDword address).toNat + byteOffset address = address.toNat := by
  unfold alignToDword byteOffset
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 7 from rfl]
  have lower : address.toNat &&& 7 = address.toNat % 8 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod address.toNat 3
  have upperMod : (address.toNat &&& (2 ^ 64 - 1 - 7)) % 8 = 0 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_mod_two_pow,
      show (2 ^ 64 - 1 - 7 : Nat) % 2 ^ 3 = 0 from by decide]
    simp
  have upperDiv : (address.toNat &&& (2 ^ 64 - 1 - 7)) / 8 =
      address.toNat / 8 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_div_two_pow,
      show (2 ^ 64 - 1 - 7 : Nat) / 2 ^ 3 = 2 ^ 61 - 1 from by decide]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow
      (by have h := address.isLt; omega)
  have upper : address.toNat &&& (2 ^ 64 - 1 - 7) =
      address.toNat / 8 * 8 := by
    have division := Nat.div_add_mod
      (address.toNat &&& (2 ^ 64 - 1 - 7)) 8
    omega
  rw [lower, upper]
  omega

theorem variableWord_byte (state : MachineState) (base : Nat)
    (small : base + 20 ≤ 0x50000)
    (aligned : base % 4 = 0)
    (index : Fin 5) (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64 (base + 4 * index.val + byte.val)) =
      (state.getWord32
        (BitVec.ofNat 64 (base + 4 * index.val))).extractLsb'
        (8 * byte.val) 8 := by
  let wordAddress := BitVec.ofNat 64 (base + 4 * index.val)
  let byteAddress := BitVec.ofNat 64 (base + 4 * index.val + byte.val)
  have wordBound : base + 4 * index.val < 2 ^ 64 := by
    have h := index.isLt
    omega
  have byteBound : base + 4 * index.val + byte.val < 2 ^ 64 := by
    have hi := index.isLt
    have hb := byte.isLt
    omega
  have wordAligned : wordAddress.toNat % 4 = 0 := by
    dsimp [wordAddress]
    rw [BitVec.toNat_ofNat]
    have : (base + 4 * index.val) % (2 ^ 64) =
        base + 4 * index.val := Nat.mod_eq_of_lt wordBound
    rw [this]
    omega
  have sameCell : alignToDword byteAddress =
      alignToDword wordAddress := by
    apply BitVec.eq_of_toNat_eq
    have wordNat : wordAddress.toNat = base + 4 * index.val := by
      dsimp [wordAddress]
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt wordBound
    have byteNat : byteAddress.toNat =
        base + 4 * index.val + byte.val := by
      dsimp [byteAddress]
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt byteBound
    have wordSplit := aligned_base_nat_split wordAddress
    have byteSplit := aligned_base_nat_split byteAddress
    have wordOffset := byteOffset_ofNat_mod
      (base + 4 * index.val) wordBound
    have byteOffsetEq := byteOffset_ofNat_mod
      (base + 4 * index.val + byte.val) byteBound
    rw [wordNat] at wordSplit
    rw [byteNat] at byteSplit
    rw [wordOffset] at wordSplit
    rw [byteOffsetEq] at byteSplit
    have hi := index.isLt
    have hb := byte.isLt
    omega
  have wordOffset : byteOffset wordAddress =
      (base + 4 * index.val) % 8 :=
    byteOffset_ofNat_mod _ wordBound
  have byteOffsetEq : byteOffset byteAddress =
      (base + 4 * index.val + byte.val) % 8 :=
    byteOffset_ofNat_mod _ byteBound
  have quotient : byteOffset byteAddress / 4 =
      byteOffset wordAddress / 4 := by
    rw [byteOffsetEq, wordOffset]
    have hi := index.isLt
    have hb := byte.isLt
    omega
  have remainder : byteOffset byteAddress % 4 = byte.val := by
    rw [byteOffsetEq]
    have hb := byte.isLt
    omega
  have split := SphincsVerifierSecondHashHeader.extractByte_from_word32
    (state.getMem (alignToDword byteAddress))
    ⟨byteOffset byteAddress, byteOffset_lt_8⟩
  simpa only [wordAddress, byteAddress, MachineState.getByte,
    MachineState.getWord32, sameCell, quotient, remainder] using split

theorem transfer_words_to_bytes (ready original : MachineState)
    (destination source : Nat)
    (destinationSmall : destination + 20 ≤ 0x50000)
    (sourceSmall : source + 20 ≤ 0x50000)
    (destinationAligned : destination % 4 = 0)
    (sourceAligned : source % 4 = 0)
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
  have readyByte := variableWord_byte ready destination destinationSmall
    destinationAligned index byte
  have originalByte := variableWord_byte original source sourceSmall
    sourceAligned index byte
  simpa only [Nat.add_assoc, split] using
    readyByte.trans ((congrArg (fun value : BitVec 32 =>
      value.extractLsb' (8 * byte.val) 8) (words index)).trans
        originalByte.symm)

theorem positioned_pair_bytes_generic (start : MachineState)
    (pointer : Word)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0)
    (i : Nat) (hi : i < 20) :
    let positioned := firstPositionedState start
    if (parityState start).getReg .x6 = 0 then
      positioned.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        start.getByte (BitVec.ofNat 64 (0x44a00 + i)) ∧
      positioned.getByte (BitVec.ofNat 64 (0x4003c + i)) =
        start.getByte (BitVec.ofNat 64 (pointer.toNat + i))
    else
      positioned.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        start.getByte (BitVec.ofNat 64 (pointer.toNat + i)) ∧
      positioned.getByte (BitVec.ofNat 64 (0x4003c + i)) =
        start.getByte (BitVec.ofNat 64 (0x44a00 + i)) := by
  have pairWords := positioned_pair_words_generic start pointer pc pointerValue
    small aligned
  by_cases zero : (parityState start).getReg .x6 = 0
  · simp only [zero, if_true]
    constructor
    · apply transfer_words_to_bytes _ _ 0x40028 0x44a00
        (by decide) (by decide) (by decide) (by decide) _ i hi
      intro index
      have pair := pairWords index
      simp only [zero, if_true] at pair
      exact pair.1
    · apply transfer_words_to_bytes _ _ 0x4003c pointer.toNat
        (by decide) (by omega) (by decide) aligned _ i hi
      intro index
      have pair := pairWords index
      simp only [zero, if_true] at pair
      exact pair.2
  · simp only [zero, if_false]
    constructor
    · apply transfer_words_to_bytes _ _ 0x40028 pointer.toNat
        (by decide) (by omega) (by decide) aligned _ i hi
      intro index
      have pair := pairWords index
      simp only [zero, if_false] at pair
      exact pair.1
    · apply transfer_words_to_bytes _ _ 0x4003c 0x44a00
        (by decide) (by decide) (by decide) (by decide) _ i hi
      intro index
      have pair := pairWords index
      simp only [zero, if_false] at pair
      exact pair.2

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericBytes.positioned_pair_bytes_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms positioned_pair_bytes_generic

end SigGolfCandidate.SphincsVerifierFtsGenericBytes
