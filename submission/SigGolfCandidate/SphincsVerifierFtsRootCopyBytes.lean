import SigGolfCandidate.SphincsVerifierFtsRootCopy

namespace SigGolfCandidate.SphincsVerifierFtsRootCopyBytes
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsRootCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- The byte view of an aligned word buffer in the actual machine memory. -/
theorem getByte_word (state : MachineState) (base i : Nat)
    (aligned : base % 8 = 0) (bound : base + i < 2 ^ 64) :
    state.getByte (BitVec.ofNat 64 (base + i)) =
      extractByte (state.getMem (wordAddress base (i / 8))) (i % 8) := by
  have hb : base < 2 ^ 64 := by omega
  have ha : (BitVec.ofNat 64 base).toNat % 8 = 0 := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] using aligned
  have hi : (BitVec.ofNat 64 base).toNat + i < 2 ^ 64 := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] using bound
  simp only [MachineState.getByte, BitVec.ofNat_add,
    alignToDword_add_ofNat_of_aligned ha hi,
    byteOffset_add_ofNat_of_aligned ha hi, wordAddress]

theorem bytes_eq_of_words (original final : MachineState)
    (source destination count : Nat)
    (srcalign : source % 8 = 0) (dstalign : destination % 8 = 0)
    (srcbound : source + count ≤ 2 ^ 64)
    (dstbound : destination + count ≤ 2 ^ 64)
    (words : ∀ j, j < (count + 7) / 8 →
      final.getMem (wordAddress destination j) =
        original.getMem (wordAddress source j))
    (i : Nat) (hi : i < count) :
    final.getByte (BitVec.ofNat 64 (destination + i)) =
      original.getByte (BitVec.ofNat 64 (source + i)) := by
  rw [getByte_word final destination i dstalign (by omega),
    getByte_word original source i srcalign (by omega),
    words (i / 8) (by omega)]

/-- Every one of the 480 copied root bytes matches the source region. -/
theorem rootCopy_bytes (state : MachineState)
    (pc : state.pc = 0x1c74)
    (source : state.getReg .x6 = 0x44100)
    (destination : state.getReg .x7 = 0x40028)
    (count : state.getReg .x10 = 60) :
    ∃ final,
      OrdinarySteps SphincsImages.verify state 360 final ∧
      final.pc = 0x1c8c ∧
      (∀ i, i < 480 →
        final.getByte (BitVec.ofNat 64 (0x40028 + i)) =
          state.getByte (BitVec.ofNat 64 (0x44100 + i))) := by
  obtain ⟨final, trace, finalPc, copied, _⟩ :=
    rootCopy_all state pc source destination count
  refine ⟨final, trace, finalPc, ?_⟩
  intro i hi
  apply bytes_eq_of_words state final 0x44100 0x40028 480
    (by decide) (by decide) (by decide) (by decide) _ i hi
  intro j hj
  simpa only [wordAddress] using copied j (by omega)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootCopyBytes.rootCopy_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootCopy_bytes

end SigGolfCandidate.SphincsVerifierFtsRootCopyBytes
