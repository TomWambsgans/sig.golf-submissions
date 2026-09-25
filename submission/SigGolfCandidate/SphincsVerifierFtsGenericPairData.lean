import SigGolfCandidate.SphincsVerifierFtsGenericCopyData

/-! Both FORS pair orientations with a variable witness-path address. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericPairData
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsRightPath
open SigGolfCandidate.SphincsVerifierFtsLeftPath
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsGenericCopyData
set_option maxRecDepth 16384

theorem rightPair_data_generic (branched : MachineState) (pointer : Word)
    (pointerValue : branched.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (index : Fin 5) :
    let pointers := rightPointers branched
    let first := copyRootState pointers
    let pair := rightFinishState first
    pair.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      branched.getWord32
        (BitVec.ofNat 64 (pointer.toNat + 4 * index.val)) ∧
      pair.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        branched.getWord32
          (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  let pointers := rightPointers branched
  let first := copyRootState pointers
  have source : pointers.getReg .x6 = BitVec.ofNat 64 pointer.toNat := by
    rw [(rightPointers_regs branched).1, pointerValue]
    simp
  have destination := (rightPointers_regs branched).2
  constructor
  · rw [rightFinish_sibling,
      copyRoot_data_belowHash pointers pointer.toNat 0x40028 small
        (Or.inl rfl) source destination,
      rightPointers_word]
  · rw [rightFinish_current, rightCopy_current_frame pointers destination,
      rightPointers_word]

theorem leftPair_data_generic (branched : MachineState) (pointer : Word)
    (pointerValue : branched.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (index : Fin 5) :
    (leftPairState branched).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      branched.getWord32
        (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) ∧
      (leftPairState branched).getWord32
        (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        branched.getWord32
          (BitVec.ofNat 64 (pointer.toNat + 4 * index.val)) := by
  let currentPointers := leftCurrentPointers branched
  let currentCopy := copyRootState currentPointers
  let siblingPointers := leftSiblingPointers currentCopy
  have currentSource := (leftCurrentPointers_regs branched).1
  have currentDestination := (leftCurrentPointers_regs branched).2
  have pointerAtCopy : currentCopy.getMem 0x43028 = pointer := by
    rw [leftCurrentCopy_pointer currentPointers currentDestination,
      leftCurrentPointers_mem]
    exact pointerValue
  have siblingSource : siblingPointers.getReg .x6 =
      BitVec.ofNat 64 pointer.toNat := by
    rw [(leftSiblingPointers_regs currentCopy).1, pointerAtCopy]
    simp
  have siblingDestination := (leftSiblingPointers_regs currentCopy).2
  constructor
  · unfold leftPairState
    rw [rightCurrentCopy_preserve_sibling siblingPointers siblingDestination,
      leftSiblingPointers_word,
      leftCurrentCopy_data currentPointers currentSource currentDestination,
      leftCurrentPointers_word]
  · unfold leftPairState
    rw [copyRoot_data_belowHash siblingPointers pointer.toNat 0x4003c small
        (Or.inr rfl) siblingSource siblingDestination,
      leftSiblingPointers_word,
      copyRoot_source_frame currentPointers pointer.toNat 0x40028 small
        (Or.inl rfl) currentDestination,
      leftCurrentPointers_word]

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericPairData.leftPair_data_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms leftPair_data_generic

end SigGolfCandidate.SphincsVerifierFtsGenericPairData
