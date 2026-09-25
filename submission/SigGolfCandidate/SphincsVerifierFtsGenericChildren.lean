import SigGolfCandidate.SphincsVerifierFtsGenericPair

/-! Parent-hash child words after a FORS pair at an arbitrary path pointer. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericChildren
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsGenericPair
set_option maxRecDepth 16384

theorem positioned_pair_words_generic (start : MachineState) (pointer : Word)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0)
    (index : Fin 5) :
    let positioned := firstPositionedState start
    if (parityState start).getReg .x6 = 0 then
      positioned.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        start.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) ∧
      positioned.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        start.getWord32
          (BitVec.ofNat 64 (pointer.toNat + 4 * index.val))
    else
      positioned.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        start.getWord32
          (BitVec.ofNat 64 (pointer.toNat + 4 * index.val)) ∧
      positioned.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        start.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  let pair := pairState start
  let advanced := advancePointerState pair
  let shifted := shiftIndexState advanced
  let positioned := levelPositionState shifted
  have pairWords :=
    (pair_trace_and_data_generic start pointer pc pointerValue small aligned).2.2
      index
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

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericChildren.positioned_pair_words_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms positioned_pair_words_generic

end SigGolfCandidate.SphincsVerifierFtsGenericChildren
