import SigGolfCandidate.SphincsVerifierFtsGenericPairData

/-! Trace and five-word data invariant for a FORS pair at any bounded witness pointer. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericPair
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsRightPath
open SigGolfCandidate.SphincsVerifierFtsLeftPath
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsGenericPairTrace
open SigGolfCandidate.SphincsVerifierFtsGenericPairData
set_option maxRecDepth 16384

theorem pair_trace_and_data_generic (start : MachineState) (pointer : Word)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0) :
    let parity := parityState start
    let pair := pairState start
    OrdinarySteps SphincsImages.verify start
      (if parity.getReg .x6 = 0 then 34 else 35) pair ∧
    pair.pc = 0x1a14 ∧
    ∀ index : Fin 5,
      if parity.getReg .x6 = 0 then
        pair.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
          start.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) ∧
        pair.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
          start.getWord32
            (BitVec.ofNat 64 (pointer.toNat + 4 * index.val))
      else
        pair.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
          start.getWord32
            (BitVec.ofNat 64 (pointer.toNat + 4 * index.val)) ∧
        pair.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
          start.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  have admissible : PathPointerAdmissible pointer := by
    exact ⟨aligned, by have h := small; unfold MEMORY_BYTES; omega⟩
  have trace := pair_trace_generic start pointer pc pointerValue admissible
  let parity := parityState start
  let branched := branchState parity
  have atBranch : branched.getMem 0x43028 = pointer := by
    rw [branch_mem, parity_mem]
    exact pointerValue
  by_cases zero : parity.getReg .x6 = 0
  · change (parityState start).getReg .x6 = 0 at zero
    have data := leftPair_data_generic branched pointer atBranch small
    simp only [pairState, zero, if_true] at trace ⊢
    refine ⟨trace.1, trace.2, ?_⟩
    intro index
    simpa only [branched, parity, branch_word, parity_word] using data index
  · change (parityState start).getReg .x6 ≠ 0 at zero
    have data := rightPair_data_generic branched pointer atBranch small
    simp only [pairState, zero, if_false] at trace ⊢
    refine ⟨trace.1, trace.2, ?_⟩
    intro index
    simpa only [branched, parity, branch_word, parity_word] using data index

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericPair.pair_trace_and_data_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pair_trace_and_data_generic

end SigGolfCandidate.SphincsVerifierFtsGenericPair
