import SigGolfCandidate.SphincsVerifierFtsParentFirstQuery

/-! Both FORS pair-copy branches with a bounded, aligned path pointer. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericPairTrace
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsRightPath
open SigGolfCandidate.SphincsVerifierFtsLeftPath
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 500000

def PathPointerAdmissible (pointer : Word) : Prop :=
  pointer.toNat % 4 = 0 ∧ pointer.toNat + 20 ≤ MEMORY_BYTES

theorem rightPath_generic (start : MachineState) (pointer : Word)
    (pc : (parityState start).pc = 0x1924)
    (odd : (parityState start).getReg .x6 ≠ 0)
    (pointerValue : start.getMem 0x43028 = pointer)
    (admissible : PathPointerAdmissible pointer) :
    let parity := parityState start
    let branched := branchState parity
    let first := copyRootState (rightPointers branched)
    let pair := rightFinishState first
    OrdinarySteps SphincsImages.verify parity 31 pair ∧
      pair.pc = 0x1a14 := by
  let parity := parityState start
  let branched := branchState parity
  let pointers := rightPointers branched
  let first := copyRootState pointers
  have branchTrace := branch_block parity pc
  have branchPc := branch_pc_odd parity pc odd
  have pointerAtBranch : branched.getMem 0x43028 = pointer := by
    rw [branch_mem, parity_mem]
    exact pointerValue
  have source : pointers.getReg .x6 = BitVec.ofNat 64 pointer.toNat := by
    rw [(rightPointers_regs branched).1, pointerAtBranch]
    simp
  have destination := (rightPointers_regs branched).2
  have pointerTrace := rightPointers_block branched branchPc
  have pointersPc := rightPointers_pc branched branchPc
  have copied := copy20_block_general SphincsImages.verify 591
    rightCopy_code pointers pointer.toNat 0x40028
    (by simpa using pointersPc) source destination
    admissible.1 admissible.2 (by decide) (by decide) (by decide)
  have copiedPc := rightCopy_pc pointers pointersPc
  have finish := rightFinish_block first copiedPc
  exact ⟨((branchTrace.append pointerTrace).append copied).append finish.1,
    finish.2⟩

theorem leftPath_generic (start : MachineState) (pointer : Word)
    (pc : (parityState start).pc = 0x1924)
    (even : (parityState start).getReg .x6 = 0)
    (pointerValue : start.getMem 0x43028 = pointer)
    (admissible : PathPointerAdmissible pointer) :
    let parity := parityState start
    let branched := branchState parity
    let pair := leftPairState branched
    OrdinarySteps SphincsImages.verify parity 30 pair ∧
      pair.pc = 0x1a14 := by
  let parity := parityState start
  let branched := branchState parity
  let currentPointers := leftCurrentPointers branched
  let currentCopy := copyRootState currentPointers
  let siblingPointers := leftSiblingPointers currentCopy
  have branchTrace := branch_block parity pc
  have branchPc := branch_pc_even parity pc even
  have currentPointersTrace := leftCurrentPointers_block branched branchPc
  have currentPointersPc := leftCurrentPointers_pc branched branchPc
  have currentSource := (leftCurrentPointers_regs branched).1
  have currentDestination := (leftCurrentPointers_regs branched).2
  have currentTrace := leftCurrentCopy_block currentPointers
    currentPointersPc currentSource currentDestination
  have currentPc := leftCurrentCopy_pc currentPointers currentPointersPc
  have pointerAtBranch : branched.getMem 0x43028 = pointer := by
    rw [branch_mem, parity_mem]
    exact pointerValue
  have pointerAtCopy : currentCopy.getMem 0x43028 = pointer := by
    rw [leftCurrentCopy_pointer currentPointers currentDestination,
      leftCurrentPointers_mem]
    exact pointerAtBranch
  have siblingPointersTrace := leftSiblingPointers_block currentCopy currentPc
  have siblingPointersPc := leftSiblingPointers_pc currentCopy currentPc
  have siblingSource : siblingPointers.getReg .x6 =
      BitVec.ofNat 64 pointer.toNat := by
    rw [(leftSiblingPointers_regs currentCopy).1, pointerAtCopy]
    simp
  have siblingDestination := (leftSiblingPointers_regs currentCopy).2
  have siblingTrace := copy20_block_general SphincsImages.verify 635
    leftSiblingCopy_code siblingPointers pointer.toNat 0x4003c
    (by simpa using siblingPointersPc) siblingSource siblingDestination
    admissible.1 admissible.2 (by decide) (by decide) (by decide)
  exact ⟨(((branchTrace.append currentPointersTrace).append currentTrace).append
      siblingPointersTrace).append siblingTrace,
    leftSiblingCopy_pc siblingPointers siblingPointersPc⟩

theorem pair_trace_generic (start : MachineState) (pointer : Word)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (admissible : PathPointerAdmissible pointer) :
    let parity := parityState start
    let pair := pairState start
    OrdinarySteps SphincsImages.verify start
      (if parity.getReg .x6 = 0 then 34 else 35) pair ∧
      pair.pc = 0x1a14 := by
  let parity := parityState start
  have front := parity_block start pc
  have parityPc := parity_pc start pc
  by_cases zero : parity.getReg .x6 = 0
  · change (parityState start).getReg .x6 = 0 at zero
    have back := leftPath_generic start pointer parityPc zero pointerValue
      admissible
    have result : OrdinarySteps SphincsImages.verify start 34
        (leftPairState (branchState (parityState start))) ∧
        (leftPairState (branchState (parityState start))).pc = 0x1a14 := by
      exact ⟨by simpa using front.append back.1, back.2⟩
    simpa only [pairState, zero, if_true] using result
  · change (parityState start).getReg .x6 ≠ 0 at zero
    have back := rightPath_generic start pointer parityPc zero pointerValue
      admissible
    have result : OrdinarySteps SphincsImages.verify start 35
        (rightFinishState (copyRootState
          (rightPointers (branchState (parityState start))))) ∧
        (rightFinishState (copyRootState
          (rightPointers (branchState (parityState start))))).pc = 0x1a14 := by
      exact ⟨by simpa using front.append back.1, back.2⟩
    simpa only [pairState, zero, if_false] using result

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericPairTrace.pair_trace_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pair_trace_generic

end SigGolfCandidate.SphincsVerifierFtsGenericPairTrace
