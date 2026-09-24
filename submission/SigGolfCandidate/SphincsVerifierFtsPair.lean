import SigGolfCandidate.SphincsVerifierFtsLeftPath

/-! Both orientations of the first FORS authentication pair join at the parent-hash input. -/

namespace SigGolfCandidate.SphincsVerifierFtsPair
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsRightPath
open SigGolfCandidate.SphincsVerifierFtsLeftPath
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def pairState (start : MachineState) : MachineState :=
  let parity := parityState start
  let branched := branchState parity
  if parity.getReg .x6 = 0 then leftPairState branched
  else rightFinishState (copyRootState (rightPointers branched))

theorem copyRoot_pointer_frame (state : MachineState)
    (destination : state.getReg .x7 = 0x40028 ∨
      state.getReg .x7 = 0x4003c) :
    (copyRootState state).getMem 0x43028 =
      state.getMem 0x43028 := by
  apply copyRoot_mem_frame
  intro offset
  rcases destination with h | h <;> rw [h] <;>
    fin_cases offset <;> decide

theorem rightPair_pointer_frame (branched : MachineState) :
    (rightFinishState (copyRootState (rightPointers branched))).getMem
        0x43028 = branched.getMem 0x43028 := by
  let first := copyRootState (rightPointers branched)
  change (rightJump (copyRootState (rightCurrentPointers first))).getMem
    0x43028 = _
  rw [rightJump_mem,
    copyRoot_pointer_frame _ (Or.inr (rightCurrentPointers_regs first).2),
    rightCurrentPointers_mem,
    copyRoot_pointer_frame _ (Or.inl (rightPointers_regs branched).2),
    rightPointers_mem]

theorem leftPair_pointer_frame (branched : MachineState) :
    (leftPairState branched).getMem 0x43028 =
      branched.getMem 0x43028 := by
  let first := copyRootState (leftCurrentPointers branched)
  change (copyRootState (leftSiblingPointers first)).getMem 0x43028 = _
  rw [copyRoot_pointer_frame _
      (Or.inr (leftSiblingPointers_regs first).2),
    leftSiblingPointers_mem,
    copyRoot_pointer_frame _
      (Or.inl (leftCurrentPointers_regs branched).2),
    leftCurrentPointers_mem]

theorem pair_pointer_frame (start : MachineState) :
    (pairState start).getMem 0x43028 = start.getMem 0x43028 := by
  let parity := parityState start
  let branched := branchState parity
  by_cases zero : parity.getReg .x6 = 0
  · change (parityState start).getReg .x6 = 0 at zero
    simp only [pairState, zero, if_true]
    rw [leftPair_pointer_frame, branch_mem, parity_mem]
  · change (parityState start).getReg .x6 ≠ 0 at zero
    simp only [pairState, zero, if_false]
    rw [rightPair_pointer_frame, branch_mem, parity_mem]

theorem copyRoot_scratch_frame (state : MachineState) (address : Word)
    (destination : state.getReg .x7 = 0x40028 ∨
      state.getReg .x7 = 0x4003c)
    (outside28 : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x40028 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)))
    (outside3c : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x4003c + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val))) :
    (copyRootState state).getMem address = state.getMem address := by
  apply copyRoot_mem_frame
  intro offset
  rcases destination with h | h
  · rw [h]
    exact outside28 offset
  · rw [h]
    exact outside3c offset

theorem rightPair_scratch_frame (branched : MachineState)
    (address : Word)
    (outside28 : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x40028 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)))
    (outside3c : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x4003c + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val))) :
    (rightFinishState (copyRootState (rightPointers branched))).getMem
        address = branched.getMem address := by
  let first := copyRootState (rightPointers branched)
  change (rightJump (copyRootState (rightCurrentPointers first))).getMem
    address = _
  rw [rightJump_mem,
    copyRoot_scratch_frame _ address
      (Or.inr (rightCurrentPointers_regs first).2) outside28 outside3c,
    rightCurrentPointers_mem,
    copyRoot_scratch_frame _ address
      (Or.inl (rightPointers_regs branched).2) outside28 outside3c,
    rightPointers_mem]

theorem leftPair_scratch_frame (branched : MachineState)
    (address : Word)
    (outside28 : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x40028 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)))
    (outside3c : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x4003c + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val))) :
    (leftPairState branched).getMem address =
      branched.getMem address := by
  let first := copyRootState (leftCurrentPointers branched)
  change (copyRootState (leftSiblingPointers first)).getMem address = _
  rw [copyRoot_scratch_frame _ address
      (Or.inr (leftSiblingPointers_regs first).2) outside28 outside3c,
    leftSiblingPointers_mem,
    copyRoot_scratch_frame _ address
      (Or.inl (leftCurrentPointers_regs branched).2) outside28 outside3c,
    leftCurrentPointers_mem]

theorem pair_scratch_frame (start : MachineState) (address : Word)
    (outside28 : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x40028 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)))
    (outside3c : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x4003c + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val))) :
    (pairState start).getMem address = start.getMem address := by
  let parity := parityState start
  let branched := branchState parity
  by_cases zero : parity.getReg .x6 = 0
  · change (parityState start).getReg .x6 = 0 at zero
    simp only [pairState, zero, if_true]
    rw [leftPair_scratch_frame _ address outside28 outside3c,
      branch_mem, parity_mem]
  · change (parityState start).getReg .x6 ≠ 0 at zero
    simp only [pairState, zero, if_false]
    rw [rightPair_scratch_frame _ address outside28 outside3c,
      branch_mem, parity_mem]

theorem pair_level_frame (start : MachineState) :
    (pairState start).getMem 0x43048 = start.getMem 0x43048 := by
  apply pair_scratch_frame
  all_goals intro offset <;> fin_cases offset <;> decide

theorem pair_selector_frame (start : MachineState) :
    (pairState start).getMem 0x43070 = start.getMem 0x43070 := by
  apply pair_scratch_frame
  all_goals intro offset <;> fin_cases offset <;> decide

theorem pair_trace_and_data (start : MachineState)
    (pc : (parityState start).pc = 0x1924)
    (pointer : start.getMem 0x43028 = 0x22cf0) :
    let parity := parityState start
    let pair := pairState start
    OrdinarySteps SphincsImages.verify parity
      (if parity.getReg .x6 = 0 then 30 else 31) pair ∧
    pair.pc = 0x1a14 ∧
    ∀ index : Fin 5,
      if parity.getReg .x6 = 0 then
        pair.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
          start.getWord32
            (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) ∧
        pair.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
          start.getWord32
            (BitVec.ofNat 64 (0x22cf0 + 4 * index.val))
      else
        pair.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
          start.getWord32
            (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)) ∧
        pair.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
          start.getWord32
            (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  let parity := parityState start
  by_cases zero : parity.getReg .x6 = 0
  · have trace := leftPath_from_parity start pc zero pointer
    have data := leftPath_pair_data start pointer
    change (parityState start).getReg .x6 = 0 at zero
    simp only [pairState, zero, if_true]
    exact ⟨trace.1, trace.2, fun index => data index⟩
  · have trace := rightPath_to_pair start pc zero pointer
    have data := rightPath_pair_data start pointer
    change (parityState start).getReg .x6 ≠ 0 at zero
    simp only [pairState, zero, if_false]
    exact ⟨trace.1, trace.2, fun index => data index⟩

theorem pair_from_level_start (start : MachineState)
    (pc : start.pc = 0x1914)
    (pointer : start.getMem 0x43028 = 0x22cf0) :
    let parity := parityState start
    let pair := pairState start
    OrdinarySteps SphincsImages.verify start
      (if parity.getReg .x6 = 0 then 34 else 35) pair ∧
      pair.pc = 0x1a14 := by
  have front := parity_block start pc
  have back := pair_trace_and_data start (parity_pc start pc) pointer
  have trace := front.append back.1
  by_cases zero : (parityState start).getReg .x6 = 0
  · change (parityState start).getReg .x6 = 0#64 at zero
    exact ⟨by simpa [zero] using trace, back.2.1⟩
  · change (parityState start).getReg .x6 ≠ 0#64 at zero
    exact ⟨by simpa [zero] using trace, back.2.1⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPair.pair_trace_and_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pair_trace_and_data

end SigGolfCandidate.SphincsVerifierFtsPair
