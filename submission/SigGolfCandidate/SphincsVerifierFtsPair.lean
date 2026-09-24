import SigGolfCandidate.SphincsVerifierFtsLeftPath

/-! Both orientations of the first FORS authentication pair join at the parent-hash input. -/

namespace SigGolfCandidate.SphincsVerifierFtsPair
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsRightPath
open SigGolfCandidate.SphincsVerifierFtsLeftPath
open SigGolfCandidate.SphincsVerifierCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def pairState (start : MachineState) : MachineState :=
  let parity := parityState start
  let branched := branchState parity
  if parity.getReg .x6 = 0 then leftPairState branched
  else rightFinishState (copyRootState (rightPointers branched))

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
