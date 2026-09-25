import SigGolfCandidate.SphincsVerifierFtsGenericBytes

/-! Generic FORS parent positioning and pointer advancement. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericPosition
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsGenericPairTrace
open SigGolfCandidate.SphincsVerifierFtsParentExecution
set_option maxRecDepth 16384

theorem positioned_trace_generic (start : MachineState) (pointer : Word)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (admissible : PathPointerAdmissible pointer) :
    let pair := pairState start
    let advanced := advancePointerState pair
    let shifted := shiftIndexState advanced
    let positioned := levelPositionState shifted
    OrdinarySteps SphincsImages.verify pair 23 positioned ∧
    positioned.pc = 0x1a70 ∧
    positioned.getMem 0x43028 = pointer + 20 ∧
    positioned.getMem 0x43010 = start.getMem 0x43048 ∧
    positioned.getMem 0x43070 = start.getMem 0x43070 >>> 1 ∧
    positioned.getMem 0x43018 = start.getMem 0x43070 >>> 1 := by
  let pair := pairState start
  let advanced := advancePointerState pair
  let shifted := shiftIndexState advanced
  let positioned := levelPositionState shifted
  have pairTrace := pair_trace_generic start pointer pc pointerValue admissible
  have advanceTrace := advancePointer_block pair pairTrace.2
  have advancePc := advancePointer_pc pair pairTrace.2
  have shiftTrace := shiftIndex_block advanced advancePc
  have shiftPc := shiftIndex_pc advanced advancePc
  have positionTrace := levelPosition_block shifted shiftPc
  have positionPc := levelPosition_pc shifted shiftPc
  have pairPointer : pair.getMem 0x43028 = pointer := by
    rw [pair_pointer_frame]
    exact pointerValue
  have pairLevel : pair.getMem 0x43048 = start.getMem 0x43048 :=
    pair_level_frame start
  have pairSelector : pair.getMem 0x43070 = start.getMem 0x43070 :=
    pair_selector_frame start
  have shiftedLevel : shifted.getMem 0x43048 = start.getMem 0x43048 := by
    rw [shiftIndex_mem_frame _ 0x43048 (by decide) (by decide),
      advancePointer_mem_frame _ 0x43048 (by decide), pairLevel]
  have advancedSelector : advanced.getMem 0x43070 =
      start.getMem 0x43070 := by
    rw [advancePointer_mem_frame _ 0x43070 (by decide), pairSelector]
  have shiftedCells := shiftIndex_cells advanced
  exact ⟨(advanceTrace.append shiftTrace).append positionTrace,
    positionPc,
    by rw [levelPosition_mem_frame _ 0x43028 (by decide),
        shiftIndex_mem_frame _ 0x43028 (by decide) (by decide),
        advancePointer_cell, pairPointer],
    by rw [levelPosition_cell]; exact shiftedLevel,
    by rw [levelPosition_mem_frame _ 0x43070 (by decide),
        shiftedCells.1, advancedSelector],
    by rw [levelPosition_mem_frame _ 0x43018 (by decide),
        shiftedCells.2, advancedSelector]⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericPosition.positioned_trace_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms positioned_trace_generic

end SigGolfCandidate.SphincsVerifierFtsGenericPosition
