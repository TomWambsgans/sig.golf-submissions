import SigGolfCandidate.SphincsVerifierFtsGenericLoop

/-! Complete FORS parent trace through the HASH call site, for any bounded path pointer. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericReadyTrace
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsGenericPairTrace
open SigGolfCandidate.SphincsVerifierFtsGenericPosition
set_option maxRecDepth 16384

theorem parentReady_trace_generic (start : MachineState) (pointer : Word)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (admissible : PathPointerAdmissible pointer) :
    let pair := pairState start
    let ready := firstParentReadyState start
    OrdinarySteps SphincsImages.verify pair 65 ready ∧
      ready.pc = 0x1b18 := by
  have positioned := positioned_trace_generic start pointer pc pointerValue
    admissible
  have prepared := parentHashReady_block (firstPositionedState start)
    positioned.2.1
  exact ⟨positioned.1.append prepared.1, prepared.2.1⟩

theorem parentReady_fullTrace_generic (start : MachineState)
    (pointer : Word)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (admissible : PathPointerAdmissible pointer) :
    let parity := SigGolfCandidate.SphincsVerifierFtsLevelBranch.parityState start
    let ready := firstParentReadyState start
    OrdinarySteps SphincsImages.verify start
      ((if parity.getReg .x6 = 0 then 34 else 35) + 65) ready ∧
      ready.pc = 0x1b18 := by
  have pair := pair_trace_generic start pointer pc pointerValue admissible
  have rest := parentReady_trace_generic start pointer pc pointerValue admissible
  exact ⟨pair.1.append rest.1, rest.2⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericReadyTrace.parentReady_fullTrace_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentReady_fullTrace_generic

end SigGolfCandidate.SphincsVerifierFtsGenericReadyTrace
