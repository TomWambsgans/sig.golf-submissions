import SigGolfCandidate.SphincsVerifierFtsSelectorArithmetic

/-! Carry the FORS loop invariant across one parent HASH and loopback. -/

namespace SigGolfCandidate.SphincsVerifierFtsRoundInvariant
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierFtsResultWitness
open SigGolfCandidate.SphincsVerifierFtsResultPointer
open SigGolfCandidate.SphincsVerifierFtsResultControls
open SigGolfCandidate.SphincsVerifierFtsSelectorArithmetic
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolfCandidate.SphincsVerifierFtsGenericPairTrace
open SigGolfCandidate.SphincsVerifierFtsGenericPosition
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
set_option maxRecDepth 16384

def parentRoundState (start : MachineState) (answer : BitVec 256) :
    MachineState :=
  let ready := firstParentReadyState start
  SphincsVerifierFtsParentLoop.levelBranchState
    (SphincsVerifierFtsParentLoop.levelCheckState
      (SphincsVerifierFtsParentLevel.advanceLevelState
        (SphincsVerifierFtsParentResult.resultState (writeHash ready answer))))

theorem ready_destination (start : MachineState) :
    (firstParentReadyState start).getReg .x12 = 0x42000 :=
  (hashRegisters_ready _).2.2.1

theorem parentRound_witness (start : MachineState)
    (answer : BitVec 256) (signature : Signature)
    (witness : FtsWitness start signature) :
    FtsWitness (parentRoundState start answer) signature := by
  exact fullParent_FtsWitness _ answer signature (ready_destination start)
    (firstParentReady_FtsWitness start signature witness)

theorem parentRound_pointer (start : MachineState)
    (answer : BitVec 256) (pointer : Word)
    (pointerValue : start.getMem 0x43028 = pointer) :
    (parentRoundState start answer).getMem 0x43028 = pointer + 20 := by
  unfold parentRoundState
  rw [fullParent_pointer _ answer (ready_destination start),
    firstParentReady_pointer, pointerValue]

theorem parentRound_selector (start : MachineState)
    (answer : BitVec 256) (pointer : Word)
    (leaf : FtsLeaf) (level : Nat)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (admissible : PathPointerAdmissible pointer)
    (selector : start.getMem 0x43070 =
      BitVec.ofNat 64 leaf.val >>> level) :
    (parentRoundState start answer).getMem 0x43070 =
      BitVec.ofNat 64 leaf.val >>> (level + 1) := by
  have positioned := positioned_trace_generic start pointer pc pointerValue
    admissible
  have shiftedSelector :
      (firstPositionedState start).getMem 0x43070 =
        start.getMem 0x43070 >>> 1 := by
    simpa only [firstPositionedState] using positioned.2.2.2.2.1
  unfold parentRoundState
  rw [fullParent_selector _ answer (ready_destination start)]
  change (parentHashReadyState (firstPositionedState start)).getMem
    0x43070 = _
  rw [parentHashReady_mem_frame _ 0x43070 (Or.inr (by decide)),
    shiftedSelector, selector]
  exact selector_next leaf level

theorem parentRound_level (start : MachineState)
    (answer : BitVec 256) (level : Nat)
    (levelValue : start.getMem 0x43048 = BitVec.ofNat 64 level) :
    (parentRoundState start answer).getMem 0x43048 =
      BitVec.ofNat 64 (level + 1) := by
  have shiftedLevel :
      (firstPositionedState start).getMem 0x43048 =
        start.getMem 0x43048 := by
    change (levelPositionState
      (shiftIndexState (advancePointerState (pairState start)))).getMem
      0x43048 = _
    rw [levelPosition_mem_frame _ 0x43048 (by decide),
      shiftIndex_mem_frame _ 0x43048 (by decide) (by decide),
      advancePointer_mem_frame _ 0x43048 (by decide),
      pair_level_frame]
  unfold parentRoundState
  rw [fullParent_level _ answer (ready_destination start)]
  change (parentHashReadyState (firstPositionedState start)).getMem
    0x43048 + 1 = _
  rw [parentHashReady_mem_frame _ 0x43048 (Or.inr (by decide)),
    shiftedLevel, levelValue]
  simp [BitVec.ofNat_add]

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRoundInvariant.parentRound_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentRound_witness

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRoundInvariant.parentRound_selector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentRound_selector

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRoundInvariant.parentRound_level' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentRound_level

end SigGolfCandidate.SphincsVerifierFtsRoundInvariant
