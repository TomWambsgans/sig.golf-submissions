import SigGolfCandidate.SphincsVerifierFtsWitnessQuery
import SigGolfCandidate.SphincsVerifierFtsGenericReadyTrace

/-! Exact instruction traces before and after one FORS parent HASH. -/

namespace SigGolfCandidate.SphincsVerifierFtsRoundTrace
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierFtsParentResult
open SigGolfCandidate.SphincsVerifierFtsParentLevel
open SigGolfCandidate.SphincsVerifierFtsParentLoop
open SigGolfCandidate.SphincsVerifierFtsRoundInvariant
open SigGolfCandidate.SphincsVerifierFtsGenericReadyTrace
open SigGolfCandidate.SphincsVerifierFtsGenericPairTrace
open SigGolfCandidate.SphincsVerifierFtsParentHash
open SigGolfCandidate.SphincsVerifierFtsResultControls
open SigGolfCandidate.SphincsVerifierFtsGenericLoop
set_option maxRecDepth 16384

theorem parentRound_readyTrace (start : MachineState) (pointer : Word)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (admissible : PathPointerAdmissible pointer) :
    OrdinarySteps SphincsImages.verify start
      ((if (SigGolfCandidate.SphincsVerifierFtsLevelBranch.parityState start).getReg .x6 = 0
        then 34 else 35) + 65) (firstParentReadyState start) ∧
      (firstParentReadyState start).pc = 0x1b18 :=
  parentReady_fullTrace_generic start pointer pc pointerValue admissible

theorem parentRound_tailTrace (start : MachineState)
    (answer : BitVec 256)
    (readyPc : (firstParentReadyState start).pc = 0x1b18) :
    OrdinarySteps SphincsImages.verify
      (writeHash (firstParentReadyState start) answer) 26
      (parentRoundState start answer) := by
  let ready := firstParentReadyState start
  let hashed := writeHash ready answer
  let copied := resultState hashed
  let advanced := advanceLevelState copied
  let checked := levelCheckState advanced
  let branched := levelBranchState checked
  have hashedPc : hashed.pc = 0x1b1c := by
    simp [hashed, writeHash]
    rw [show ready.pc = 0x1b18 from readyPc]
    decide
  have copyTrace := result_block hashed hashedPc
  have copiedPc := result_pc hashed hashedPc
  have advanceTrace := advanceLevel_block copied copiedPc
  have advancedPc := advanceLevel_pc copied copiedPc
  have checkTrace := levelCheck_block advanced advancedPc
  have checkedPc := levelCheck_pc advanced advancedPc
  have branchTrace := levelBranch_block checked checkedPc
  have trace := ((copyTrace.append advanceTrace).append checkTrace).append
    branchTrace
  simpa only [parentRoundState, Nat.reduceAdd] using trace

theorem parentRound_pc_repeat (start : MachineState)
    (answer : BitVec 256) (roundLevel : Nat)
    (readyPc : (firstParentReadyState start).pc = 0x1b18)
    (levelValue : start.getMem 0x43048 = BitVec.ofNat 64 roundLevel)
    (notFinal : roundLevel < 8) :
    (parentRoundState start answer).pc = 0x1914 := by
  let ready := firstParentReadyState start
  let hashed := writeHash ready answer
  let copied := resultState hashed
  have hashedPc : hashed.pc = 0x1b1c := by
    simp [hashed, writeHash]
    rw [show ready.pc = 0x1b18 from readyPc]
    decide
  have copiedPc := result_pc hashed hashedPc
  have copiedLevel : copied.getMem 0x43048 =
      BitVec.ofNat 64 roundLevel := by
    change (resultState (writeHash ready answer)).getMem 0x43048 = _
    rw [hashedResult_mem_frame ready answer 0x43048
      (ready_destination start) (by decide) (by decide) (by decide)
      (by decide) (by intro offset; fin_cases offset <;> decide),
      firstParentReady_level, levelValue]
  have loop := parent_loopBack_generic copied roundLevel copiedPc
    copiedLevel notFinal
  simpa only [parentRoundState] using loop.2.1

theorem parentRound_pc_done (start : MachineState)
    (answer : BitVec 256)
    (readyPc : (firstParentReadyState start).pc = 0x1b18)
    (levelValue : start.getMem 0x43048 = 8) :
    (parentRoundState start answer).pc = 0x1b84 := by
  let ready := firstParentReadyState start
  let hashed := writeHash ready answer
  let copied := resultState hashed
  have hashedPc : hashed.pc = 0x1b1c := by
    simp [hashed, writeHash]
    rw [show ready.pc = 0x1b18 from readyPc]
    decide
  have copiedPc := result_pc hashed hashedPc
  have copiedLevel : copied.getMem 0x43048 = 8 := by
    change (resultState (writeHash ready answer)).getMem 0x43048 = _
    rw [hashedResult_mem_frame ready answer 0x43048
      (ready_destination start) (by decide) (by decide) (by decide)
      (by decide) (by intro offset; fin_cases offset <;> decide),
      firstParentReady_level, levelValue]
  have loop := parent_loopDone copied copiedPc copiedLevel
  simpa only [parentRoundState] using loop.2.1

theorem parentRound_executes (hash : Hash) (start : MachineState)
    (pointer : Word) (steps : Nat) (result : Execution)
    (pc : start.pc = 0x1914)
    (pointerValue : start.getMem 0x43028 = pointer)
    (admissible : PathPointerAdmissible pointer)
    (tail : Executes hash SphincsImages.verify
      (parentRoundState start
        (hash (hashInput (firstParentReadyState start)))) steps result) :
    let pre := if (SigGolfCandidate.SphincsVerifierFtsLevelBranch.parityState start).getReg .x6 = 0
      then 34 else 35
    Executes hash SphincsImages.verify start
      (((steps + 26) + 1) + (pre + 65))
      (((result.charge 26 0 0).charge 16 1 2).charge (pre + 65) 0 0) := by
  let ready := firstParentReadyState start
  let answer := hash (hashInput ready)
  have front := parentRound_readyTrace start pointer pc pointerValue admissible
  have back := parentRound_tailTrace start answer front.2
  have after : Executes hash SphincsImages.verify (writeHash ready answer)
      (steps + 26) (result.charge 26 0 0) :=
    back.then_executes tail
  have regs := hashRegisters_ready
    (parentReadyState (firstPositionedState start))
  have middle : Executes hash SphincsImages.verify ready
      ((steps + 26) + 1) ((result.charge 26 0 0).charge 16 1 2) :=
    hash_step hash ready front.2 regs.1 regs.2.1 regs.2.2.1
      regs.2.2.2 (steps + 26) (result.charge 26 0 0) after
  exact front.1.then_executes middle

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRoundTrace.parentRound_tailTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentRound_tailTrace

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRoundTrace.parentRound_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentRound_executes

end SigGolfCandidate.SphincsVerifierFtsRoundTrace
