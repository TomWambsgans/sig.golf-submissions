import SigGolfCandidate.SphincsVerifierWotsStepNext
import SigGolfCandidate.SphincsVerifierWotsLoop

namespace SigGolfCandidate.SphincsVerifierWotsStepIteration
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierWotsStepBody
open SigGolfCandidate.SphincsVerifierWotsStepCheck
open SigGolfCandidate.SphincsVerifierWotsStepHashReady
open SigGolfCandidate.SphincsVerifierWotsStepHash
open SigGolfCandidate.SphincsVerifierWotsStepNext
open SigGolfCandidate.SphincsVerifierWotsLoop
open SigGolfCandidate.SphincsVerifierCopyMemory
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def stepReady (state : MachineState) : MachineState :=
  stepHashReadyState (stepHashPrefixState state)

def stepAfterHash (hash : Hash) (state : MachineState) : MachineState :=
  writeHash (stepReady state) (hash (hashInput (stepReady state)))

def stepNext (hash : Hash) (state : MachineState) : MachineState :=
  stepReturnState (stepAnswerCopyState (stepAfterHash hash state))

theorem stepValueCopied_stepCell (state : MachineState) :
    (stepValueCopied state).getMem 0x43058 = state.getMem 0x43058 := by
  have destination : (stepValuePointers state).getReg .x7 = 0x40028 := by
    simp [stepValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (stepValuePointers state) 0x43058
    (by intro offset; rw [destination]; fin_cases offset <;> decide)
  have pointerFrame : (stepValuePointers state).getMem 0x43058 =
      state.getMem 0x43058 := by
    simp [stepValuePointers, execInstrBr]
  exact frame.trans pointerFrame

theorem stepHashPrefix_stepCell (state : MachineState) :
    (stepHashPrefixState state).getMem 0x43058 =
      state.getMem 0x43058 := by
  have positioned : (stepPositionState (stepValueCopied state)).getMem
      0x43058 = (stepValueCopied state).getMem 0x43058 := by
    simp [stepPositionState, execInstrBr, signExtend12,
      MachineState.getMem_setMem_ne,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact positioned.trans (stepValueCopied_stepCell state)

theorem stepTag_stepCell (state : MachineState) :
    (stepTagState state).getMem 0x43058 =
      state.getMem 0x43058 := by
  simp [stepTagState, execInstrBr, signExtend12, setWord32_eq,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    show (274520#64) ≠ alignToDword (262144#64) by decide]

theorem stepHeader_stepCell (state : MachineState) :
    (stepHeaderState state).getMem 0x43058 =
      state.getMem 0x43058 := by
  let tagged := stepTagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagDst : tagged.getReg .x7 = 0x40000 := by
    simp [tagged, stepTagState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have positionDst : positioned.getReg .x7 = 0x40000 := by
    rw [SphincsVerifierHeader.position_hash_pointer]; exact tagDst
  have treeDst : treed.getReg .x7 = 0x40000 := by
    rw [SphincsVerifierHeader.tree_hash_pointer]; exact positionDst
  have positionCell : positioned.getMem 0x43058 = tagged.getMem 0x43058 := by
    simp only [positioned, SphincsVerifierHeader.positionState,
      execInstrBr, MachineState.getMem_setPC]
    rw [SphincsVerifierHeader.positionBeforeStore_pointer, tagDst]
    rw [setWord32_eq]
    rw [MachineState.getMem_setMem_ne (by decide)]
    exact SphincsVerifierHeader.positionBeforeStore_memory tagged _
  have treeCell : treed.getMem 0x43058 = positioned.getMem 0x43058 := by
    simp only [treed, SphincsVerifierHeader.treeState,
      execInstrBr, MachineState.getMem_setPC]
    rw [SphincsVerifierHeader.treeBeforeStore_pointer, positionDst]
    rw [MachineState.getMem_setMem_ne (by decide)]
    exact SphincsVerifierHeader.treeBeforeStore_memory positioned _
  have indexCell : (SphincsVerifierHeader.indexState treed).getMem
      0x43058 = treed.getMem 0x43058 := by
    simp only [SphincsVerifierHeader.indexState,
      execInstrBr, MachineState.getMem_setPC]
    rw [SphincsVerifierHeader.indexBeforeStore_pointer, treeDst]
    rw [setWord32_eq]
    rw [MachineState.getMem_setMem_ne (by decide)]
    exact SphincsVerifierHeader.indexBeforeStore_memory treed _
  exact indexCell.trans (treeCell.trans
    (positionCell.trans (stepTag_stepCell state)))

theorem stepParameter_stepCell (state : MachineState) :
    (stepParameterState state).getMem 0x43058 =
      state.getMem 0x43058 := by
  have destination : (stepParameterPointers state).getReg .x7 =
      0x40014 := by
    simp [stepParameterPointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (stepParameterPointers state) 0x43058
    (by intro offset; rw [destination]; fin_cases offset <;> decide)
  have pointerFrame : (stepParameterPointers state).getMem 0x43058 =
      state.getMem 0x43058 := by
    simp [stepParameterPointers, execInstrBr]
  exact frame.trans pointerFrame

theorem stepReady_stepCell (state : MachineState) :
    (stepReady state).getMem 0x43058 = state.getMem 0x43058 := by
  have regFrame : ∀ pre : MachineState,
      (stepHashRegistersState pre).getMem 0x43058 =
        pre.getMem 0x43058 := by
    intro pre
    simp [stepHashRegistersState, execInstrBr]
  exact (regFrame _).trans
    ((stepParameter_stepCell _).trans
      ((stepHeader_stepCell _).trans (stepHashPrefix_stepCell state)))

theorem stepAfterHash_stepCell (hash : Hash) (state : MachineState) :
    (stepAfterHash hash state).getMem 0x43058 =
      state.getMem 0x43058 := by
  have destination : (stepReady state).getReg .x12 = 0x42000 := by
    simp [stepReady, stepHashReadyState, stepHashRegistersState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  have frame := SphincsVerifierFtsLevelInit.writeHash_mem_frame
    (stepReady state) (hash (hashInput (stepReady state)))
    destination 0x43058 (by decide) (by decide) (by decide) (by decide)
  exact frame.trans (stepReady_stepCell state)

theorem stepAnswerCopy_stepCell (state : MachineState) :
    (stepAnswerCopyState state).getMem 0x43058 =
      state.getMem 0x43058 := by
  have destination : (stepAnswerPointersState state).getReg .x7 =
      0x44b00 := by
    simp [stepAnswerPointersState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (stepAnswerPointersState state) 0x43058
    (by intro offset; rw [destination]; fin_cases offset <;> decide)
  have pointerFrame : (stepAnswerPointersState state).getMem 0x43058 =
      state.getMem 0x43058 := by
    simp [stepAnswerPointersState, execInstrBr]
  exact frame.trans pointerFrame

theorem stepNext_stepCell (hash : Hash) (state : MachineState) :
    (stepNext hash state).getMem 0x43058 =
      state.getMem 0x43058 + 1 := by
  rw [stepNext, stepReturn_cell,
    stepAnswerCopy_stepCell, stepAfterHash_stepCell]

theorem stepNext_pc (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x2788) :
    (stepNext hash state).pc = 0x2774 := by
  have pre := stepHashPrefix_block state pc
  have ready := stepHashReady_block (stepHashPrefixState state) pre.2
  have hashPc : (stepAfterHash hash state).pc = 0x2894 := by
    simp [stepAfterHash, stepReady, writeHash, ready.2.1]
  have copy := stepAnswerCopy_block (stepAfterHash hash state) hashPc
  exact (stepReturn_block (stepAnswerCopyState (stepAfterHash hash state))
    copy.2).2

theorem stepCheck_stepCell (state : MachineState) :
    (stepCheckState state).getMem 0x43058 =
      state.getMem 0x43058 := by
  simp [stepCheckState, execInstrBr]

def stepRound (hash : Hash) (state : MachineState) : MachineState :=
  stepNext hash (stepCheckState state)

theorem stepRound_cell (hash : Hash) (state : MachineState) :
    (stepRound hash state).getMem 0x43058 =
      state.getMem 0x43058 + 1 := by
  rw [stepRound, stepNext_stepCell, stepCheck_stepCell]

theorem stepRound_pc (hash : Hash) (state : MachineState)
    (step : Fin 8) (pc : state.pc = 0x2774)
    (cell : state.getMem 0x43058 = BitVec.ofNat 64 step.val)
    (small : step.val < 7) :
    (stepRound hash state).pc = 0x2774 := by
  have checked := stepCheck_block state step pc cell
  have nextPc : (stepCheckState state).pc = 0x2788 := by
    simpa [show step.val ≠ 7 by omega] using checked.2
  exact stepNext_pc hash (stepCheckState state) nextPc

theorem step_iteration (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x2788)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (stepNext hash state) steps result) :
    Executes hash SphincsImages.verify state (steps + 89)
      (result.charge 96 1 1) := by
  obtain ⟨pre, prePc⟩ := stepHashPrefix_block state pc
  obtain ⟨ready, readyPc, source, bits, destination, service⟩ :=
    stepHashReady_block (stepHashPrefixState state) prePc
  have hashPc : (stepAfterHash hash state).pc = 0x2894 := by
    simp [stepAfterHash, stepReady, writeHash, readyPc]
  obtain ⟨copy, copyPc⟩ :=
    stepAnswerCopy_block (stepAfterHash hash state) hashPc
  obtain ⟨advance, _⟩ :=
    stepReturn_block (stepAnswerCopyState (stepAfterHash hash state)) copyPc
  have after : Executes hash SphincsImages.verify
      (stepAfterHash hash state) (steps + 22)
      (result.charge 22 0 0) := by
    simpa [stepNext] using (copy.append advance).then_executes tail
  have hashStep := step_hash_call hash (stepReady state)
    readyPc source bits destination service (steps + 22)
    (result.charge 22 0 0) after
  have before := pre.append ready
  have all := before.then_executes hashStep
  simpa [stepReady, stepAfterHash, Execution.charge, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using all


theorem stepRound_exec (hash : Hash) (state : MachineState)
    (step : Fin 8) (pc : state.pc = 0x2774)
    (cell : state.getMem 0x43058 = BitVec.ofNat 64 step.val)
    (small : step.val < 7)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (stepRound hash state) steps result) :
    Executes hash SphincsImages.verify state (steps + 94)
      (result.charge 101 1 1) := by
  have checked := stepCheck_block state step pc cell
  have nextPc : (stepCheckState state).pc = 0x2788 := by
    simpa [show step.val ≠ 7 by omega] using checked.2
  have body := step_iteration hash (stepCheckState state) nextPc
    steps result (by simpa [stepRound] using tail)
  have all := checked.1.then_executes body
  simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using all

theorem stepLoop_to_seven (hash : Hash) (start : Fin 8)
    (state : MachineState)
    (pc : state.pc = 0x2774)
    (cell : state.getMem 0x43058 = BitVec.ofNat 64 start.val) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc = 0x2774 ∧
      final.getMem 0x43058 = 7 ∧
      steps ≤ 94 * (7 - start.val) ∧
      cycles ≤ 101 * (7 - start.val) ∧
      calls ≤ 7 - start.val ∧
      blocks ≤ 7 - start.val ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  let Inv : Nat → MachineState → Prop := fun i current =>
    current.pc = 0x2774 ∧
    current.getMem 0x43058 = BitVec.ofNat 64 (start.val + i)
  have next (i : Nat) (current : MachineState)
      (bound : i < 7 - start.val) (inv : Inv i current) :
      ∃ (following : MachineState) (steps cycles calls blocks : Nat),
        Inv (i + 1) following ∧
        steps ≤ 94 ∧ cycles ≤ 101 ∧ calls ≤ 1 ∧ blocks ≤ 1 ∧
        ∀ (tailSteps : Nat) (result : Execution),
          Executes hash SphincsImages.verify following tailSteps result →
          Executes hash SphincsImages.verify current (tailSteps + steps)
            (result.charge cycles calls blocks) := by
    let digit : Fin 8 := ⟨start.val + i, by have := start.isLt; omega⟩
    have small : digit.val < 7 := by dsimp [digit]; omega
    have currentCell : current.getMem 0x43058 =
        BitVec.ofNat 64 digit.val := inv.2
    refine ⟨stepRound hash current, 94, 101, 1, 1, ?_, by decide,
      by decide, by decide, by decide, ?_⟩
    · constructor
      · exact stepRound_pc hash current digit inv.1 currentCell small
      · rw [stepRound_cell, currentCell]
        change BitVec.ofNat 64 (start.val + i) +
          BitVec.ofNat 64 1 =
          BitVec.ofNat 64 (start.val + (i + 1))
        rw [← BitVec.ofNat_add]
        congr 1
    · intro tailSteps result tail
      exact stepRound_exec hash current digit inv.1 currentCell small
        tailSteps result tail
  obtain ⟨final, steps, cycles, calls, blocks, finalInv,
      stepBound, cycleBound, callBound, blockBound, run⟩ :=
    bounded_loop hash SphincsImages.verify Inv (7 - start.val)
      94 101 1 1 next 0 (7 - start.val) state
      (by omega) ⟨pc, by simpa [Inv] using cell⟩
  refine ⟨final, steps, cycles, calls, blocks, finalInv.1, ?_,
    stepBound, cycleBound, by simpa using callBound,
    by simpa using blockBound, run⟩
  have sum : start.val + (7 - start.val) = 7 := by
    have := start.isLt
    omega
  simpa [Inv, sum] using finalInv.2

theorem stepLoop_to_chain_end (hash : Hash) (start : Fin 8)
    (state : MachineState)
    (pc : state.pc = 0x2774)
    (cell : state.getMem 0x43058 = BitVec.ofNat 64 start.val) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc = 0x28ec ∧
      steps ≤ 94 * (7 - start.val) + 5 ∧
      cycles ≤ 101 * (7 - start.val) + 5 ∧
      calls ≤ 7 - start.val ∧
      blocks ≤ 7 - start.val ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  obtain ⟨seven, steps, cycles, calls, blocks, sevenPc,
    sevenCell, stepBound, cycleBound, callBound, blockBound, run⟩ :=
    stepLoop_to_seven hash start state pc cell
  have checked := stepCheck_block seven (⟨7, by decide⟩ : Fin 8)
    sevenPc (by simpa using sevenCell)
  refine ⟨stepCheckState seven, steps + 5, cycles + 5,
    calls, blocks, by simpa using checked.2,
    by omega, by omega, callBound, blockBound, ?_⟩
  intro tailSteps result tail
  have after := checked.1.then_executes tail
  have before := run (tailSteps + 5) (result.charge 5 0 0) after
  simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using before

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepIteration.step_iteration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_iteration

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepIteration.stepLoop_to_chain_end' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepLoop_to_chain_end

end SigGolfCandidate.SphincsVerifierWotsStepIteration
