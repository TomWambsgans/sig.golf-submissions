import SigGolfCandidate.SphincsVerifierWotsStepBody
import SigGolfCandidate.SphincsVerifierHeader
import SigGolfCandidate.SphincsVerifierFtsForestHashReady

namespace SigGolfCandidate.SphincsVerifierWotsStepHashReady
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def stepTagState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.ADDI .x6 .x0 257)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 0)
  let state := execInstrBr state (.LD .x7 .x28 0)
  let state := execInstrBr state (.SLLI .x7 .x7 16)
  let state := execInstrBr state (.ADD .x6 .x6 .x7)
  let state := execInstrBr state (.LUI .x7 0x40)
  let state := execInstrBr state (.ADDI .x7 .x7 0)
  execInstrBr state (.SW .x7 .x6 0)

theorem stepTag_block (state : MachineState)
    (pc : state.pc = 0x27ec) :
    OrdinarySteps SphincsImages.verify state 9 (stepTagState state) ∧
    (stepTagState state).pc = 0x2810 ∧
    (stepTagState state).getReg .x7 = 0x40000 := by
  let s1 := execInstrBr state (.ADDI .x6 .x0 257)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.LD .x7 .x28 0)
  let s5 := execInstrBr s4 (.SLLI .x7 .x7 16)
  let s6 := execInstrBr s5 (.ADD .x6 .x6 .x7)
  let s7 := execInstrBr s6 (.LUI .x7 0x40)
  let s8 := execInstrBr s7 (.ADDI .x7 .x7 0)
  let s9 := execInstrBr s8 (.SW .x7 .x6 0)
  have p1 : s1.pc = 0x27f0 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x27f4 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x27f8 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x27fc := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x2800 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x2804 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x2808 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x280c := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x2810 := by simp [s9, execInstrBr, p8]
  have trace : OrdinarySteps SphincsImages.verify state 9 s9 := by
    apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 257)) 8
    · rw [fetch_index SphincsImages.verify state 1531 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x43)) 7
    · rw [fetch_index SphincsImages.verify s1 1532 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 6
    · rw [fetch_index SphincsImages.verify s2 1533 (by decide)
        (by simpa using p2)]
      decide
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.LD .x7 .x28 0)) 5
    · rw [fetch_index SphincsImages.verify s3 1534 (by decide)
        (by simpa using p3)]
      decide
    · simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s3, s2,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x7 .x7 16)) 4
    · rw [fetch_index SphincsImages.verify s4 1535 (by decide)
        (by simpa using p4)]
      decide
    · rfl
    apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x6 .x6 .x7)) 3
    · rw [fetch_index SphincsImages.verify s5 1536 (by decide)
        (by simpa using p5)]
      decide
    · rfl
    apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x7 0x40)) 2
    · rw [fetch_index SphincsImages.verify s6 1537 (by decide)
        (by simpa using p6)]
      decide
    · rfl
    apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x7 .x7 0)) 1
    · rw [fetch_index SphincsImages.verify s7 1538 (by decide)
        (by simpa using p7)]
      decide
    · rfl
    apply OrdinarySteps.step s8 s9 _ (.base (.SW .x7 .x6 0)) 0
    · rw [fetch_index SphincsImages.verify s8 1539 (by decide)
        (by simpa using p8)]
      decide
    · simp [s9, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s8, s7,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [stepTagState] using trace,
    by simpa only [stepTagState] using p9, ?_⟩
  simp [stepTagState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq]

theorem stepPositionField_block (state : MachineState)
    (pc : state.pc = 0x2810)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.positionState state) ∧
    (SphincsVerifierHeader.positionState state).pc = 0x2820 := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 16)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SW .x7 .x6 4)
  have p1 : s1.pc = 0x2814 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x2818 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x281c := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x2820 := by simp [s4, execInstrBr, p3]
  have trace : OrdinarySteps SphincsImages.verify state 4 s4 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
    · rw [fetch_index SphincsImages.verify state 1540 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 16)) 2
    · rw [fetch_index SphincsImages.verify s1 1541 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
    · rw [fetch_index SphincsImages.verify s2 1542 (by decide)
        (by simpa using p2)]
      decide
    · have pointer : s2.getReg .x28 = 0x43010 := by
        simp [s2, s1, execInstrBr, signExtend12,
          MachineState.getReg_setReg_eq]
      simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, signExtend12, pointer, MEMORY_BYTES]
    apply OrdinarySteps.step s3 s4 _ (.base (.SW .x7 .x6 4)) 0
    · rw [fetch_index SphincsImages.verify s3 1543 (by decide)
        (by simpa using p3)]
      decide
    · have pointer : s3.getReg .x7 = 0x40000 := by
        simp [s3, s2, s1, execInstrBr, destination,
          MachineState.getReg_setReg_eq,
          MachineState.getReg_setReg_ne]
      simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, signExtend12, pointer, MEMORY_BYTES]
    exact OrdinarySteps.refl _
  exact ⟨by simpa only [SphincsVerifierHeader.positionState,
        SphincsVerifierHeader.positionBeforeStore] using trace,
    by simpa only [SphincsVerifierHeader.positionState,
        SphincsVerifierHeader.positionBeforeStore] using p4⟩

theorem stepTreeField_block (state : MachineState)
    (pc : state.pc = 0x2820)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.treeState state) ∧
    (SphincsVerifierHeader.treeState state).pc = 0x2830 := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SD .x7 .x6 8)
  have p1 : s1.pc = 0x2824 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x2828 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x282c := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x2830 := by simp [s4, execInstrBr, p3]
  have trace : OrdinarySteps SphincsImages.verify state 4 s4 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
    · rw [fetch_index SphincsImages.verify state 1544 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 2
    · rw [fetch_index SphincsImages.verify s1 1545 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
    · rw [fetch_index SphincsImages.verify s2 1546 (by decide)
        (by simpa using p2)]
      decide
    · have pointer : s2.getReg .x28 = 0x43008 := by
        simp [s2, s1, execInstrBr, signExtend12,
          MachineState.getReg_setReg_eq]
      simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, signExtend12, pointer, MEMORY_BYTES]
    apply OrdinarySteps.step s3 s4 _ (.base (.SD .x7 .x6 8)) 0
    · rw [fetch_index SphincsImages.verify s3 1547 (by decide)
        (by simpa using p3)]
      decide
    · have pointer : s3.getReg .x7 = 0x40000 := by
        simp [s3, s2, s1, execInstrBr, destination,
          MachineState.getReg_setReg_eq,
          MachineState.getReg_setReg_ne]
      simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, signExtend12, pointer, MEMORY_BYTES]
    exact OrdinarySteps.refl _
  exact ⟨by simpa only [SphincsVerifierHeader.treeState,
        SphincsVerifierHeader.treeBeforeStore] using trace,
    by simpa only [SphincsVerifierHeader.treeState,
        SphincsVerifierHeader.treeBeforeStore] using p4⟩

theorem stepIndexField_block (state : MachineState)
    (pc : state.pc = 0x2830)
    (destination : state.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify state 4
      (SphincsVerifierHeader.indexState state) ∧
    (SphincsVerifierHeader.indexState state).pc = 0x2840 := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 24)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SW .x7 .x6 16)
  have p1 : s1.pc = 0x2834 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x2838 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x283c := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x2840 := by simp [s4, execInstrBr, p3]
  have trace : OrdinarySteps SphincsImages.verify state 4 s4 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 3
    · rw [fetch_index SphincsImages.verify state 1548 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 24)) 2
    · rw [fetch_index SphincsImages.verify s1 1549 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 1
    · rw [fetch_index SphincsImages.verify s2 1550 (by decide)
        (by simpa using p2)]
      decide
    · have pointer : s2.getReg .x28 = 0x43018 := by
        simp [s2, s1, execInstrBr, signExtend12,
          MachineState.getReg_setReg_eq]
      simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, signExtend12, pointer, MEMORY_BYTES]
    apply OrdinarySteps.step s3 s4 _ (.base (.SW .x7 .x6 16)) 0
    · rw [fetch_index SphincsImages.verify s3 1551 (by decide)
        (by simpa using p3)]
      decide
    · have pointer : s3.getReg .x7 = 0x40000 := by
        simp [s3, s2, s1, execInstrBr, destination,
          MachineState.getReg_setReg_eq,
          MachineState.getReg_setReg_ne]
      simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, signExtend12, pointer, MEMORY_BYTES]
    exact OrdinarySteps.refl _
  exact ⟨by simpa only [SphincsVerifierHeader.indexState,
        SphincsVerifierHeader.indexBeforeStore] using trace,
    by simpa only [SphincsVerifierHeader.indexState,
        SphincsVerifierHeader.indexBeforeStore] using p4⟩

def stepHeaderState (state : MachineState) : MachineState :=
  SphincsVerifierHeader.indexState
    (SphincsVerifierHeader.treeState
      (SphincsVerifierHeader.positionState (stepTagState state)))

private theorem positionReg (state : MachineState) :
    (SphincsVerifierHeader.positionState state).getReg .x7 =
      state.getReg .x7 := by
  simp [SphincsVerifierHeader.positionState,
    SphincsVerifierHeader.positionBeforeStore, execInstrBr,
    MachineState.getReg_setReg_ne]

private theorem treeReg (state : MachineState) :
    (SphincsVerifierHeader.treeState state).getReg .x7 =
      state.getReg .x7 := by
  simp [SphincsVerifierHeader.treeState,
    SphincsVerifierHeader.treeBeforeStore, execInstrBr,
    MachineState.getReg_setReg_ne]

theorem stepHeader_block (state : MachineState)
    (pc : state.pc = 0x27ec) :
    OrdinarySteps SphincsImages.verify state 21
      (stepHeaderState state) ∧
    (stepHeaderState state).pc = 0x2840 := by
  have tag := stepTag_block state pc
  have position := stepPositionField_block (stepTagState state)
    tag.2.1 tag.2.2
  have dest1 : (SphincsVerifierHeader.positionState
      (stepTagState state)).getReg .x7 = 0x40000 :=
    (positionReg (stepTagState state)).trans tag.2.2
  have tree := stepTreeField_block
    (SphincsVerifierHeader.positionState (stepTagState state))
    position.2 dest1
  have dest2 : (SphincsVerifierHeader.treeState
      (SphincsVerifierHeader.positionState
        (stepTagState state))).getReg .x7 = 0x40000 :=
    (treeReg _).trans dest1
  have index := stepIndexField_block
    (SphincsVerifierHeader.treeState
      (SphincsVerifierHeader.positionState (stepTagState state)))
    tree.2 dest2
  refine ⟨?_, index.2⟩
  simpa [stepHeaderState] using
    ((tag.1.append position.1).append tree.1).append index.1

def stepParameterPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x23)
  let state := execInstrBr state (.ADDI .x6 .x6 (-844))
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 20)

theorem stepParameterPointers_block (state : MachineState)
    (pc : state.pc = 0x2840) :
    OrdinarySteps SphincsImages.verify state 4
      (stepParameterPointers state) ∧
    (stepParameterPointers state).pc = 0x2850 ∧
    (stepParameterPointers state).getReg .x6 = 0x22cb4 ∧
    (stepParameterPointers state).getReg .x7 = 0x40014 := by
  let s1 := execInstrBr state (.LUI .x6 0x23)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-844))
  let s3 := execInstrBr s2 (.LUI .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 20)
  have p1 : s1.pc = 0x2844 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x2848 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x284c := by simp [s3, execInstrBr, p2]
  have trace : OrdinarySteps SphincsImages.verify state 4 s4 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x23)) 3
    · rw [fetch_index SphincsImages.verify state 1552 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-844))) 2
    · rw [fetch_index SphincsImages.verify s1 1553 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x40)) 1
    · rw [fetch_index SphincsImages.verify s2 1554 (by decide)
        (by simpa using p2)]
      decide
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 20)) 0
    · rw [fetch_index SphincsImages.verify s3 1555 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [stepParameterPointers] using trace,
    by simp [stepParameterPointers, execInstrBr, pc], ?_, ?_⟩
  · simp [stepParameterPointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  · simp [stepParameterPointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]

theorem step_parameter_copy_code : Copy20Code SphincsImages.verify 1556 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

def stepParameterState (state : MachineState) : MachineState :=
  copyRootState (stepParameterPointers state)

theorem stepParameter_block (state : MachineState)
    (pc : state.pc = 0x2840) :
    OrdinarySteps SphincsImages.verify state 14
      (stepParameterState state) ∧
    (stepParameterState state).pc = 0x2878 := by
  obtain ⟨pre, prePc, source, destination⟩ :=
    stepParameterPointers_block state pc
  have copy := copy20_block_general SphincsImages.verify 1556
    step_parameter_copy_code (stepParameterPointers state)
    0x22cb4 0x40014 (by simpa using prePc)
    source destination (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine ⟨by simpa only [stepParameterState] using pre.append copy, ?_⟩
  exact copy20_final_pc (stepParameterPointers state) 1556
    (by simpa using prePc)

def stepHashRegistersState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x10 0x40)
  let state := execInstrBr state (.ADDI .x10 .x10 0)
  let state := execInstrBr state (.ADDI .x11 .x0 480)
  let state := execInstrBr state (.LUI .x12 0x42)
  let state := execInstrBr state (.ADDI .x12 .x12 0)
  execInstrBr state (.ADDI .x5 .x0 1)

theorem stepHashRegisters_block (state : MachineState)
    (pc : state.pc = 0x2878) :
    OrdinarySteps SphincsImages.verify state 6
      (stepHashRegistersState state) ∧
    (stepHashRegistersState state).pc = 0x2890 ∧
    (stepHashRegistersState state).getReg .x10 = 0x40000 ∧
    (stepHashRegistersState state).getReg .x11 = 480 ∧
    (stepHashRegistersState state).getReg .x12 = 0x42000 ∧
    (stepHashRegistersState state).getReg .x5 = 1 := by
  let s1 := execInstrBr state (.LUI .x10 0x40)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 480)
  let s4 := execInstrBr s3 (.LUI .x12 0x42)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 0)
  let s6 := execInstrBr s5 (.ADDI .x5 .x0 1)
  have p1 : s1.pc = 0x287c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x2880 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x2884 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x2888 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x288c := by simp [s5, execInstrBr, p4]
  have trace : OrdinarySteps SphincsImages.verify state 6 s6 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x10 0x40)) 5
    · rw [fetch_index SphincsImages.verify state 1566 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 4
    · rw [fetch_index SphincsImages.verify s1 1567 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 480)) 3
    · rw [fetch_index SphincsImages.verify s2 1568 (by decide)
        (by simpa using p2)]
      decide
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x42)) 2
    · rw [fetch_index SphincsImages.verify s3 1569 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 0)) 1
    · rw [fetch_index SphincsImages.verify s4 1570 (by decide)
        (by simpa using p4)]
      decide
    · rfl
    apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x5 .x0 1)) 0
    · rw [fetch_index SphincsImages.verify s5 1571 (by decide)
        (by simpa using p5)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [stepHashRegistersState] using trace, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [stepHashRegistersState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def stepHashReadyState (state : MachineState) : MachineState :=
  stepHashRegistersState (stepParameterState (stepHeaderState state))

theorem stepHashReady_block (state : MachineState)
    (pc : state.pc = 0x27ec) :
    OrdinarySteps SphincsImages.verify state 41
      (stepHashReadyState state) ∧
    (stepHashReadyState state).pc = 0x2890 ∧
    (stepHashReadyState state).getReg .x10 = 0x40000 ∧
    (stepHashReadyState state).getReg .x11 = 480 ∧
    (stepHashReadyState state).getReg .x12 = 0x42000 ∧
    (stepHashReadyState state).getReg .x5 = 1 := by
  obtain ⟨header, headerPc⟩ := stepHeader_block state pc
  obtain ⟨parameter, parameterPc⟩ :=
    stepParameter_block (stepHeaderState state) headerPc
  obtain ⟨regs, regsPc, src, bits, dst, service⟩ :=
    stepHashRegisters_block
      (stepParameterState (stepHeaderState state)) parameterPc
  refine ⟨?_, regsPc, src, bits, dst, service⟩
  simpa [stepHashReadyState] using (header.append parameter).append regs

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepHashReady.stepTag_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepTag_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepHashReady.stepPositionField_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepPositionField_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepHashReady.stepTreeField_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepTreeField_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepHashReady.stepIndexField_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepIndexField_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepHashReady.stepHeader_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepHeader_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepHashReady.stepParameter_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepParameter_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepHashReady.stepHashReady_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepHashReady_block

end SigGolfCandidate.SphincsVerifierWotsStepHashReady
