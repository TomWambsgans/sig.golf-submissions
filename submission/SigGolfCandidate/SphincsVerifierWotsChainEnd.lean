import SigGolfCandidate.SphincsVerifierWotsStepIteration

namespace SigGolfCandidate.SphincsVerifierWotsChainEnd
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def endpointPointersState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x44)
  let state := execInstrBr state (.ADDI .x6 .x6 768)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 80)
  let state := execInstrBr state (.LD .x7 .x28 0)
  let state := execInstrBr state (.SLLI .x10 .x7 2)
  let state := execInstrBr state (.SLLI .x11 .x7 4)
  let state := execInstrBr state (.ADD .x10 .x10 .x11)
  execInstrBr state (.ADD .x7 .x6 .x10)

theorem endpointPointers_block (state : MachineState)
    (pc : state.pc = 0x28ec) :
    OrdinarySteps SphincsImages.verify state 9
      (endpointPointersState state) ∧
    (endpointPointersState state).pc = 0x2910 := by
  let s1 := execInstrBr state (.LUI .x6 0x44)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 768)
  let s3 := execInstrBr s2 (.LUI .x28 0x43)
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 80)
  let s5 := execInstrBr s4 (.LD .x7 .x28 0)
  let s6 := execInstrBr s5 (.SLLI .x10 .x7 2)
  let s7 := execInstrBr s6 (.SLLI .x11 .x7 4)
  let s8 := execInstrBr s7 (.ADD .x10 .x10 .x11)
  let s9 := execInstrBr s8 (.ADD .x7 .x6 .x10)
  have p1 : s1.pc = 0x28f0 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x28f4 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x28f8 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x28fc := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x2900 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x2904 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x2908 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x290c := by simp [s8, execInstrBr, p7]
  have trace : OrdinarySteps SphincsImages.verify state 9 s9 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x44)) 8
    · rw [fetch_index SphincsImages.verify state 1595 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 768)) 7
    · rw [fetch_index SphincsImages.verify s1 1596 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x28 0x43)) 6
    · rw [fetch_index SphincsImages.verify s2 1597 (by decide)
        (by simpa using p2)]
      decide
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x28 80)) 5
    · rw [fetch_index SphincsImages.verify s3 1598 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.LD .x7 .x28 0)) 4
    · rw [fetch_index SphincsImages.verify s4 1599 (by decide)
        (by simpa using p4)]
      decide
    · simp [s5, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s4, s3,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    apply OrdinarySteps.step s5 s6 _ (.base (.SLLI .x10 .x7 2)) 3
    · rw [fetch_index SphincsImages.verify s5 1600 (by decide)
        (by simpa using p5)]
      decide
    · rfl
    apply OrdinarySteps.step s6 s7 _ (.base (.SLLI .x11 .x7 4)) 2
    · rw [fetch_index SphincsImages.verify s6 1601 (by decide)
        (by simpa using p6)]
      decide
    · rfl
    apply OrdinarySteps.step s7 s8 _ (.base (.ADD .x10 .x10 .x11)) 1
    · rw [fetch_index SphincsImages.verify s7 1602 (by decide)
        (by simpa using p7)]
      decide
    · rfl
    apply OrdinarySteps.step s8 s9 _ (.base (.ADD .x7 .x6 .x10)) 0
    · rw [fetch_index SphincsImages.verify s8 1603 (by decide)
        (by simpa using p8)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  exact ⟨by simpa only [endpointPointersState] using trace,
    by simpa only [endpointPointersState] using
      (show s9.pc = 0x2910 by simp [s9, execInstrBr, p8])⟩

theorem endpointPointers_regs (state : MachineState)
    (chain : Fin 52)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val) :
    (endpointPointersState state).getReg .x7 =
      BitVec.ofNat 64 (0x44300 + 20 * chain.val) := by
  have hc : state.getMem (274512#64) =
      BitVec.ofNat 64 chain.val := by simpa using counter
  fin_cases chain <;>
    simp [endpointPointersState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      hc]

def endpointSourceState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x45)
  execInstrBr state (.ADDI .x6 .x6 (-1280))

theorem endpointSource_block (state : MachineState)
    (pc : state.pc = 0x2910) :
    OrdinarySteps SphincsImages.verify state 2
      (endpointSourceState state) ∧
    (endpointSourceState state).pc = 0x2918 ∧
    (endpointSourceState state).getReg .x6 = 0x44b00 ∧
    (endpointSourceState state).getReg .x7 = state.getReg .x7 := by
  let s1 := execInstrBr state (.LUI .x6 0x45)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-1280))
  have p1 : s1.pc = 0x2914 := by simp [s1, execInstrBr, pc]
  have trace : OrdinarySteps SphincsImages.verify state 2 s2 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x45)) 1
    · rw [fetch_index SphincsImages.verify state 1604 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-1280))) 0
    · rw [fetch_index SphincsImages.verify s1 1605 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [endpointSourceState] using trace, ?_, ?_, ?_⟩
  · simp [endpointSourceState, execInstrBr, pc]
  · simp [endpointSourceState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  · simp [endpointSourceState, execInstrBr,
      MachineState.getReg_setReg_ne]

theorem endpoint_copy_code : Copy20Code SphincsImages.verify 1606 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

def endpointCopied (state : MachineState) : MachineState :=
  copyRootState (endpointSourceState (endpointPointersState state))

theorem endpointCopied_block (state : MachineState) (chain : Fin 52)
    (pc : state.pc = 0x28ec)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val) :
    OrdinarySteps SphincsImages.verify state 21 (endpointCopied state) ∧
    (endpointCopied state).pc = 0x2940 := by
  obtain ⟨pointers, pointerPc⟩ := endpointPointers_block state pc
  obtain ⟨sourceSetup, copyPc, source, destFrame⟩ :=
    endpointSource_block (endpointPointersState state) pointerPc
  have destination :
      (endpointSourceState (endpointPointersState state)).getReg .x7 =
        BitVec.ofNat 64 (0x44300 + 20 * chain.val) :=
    destFrame.trans (endpointPointers_regs state chain counter)
  have copy := copy20_block_general SphincsImages.verify 1606
    endpoint_copy_code
    (endpointSourceState (endpointPointersState state))
    0x44b00 (0x44300 + 20 * chain.val)
    (by simpa using copyPc) source destination
    (by decide) (by decide)
    (by have := chain.isLt; omega)
    (by have := chain.isLt; simp [MEMORY_BYTES]; omega)
    (by decide)
  refine ⟨by simpa only [endpointCopied] using
    (pointers.append sourceSetup).append copy, ?_⟩
  exact copy20_final_pc
    (endpointSourceState (endpointPointersState state)) 1606
    (by simpa using copyPc)

theorem endpointCopied_controlFrame (state : MachineState)
    (chain : Fin 52)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val) :
    (endpointCopied state).getMem 0x43050 = state.getMem 0x43050 ∧
    (endpointCopied state).getMem 0x43028 = state.getMem 0x43028 := by
  let pointers := endpointSourceState (endpointPointersState state)
  have destination : pointers.getReg .x7 =
      BitVec.ofNat 64 (0x44300 + 20 * chain.val) := by
    simpa [pointers, endpointSourceState, execInstrBr,
      MachineState.getReg_setReg_ne] using
      endpointPointers_regs state chain counter
  have frame (address : Word)
      (either : address = 0x43050 ∨ address = 0x43028) :
      (copyRootState pointers).getMem address =
        pointers.getMem address := by
    apply copyRoot_mem_frame
    intro offset
    rw [destination]
    rcases either with rfl | rfl <;>
      fin_cases chain <;> fin_cases offset <;> decide
  have pointerFrame (address : Word) :
      pointers.getMem address = state.getMem address := by
    simp [pointers, endpointSourceState, endpointPointersState,
      execInstrBr]
  exact ⟨(frame 0x43050 (Or.inl rfl)).trans (pointerFrame _),
    (frame 0x43028 (Or.inr rfl)).trans (pointerFrame _)⟩

def pointerAdvanceState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.ADDI .x6 .x6 20)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  execInstrBr state (.SD .x28 .x6 0)

theorem pointerAdvance_block (state : MachineState)
    (pc : state.pc = 0x2940) :
    OrdinarySteps SphincsImages.verify state 7
      (pointerAdvanceState state) ∧
    (pointerAdvanceState state).pc = 0x295c := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 40)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 20)
  let s5 := execInstrBr s4 (.LUI .x28 0x43)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 40)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x2944 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x2948 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x294c := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x2950 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x2954 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x2958 := by simp [s6, execInstrBr, p5]
  have trace : OrdinarySteps SphincsImages.verify state 7 s7 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 6
    · rw [fetch_index SphincsImages.verify state 1616 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 40)) 5
    · rw [fetch_index SphincsImages.verify s1 1617 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 4
    · rw [fetch_index SphincsImages.verify s2 1618 (by decide)
        (by simpa using p2)]
      decide
    · simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s2, s1,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 20)) 3
    · rw [fetch_index SphincsImages.verify s3 1619 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x43)) 2
    · rw [fetch_index SphincsImages.verify s4 1620 (by decide)
        (by simpa using p4)]
      decide
    · rfl
    apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 40)) 1
    · rw [fetch_index SphincsImages.verify s5 1621 (by decide)
        (by simpa using p5)]
      decide
    · rfl
    apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 0
    · rw [fetch_index SphincsImages.verify s6 1622 (by decide)
        (by simpa using p6)]
      decide
    · simp [s7, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s6, s5,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    exact OrdinarySteps.refl _
  exact ⟨by simpa only [pointerAdvanceState] using trace,
    by simpa only [pointerAdvanceState] using
      (show s7.pc = 0x295c by simp [s7, execInstrBr, p6])⟩

theorem pointerAdvance_cell (state : MachineState) :
    (pointerAdvanceState state).getMem 0x43028 =
      state.getMem 0x43028 + 20 := by
  simp [pointerAdvanceState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem pointerAdvance_chainFrame (state : MachineState) :
    (pointerAdvanceState state).getMem 0x43050 =
      state.getMem 0x43050 := by
  simp [pointerAdvanceState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]


def chainAdvanceState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 80)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.ADDI .x6 .x6 1)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 80)
  execInstrBr state (.SD .x28 .x6 0)

theorem chainAdvance_block (state : MachineState)
    (pc : state.pc = 0x295c) :
    OrdinarySteps SphincsImages.verify state 7
      (chainAdvanceState state) ∧
    (chainAdvanceState state).pc = 0x2978 := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 80)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1)
  let s5 := execInstrBr s4 (.LUI .x28 0x43)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 80)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x2960 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x2964 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x2968 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x296c := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x2970 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x2974 := by simp [s6, execInstrBr, p5]
  have trace : OrdinarySteps SphincsImages.verify state 7 s7 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 6
    · rw [fetch_index SphincsImages.verify state 1623 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 80)) 5
    · rw [fetch_index SphincsImages.verify s1 1624 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 4
    · rw [fetch_index SphincsImages.verify s2 1625 (by decide)
        (by simpa using p2)]
      decide
    · simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s2, s1,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1)) 3
    · rw [fetch_index SphincsImages.verify s3 1626 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x43)) 2
    · rw [fetch_index SphincsImages.verify s4 1627 (by decide)
        (by simpa using p4)]
      decide
    · rfl
    apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 80)) 1
    · rw [fetch_index SphincsImages.verify s5 1628 (by decide)
        (by simpa using p5)]
      decide
    · rfl
    apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 0
    · rw [fetch_index SphincsImages.verify s6 1629 (by decide)
        (by simpa using p6)]
      decide
    · simp [s7, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s6, s5,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    exact OrdinarySteps.refl _
  exact ⟨by simpa only [chainAdvanceState] using trace,
    by simpa only [chainAdvanceState] using
      (show s7.pc = 0x2978 by simp [s7, execInstrBr, p6])⟩

theorem chainAdvance_cell (state : MachineState) :
    (chainAdvanceState state).getMem 0x43050 =
      state.getMem 0x43050 + 1 := by
  simp [chainAdvanceState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem chainAdvance_pointerFrame (state : MachineState) :
    (chainAdvanceState state).getMem 0x43028 =
      state.getMem 0x43028 := by
  simp [chainAdvanceState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def chainBranchState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 80)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.ADDI .x7 .x0 52)
  execInstrBr state (.BNE .x6 .x7 (-632))

theorem chainBranch_block (state : MachineState) (next : Fin 53)
    (pc : state.pc = 0x2978)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 next.val) :
    OrdinarySteps SphincsImages.verify state 5
      (chainBranchState state) ∧
    (chainBranchState state).pc =
      (if next.val = 52 then 0x298c else 0x2710) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 80)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 52)
  let s5 := execInstrBr s4 (.BNE .x6 .x7 (-632))
  have p1 : s1.pc = 0x297c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x2980 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x2984 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x2988 := by simp [s4, execInstrBr, p3]
  have trace : OrdinarySteps SphincsImages.verify state 5 s5 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 4
    · rw [fetch_index SphincsImages.verify state 1630 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 80)) 3
    · rw [fetch_index SphincsImages.verify s1 1631 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 2
    · rw [fetch_index SphincsImages.verify s2 1632 (by decide)
        (by simpa using p2)]
      decide
    · simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s2, s1,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x0 52)) 1
    · rw [fetch_index SphincsImages.verify s3 1633 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.BNE .x6 .x7 (-632))) 0
    · rw [fetch_index SphincsImages.verify s4 1634 (by decide)
        (by simpa using p4)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [chainBranchState] using trace, ?_⟩
  have loaded : s4.getReg .x6 = BitVec.ofNat 64 next.val := by
    simpa [s4, s3, s2, s1, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
      using counter
  have limit : s4.getReg .x7 = 52 := by
    simp [s4, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  change s5.pc = _
  fin_cases next <;>
    simp [s5, execInstrBr, p4, loaded, limit, signExtend13]

theorem chainBranch_controlFrame (state : MachineState) :
    (chainBranchState state).getMem 0x43050 = state.getMem 0x43050 ∧
    (chainBranchState state).getMem 0x43028 = state.getMem 0x43028 := by
  simp [chainBranchState, execInstrBr]

def chainEndState (state : MachineState) : MachineState :=
  chainBranchState (chainAdvanceState
    (pointerAdvanceState (endpointCopied state)))

theorem chainEnd_block (state : MachineState) (chain : Fin 52)
    (pc : state.pc = 0x28ec)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val) :
    OrdinarySteps SphincsImages.verify state 40 (chainEndState state) ∧
    (chainEndState state).pc =
      (if chain.val + 1 = 52 then 0x298c else 0x2710) ∧
    (chainEndState state).getMem 0x43050 =
      BitVec.ofNat 64 (chain.val + 1) := by
  obtain ⟨copied, copiedPc⟩ := endpointCopied_block state chain pc counter
  have frame := endpointCopied_controlFrame state chain counter
  obtain ⟨pointerAdvance, pointerPc⟩ :=
    pointerAdvance_block (endpointCopied state) copiedPc
  obtain ⟨chainAdvance, chainPc⟩ :=
    chainAdvance_block (pointerAdvanceState (endpointCopied state)) pointerPc
  let next : Fin 53 := ⟨chain.val + 1, by have := chain.isLt; omega⟩
  have nextCounter :
      (chainAdvanceState (pointerAdvanceState (endpointCopied state))).getMem
        0x43050 = BitVec.ofNat 64 next.val := by
    rw [chainAdvance_cell, pointerAdvance_chainFrame, frame.1,
      counter]
    change BitVec.ofNat 64 chain.val + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (chain.val + 1)
    rw [← BitVec.ofNat_add]
  obtain ⟨branch, branchPc⟩ :=
    chainBranch_block
      (chainAdvanceState (pointerAdvanceState (endpointCopied state)))
      next chainPc nextCounter
  refine ⟨?_, by simpa [chainEndState, next] using branchPc, ?_⟩
  · simpa [chainEndState] using
      ((copied.append pointerAdvance).append chainAdvance).append branch
  · simpa [chainEndState] using
      (chainBranch_controlFrame _).1.trans nextCounter

theorem chainEnd_pointer (state : MachineState) (chain : Fin 52)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val)) :
    (chainEndState state).getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * (chain.val + 1)) := by
  have frame := endpointCopied_controlFrame state chain counter
  rw [chainEndState, (chainBranch_controlFrame _).2,
    chainAdvance_pointerFrame, pointerAdvance_cell, frame.2, pointer]
  change BitVec.ofNat 64 (0x2547c + 20 * chain.val) +
    BitVec.ofNat 64 20 =
    BitVec.ofNat 64 (0x2547c + 20 * (chain.val + 1))
  rw [← BitVec.ofNat_add]
  congr 1

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainEnd.endpointPointers_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms endpointPointers_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainEnd.endpointCopied_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms endpointCopied_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainEnd.chainEnd_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chainEnd_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainEnd.chainEnd_pointer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainEnd_pointer

end SigGolfCandidate.SphincsVerifierWotsChainEnd

namespace SigGolfCandidate.SphincsVerifierWotsChainEndGeneral
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsChainEnd
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem chainEnd_pointer_general (state : MachineState) (chain : Fin 52)
    (sourceBase : Nat)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (sourceBase + 20 * chain.val)) :
    (chainEndState state).getMem 0x43028 =
      BitVec.ofNat 64 (sourceBase + 20 * (chain.val + 1)) := by
  have frame := endpointCopied_controlFrame state chain counter
  rw [chainEndState, (chainBranch_controlFrame _).2,
    chainAdvance_pointerFrame, pointerAdvance_cell, frame.2, pointer]
  change BitVec.ofNat 64 (sourceBase + 20 * chain.val) +
    BitVec.ofNat 64 20 =
    BitVec.ofNat 64 (sourceBase + 20 * (chain.val + 1))
  rw [← BitVec.ofNat_add]
  congr 1


/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainEndGeneral.chainEnd_pointer_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainEnd_pointer_general

end SigGolfCandidate.SphincsVerifierWotsChainEndGeneral
