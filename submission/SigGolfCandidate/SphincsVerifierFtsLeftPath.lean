import SigGolfCandidate.SphincsVerifierFtsRightPath

/-! Start the left-oriented first FORS authentication-path level. -/

namespace SigGolfCandidate.SphincsVerifierFtsLeftPath
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopy20DataGeneral
open SigGolfCandidate.SphincsVerifierFtsRightPath
set_option maxRecDepth 16384

def leftCurrentPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x45)
  let state := execInstrBr state (.ADDI .x6 .x6 (-1536))
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 40)

theorem leftCurrentPointers_pc (state : MachineState)
    (pc : state.pc = 0x19a0) :
    (leftCurrentPointers state).pc = 0x19b0 := by
  simp [leftCurrentPointers, execInstrBr, pc]

theorem leftCurrentPointers_regs (state : MachineState) :
    (leftCurrentPointers state).getReg .x6 = 0x44a00 ∧
      (leftCurrentPointers state).getReg .x7 = 0x40028 := by
  constructor <;>
    simp [leftCurrentPointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem leftCurrentPointers_mem (state : MachineState) (address : Word) :
    (leftCurrentPointers state).getMem address = state.getMem address := by
  simp [leftCurrentPointers, execInstrBr]

theorem leftCurrentPointers_word (state : MachineState) (address : Word) :
    (leftCurrentPointers state).getWord32 address =
      state.getWord32 address := by
  simp [leftCurrentPointers, execInstrBr]

theorem leftCurrentPointers_block (state : MachineState)
    (pc : state.pc = 0x19a0) :
    OrdinarySteps SphincsImages.verify state 4
      (leftCurrentPointers state) := by
  let s1 := execInstrBr state (.LUI .x6 0x45)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-1536))
  let s3 := execInstrBr s2 (.LUI .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 40)
  have p1 : s1.pc = 0x19a4 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x19a8 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x19ac := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x45)) 3
  · rw [fetch_index SphincsImages.verify state 616 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-1536))) 2
  · rw [fetch_index SphincsImages.verify s1 617 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x40)) 1
  · rw [fetch_index SphincsImages.verify s2 618 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 40)) 0
  · rw [fetch_index SphincsImages.verify s3 619 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

set_option maxHeartbeats 0 in
theorem leftCurrentCopy_code : Copy20Code SphincsImages.verify 620 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

theorem leftCurrentCopy_block (state : MachineState)
    (pc : state.pc = 0x19b0)
    (source : state.getReg .x6 = 0x44a00)
    (destination : state.getReg .x7 = 0x40028) :
    OrdinarySteps SphincsImages.verify state 10
      (copyRootState state) := by
  apply copy20_block_general SphincsImages.verify 620
    leftCurrentCopy_code state 0x44a00 0x40028
    (by simpa using pc) source destination
  all_goals decide

theorem leftCurrentCopy_pc (state : MachineState)
    (pc : state.pc = 0x19b0) :
    (copyRootState state).pc = 0x19d8 := by
  simpa using copy20_final_pc state 620 (by simpa using pc)

theorem leftCurrentCopy_pointer (state : MachineState)
    (destination : state.getReg .x7 = 0x40028) :
    (copyRootState state).getMem 0x43028 = state.getMem 0x43028 := by
  apply copyRoot_mem_frame
  intro offset
  rw [destination]
  fin_cases offset <;> decide

theorem leftCurrent_source_frame (written read : Fin 5)
    (state : MachineState) (destination : state.getReg .x7 = 0x40028) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x44a00 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

private def LeftCurrentInvariant (original : MachineState) (count : Nat)
    (state : MachineState) : Prop :=
  state.getReg .x6 = 0x44a00 ∧
  state.getReg .x7 = 0x40028 ∧
  (∀ index : Fin 5,
    state.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val))) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)))

private theorem leftCurrentStep (original state : MachineState) (slot : Fin 5)
    (invariant : LeftCurrentInvariant original slot.val state) :
    LeftCurrentInvariant original (slot.val + 1)
      (copyWordState slot state) := by
  rcases invariant with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ := copyWord_pointers slot state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination, ?_, ?_⟩
  · intro index
    rw [leftCurrent_source_frame slot index state destination]
    exact sourceWords index
  · intro index before
    by_cases same : slot = index
    · subst index
      rw [copyWord_data_general slot state 0x44a00 0x40028 source destination]
      exact sourceWords slot
    · rw [copyWord_other_fts slot index same state destination]
      have smaller : index.val < slot.val := by
        have unequal : slot.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact copiedWords index smaller

theorem leftCurrentCopy_data (original : MachineState)
    (source : original.getReg .x6 = 0x44a00)
    (destination : original.getReg .x7 = 0x40028)
    (index : Fin 5) :
    (copyRootState original).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      original.getWord32
        (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  have initial : LeftCurrentInvariant original 0 original := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro index impossible
    omega
  have after0 := leftCurrentStep original original 0 initial
  have after1 := leftCurrentStep original (copyWordState 0 original) 1 after0
  have after2 := leftCurrentStep original (copyWordState 1
    (copyWordState 0 original)) 2 after1
  have after3 := leftCurrentStep original (copyWordState 2
    (copyWordState 1 (copyWordState 0 original))) 3 after2
  have after4 := leftCurrentStep original (copyWordState 3
    (copyWordState 2 (copyWordState 1 (copyWordState 0 original)))) 4 after3
  exact after4.2.2.2 index (by have := index.isLt; omega)

theorem leftCurrentCopy_witness_frame (state : MachineState)
    (destination : state.getReg .x7 = 0x40028) (index : Fin 5) :
    (copyRootState state).getWord32
      (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)) =
      state.getWord32
        (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)) := by
  simp only [MachineState.getWord32]
  rw [copyRoot_mem_frame]
  intro offset
  rw [destination]
  fin_cases index <;> fin_cases offset <;> decide

def leftSiblingPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 60)

theorem leftSiblingPointers_pc (state : MachineState)
    (pc : state.pc = 0x19d8) :
    (leftSiblingPointers state).pc = 0x19ec := by
  simp [leftSiblingPointers, execInstrBr, pc]

theorem leftSiblingPointers_regs (state : MachineState) :
    (leftSiblingPointers state).getReg .x6 = state.getMem 0x43028 ∧
      (leftSiblingPointers state).getReg .x7 = 0x4003c := by
  constructor <;>
    simp [leftSiblingPointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem leftSiblingPointers_word (state : MachineState) (address : Word) :
    (leftSiblingPointers state).getWord32 address =
      state.getWord32 address := by
  simp [leftSiblingPointers, execInstrBr]

theorem leftSiblingPointers_block (state : MachineState)
    (pc : state.pc = 0x19d8) :
    OrdinarySteps SphincsImages.verify state 5
      (leftSiblingPointers state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 40)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x7 0x40)
  let s5 := execInstrBr s4 (.ADDI .x7 .x7 60)
  have p1 : s1.pc = 0x19dc := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x19e0 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x19e4 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x19e8 := by simp [s4, execInstrBr, p3]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 4
  · rw [fetch_index SphincsImages.verify state 630 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 40)) 3
  · rw [fetch_index SphincsImages.verify s1 631 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 2
  · rw [fetch_index SphincsImages.verify s2 632 (by decide)
      (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x7 0x40)) 1
  · rw [fetch_index SphincsImages.verify s3 633 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x7 .x7 60)) 0
  · rw [fetch_index SphincsImages.verify s4 634 (by decide)
      (by simpa using p4)]
    decide
  · rfl
  exact OrdinarySteps.refl _

set_option maxHeartbeats 0 in
theorem leftSiblingCopy_code : Copy20Code SphincsImages.verify 635 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

theorem leftSiblingCopy_block (state : MachineState)
    (pc : state.pc = 0x19ec)
    (source : state.getReg .x6 = 0x22cf0)
    (destination : state.getReg .x7 = 0x4003c) :
    OrdinarySteps SphincsImages.verify state 10
      (copyRootState state) := by
  apply copy20_block_general SphincsImages.verify 635
    leftSiblingCopy_code state 0x22cf0 0x4003c
    (by simpa using pc) source destination
  all_goals decide

theorem leftSiblingCopy_pc (state : MachineState)
    (pc : state.pc = 0x19ec) :
    (copyRootState state).pc = 0x1a14 := by
  simpa using copy20_final_pc state 635 (by simpa using pc)

theorem leftSibling_source_frame (written read : Fin 5)
    (state : MachineState) (destination : state.getReg .x7 = 0x4003c) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x22cf0 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cf0 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

private def LeftSiblingInvariant (original : MachineState) (count : Nat)
    (state : MachineState) : Prop :=
  state.getReg .x6 = 0x22cf0 ∧
  state.getReg .x7 = 0x4003c ∧
  (∀ index : Fin 5,
    state.getWord32 (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22cf0 + 4 * index.val))) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)))

private theorem leftSiblingStep (original state : MachineState) (slot : Fin 5)
    (invariant : LeftSiblingInvariant original slot.val state) :
    LeftSiblingInvariant original (slot.val + 1)
      (copyWordState slot state) := by
  rcases invariant with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ := copyWord_pointers slot state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination, ?_, ?_⟩
  · intro index
    rw [leftSibling_source_frame slot index state destination]
    exact sourceWords index
  · intro index before
    by_cases same : slot = index
    · subst index
      rw [copyWord_data_general slot state 0x22cf0 0x4003c source destination]
      exact sourceWords slot
    · rw [rightCurrent_other slot index same state destination]
      have smaller : index.val < slot.val := by
        have unequal : slot.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact copiedWords index smaller

theorem leftSiblingCopy_data (original : MachineState)
    (source : original.getReg .x6 = 0x22cf0)
    (destination : original.getReg .x7 = 0x4003c)
    (index : Fin 5) :
    (copyRootState original).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
      original.getWord32
        (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)) := by
  have initial : LeftSiblingInvariant original 0 original := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro index impossible
    omega
  have after0 := leftSiblingStep original original 0 initial
  have after1 := leftSiblingStep original (copyWordState 0 original) 1 after0
  have after2 := leftSiblingStep original (copyWordState 1
    (copyWordState 0 original)) 2 after1
  have after3 := leftSiblingStep original (copyWordState 2
    (copyWordState 1 (copyWordState 0 original))) 3 after2
  have after4 := leftSiblingStep original (copyWordState 3
    (copyWordState 2 (copyWordState 1 (copyWordState 0 original)))) 4 after3
  exact after4.2.2.2 index (by have := index.isLt; omega)

def leftPairState (state : MachineState) : MachineState :=
  let currentPointers := leftCurrentPointers state
  let currentCopy := copyRootState currentPointers
  let siblingPointers := leftSiblingPointers currentCopy
  copyRootState siblingPointers

theorem leftPair_data (branched : MachineState)
    (pointer : branched.getMem 0x43028 = 0x22cf0)
    (index : Fin 5) :
    (leftPairState branched).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      branched.getWord32
        (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) ∧
      (leftPairState branched).getWord32
        (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        branched.getWord32
          (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)) := by
  let currentPointers := leftCurrentPointers branched
  let currentCopy := copyRootState currentPointers
  let siblingPointers := leftSiblingPointers currentCopy
  have currentSource := (leftCurrentPointers_regs branched).1
  have currentDestination := (leftCurrentPointers_regs branched).2
  have pointerAtCopy : currentCopy.getMem 0x43028 = 0x22cf0 := by
    rw [leftCurrentCopy_pointer currentPointers currentDestination,
      leftCurrentPointers_mem]
    exact pointer
  have siblingSource : siblingPointers.getReg .x6 = 0x22cf0 :=
    (leftSiblingPointers_regs currentCopy).1.trans pointerAtCopy
  have siblingDestination : siblingPointers.getReg .x7 = 0x4003c :=
    (leftSiblingPointers_regs currentCopy).2
  constructor
  · unfold leftPairState
    rw [rightCurrentCopy_preserve_sibling siblingPointers siblingDestination,
      leftSiblingPointers_word,
      leftCurrentCopy_data currentPointers currentSource currentDestination,
      leftCurrentPointers_word]
  · unfold leftPairState
    rw [leftSiblingCopy_data siblingPointers siblingSource siblingDestination,
      leftSiblingPointers_word,
      leftCurrentCopy_witness_frame currentPointers currentDestination,
      leftCurrentPointers_word]

theorem leftPath_pair_data (start : MachineState)
    (pointer : start.getMem 0x43028 = 0x22cf0)
    (index : Fin 5) :
    let parity := parityState start
    let branched := branchState parity
    let pair := leftPairState branched
    pair.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      start.getWord32
        (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) ∧
      pair.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        start.getWord32
          (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)) := by
  let parity := parityState start
  let branched := branchState parity
  have pointerAtBranch : branched.getMem 0x43028 = 0x22cf0 := by
    rw [branch_mem, parity_mem]
    exact pointer
  have pair := leftPair_data branched pointerAtBranch index
  exact ⟨by rw [pair.1, branch_word, parity_word],
    by rw [pair.2, branch_word, parity_word]⟩

theorem leftPath_from_parity (start : MachineState)
    (pc : (parityState start).pc = 0x1924)
    (even : (parityState start).getReg .x6 = 0)
    (pointer : start.getMem 0x43028 = 0x22cf0) :
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
  have source := (leftCurrentPointers_regs branched).1
  have destination := (leftCurrentPointers_regs branched).2
  have currentTrace := leftCurrentCopy_block currentPointers
    currentPointersPc source destination
  have currentPc := leftCurrentCopy_pc currentPointers currentPointersPc
  have pointerAtBranch : branched.getMem 0x43028 = 0x22cf0 := by
    rw [branch_mem, parity_mem]
    exact pointer
  have pointerAtCopy : currentCopy.getMem 0x43028 = 0x22cf0 := by
    rw [leftCurrentCopy_pointer currentPointers destination,
      leftCurrentPointers_mem]
    exact pointerAtBranch
  have siblingPointersTrace := leftSiblingPointers_block currentCopy currentPc
  have siblingPointersPc := leftSiblingPointers_pc currentCopy currentPc
  have siblingSource : siblingPointers.getReg .x6 = 0x22cf0 :=
    (leftSiblingPointers_regs currentCopy).1.trans pointerAtCopy
  have siblingDestination : siblingPointers.getReg .x7 = 0x4003c :=
    (leftSiblingPointers_regs currentCopy).2
  have siblingTrace := leftSiblingCopy_block siblingPointers
    siblingPointersPc siblingSource siblingDestination
  exact ⟨(((branchTrace.append currentPointersTrace).append currentTrace).append
      siblingPointersTrace).append siblingTrace,
    leftSiblingCopy_pc siblingPointers siblingPointersPc⟩

end SigGolfCandidate.SphincsVerifierFtsLeftPath
