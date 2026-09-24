import SigGolfCandidate.SphincsVerifierFtsLevelBranch

/-! Start the right-oriented first FORS authentication-path level. -/

namespace SigGolfCandidate.SphincsVerifierFtsRightPath
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopy20DataGeneral
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
set_option maxRecDepth 16384

def rightPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 40)

theorem rightPointers_pc (state : MachineState)
    (pc : state.pc = 0x1928) :
    (rightPointers state).pc = 0x193c := by
  simp [rightPointers, execInstrBr, pc]

theorem rightPointers_regs (state : MachineState) :
    (rightPointers state).getReg .x6 = state.getMem 0x43028 ∧
      (rightPointers state).getReg .x7 = 0x40028 := by
  constructor <;>
    simp [rightPointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem rightPointers_mem (state : MachineState) (address : Word) :
    (rightPointers state).getMem address = state.getMem address := by
  simp [rightPointers, execInstrBr]

theorem rightPointers_word (state : MachineState) (address : Word) :
    (rightPointers state).getWord32 address =
      state.getWord32 address := by
  simp [rightPointers, execInstrBr]

theorem rightPointers_block (state : MachineState)
    (pc : state.pc = 0x1928) :
    OrdinarySteps SphincsImages.verify state 5 (rightPointers state) := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 40)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x7 0x40)
  let s5 := execInstrBr s4 (.ADDI .x7 .x7 40)
  have p1 : s1.pc = 0x192c := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1930 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1934 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x1938 := by simp [s4, execInstrBr, p3]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 4
  · rw [fetch_index SphincsImages.verify state 586 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 40)) 3
  · rw [fetch_index SphincsImages.verify s1 587 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 2
  · rw [fetch_index SphincsImages.verify s2 588 (by decide)
      (by simpa using p2)]
    decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x7 0x40)) 1
  · rw [fetch_index SphincsImages.verify s3 589 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x7 .x7 40)) 0
  · rw [fetch_index SphincsImages.verify s4 590 (by decide)
      (by simpa using p4)]
    decide
  · rfl
  exact OrdinarySteps.refl _

set_option maxHeartbeats 0 in
theorem rightCopy_code : Copy20Code SphincsImages.verify 591 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

theorem rightCopy_block (state : MachineState)
    (pc : state.pc = 0x193c)
    (source : state.getReg .x6 = 0x22cf0)
    (destination : state.getReg .x7 = 0x40028) :
    OrdinarySteps SphincsImages.verify state 10
      (copyRootState state) := by
  apply copy20_block_general SphincsImages.verify 591 rightCopy_code state
    0x22cf0 0x40028 (by simpa using pc) source destination
  all_goals decide

theorem rightCopy_pc (state : MachineState) (pc : state.pc = 0x193c) :
    (copyRootState state).pc = 0x1964 := by
  simpa using copy20_final_pc state 591 (by simpa using pc)

theorem rightCopy_source_frame (written read : Fin 5)
    (state : MachineState) (destination : state.getReg .x7 = 0x40028) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x22cf0 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cf0 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

private def RightCopyInvariant (original : MachineState) (count : Nat)
    (state : MachineState) : Prop :=
  state.getReg .x6 = 0x22cf0 ∧
  state.getReg .x7 = 0x40028 ∧
  (∀ index : Fin 5,
    state.getWord32 (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22cf0 + 4 * index.val))) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)))

private theorem rightCopyStep (original state : MachineState) (slot : Fin 5)
    (invariant : RightCopyInvariant original slot.val state) :
    RightCopyInvariant original (slot.val + 1)
      (copyWordState slot state) := by
  rcases invariant with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ := copyWord_pointers slot state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination, ?_, ?_⟩
  · intro index
    rw [rightCopy_source_frame slot index state destination]
    exact sourceWords index
  · intro index before
    by_cases same : slot = index
    · subst index
      rw [copyWord_data_general slot state 0x22cf0 0x40028 source destination]
      exact sourceWords slot
    · rw [copyWord_other_fts slot index same state destination]
      have smaller : index.val < slot.val := by
        have unequal : slot.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact copiedWords index smaller

theorem rightCopy_data (original : MachineState)
    (source : original.getReg .x6 = 0x22cf0)
    (destination : original.getReg .x7 = 0x40028)
    (index : Fin 5) :
    (copyRootState original).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      original.getWord32
        (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)) := by
  have initial : RightCopyInvariant original 0 original := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro index impossible
    omega
  have after0 := rightCopyStep original original 0 initial
  have after1 := rightCopyStep original (copyWordState 0 original) 1 after0
  have after2 := rightCopyStep original (copyWordState 1
    (copyWordState 0 original)) 2 after1
  have after3 := rightCopyStep original (copyWordState 2
    (copyWordState 1 (copyWordState 0 original))) 3 after2
  have after4 := rightCopyStep original (copyWordState 3
    (copyWordState 2 (copyWordState 1 (copyWordState 0 original)))) 4 after3
  exact after4.2.2.2 index (by have := index.isLt; omega)

theorem rightCopy_current_frame (state : MachineState)
    (destination : state.getReg .x7 = 0x40028) (index : Fin 5) :
    (copyRootState state).getWord32
      (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) =
      state.getWord32
        (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  simp only [MachineState.getWord32]
  rw [copyRoot_mem_frame]
  intro offset
  rw [destination]
  fin_cases index <;> fin_cases offset <;> decide

theorem rightPath_from_parity (start : MachineState)
    (pc : (parityState start).pc = 0x1924)
    (odd : (parityState start).getReg .x6 ≠ 0)
    (pointer : start.getMem 0x43028 = 0x22cf0) :
    let parity := parityState start
    let branched := branchState parity
    let pointers := rightPointers branched
    let copied := copyRootState pointers
    OrdinarySteps SphincsImages.verify parity 16 copied ∧
      copied.pc = 0x1964 := by
  let parity := parityState start
  let branched := branchState parity
  let pointers := rightPointers branched
  have branchTrace := branch_block parity pc
  have branchPc := branch_pc_odd parity pc odd
  have pointerAtBranch : branched.getMem 0x43028 = 0x22cf0 := by
    rw [branch_mem, parity_mem]
    exact pointer
  have source : pointers.getReg .x6 = 0x22cf0 := by
    rw [(rightPointers_regs branched).1]
    exact pointerAtBranch
  have destination : pointers.getReg .x7 = 0x40028 :=
    (rightPointers_regs branched).2
  have pointerTrace := rightPointers_block branched branchPc
  have pointersPc := rightPointers_pc branched branchPc
  have copyTrace := rightCopy_block pointers pointersPc source destination
  exact ⟨(branchTrace.append pointerTrace).append copyTrace,
    rightCopy_pc pointers pointersPc⟩

def rightCurrentPointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x45)
  let state := execInstrBr state (.ADDI .x6 .x6 (-1536))
  let state := execInstrBr state (.LUI .x7 0x40)
  execInstrBr state (.ADDI .x7 .x7 60)

theorem rightCurrentPointers_regs (state : MachineState) :
    (rightCurrentPointers state).getReg .x6 = 0x44a00 ∧
      (rightCurrentPointers state).getReg .x7 = 0x4003c := by
  constructor <;>
    simp [rightCurrentPointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem rightCurrentPointers_pc (state : MachineState)
    (pc : state.pc = 0x1964) :
    (rightCurrentPointers state).pc = 0x1974 := by
  simp [rightCurrentPointers, execInstrBr, pc]

theorem rightCurrentPointers_word (state : MachineState)
    (address : Word) :
    (rightCurrentPointers state).getWord32 address =
      state.getWord32 address := by
  simp [rightCurrentPointers, execInstrBr]

theorem rightCurrentPointers_block (state : MachineState)
    (pc : state.pc = 0x1964) :
    OrdinarySteps SphincsImages.verify state 4
      (rightCurrentPointers state) := by
  let s1 := execInstrBr state (.LUI .x6 0x45)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 (-1536))
  let s3 := execInstrBr s2 (.LUI .x7 0x40)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 60)
  have p1 : s1.pc = 0x1968 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x196c := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1970 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x45)) 3
  · rw [fetch_index SphincsImages.verify state 601 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 (-1536))) 2
  · rw [fetch_index SphincsImages.verify s1 602 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x40)) 1
  · rw [fetch_index SphincsImages.verify s2 603 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 60)) 0
  · rw [fetch_index SphincsImages.verify s3 604 (by decide)
      (by simpa using p3)]
    decide
  · rfl
  exact OrdinarySteps.refl _

set_option maxHeartbeats 0 in
theorem rightCurrentCopy_code : Copy20Code SphincsImages.verify 605 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

theorem rightCurrentCopy_block (state : MachineState)
    (pc : state.pc = 0x1974)
    (source : state.getReg .x6 = 0x44a00)
    (destination : state.getReg .x7 = 0x4003c) :
    OrdinarySteps SphincsImages.verify state 10
      (copyRootState state) := by
  apply copy20_block_general SphincsImages.verify 605
    rightCurrentCopy_code state 0x44a00 0x4003c
    (by simpa using pc) source destination
  all_goals decide

theorem rightCurrentCopy_pc (state : MachineState)
    (pc : state.pc = 0x1974) :
    (copyRootState state).pc = 0x199c := by
  simpa using copy20_final_pc state 605 (by simpa using pc)

theorem rightCurrent_other (written read : Fin 5)
    (different : written ≠ read) (state : MachineState)
    (destination : state.getReg .x7 = 0x4003c) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * read.val)) =
      state.getWord32
        (BitVec.ofNat 64 (0x4003c + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

theorem rightCurrent_source_frame (written read : Fin 5)
    (state : MachineState) (destination : state.getReg .x7 = 0x4003c) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x44a00 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

theorem rightCurrent_sibling_frame (written read : Fin 5)
    (state : MachineState) (destination : state.getReg .x7 = 0x4003c) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

theorem rightCurrentCopy_preserve_sibling (state : MachineState)
    (destination : state.getReg .x7 = 0x4003c) (index : Fin 5) :
    (copyRootState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32
        (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  let s1 := copyWordState 0 state
  let s2 := copyWordState 1 s1
  let s3 := copyWordState 2 s2
  let s4 := copyWordState 3 s3
  have d1 : s1.getReg .x7 = 0x4003c :=
    (copyWord_pointers 0 state).2.trans destination
  have d2 : s2.getReg .x7 = 0x4003c :=
    (copyWord_pointers 1 s1).2.trans d1
  have d3 : s3.getReg .x7 = 0x4003c :=
    (copyWord_pointers 2 s2).2.trans d2
  have d4 : s4.getReg .x7 = 0x4003c :=
    (copyWord_pointers 3 s3).2.trans d3
  change (copyWordState 4 s4).getWord32
    (BitVec.ofNat 64 (0x40028 + 4 * index.val)) = _
  rw [rightCurrent_sibling_frame 4 index s4 d4,
    rightCurrent_sibling_frame 3 index s3 d3,
    rightCurrent_sibling_frame 2 index s2 d2,
    rightCurrent_sibling_frame 1 index s1 d1,
    rightCurrent_sibling_frame 0 index state destination]

private def RightCurrentInvariant (original : MachineState) (count : Nat)
    (state : MachineState) : Prop :=
  state.getReg .x6 = 0x44a00 ∧
  state.getReg .x7 = 0x4003c ∧
  (∀ index : Fin 5,
    state.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val))) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)))

private theorem rightCurrentStep (original state : MachineState)
    (slot : Fin 5)
    (invariant : RightCurrentInvariant original slot.val state) :
    RightCurrentInvariant original (slot.val + 1)
      (copyWordState slot state) := by
  rcases invariant with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ := copyWord_pointers slot state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination, ?_, ?_⟩
  · intro index
    rw [rightCurrent_source_frame slot index state destination]
    exact sourceWords index
  · intro index before
    by_cases same : slot = index
    · subst index
      rw [copyWord_data_general slot state 0x44a00 0x4003c source destination]
      exact sourceWords slot
    · rw [rightCurrent_other slot index same state destination]
      have smaller : index.val < slot.val := by
        have unequal : slot.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact copiedWords index smaller

theorem rightCurrentCopy_data (original : MachineState)
    (source : original.getReg .x6 = 0x44a00)
    (destination : original.getReg .x7 = 0x4003c)
    (index : Fin 5) :
    (copyRootState original).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
      original.getWord32
        (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  have initial : RightCurrentInvariant original 0 original := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro index impossible
    omega
  have after0 := rightCurrentStep original original 0 initial
  have after1 := rightCurrentStep original (copyWordState 0 original) 1 after0
  have after2 := rightCurrentStep original (copyWordState 1
    (copyWordState 0 original)) 2 after1
  have after3 := rightCurrentStep original (copyWordState 2
    (copyWordState 1 (copyWordState 0 original))) 3 after2
  have after4 := rightCurrentStep original (copyWordState 3
    (copyWordState 2 (copyWordState 1 (copyWordState 0 original)))) 4 after3
  exact after4.2.2.2 index (by have := index.isLt; omega)

def rightJump (state : MachineState) : MachineState :=
  execInstrBr state (.JAL .x0 120)

theorem rightJump_block (state : MachineState)
    (pc : state.pc = 0x199c) :
    OrdinarySteps SphincsImages.verify state 1 (rightJump state) := by
  apply OrdinarySteps.step state _ _ (.base (.JAL .x0 120)) 0
  · rw [fetch_index SphincsImages.verify state 615 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem rightJump_pc (state : MachineState)
    (pc : state.pc = 0x199c) :
    (rightJump state).pc = 0x1a14 := by
  simp [rightJump, execInstrBr, pc, signExtend21]

theorem rightJump_word (state : MachineState) (address : Word) :
    (rightJump state).getWord32 address = state.getWord32 address := by
  simp [rightJump, execInstrBr]

def rightFinishState (state : MachineState) : MachineState :=
  rightJump (copyRootState (rightCurrentPointers state))

theorem rightFinish_sibling (state : MachineState) (index : Fin 5) :
    (rightFinishState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32
        (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  unfold rightFinishState
  rw [rightJump_word,
    rightCurrentCopy_preserve_sibling _
      (rightCurrentPointers_regs state).2,
    rightCurrentPointers_word]

theorem rightFinish_current (state : MachineState) (index : Fin 5) :
    (rightFinishState state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
      state.getWord32
        (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  let pointers := rightCurrentPointers state
  have source := (rightCurrentPointers_regs state).1
  have destination := (rightCurrentPointers_regs state).2
  unfold rightFinishState
  rw [rightJump_word,
    rightCurrentCopy_data pointers source destination index,
    rightCurrentPointers_word]

theorem rightPair_data (branched : MachineState)
    (pointer : branched.getMem 0x43028 = 0x22cf0)
    (index : Fin 5) :
    let pointers := rightPointers branched
    let first := copyRootState pointers
    let pair := rightFinishState first
    pair.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      branched.getWord32
        (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)) ∧
      pair.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        branched.getWord32
          (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  let pointers := rightPointers branched
  let first := copyRootState pointers
  have source : pointers.getReg .x6 = 0x22cf0 :=
    (rightPointers_regs branched).1.trans pointer
  have destination : pointers.getReg .x7 = 0x40028 :=
    (rightPointers_regs branched).2
  constructor
  · rw [rightFinish_sibling, rightCopy_data pointers source destination,
      rightPointers_word]
  · rw [rightFinish_current, rightCopy_current_frame pointers destination,
      rightPointers_word]

theorem rightPath_pair_data (start : MachineState)
    (pointer : start.getMem 0x43028 = 0x22cf0)
    (index : Fin 5) :
    let parity := parityState start
    let branched := branchState parity
    let pair := rightFinishState (copyRootState (rightPointers branched))
    pair.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      start.getWord32
        (BitVec.ofNat 64 (0x22cf0 + 4 * index.val)) ∧
      pair.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        start.getWord32
          (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  let parity := parityState start
  let branched := branchState parity
  have pointerAtBranch : branched.getMem 0x43028 = 0x22cf0 := by
    rw [branch_mem, parity_mem]
    exact pointer
  have pair := rightPair_data branched pointerAtBranch index
  exact ⟨by rw [pair.1, branch_word, parity_word],
    by rw [pair.2, branch_word, parity_word]⟩

theorem rightFinish_block (state : MachineState)
    (pc : state.pc = 0x1964) :
    OrdinarySteps SphincsImages.verify state 15
      (rightFinishState state) ∧
      (rightFinishState state).pc = 0x1a14 := by
  let pointers := rightCurrentPointers state
  let copied := copyRootState pointers
  have front := rightCurrentPointers_block state pc
  have pointersPc := rightCurrentPointers_pc state pc
  have source := (rightCurrentPointers_regs state).1
  have destination := (rightCurrentPointers_regs state).2
  have copy := rightCurrentCopy_block pointers pointersPc source destination
  have copiedPc := rightCurrentCopy_pc pointers pointersPc
  have jump := rightJump_block copied copiedPc
  exact ⟨(front.append copy).append jump,
    rightJump_pc copied copiedPc⟩

theorem rightPath_to_pair (start : MachineState)
    (pc : (parityState start).pc = 0x1924)
    (odd : (parityState start).getReg .x6 ≠ 0)
    (pointer : start.getMem 0x43028 = 0x22cf0) :
    let parity := parityState start
    let branched := branchState parity
    let first := copyRootState (rightPointers branched)
    let pair := rightFinishState first
    OrdinarySteps SphincsImages.verify parity 31 pair ∧
      pair.pc = 0x1a14 := by
  let parity := parityState start
  let branched := branchState parity
  let first := copyRootState (rightPointers branched)
  have front := rightPath_from_parity start pc odd pointer
  have back := rightFinish_block first front.2
  exact ⟨front.1.append back.1, back.2⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRightPath.rightCopy_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rightCopy_block

end SigGolfCandidate.SphincsVerifierFtsRightPath
