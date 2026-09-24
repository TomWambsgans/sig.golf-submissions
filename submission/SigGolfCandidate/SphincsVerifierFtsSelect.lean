import SigGolfCandidate.SphincsVerifierFtsTreeHeader

/-! Load the current FORS leaf selector and initialize the tree position. -/

namespace SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsEntry
open SigGolfCandidate.SphincsVerifierLastLeaf
open SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierMessageHash
set_option maxRecDepth 16384

def ftsSelectState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.ADDI .x6 .x0 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 16)
  let state := execInstrBr state (.SD .x28 .x6 0)
  let state := execInstrBr state (.LUI .x6 0x45)
  let state := execInstrBr state (.ADDI .x6 .x6 (-2048))
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 64)
  let state := execInstrBr state (.LD .x7 .x28 0)
  let state := execInstrBr state (.ADD .x6 .x6 .x7)
  let state := execInstrBr state (.LBU .x10 .x6 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 32)
  let state := execInstrBr state (.SD .x28 .x10 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 112)
  execInstrBr state (.SD .x28 .x10 0)

theorem ftsSelect_block (state : MachineState) (tree : Fin 24)
    (pc : state.pc = 0x176c)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val) :
    OrdinarySteps SphincsImages.verify state 17 (ftsSelectState state) := by
  change state.getMem (274496#64) = BitVec.ofNat 64 tree.val at counter
  let s1 := execInstrBr state (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 16)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.LUI .x6 0x45)
  let s6 := execInstrBr s5 (.ADDI .x6 .x6 (-2048))
  let s7 := execInstrBr s6 (.LUI .x28 0x43)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 64)
  let s9 := execInstrBr s8 (.LD .x7 .x28 0)
  let s10 := execInstrBr s9 (.ADD .x6 .x6 .x7)
  let s11 := execInstrBr s10 (.LBU .x10 .x6 0)
  let s12 := execInstrBr s11 (.LUI .x28 0x43)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 32)
  let s14 := execInstrBr s13 (.SD .x28 .x10 0)
  let s15 := execInstrBr s14 (.LUI .x28 0x43)
  let s16 := execInstrBr s15 (.ADDI .x28 .x28 112)
  let s17 := execInstrBr s16 (.SD .x28 .x10 0)
  have p1 : s1.pc = 0x1770 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x1774 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1778 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x177c := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x1780 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x1784 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x1788 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x178c := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x1790 := by simp [s9, execInstrBr, p8]
  have p10 : s10.pc = 0x1794 := by simp [s10, execInstrBr, p9]
  have p11 : s11.pc = 0x1798 := by simp [s11, execInstrBr, p10]
  have p12 : s12.pc = 0x179c := by simp [s12, execInstrBr, p11]
  have p13 : s13.pc = 0x17a0 := by simp [s13, execInstrBr, p12]
  have p14 : s14.pc = 0x17a4 := by simp [s14, execInstrBr, p13]
  have p15 : s15.pc = 0x17a8 := by simp [s15, execInstrBr, p14]
  have p16 : s16.pc = 0x17ac := by simp [s16, execInstrBr, p15]
  apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 0)) 16
  · rw [fetch_index SphincsImages.verify state 475 (by decide) (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x43)) 15
  · rw [fetch_index SphincsImages.verify s1 476 (by decide) (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 16)) 14
  · rw [fetch_index SphincsImages.verify s2 477 (by decide) (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 13
  · rw [fetch_index SphincsImages.verify s3 478 (by decide) (by simpa using p3)]
    decide
  ·
    simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, counter]
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x6 0x45)) 12
  · rw [fetch_index SphincsImages.verify s4 479 (by decide) (by simpa using p4)]
    decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x6 .x6 (-2048))) 11
  · rw [fetch_index SphincsImages.verify s5 480 (by decide) (by simpa using p5)]
    decide
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x43)) 10
  · rw [fetch_index SphincsImages.verify s6 481 (by decide) (by simpa using p6)]
    decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 64)) 9
  · rw [fetch_index SphincsImages.verify s7 482 (by decide) (by simpa using p7)]
    decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x7 .x28 0)) 8
  · rw [fetch_index SphincsImages.verify s8 483 (by decide) (by simpa using p8)]
    decide
  ·
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, counter]
  apply OrdinarySteps.step s9 s10 _ (.base (.ADD .x6 .x6 .x7)) 7
  · rw [fetch_index SphincsImages.verify s9 484 (by decide) (by simpa using p9)]
    decide
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LBU .x10 .x6 0)) 6
  · rw [fetch_index SphincsImages.verify s10 485 (by decide) (by simpa using p10)]
    decide
  · fin_cases tree <;>
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, counter]
  apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 0x43)) 5
  · rw [fetch_index SphincsImages.verify s11 486 (by decide) (by simpa using p11)]
    decide
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 32)) 4
  · rw [fetch_index SphincsImages.verify s12 487 (by decide) (by simpa using p12)]
    decide
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.SD .x28 .x10 0)) 3
  · rw [fetch_index SphincsImages.verify s13 488 (by decide) (by simpa using p13)]
    decide
  ·
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, counter]
  apply OrdinarySteps.step s14 s15 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s14 489 (by decide) (by simpa using p14)]
    decide
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADDI .x28 .x28 112)) 1
  · rw [fetch_index SphincsImages.verify s15 490 (by decide) (by simpa using p15)]
    decide
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.SD .x28 .x10 0)) 0
  · rw [fetch_index SphincsImages.verify s16 491 (by decide) (by simpa using p16)]
    decide
  ·
    simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, counter]
  exact OrdinarySteps.refl _

theorem ftsSelect_pc (state : MachineState) (pc : state.pc = 0x176c) :
    (ftsSelectState state).pc = 0x17b0 := by
  simp [ftsSelectState, execInstrBr, pc]

theorem ftsSelect_position (state : MachineState) :
    (ftsSelectState state).getMem 0x43010 = 0 := by
  simp [ftsSelectState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem ftsSelect_leaf (state : MachineState) (tree : Fin 24)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val) :
    (ftsSelectState state).getMem 0x43020 =
      (state.getByte (BitVec.ofNat 64 (0x44800 + tree.val))).zeroExtend 64 ∧
    (ftsSelectState state).getMem 0x43070 =
      (state.getByte (BitVec.ofNat 64 (0x44800 + tree.val))).zeroExtend 64 := by
  change state.getMem (274496#64) = BitVec.ofNat 64 tree.val at counter
  fin_cases tree <;> constructor <;>
    simp [ftsSelectState, execInstrBr, signExtend12,
      MachineState.getMem_setMem_ne, MachineState.getByte,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      alignToDword, counter]

theorem ftsSelect_mem_frame (state : MachineState) (address : Word)
    (notPosition : address ≠ 0x43010)
    (notLeaf : address ≠ 0x43020)
    (notBit : address ≠ 0x43070) :
    (ftsSelectState state).getMem address = state.getMem address := by
  change address ≠ (274448#64) at notPosition
  change address ≠ (274464#64) at notLeaf
  change address ≠ (274544#64) at notBit
  simp [ftsSelectState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne, notPosition, notLeaf, notBit,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

set_option maxHeartbeats 0 in
theorem ftsSelect_selector_byte (state : MachineState) (tree : Fin 24) :
    (ftsSelectState state).getByte
      (BitVec.ofNat 64 (0x44800 + tree.val)) =
      state.getByte (BitVec.ofNat 64 (0x44800 + tree.val)) := by
  fin_cases tree <;>
    simp [ftsSelectState, execInstrBr, signExtend12,
      MachineState.getByte, MachineState.getMem_setPC,
      MachineState.getMem_setReg, MachineState.getMem_setMem_ne,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      alignToDword]

theorem messageReady_admissible_ftsSelect (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer)) :
    let initial := indexStoredState (indexValueState (writeHash state answer))
    let selected := leafStates initial 24 (by decide)
    let accepted := lastAcceptState selected
    let entered := ftsEntryState accepted
    let header := ftsTreeHeaderState entered
    let final := ftsSelectState header
    OrdinarySteps SphincsImages.verify (writeHash state answer) 322 final ∧
      final.pc = 0x17b0 ∧
      final.getMem 0x43000 = 0 ∧
      final.getMem 0x43008 =
        BitVec.ofNat 64 (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest answer)).val ∧
      final.getMem 0x43028 = 0x22cdc ∧
      final.getMem 0x43020 =
        (header.getByte (BitVec.ofNat 64 0x44800)).zeroExtend 64 ∧
      final.getMem 0x43070 =
        (header.getByte (BitVec.ofNat 64 0x44800)).zeroExtend 64 ∧
      (final.getMem 0x43020).toNat = abstractLeaf answer (0 : Fin 24) ∧
      ∀ tree : Fin 24,
        (final.getByte (BitVec.ofNat 64 (0x44800 + tree.val))).toNat =
          abstractLeaf answer tree := by
  obtain ⟨front, headerPc, layer, treeIndex, pointer, selectors⟩ :=
    messageReady_admissible_treeHeader state pk message randomness
      ready pc answer admissible
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selected := leafStates initial 24 (by decide)
  let accepted := lastAcceptState selected
  let entered := ftsEntryState accepted
  let header := ftsTreeHeaderState entered
  have counter : header.getMem 0x43040 = BitVec.ofNat 64 (0 : Fin 24).val := by
    rw [ftsTreeHeader_mem_frame _ 0x43040 (by decide) (by decide)]
    exact (ftsEntry_cells accepted).1
  have back := ftsSelect_block header 0 headerPc counter
  have finalPc := ftsSelect_pc header headerPc
  have leaf := ftsSelect_leaf header 0 counter
  have selectedZero := selectors (0 : Fin 24)
  exact ⟨by simpa [initial, selected, accepted, entered, header] using
      front.append back,
    finalPc,
    by rw [ftsSelect_mem_frame _ 0x43000 (by decide) (by decide) (by decide)];
       exact layer,
    by rw [ftsSelect_mem_frame _ 0x43008 (by decide) (by decide) (by decide)];
       exact treeIndex,
    by rw [ftsSelect_mem_frame _ 0x43028 (by decide) (by decide) (by decide)];
       exact pointer,
    by simpa using leaf.1,
    by simpa using leaf.2,
    by
      rw [leaf.1]
      change ((header.getByte (BitVec.ofNat 64 0x44800)).setWidth 64).toNat = _
      rw [BitVec.toNat_setWidth_of_le (show 8 ≤ 64 by decide)]
      simpa using selectedZero,
    by intro tree
       rw [ftsSelect_selector_byte]
       exact selectors tree⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsSelect.messageReady_admissible_ftsSelect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_admissible_ftsSelect

end SigGolfCandidate.SphincsVerifierFtsSelect
