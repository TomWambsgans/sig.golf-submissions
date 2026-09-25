import SigGolfCandidate.SphincsVerifierWotsChainSetup
import SigGolfCandidate.SphincsVerifierFtsCopyAccess
import SigGolfCandidate.SphincsVerifierCopyMemory

import SigGolfCandidate.SphincsMaskedKeygenPrefix

namespace SigGolfCandidate.SphincsVerifierWotsChainEntry
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierCopyMemory
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def chainValuePointers (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 40)
  let state := execInstrBr state (.LD .x6 .x28 0)
  let state := execInstrBr state (.LUI .x7 0x45)
  execInstrBr state (.ADDI .x7 .x7 (-1280))

theorem chainValuePointers_block (state : MachineState) (chain : Fin 52)
    (pc : state.pc = 0x2710)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val)) :
    OrdinarySteps SphincsImages.verify state 5
      (chainValuePointers state) ∧
    (chainValuePointers state).pc = 0x2724 ∧
    (chainValuePointers state).getReg .x6 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val) ∧
    (chainValuePointers state).getReg .x7 = 0x44b00 := by
  let s1 := execInstrBr state (.LUI .x28 0x43)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 40)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x7 0x45)
  let s5 := execInstrBr s4 (.ADDI .x7 .x7 (-1280))
  have p1 : s1.pc = 0x2714 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x2718 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x271c := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x2720 := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x2724 := by simp [s5, execInstrBr, p4]
  have trace : OrdinarySteps SphincsImages.verify state 5 s5 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x28 0x43)) 4
    · rw [fetch_index SphincsImages.verify state 1476 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 40)) 3
    · rw [fetch_index SphincsImages.verify s1 1477 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 2
    · rw [fetch_index SphincsImages.verify s2 1478 (by decide)
        (by simpa using p2)]
      decide
    · simp [s3, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s2, s1,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x7 0x45)) 1
    · rw [fetch_index SphincsImages.verify s3 1479 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x7 .x7 (-1280))) 0
    · rw [fetch_index SphincsImages.verify s4 1480 (by decide)
        (by simpa using p4)]
      decide
    · rfl
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [chainValuePointers] using trace,
    by simpa only [chainValuePointers] using p5, ?_, ?_⟩
  · simpa [chainValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
      using pointer
  · simp [chainValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]

theorem chain_value_copy_code : Copy20Code SphincsImages.verify 1481 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

def chainValueCopied (state : MachineState) : MachineState :=
  copyRootState (chainValuePointers state)

theorem chainValueCopied_block (state : MachineState) (chain : Fin 52)
    (pc : state.pc = 0x2710)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val)) :
    OrdinarySteps SphincsImages.verify state 15
      (chainValueCopied state) ∧
    (chainValueCopied state).pc = 0x274c := by
  obtain ⟨pre, prePc, source, destination⟩ :=
    chainValuePointers_block state chain pc pointer
  have copy := copy20_block_general SphincsImages.verify 1481
    chain_value_copy_code (chainValuePointers state)
    (0x2547c + 20 * chain.val) 0x44b00
    (by simpa using prePc) source destination
    (by have := chain.isLt; omega)
    (by dsimp [MEMORY_BYTES]; have := chain.isLt; omega)
    (by decide) (by decide) (by decide)
  refine ⟨by simpa only [chainValueCopied] using pre.append copy, ?_⟩
  exact copy20_final_pc (chainValuePointers state) 1481
    (by simpa using prePc)

def chainDigitState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.LUI .x6 0x44)
  let state := execInstrBr state (.ADDI .x6 .x6 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 80)
  let state := execInstrBr state (.LD .x7 .x28 0)
  let state := execInstrBr state (.ADD .x6 .x6 .x7)
  let state := execInstrBr state (.LBU .x10 .x6 0)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 88)
  execInstrBr state (.SD .x28 .x10 0)

theorem chainDigit_block (state : MachineState) (chain : Fin 52)
    (pc : state.pc = 0x274c)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val) :
    OrdinarySteps SphincsImages.verify state 10 (chainDigitState state) ∧
    (chainDigitState state).pc = 0x2774 := by
  let s1 := execInstrBr state (.LUI .x6 0x44)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LUI .x28 0x43)
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 80)
  let s5 := execInstrBr s4 (.LD .x7 .x28 0)
  let s6 := execInstrBr s5 (.ADD .x6 .x6 .x7)
  let s7 := execInstrBr s6 (.LBU .x10 .x6 0)
  let s8 := execInstrBr s7 (.LUI .x28 0x43)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 88)
  let s10 := execInstrBr s9 (.SD .x28 .x10 0)
  have p1 : s1.pc = 0x2750 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x2754 := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x2758 := by simp [s3, execInstrBr, p2]
  have p4 : s4.pc = 0x275c := by simp [s4, execInstrBr, p3]
  have p5 : s5.pc = 0x2760 := by simp [s5, execInstrBr, p4]
  have p6 : s6.pc = 0x2764 := by simp [s6, execInstrBr, p5]
  have p7 : s7.pc = 0x2768 := by simp [s7, execInstrBr, p6]
  have p8 : s8.pc = 0x276c := by simp [s8, execInstrBr, p7]
  have p9 : s9.pc = 0x2770 := by simp [s9, execInstrBr, p8]
  have p10 : s10.pc = 0x2774 := by simp [s10, execInstrBr, p9]
  have trace : OrdinarySteps SphincsImages.verify state 10 s10 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x44)) 9
    · rw [fetch_index SphincsImages.verify state 1491 (by decide)
        (by simpa using pc)]
      decide
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 8
    · rw [fetch_index SphincsImages.verify s1 1492 (by decide)
        (by simpa using p1)]
      decide
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x28 0x43)) 7
    · rw [fetch_index SphincsImages.verify s2 1493 (by decide)
        (by simpa using p2)]
      decide
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x28 80)) 6
    · rw [fetch_index SphincsImages.verify s3 1494 (by decide)
        (by simpa using p3)]
      decide
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.LD .x7 .x28 0)) 5
    · rw [fetch_index SphincsImages.verify s4 1495 (by decide)
        (by simpa using p4)]
      decide
    · simp [s5, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s4, s3,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x6 .x6 .x7)) 4
    · rw [fetch_index SphincsImages.verify s5 1496 (by decide)
        (by simpa using p5)]
      decide
    · rfl
    apply OrdinarySteps.step s6 s7 _ (.base (.LBU .x10 .x6 0)) 3
    · rw [fetch_index SphincsImages.verify s6 1497 (by decide)
        (by simpa using p6)]
      decide
    · have address : s6.getReg .x6 =
          BitVec.ofNat 64 (0x44000 + chain.val) := by
        have hc : state.getMem (274512#64) = BitVec.ofNat 64 chain.val := by
          simpa using counter
        simp [s6, s5, s4, s3, s2, s1, execInstrBr,
          signExtend12, MachineState.getReg_setReg_eq,
          MachineState.getReg_setReg_ne, hc,
          ← BitVec.ofNat_add]
      have valid : memoryArgumentsValid s6 (.LBU .x10 .x6 0) = true := by
        simp [memoryArgumentsValid, address, signExtend12,
          accessValid, rangeValid, MEMORY_BYTES]
        have := chain.isLt
        omega
      simp [s7, ordinaryStep, memoryArgumentsValid, address,
        signExtend12, accessValid, rangeValid, MEMORY_BYTES]
      fin_cases chain <;> decide
    apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x43)) 2
    · rw [fetch_index SphincsImages.verify s7 1498 (by decide)
        (by simpa using p7)]
      decide
    · rfl
    apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 88)) 1
    · rw [fetch_index SphincsImages.verify s8 1499 (by decide)
        (by simpa using p8)]
      decide
    · rfl
    apply OrdinarySteps.step s9 s10 _ (.base (.SD .x28 .x10 0)) 0
    · rw [fetch_index SphincsImages.verify s9 1500 (by decide)
        (by simpa using p9)]
      decide
    · simp [s10, ordinaryStep, memoryArgumentsValid, accessValid,
        rangeValid, execInstrBr, signExtend12, s9, s8,
        MachineState.getReg_setReg_eq, MEMORY_BYTES]
    exact OrdinarySteps.refl _
  exact ⟨by simpa only [chainDigitState] using trace,
    by simpa only [chainDigitState] using p10⟩

theorem chainValueCopied_counter (state : MachineState) :
    (chainValueCopied state).getMem 0x43050 = state.getMem 0x43050 := by
  have destination : (chainValuePointers state).getReg .x7 = 0x44b00 := by
    simp [chainValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (chainValuePointers state) 0x43050
    (by intro offset; rw [destination]; fin_cases offset <;> decide)
  have pointerFrame : (chainValuePointers state).getMem 0x43050 =
      state.getMem 0x43050 := by
    simp [chainValuePointers, execInstrBr]
  exact frame.trans pointerFrame

def chainEntryState (state : MachineState) : MachineState :=
  chainDigitState (chainValueCopied state)

theorem chainEntry_block (state : MachineState) (chain : Fin 52)
    (pc : state.pc = 0x2710)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val))
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val) :
    OrdinarySteps SphincsImages.verify state 25
      (chainEntryState state) ∧
    (chainEntryState state).pc = 0x2774 := by
  have copy := chainValueCopied_block state chain pc pointer
  have counter' : (chainValueCopied state).getMem 0x43050 =
      BitVec.ofNat 64 chain.val :=
    (chainValueCopied_counter state).trans counter
  have digit := chainDigit_block (chainValueCopied state) chain copy.2 counter'
  refine ⟨?_, digit.2⟩
  simpa [chainEntryState] using copy.1.append digit.1

theorem chainDigit_step (state : MachineState) (chain : Fin 52)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val) :
    (chainDigitState state).getMem 0x43058 =
      (state.getByte (BitVec.ofNat 64 (0x44000 + chain.val))).zeroExtend 64 := by
  have hc : state.getMem (274512#64) = BitVec.ofNat 64 chain.val := by
    simpa using counter
  fin_cases chain <;>
    simp [chainDigitState, execInstrBr, signExtend12,
      MachineState.getMem_setMem_eq,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      hc, MachineState.getByte]

theorem chainValueCopied_digit (state : MachineState) (chain : Fin 52) :
    (chainValueCopied state).getByte
      (BitVec.ofNat 64 (0x44000 + chain.val)) =
      state.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) := by
  let address : Word := BitVec.ofNat 64 (0x44000 + chain.val)
  have destination : (chainValuePointers state).getReg .x7 = 0x44b00 := by
    simp [chainValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have frame := copyRoot_mem_frame (chainValuePointers state)
    (alignToDword address)
    (by
      intro offset
      rw [destination]
      fin_cases chain <;> fin_cases offset <;> decide)
  have pointerFrame : (chainValuePointers state).getByte address =
      state.getByte address := by
    simp [chainValuePointers, execInstrBr, MachineState.getByte]
  change (copyRootState (chainValuePointers state)).getByte address =
    state.getByte address
  calc
    (copyRootState (chainValuePointers state)).getByte address =
        (chainValuePointers state).getByte address := by
          simpa [MachineState.getByte] using
            congrArg (fun value : BitVec 64 =>
              extractByte value (byteOffset address)) frame
    _ = state.getByte address := pointerFrame

theorem chainEntry_step (state : MachineState) (chain : Fin 52)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val) :
    (chainEntryState state).getMem 0x43058 =
      (state.getByte (BitVec.ofNat 64 (0x44000 + chain.val))).zeroExtend 64 := by
  have counter' : (chainValueCopied state).getMem 0x43050 =
      BitVec.ofNat 64 chain.val :=
    (chainValueCopied_counter state).trans counter
  exact (chainDigit_step (chainValueCopied state) chain counter').trans
    (congrArg (fun b : Byte => b.zeroExtend 64)
      (chainValueCopied_digit state chain))

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainEntry.chainValueCopied_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainValueCopied_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainEntry.chainDigit_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainDigit_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainEntry.chainEntry_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainEntry_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainEntry.chainDigit_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainDigit_step

/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainEntry.chainEntry_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainEntry_step

end SigGolfCandidate.SphincsVerifierWotsChainEntry

namespace SigGolfCandidate.SphincsVerifierWotsChainEntryGeneral
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsChainEntry
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def pointerSchedule : List (Word × Instr) := [
  (0x2710, .LUI .x28 0x43),
  (0x2714, .ADDI .x28 .x28 40),
  (0x2718, .LD .x6 .x28 0),
  (0x271c, .LUI .x7 0x45),
  (0x2720, .ADDI .x7 .x7 (-1280))]

theorem pointer_code : ∀ e ∈ pointerSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify e.1 =
      some (.base e.2) := by decide

theorem pointer_checked (s : MachineState) (pc : s.pc = 0x2710) :
    Checked pointerSchedule s := by
  simp [Checked, pointerSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc] <;> bv_decide

theorem pointer_state_eq (s : MachineState) :
    runSchedule pointerSchedule s = chainValuePointers s := by
  rfl

theorem pointer_block (s : MachineState) (pc : s.pc = 0x2710) :
    OrdinarySteps SphincsImages.verify s 5 (chainValuePointers s) := by
  have h := checked_sound SphincsImages.verify pointerSchedule
    pointer_code s (pointer_checked s pc)
  rw [pointer_state_eq] at h
  simpa [pointerSchedule] using h

theorem pointer_pc (s : MachineState) (pc : s.pc = 0x2710) :
    (chainValuePointers s).pc = 0x2724 := by
  simp [chainValuePointers, execInstrBr, pc]

theorem pointer_source (s : MachineState) (sourceBase : Nat)
    (pointer : s.getMem 0x43028 = BitVec.ofNat 64 sourceBase) :
    (chainValuePointers s).getReg .x6 = BitVec.ofNat 64 sourceBase := by
  simpa [chainValuePointers, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using pointer

theorem pointer_destination (s : MachineState) :
    (chainValuePointers s).getReg .x7 = 0x44b00 := by
  simp [chainValuePointers, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq]

theorem chainValueCopied_block_general (s : MachineState)
    (sourceBase : Nat) (small : sourceBase + 20 ≤ 0x40000)
    (aligned : sourceBase % 4 = 0)
    (pc : s.pc = 0x2710)
    (pointer : s.getMem 0x43028 = BitVec.ofNat 64 sourceBase) :
    OrdinarySteps SphincsImages.verify s 15 (chainValueCopied s) ∧
      (chainValueCopied s).pc = 0x274c := by
  have pre := pointer_block s pc
  have copy := copy20_block_general SphincsImages.verify 1481
    chain_value_copy_code (chainValuePointers s) sourceBase 0x44b00
    (by simpa using pointer_pc s pc)
    (pointer_source s sourceBase pointer) (pointer_destination s)
    aligned (by dsimp [MEMORY_BYTES]; omega)
    (by decide) (by decide) (by decide)
  refine ⟨by simpa only [chainValueCopied] using pre.append copy, ?_⟩
  exact copy20_final_pc (chainValuePointers s) 1481
    (by simpa using pointer_pc s pc)

theorem chainEntry_block_general (s : MachineState) (chain : Fin 52)
    (sourceBase : Nat) (small : sourceBase + 20 ≤ 0x40000)
    (aligned : sourceBase % 4 = 0)
    (pc : s.pc = 0x2710)
    (pointer : s.getMem 0x43028 = BitVec.ofNat 64 sourceBase)
    (counter : s.getMem 0x43050 = BitVec.ofNat 64 chain.val) :
    OrdinarySteps SphincsImages.verify s 25 (chainEntryState s) ∧
      (chainEntryState s).pc = 0x2774 := by
  have copy := chainValueCopied_block_general s sourceBase small aligned pc pointer
  have counter' : (chainValueCopied s).getMem 0x43050 =
      BitVec.ofNat 64 chain.val :=
    (chainValueCopied_counter s).trans counter
  have digit := chainDigit_block (chainValueCopied s) chain copy.2 counter'
  refine ⟨?_, digit.2⟩
  simpa [chainEntryState] using copy.1.append digit.1


/-- info: 'SigGolfCandidate.SphincsVerifierWotsChainEntryGeneral.chainEntry_block_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainEntry_block_general

end SigGolfCandidate.SphincsVerifierWotsChainEntryGeneral
