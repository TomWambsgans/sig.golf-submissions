import SigGolfCandidate.SphincsVerifierFtsCopyPointers

namespace SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
set_option maxRecDepth 16384

theorem copy_access (base : Nat) (aligned : base % 4 = 0)
    (bounded : base + 20 ≤ MEMORY_BYTES) (offset : Fin 5) :
    accessValid
      (BitVec.ofNat 64 base + signExtend12 (4#12 * BitVec.ofNat 12 offset.val)) 4 = true := by
  have address : BitVec.ofNat 64 base +
      signExtend12 (4#12 * BitVec.ofNat 12 offset.val) =
      BitVec.ofNat 64 (base + 4 * offset.val) := by
    fin_cases offset <;> simp [signExtend12, ← BitVec.ofNat_add]
  rw [address]
  have small : base + 4 * offset.val < 2 ^ 64 := by
    have ht : offset.val < 5 := offset.isLt
    dsimp [MEMORY_BYTES] at bounded
    omega
  have within : base + 4 * offset.val + 4 ≤ MEMORY_BYTES := by
    have ht : offset.val < 5 := offset.isLt
    omega
  simp [accessValid, rangeValid, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, within, aligned] <;> omega

/-- One exact load/store pair, with the address constrained by the memory range rather than a fixed list. -/
theorem copy20_word_block_general (image : Image) (start : Nat)
    (code : Copy20Code image start) (offset : Fin 5)
    (state : MachineState) (sourceBase destinationBase : Nat)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (start + 2 * offset.val)))
    (source : state.getReg .x6 = BitVec.ofNat 64 sourceBase)
    (destination : state.getReg .x7 = BitVec.ofNat 64 destinationBase)
    (sourceAligned : sourceBase % 4 = 0)
    (sourceBounded : sourceBase + 20 ≤ MEMORY_BYTES)
    (destinationAligned : destinationBase % 4 = 0)
    (destinationBounded : destinationBase + 20 ≤ MEMORY_BYTES)
    (small : 0x1000 + 4 * (start + 2 * offset.val + 1) < 2 ^ 64) :
    OrdinarySteps image state 2 (copyWordState offset state) := by
  let loaded := execInstrBr state (.LWU .x13 .x6 (4 * offset.val))
  let copied := execInstrBr loaded (.SW .x7 .x13 (4 * offset.val))
  have small0 : 0x1000 + 4 * (start + 2 * offset.val) < 2 ^ 64 := by omega
  have loadedPc : loaded.pc = BitVec.ofNat 64
      (0x1000 + 4 * (start + 2 * offset.val + 1)) := by
    simp only [loaded, execInstrBr, pc]
    change BitVec.ofNat 64 (0x1000 + 4 * (start + 2 * offset.val)) +
      BitVec.ofNat 64 4 = _
    rw [BitVec.ofNat_add_ofNat]
    congr 1
  apply OrdinarySteps.step state loaded _
    (.base (.LWU .x13 .x6 (4 * offset.val))) 1
  · rw [fetch_index image state _ small0 pc]
    exact code.load offset
  · have valid : memoryArgumentsValid state
        (.LWU .x13 .x6 (4#12 * BitVec.ofNat 12 offset.val)) = true := by
      simpa [memoryArgumentsValid, source] using
        copy_access sourceBase sourceAligned sourceBounded offset
    simpa [ordinaryStep, valid, loaded]
  apply OrdinarySteps.step loaded copied _
    (.base (.SW .x7 .x13 (4 * offset.val))) 0
  · rw [fetch_index image loaded _ small loadedPc]
    exact code.store offset
  · have destinationLoaded : loaded.getReg .x7 = BitVec.ofNat 64 destinationBase := by
      simp [loaded, execInstrBr, MachineState.getReg_setReg_ne, destination]
    have valid : memoryArgumentsValid loaded
        (.SW .x7 .x13 (4#12 * BitVec.ofNat 12 offset.val)) = true := by
      simpa [memoryArgumentsValid, destinationLoaded] using
        copy_access destinationBase destinationAligned destinationBounded offset
    simpa [ordinaryStep, valid, copied]
  exact OrdinarySteps.refl _

theorem copy20_block_general (image : Image) (start : Nat)
    (code : Copy20Code image start) (state : MachineState)
    (sourceBase destinationBase : Nat)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * start))
    (source : state.getReg .x6 = BitVec.ofNat 64 sourceBase)
    (destination : state.getReg .x7 = BitVec.ofNat 64 destinationBase)
    (sourceAligned : sourceBase % 4 = 0)
    (sourceBounded : sourceBase + 20 ≤ MEMORY_BYTES)
    (destinationAligned : destinationBase % 4 = 0)
    (destinationBounded : destinationBase + 20 ≤ MEMORY_BYTES)
    (small : 0x1000 + 4 * (start + 10) < 2 ^ 64) :
    OrdinarySteps image state 10 (copyRootState state) := by
  let s1 := copyWordState 0 state
  let s2 := copyWordState 1 s1
  let s3 := copyWordState 2 s2
  let s4 := copyWordState 3 s3
  let s5 := copyWordState 4 s4
  have p0 : state.pc = BitVec.ofNat 64
      (0x1000 + 4 * (start + 2 * (0 : Fin 5).val)) := by simpa using pc
  have p1 : s1.pc = BitVec.ofNat 64
      (0x1000 + 4 * (start + 2 * (1 : Fin 5).val)) := by
    simpa using copy20_word_pc 0 state start p0
  have p2 : s2.pc = BitVec.ofNat 64
      (0x1000 + 4 * (start + 2 * (2 : Fin 5).val)) := by
    simpa using copy20_word_pc 1 s1 start p1
  have p3 : s3.pc = BitVec.ofNat 64
      (0x1000 + 4 * (start + 2 * (3 : Fin 5).val)) := by
    simpa using copy20_word_pc 2 s2 start p2
  have p4 : s4.pc = BitVec.ofNat 64
      (0x1000 + 4 * (start + 2 * (4 : Fin 5).val)) := by
    simpa using copy20_word_pc 3 s3 start p3
  have src1 : s1.getReg .x6 = BitVec.ofNat 64 sourceBase :=
    (copyWord_pointers 0 state).1.trans source
  have dst1 : s1.getReg .x7 = BitVec.ofNat 64 destinationBase :=
    (copyWord_pointers 0 state).2.trans destination
  have src2 : s2.getReg .x6 = BitVec.ofNat 64 sourceBase :=
    (copyWord_pointers 1 s1).1.trans src1
  have dst2 : s2.getReg .x7 = BitVec.ofNat 64 destinationBase :=
    (copyWord_pointers 1 s1).2.trans dst1
  have src3 : s3.getReg .x6 = BitVec.ofNat 64 sourceBase :=
    (copyWord_pointers 2 s2).1.trans src2
  have dst3 : s3.getReg .x7 = BitVec.ofNat 64 destinationBase :=
    (copyWord_pointers 2 s2).2.trans dst2
  have src4 : s4.getReg .x6 = BitVec.ofNat 64 sourceBase :=
    (copyWord_pointers 3 s3).1.trans src3
  have dst4 : s4.getReg .x7 = BitVec.ofNat 64 destinationBase :=
    (copyWord_pointers 3 s3).2.trans dst3
  have b0 := copy20_word_block_general image start code 0 state
    sourceBase destinationBase p0 source destination sourceAligned sourceBounded
    destinationAligned destinationBounded (by omega)
  have b1 := copy20_word_block_general image start code 1 s1
    sourceBase destinationBase p1 src1 dst1 sourceAligned sourceBounded
    destinationAligned destinationBounded (by omega)
  have b2 := copy20_word_block_general image start code 2 s2
    sourceBase destinationBase p2 src2 dst2 sourceAligned sourceBounded
    destinationAligned destinationBounded (by omega)
  have b3 := copy20_word_block_general image start code 3 s3
    sourceBase destinationBase p3 src3 dst3 sourceAligned sourceBounded
    destinationAligned destinationBounded (by omega)
  have b4 := copy20_word_block_general image start code 4 s4
    sourceBase destinationBase p4 src4 dst4 sourceAligned sourceBounded
    destinationAligned destinationBounded (by omega)
  simpa [copyRootState, s1, s2, s3, s4, s5] using
    (((b0.append b1).append b2).append b3).append b4

/-- info: 'SigGolfCandidate.SphincsVerifierFtsCopyAccess.copy20_block_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms copy20_block_general

end SigGolfCandidate.SphincsVerifierFtsCopyAccess
