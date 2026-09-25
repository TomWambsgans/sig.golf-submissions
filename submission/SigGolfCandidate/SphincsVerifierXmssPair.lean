import SigGolfCandidate.SphincsVerifierXmssAnswer
import SigGolfCandidate.SphincsVerifierFtsLeftPath

namespace SigGolfCandidate.SphincsVerifierXmssPair
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsVerifierFtsRightPath
open SigGolfCandidate.SphincsVerifierFtsLeftPath
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def rightPc (lay : Layer) : Word := nodePc lay + 20

def rightPointersSchedule (lay : Layer) : List (Word × Instr) := [
  (rightPc lay, .LUI .x28 0x43),
  (rightPc lay + 4, .ADDI .x28 .x28 40),
  (rightPc lay + 8, .LD .x6 .x28 0),
  (rightPc lay + 12, .LUI .x7 0x40),
  (rightPc lay + 16, .ADDI .x7 .x7 40)]

theorem rightPointers_code (lay : Layer) :
    ∀ entry ∈ rightPointersSchedule lay,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by
  fin_cases lay <;> decide

theorem rightPointers_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = rightPc lay) : Checked (rightPointersSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, rightPointersSchedule, rightPc, nodePc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, signExtend12,
      MachineState.getReg_setReg_eq, pc]

theorem rightPointers_block (lay : Layer) (s : MachineState)
    (pc : s.pc = rightPc lay) :
    OrdinarySteps SphincsImages.verify s 5
      (SphincsVerifierFtsRightPath.rightPointers s) := by
  have block := checked_sound _ (rightPointersSchedule lay)
    (rightPointers_code lay) s (rightPointers_checked lay s pc)
  simpa [rightPointersSchedule, runSchedule,
    SphincsVerifierFtsRightPath.rightPointers] using block

def rightCopyIndex (lay : Layer) : Nat := 1727 + 1011 * (5 - lay.val)

theorem rightCopy_code (lay : Layer) :
    Copy20Code SphincsImages.verify (rightCopyIndex lay) := by
  fin_cases lay <;> constructor <;> intro offset <;> fin_cases offset <;> decide

theorem rightCopy_block (lay : Layer) (s : MachineState)
    (pc : s.pc = rightPc lay + 20)
    (sourceBase : Nat)
    (source : s.getReg .x6 = BitVec.ofNat 64 sourceBase)
    (destination : s.getReg .x7 = 0x40028)
    (sourceAligned : sourceBase % 4 = 0)
    (sourceBounded : sourceBase + 20 ≤ MEMORY_BYTES) :
    OrdinarySteps SphincsImages.verify s 10 (copyRootState s) := by
  apply copy20_block_general SphincsImages.verify (rightCopyIndex lay)
    (rightCopy_code lay) s sourceBase 0x40028
  · fin_cases lay <;> simpa [rightCopyIndex, rightPc, nodePc] using pc
  · exact source
  · exact destination
  · exact sourceAligned
  · exact sourceBounded
  · decide
  · decide
  · fin_cases lay <;> decide

def rightCurrentPc (lay : Layer) : Word := nodePc lay + 0x50

def rightCurrentSchedule (lay : Layer) : List (Word × Instr) := [
  (rightCurrentPc lay, .LUI .x6 0x45),
  (rightCurrentPc lay + 4, .ADDI .x6 .x6 (-1536)),
  (rightCurrentPc lay + 8, .LUI .x7 0x40),
  (rightCurrentPc lay + 12, .ADDI .x7 .x7 60)]

theorem rightCurrent_code (lay : Layer) :
    ∀ entry ∈ rightCurrentSchedule lay,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by
  fin_cases lay <;> decide

theorem rightCurrent_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = rightCurrentPc lay) :
    Checked (rightCurrentSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, rightCurrentSchedule, rightCurrentPc, nodePc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, signExtend12,
      MachineState.getReg_setReg_eq, pc]

theorem rightCurrent_block (lay : Layer) (s : MachineState)
    (pc : s.pc = rightCurrentPc lay) :
    OrdinarySteps SphincsImages.verify s 4
      (SphincsVerifierFtsRightPath.rightCurrentPointers s) := by
  have block := checked_sound _ (rightCurrentSchedule lay)
    (rightCurrent_code lay) s (rightCurrent_checked lay s pc)
  simpa [rightCurrentSchedule, runSchedule,
    SphincsVerifierFtsRightPath.rightCurrentPointers] using block

def rightCurrentCopyIndex (lay : Layer) : Nat := 1741 + 1011 * (5 - lay.val)

theorem rightCurrentCopy_code (lay : Layer) :
    Copy20Code SphincsImages.verify (rightCurrentCopyIndex lay) := by
  fin_cases lay <;> constructor <;> intro offset <;> fin_cases offset <;> decide

theorem rightCurrentCopy_block (lay : Layer) (s : MachineState)
    (pc : s.pc = rightCurrentPc lay + 16)
    (source : s.getReg .x6 = 0x44a00)
    (destination : s.getReg .x7 = 0x4003c) :
    OrdinarySteps SphincsImages.verify s 10 (copyRootState s) := by
  apply copy20_block_general SphincsImages.verify (rightCurrentCopyIndex lay)
    (rightCurrentCopy_code lay) s 0x44a00 0x4003c
  · fin_cases lay <;> simpa [rightCurrentCopyIndex, rightCurrentPc, nodePc] using pc
  · exact source
  · exact destination
  · decide
  · decide
  · decide
  · decide
  · fin_cases lay <;> decide

theorem rightJoin_site (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay + 0x88) :
    fetch SphincsImages.verify s = some (.base (.JAL .x0 120)) := by
  fin_cases lay
  · rw [fetch_index SphincsImages.verify s 6806 (by decide)
      (by simpa [nodePc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify s 5795 (by decide)
      (by simpa [nodePc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify s 4784 (by decide)
      (by simpa [nodePc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify s 3773 (by decide)
      (by simpa [nodePc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify s 2762 (by decide)
      (by simpa [nodePc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify s 1751 (by decide)
      (by simpa [nodePc] using pc)]; decide

theorem rightJoin_block (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay + 0x88) :
    OrdinarySteps SphincsImages.verify s 1
      (SphincsVerifierFtsRightPath.rightJump s) := by
  apply OrdinarySteps.step s _ _ (.base (.JAL .x0 120)) 0
  · exact rightJoin_site lay s pc
  · rfl
  · exact OrdinarySteps.refl _

theorem rightJoin_pc (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay + 0x88) :
    (SphincsVerifierFtsRightPath.rightJump s).pc = nodePc lay + 0x100 := by
  simp [SphincsVerifierFtsRightPath.rightJump, execInstrBr, pc, signExtend21]
  bv_decide

def leftPc (lay : Layer) : Word := nodePc lay + 0x8c

def leftCurrentSchedule (lay : Layer) : List (Word × Instr) := [
  (leftPc lay, .LUI .x6 0x45),
  (leftPc lay + 4, .ADDI .x6 .x6 (-1536)),
  (leftPc lay + 8, .LUI .x7 0x40),
  (leftPc lay + 12, .ADDI .x7 .x7 40)]

theorem leftCurrent_code (lay : Layer) :
    ∀ entry ∈ leftCurrentSchedule lay,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by
  fin_cases lay <;> decide

theorem leftCurrent_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = leftPc lay) : Checked (leftCurrentSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, leftCurrentSchedule, leftPc, nodePc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, signExtend12,
      MachineState.getReg_setReg_eq, pc]

theorem leftCurrent_block (lay : Layer) (s : MachineState)
    (pc : s.pc = leftPc lay) :
    OrdinarySteps SphincsImages.verify s 4
      (SphincsVerifierFtsLeftPath.leftCurrentPointers s) := by
  have block := checked_sound _ (leftCurrentSchedule lay)
    (leftCurrent_code lay) s (leftCurrent_checked lay s pc)
  simpa [leftCurrentSchedule, runSchedule,
    SphincsVerifierFtsLeftPath.leftCurrentPointers] using block

def leftCurrentCopyIndex (lay : Layer) : Nat := 1756 + 1011 * (5 - lay.val)

theorem leftCurrentCopy_code (lay : Layer) :
    Copy20Code SphincsImages.verify (leftCurrentCopyIndex lay) := by
  fin_cases lay <;> constructor <;> intro offset <;> fin_cases offset <;> decide

theorem leftCurrentCopy_block (lay : Layer) (s : MachineState)
    (pc : s.pc = leftPc lay + 16)
    (source : s.getReg .x6 = 0x44a00)
    (destination : s.getReg .x7 = 0x40028) :
    OrdinarySteps SphincsImages.verify s 10 (copyRootState s) := by
  apply copy20_block_general SphincsImages.verify (leftCurrentCopyIndex lay)
    (leftCurrentCopy_code lay) s 0x44a00 0x40028
  · fin_cases lay <;> simpa [leftCurrentCopyIndex, leftPc, nodePc] using pc
  · exact source
  · exact destination
  · decide
  · decide
  · decide
  · decide
  · fin_cases lay <;> decide

def leftSiblingPc (lay : Layer) : Word := nodePc lay + 0xc4

def leftSiblingSchedule (lay : Layer) : List (Word × Instr) := [
  (leftSiblingPc lay, .LUI .x28 0x43),
  (leftSiblingPc lay + 4, .ADDI .x28 .x28 40),
  (leftSiblingPc lay + 8, .LD .x6 .x28 0),
  (leftSiblingPc lay + 12, .LUI .x7 0x40),
  (leftSiblingPc lay + 16, .ADDI .x7 .x7 60)]

theorem leftSibling_code (lay : Layer) :
    ∀ entry ∈ leftSiblingSchedule lay,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by
  fin_cases lay <;> decide

theorem leftSibling_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = leftSiblingPc lay) : Checked (leftSiblingSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, leftSiblingSchedule, leftSiblingPc, nodePc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, signExtend12,
      MachineState.getReg_setReg_eq, pc]

theorem leftSibling_block (lay : Layer) (s : MachineState)
    (pc : s.pc = leftSiblingPc lay) :
    OrdinarySteps SphincsImages.verify s 5
      (SphincsVerifierFtsLeftPath.leftSiblingPointers s) := by
  have block := checked_sound _ (leftSiblingSchedule lay)
    (leftSibling_code lay) s (leftSibling_checked lay s pc)
  simpa [leftSiblingSchedule, runSchedule,
    SphincsVerifierFtsLeftPath.leftSiblingPointers] using block

def leftSiblingCopyIndex (lay : Layer) : Nat := 1771 + 1011 * (5 - lay.val)

theorem leftSiblingCopy_code (lay : Layer) :
    Copy20Code SphincsImages.verify (leftSiblingCopyIndex lay) := by
  fin_cases lay <;> constructor <;> intro offset <;> fin_cases offset <;> decide

theorem leftSiblingCopy_block (lay : Layer) (s : MachineState)
    (pc : s.pc = leftSiblingPc lay + 20)
    (sourceBase : Nat)
    (source : s.getReg .x6 = BitVec.ofNat 64 sourceBase)
    (destination : s.getReg .x7 = 0x4003c)
    (sourceAligned : sourceBase % 4 = 0)
    (sourceBounded : sourceBase + 20 ≤ MEMORY_BYTES) :
    OrdinarySteps SphincsImages.verify s 10 (copyRootState s) := by
  apply copy20_block_general SphincsImages.verify (leftSiblingCopyIndex lay)
    (leftSiblingCopy_code lay) s sourceBase 0x4003c
  · fin_cases lay <;> simpa [leftSiblingCopyIndex, leftSiblingPc, nodePc] using pc
  · exact source
  · exact destination
  · exact sourceAligned
  · exact sourceBounded
  · decide
  · decide
  · fin_cases lay <;> decide

theorem rightPath_block (lay : Layer) (s : MachineState)
    (pc : s.pc = rightPc lay)
    (sourceBase : Nat)
    (pointer : s.getMem 0x43028 = BitVec.ofNat 64 sourceBase)
    (aligned : sourceBase % 4 = 0)
    (bounded : sourceBase + 20 ≤ MEMORY_BYTES) :
    OrdinarySteps SphincsImages.verify s 30
      (SphincsVerifierFtsRightPath.rightFinishState
        (copyRootState (SphincsVerifierFtsRightPath.rightPointers s))) ∧
      (SphincsVerifierFtsRightPath.rightFinishState
        (copyRootState (SphincsVerifierFtsRightPath.rightPointers s))).pc =
          nodePc lay + 0x100 := by
  let p := SphincsVerifierFtsRightPath.rightPointers s
  let c := copyRootState p
  let q := SphincsVerifierFtsRightPath.rightCurrentPointers c
  let d := copyRootState q
  have hp := rightPointers_block lay s pc
  have ppc : p.pc = rightPc lay + 20 := by
    simp [p, SphincsVerifierFtsRightPath.rightPointers, execInstrBr, pc]
    bv_decide
  have src : p.getReg .x6 = BitVec.ofNat 64 sourceBase := by
    rw [(SphincsVerifierFtsRightPath.rightPointers_regs s).1]
    exact pointer
  have dst : p.getReg .x7 = 0x40028 :=
    (SphincsVerifierFtsRightPath.rightPointers_regs s).2
  have hc := rightCopy_block lay p ppc sourceBase src dst aligned bounded
  have cpc : c.pc = rightCurrentPc lay := by
    have h := copy20_final_pc p (rightCopyIndex lay) (by
      fin_cases lay <;> simpa [rightCopyIndex, rightPc, nodePc] using ppc)
    fin_cases lay <;> simpa [c, rightCopyIndex, rightCurrentPc, nodePc] using h
  have hq := rightCurrent_block lay c cpc
  have qpc : q.pc = rightCurrentPc lay + 16 := by
    simp [q, SphincsVerifierFtsRightPath.rightCurrentPointers,
      execInstrBr, cpc]
    bv_decide
  have qsrc : q.getReg .x6 = 0x44a00 :=
    (SphincsVerifierFtsRightPath.rightCurrentPointers_regs c).1
  have qdst : q.getReg .x7 = 0x4003c :=
    (SphincsVerifierFtsRightPath.rightCurrentPointers_regs c).2
  have hd := rightCurrentCopy_block lay q qpc qsrc qdst
  have dpc : d.pc = nodePc lay + 0x88 := by
    have h := copy20_final_pc q (rightCurrentCopyIndex lay) (by
      fin_cases lay <;> simpa [rightCurrentCopyIndex,
        rightCurrentPc, nodePc] using qpc)
    fin_cases lay <;> simpa [d, rightCurrentCopyIndex, nodePc] using h
  have hj := rightJoin_block lay d dpc
  exact ⟨by simpa [SphincsVerifierFtsRightPath.rightFinishState,
      p, c, q, d] using (((hp.append hc).append hq).append hd).append hj,
    by simpa [SphincsVerifierFtsRightPath.rightFinishState,
      p, c, q, d] using rightJoin_pc lay d dpc⟩

theorem leftPath_block (lay : Layer) (s : MachineState)
    (pc : s.pc = leftPc lay)
    (sourceBase : Nat)
    (pointer : s.getMem 0x43028 = BitVec.ofNat 64 sourceBase)
    (aligned : sourceBase % 4 = 0)
    (bounded : sourceBase + 20 ≤ MEMORY_BYTES) :
    OrdinarySteps SphincsImages.verify s 29
      (SphincsVerifierFtsLeftPath.leftPairState s) ∧
      (SphincsVerifierFtsLeftPath.leftPairState s).pc = nodePc lay + 0x100 := by
  let p := SphincsVerifierFtsLeftPath.leftCurrentPointers s
  let c := copyRootState p
  let q := SphincsVerifierFtsLeftPath.leftSiblingPointers c
  have hp := leftCurrent_block lay s pc
  have ppc : p.pc = leftPc lay + 16 := by
    simp [p, SphincsVerifierFtsLeftPath.leftCurrentPointers, execInstrBr, pc]
    bv_decide
  have psrc : p.getReg .x6 = 0x44a00 :=
    (SphincsVerifierFtsLeftPath.leftCurrentPointers_regs s).1
  have pdst : p.getReg .x7 = 0x40028 :=
    (SphincsVerifierFtsLeftPath.leftCurrentPointers_regs s).2
  have hc := leftCurrentCopy_block lay p ppc psrc pdst
  have cpc : c.pc = leftSiblingPc lay := by
    have h := copy20_final_pc p (leftCurrentCopyIndex lay) (by
      fin_cases lay <;> simpa [leftCurrentCopyIndex, leftPc, nodePc] using ppc)
    fin_cases lay <;> simpa [c, leftCurrentCopyIndex, leftSiblingPc, nodePc] using h
  have hq := leftSibling_block lay c cpc
  have qpc : q.pc = leftSiblingPc lay + 20 := by
    simp [q, SphincsVerifierFtsLeftPath.leftSiblingPointers, execInstrBr, cpc]
    bv_decide
  have cptr : c.getMem 0x43028 = BitVec.ofNat 64 sourceBase := by
    rw [SphincsVerifierFtsLeftPath.leftCurrentCopy_pointer p pdst,
      SphincsVerifierFtsLeftPath.leftCurrentPointers_mem]
    exact pointer
  have qsrc : q.getReg .x6 = BitVec.ofNat 64 sourceBase := by
    rw [(SphincsVerifierFtsLeftPath.leftSiblingPointers_regs c).1]
    exact cptr
  have qdst : q.getReg .x7 = 0x4003c :=
    (SphincsVerifierFtsLeftPath.leftSiblingPointers_regs c).2
  have hd := leftSiblingCopy_block lay q qpc sourceBase qsrc qdst aligned bounded
  have dpc : (copyRootState q).pc = nodePc lay + 0x100 := by
    have h := copy20_final_pc q (leftSiblingCopyIndex lay) (by
      fin_cases lay <;> simpa [leftSiblingCopyIndex, leftSiblingPc, nodePc] using qpc)
    fin_cases lay <;> simpa [leftSiblingCopyIndex, nodePc] using h
  exact ⟨by simpa [SphincsVerifierFtsLeftPath.leftPairState,
      p, c, q] using ((hp.append hc).append hq).append hd,
    by simpa [SphincsVerifierFtsLeftPath.leftPairState,
      p, c, q] using dpc⟩

#print axioms rightPointers_block
#print axioms rightCopy_block
#print axioms rightCurrent_block
#print axioms rightCurrentCopy_block
#print axioms rightJoin_block
#print axioms leftCurrent_block
#print axioms leftCurrentCopy_block
#print axioms leftSibling_block
#print axioms leftSiblingCopy_block
#print axioms rightPath_block
#print axioms leftPath_block

end SigGolfCandidate.SphincsVerifierXmssPair
