import SigGolfCandidate.SphincsVerifierXmssPrefix
import SigGolfCandidate.SphincsVerifierFtsParentSetup

namespace SigGolfCandidate.SphincsVerifierXmssNodeReady
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsVerifierXmssNodeSite
open SigGolfCandidate.SphincsVerifierXmssPrefix
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierHeader
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def tagPc (lay : Layer) : Word := nodePc lay + 0x15c

def tagSchedule (lay : Layer) : List (Word × Instr) := [
  (tagPc lay, .ADDI .x6 .x0 769),
  (tagPc lay + 4, .LUI .x28 0x43),
  (tagPc lay + 8, .ADDI .x28 .x28 0),
  (tagPc lay + 12, .LD .x7 .x28 0),
  (tagPc lay + 16, .SLLI .x7 .x7 16),
  (tagPc lay + 20, .ADD .x6 .x6 .x7),
  (tagPc lay + 24, .LUI .x7 0x40),
  (tagPc lay + 28, .ADDI .x7 .x7 0),
  (tagPc lay + 32, .SW .x7 .x6 0)]

theorem tag_code (lay : Layer) : ∀ entry ∈ tagSchedule lay,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by
  fin_cases lay <;> decide

theorem tag_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = tagPc lay) : Checked (tagSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, tagSchedule, tagPc, nodePc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

def nodeTagState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 769)
  let s := execInstrBr s (.LUI .x28 0x43)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.SLLI .x7 .x7 16)
  let s := execInstrBr s (.ADD .x6 .x6 .x7)
  let s := execInstrBr s (.LUI .x7 0x40)
  let s := execInstrBr s (.ADDI .x7 .x7 0)
  execInstrBr s (.SW .x7 .x6 0)

theorem tag_block (lay : Layer) (s : MachineState)
    (pc : s.pc = tagPc lay) :
    OrdinarySteps SphincsImages.verify s 9 (nodeTagState s) := by
  have block := checked_sound _ (tagSchedule lay)
    (tag_code lay) s (tag_checked lay s pc)
  simpa [tagSchedule, runSchedule, nodeTagState] using block

def headerPc (lay : Layer) : Word := tagPc lay + 36

def headerSchedule (lay : Layer) : List (Word × Instr) := [
  (headerPc lay, .LUI .x28 0x43),
  (headerPc lay + 4, .ADDI .x28 .x28 16),
  (headerPc lay + 8, .LD .x6 .x28 0),
  (headerPc lay + 12, .SW .x7 .x6 4),
  (headerPc lay + 16, .LUI .x28 0x43),
  (headerPc lay + 20, .ADDI .x28 .x28 8),
  (headerPc lay + 24, .LD .x6 .x28 0),
  (headerPc lay + 28, .SD .x7 .x6 8),
  (headerPc lay + 32, .LUI .x28 0x43),
  (headerPc lay + 36, .ADDI .x28 .x28 24),
  (headerPc lay + 40, .LD .x6 .x28 0),
  (headerPc lay + 44, .SW .x7 .x6 16)]

theorem header_code (lay : Layer) : ∀ entry ∈ headerSchedule lay,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by
  fin_cases lay <;> decide

theorem header_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = headerPc lay)
    (destination : s.getReg .x7 = 0x40000) :
    Checked (headerSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, headerSchedule, headerPc, tagPc, nodePc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      destination, pc]

def nodeHeaderState (s : MachineState) : MachineState :=
  indexState (treeState (positionState s))

theorem header_block (lay : Layer) (s : MachineState)
    (pc : s.pc = headerPc lay)
    (destination : s.getReg .x7 = 0x40000) :
    OrdinarySteps SphincsImages.verify s 12 (nodeHeaderState s) := by
  have block := checked_sound _ (headerSchedule lay)
    (header_code lay) s (header_checked lay s pc destination)
  simpa [headerSchedule, runSchedule, nodeHeaderState,
    indexState, indexBeforeStore, treeState, treeBeforeStore,
    positionState, positionBeforeStore] using block

def parameterPc (lay : Layer) : Word := tagPc lay + 84

def parameterSchedule (lay : Layer) : List (Word × Instr) := [
  (parameterPc lay, .LUI .x6 0x23),
  (parameterPc lay + 4, .ADDI .x6 .x6 (-844)),
  (parameterPc lay + 8, .LUI .x7 0x40),
  (parameterPc lay + 12, .ADDI .x7 .x7 20)]

theorem parameter_code (lay : Layer) : ∀ entry ∈ parameterSchedule lay,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by
  fin_cases lay <;> decide

theorem parameter_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = parameterPc lay) : Checked (parameterSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, parameterSchedule, parameterPc, tagPc, nodePc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, signExtend12,
      MachineState.getReg_setReg_eq, pc]

theorem parameterPointers_block (lay : Layer) (s : MachineState)
    (pc : s.pc = parameterPc lay) :
    OrdinarySteps SphincsImages.verify s 4
      (SphincsVerifierFtsParentParameter.parameterPointers s) := by
  have block := checked_sound _ (parameterSchedule lay)
    (parameter_code lay) s (parameter_checked lay s pc)
  simpa [parameterSchedule, runSchedule,
    SphincsVerifierFtsParentParameter.parameterPointers] using block

def parameterCopyIndex (lay : Layer) : Nat := 1829 + 1011 * (5 - lay.val)

theorem parameterCopy_code (lay : Layer) :
    Copy20Code SphincsImages.verify (parameterCopyIndex lay) := by
  fin_cases lay <;> constructor <;> intro offset <;> fin_cases offset <;> decide

theorem parameterCopy_block (lay : Layer) (s : MachineState)
    (pc : s.pc = parameterPc lay + 16)
    (source : s.getReg .x6 = 0x22cb4)
    (destination : s.getReg .x7 = 0x40014) :
    OrdinarySteps SphincsImages.verify s 10 (copyRootState s) := by
  apply copy20_block_general SphincsImages.verify (parameterCopyIndex lay)
    (parameterCopy_code lay) s 0x22cb4 0x40014
  · fin_cases lay <;> simpa [parameterCopyIndex, parameterPc, tagPc, nodePc] using pc
  · exact source
  · exact destination
  · decide
  · decide
  · decide
  · decide
  · fin_cases lay <;> decide

def registersPc (lay : Layer) : Word := tagPc lay + 140

def registersSchedule (lay : Layer) : List (Word × Instr) := [
  (registersPc lay, .LUI .x10 0x40),
  (registersPc lay + 4, .ADDI .x10 .x10 0),
  (registersPc lay + 8, .ADDI .x11 .x0 640),
  (registersPc lay + 12, .LUI .x12 0x42),
  (registersPc lay + 16, .ADDI .x12 .x12 0),
  (registersPc lay + 20, .ADDI .x5 .x0 1)]

theorem registers_code (lay : Layer) : ∀ entry ∈ registersSchedule lay,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by
  fin_cases lay <;> decide

theorem registers_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = registersPc lay) : Checked (registersSchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, registersSchedule, registersPc, tagPc, nodePc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, signExtend12,
      MachineState.getReg_setReg_eq, pc]

theorem registers_block (lay : Layer) (s : MachineState)
    (pc : s.pc = registersPc lay) :
    OrdinarySteps SphincsImages.verify s 6 (hashRegistersState s) := by
  have block := checked_sound _ (registersSchedule lay)
    (registers_code lay) s (registers_checked lay s pc)
  simpa [registersSchedule, runSchedule, hashRegistersState] using block

theorem tag_pc (lay : Layer) (s : MachineState)
    (pc : s.pc = tagPc lay) : (nodeTagState s).pc = headerPc lay := by
  simp [nodeTagState, execInstrBr, pc, headerPc]
  bv_decide

theorem tag_pointer (s : MachineState) :
    (nodeTagState s).getReg .x7 = 0x40000 := by
  simp [nodeTagState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem header_pc (lay : Layer) (s : MachineState)
    (pc : s.pc = headerPc lay) :
    (nodeHeaderState s).pc = parameterPc lay := by
  fin_cases lay <;>
    simp [nodeHeaderState, indexState, indexBeforeStore, treeState,
      treeBeforeStore, positionState, positionBeforeStore,
      execInstrBr, pc, parameterPc, headerPc, tagPc, nodePc]

theorem parameter_pc (lay : Layer) (s : MachineState)
    (pc : s.pc = parameterPc lay) :
    (SphincsVerifierFtsParentParameter.parameterPointers s).pc =
      parameterPc lay + 16 := by
  simp [SphincsVerifierFtsParentParameter.parameterPointers, execInstrBr, pc]
  bv_decide

theorem parameterCopy_pc (lay : Layer) (s : MachineState)
    (pc : s.pc = parameterPc lay + 16) :
    (copyRootState s).pc = registersPc lay := by
  have h := copy20_final_pc s (parameterCopyIndex lay) (by
    fin_cases lay <;> simpa [parameterCopyIndex, parameterPc, tagPc, nodePc]
      using pc)
  fin_cases lay <;> simpa [parameterCopyIndex, registersPc, tagPc, nodePc]
    using h

theorem registers_pc (lay : Layer) (s : MachineState)
    (pc : s.pc = registersPc lay) :
    (hashRegistersState s).pc = nodeHashPc lay := by
  fin_cases lay <;>
    simp [hashRegistersState, execInstrBr, pc, registersPc, tagPc,
      nodeHashPc, nodePc]

def nodeReadyState (s : MachineState) : MachineState :=
  hashRegistersState
    (copyRootState (SphincsVerifierFtsParentParameter.parameterPointers
      (nodeHeaderState (nodeTagState s))))

theorem ready_block (lay : Layer) (s : MachineState)
    (pc : s.pc = tagPc lay) :
    OrdinarySteps SphincsImages.verify s 41 (nodeReadyState s) ∧
      (nodeReadyState s).pc = nodeHashPc lay ∧
      (nodeReadyState s).getReg .x10 = 0x40000 ∧
      (nodeReadyState s).getReg .x11 = 640 ∧
      (nodeReadyState s).getReg .x12 = 0x42000 ∧
      (nodeReadyState s).getReg .x5 = 1 := by
  let t := nodeTagState s
  let h := nodeHeaderState t
  let p := SphincsVerifierFtsParentParameter.parameterPointers h
  let c := copyRootState p
  have first := tag_block lay s pc
  have tpc := tag_pc lay s pc
  have dst := tag_pointer s
  have second := header_block lay t tpc dst
  have hpc := header_pc lay t tpc
  have third := parameterPointers_block lay h hpc
  have ppc := parameter_pc lay h hpc
  have src : p.getReg .x6 = 0x22cb4 :=
    (SphincsVerifierFtsParentParameter.parameterPointers_regs h).1
  have pdst : p.getReg .x7 = 0x40014 :=
    (SphincsVerifierFtsParentParameter.parameterPointers_regs h).2
  have fourth := parameterCopy_block lay p ppc src pdst
  have cpc := parameterCopy_pc lay p ppc
  have fifth := registers_block lay c cpc
  have regs := hashRegisters_ready c
  exact ⟨by simpa [nodeReadyState, t, h, p, c] using
      (((first.append second).append third).append fourth).append fifth,
    by simpa [nodeReadyState, t, h, p, c] using registers_pc lay c cpc,
    regs.1, regs.2.1, regs.2.2.1, regs.2.2.2⟩

#print axioms tag_block
#print axioms header_block
#print axioms parameterPointers_block
#print axioms parameterCopy_block
#print axioms registers_block
#print axioms ready_block

end SigGolfCandidate.SphincsVerifierXmssNodeReady
