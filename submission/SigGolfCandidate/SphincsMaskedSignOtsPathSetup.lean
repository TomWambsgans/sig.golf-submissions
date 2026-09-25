import SigGolfCandidate.SphincsMaskedSignOtsPath

namespace SigGolfCandidate.SphincsMaskedSignOtsPathSetup
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SigGolfCandidate.SphincsMaskedSignOtsPath
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
open SphincsMaskedSignOtsShift SphincsMaskedSignOtsTree SphincsMaskedSignOtsParents
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Compute the sibling cache address and signature-output address. -/
def setupCode : List (Word × Instr) := [
  (0x1938, .LUI .x28 67), (0x193c, .ADDI .x28 .x28 112),
  (0x1940, .LD .x6 .x28 0), (0x1944, .XORI .x6 .x6 1),
  (0x1948, .SLLI .x10 .x6 2), (0x194c, .SLLI .x11 .x6 4),
  (0x1950, .ADD .x10 .x10 .x11),
  (0x1954, .LUI .x28 67), (0x1958, .ADDI .x28 .x28 192),
  (0x195c, .LD .x6 .x28 0), (0x1960, .ADD .x6 .x6 .x10),
  (0x1964, .LUI .x28 67), (0x1968, .ADDI .x28 .x28 160),
  (0x196c, .LD .x7 .x28 0)]

def setupState (location : Fin 5) (s : MachineState) : MachineState :=
  runSchedule (schedule (delta location) setupCode) s

theorem setup_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (590+offset location) setupCode := by
  fin_cases location <;> rfl

theorem setup_encoded (location : Fin 5) : ∀ e ∈ setupCode,
    instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  apply encoded_of_block _ (590+offset location) _ _ (setup_image location)
  · have h := SphincsMaskedSignOtsParents.offset_bound location
    change 590+offset location+14≤11000
    omega
  · intro i
    have h : ∀ i : Fin setupCode.length,
        setupCode[i.val].1=BitVec.ofNat 64 (0x1938+4*i.val) := by decide
    rw [h i,delta,←BitVec.ofNat_add]
    congr 1
    omega

theorem setup_checked (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x1938+delta location) : Checked (schedule (delta location) setupCode) s := by
  fin_cases location <;>
    simp [schedule,setupCode,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
      accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]
  all_goals decide

theorem setup_block (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x1938+delta location) :
    OrdinarySteps SphincsMaskedImages.sign s 14 (setupState location s) := by
  have encoded : ∀ e∈schedule (delta location) setupCode,
      instructionAt SphincsMaskedImages.sign e.1=some (.base e.2) := by
    intro e he
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp he
    exact setup_encoded location original member
  have trace := checked_sound SphincsMaskedImages.sign (schedule (delta location) setupCode)
    encoded s (setup_checked location s pc)
  simpa [setupState,schedule,setupCode] using trace

theorem setup_pc (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x1938+delta location) :
    (setupState location s).pc=0x1970+delta location := by
  simp [setupState,schedule,setupCode,runSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]
  fin_cases location <;> decide

theorem setup_regs (location : Fin 5) (s : MachineState) (level bit pointer : Nat)
    (ctrl : PathControls location s level bit pointer) :
    (setupState location s).getReg .x6 = BitVec.ofNat 64
      (Levels.cacheBase location level + 20 * (bit ^^^ 1)) ∧
    (setupState location s).getReg .x7 = BitVec.ofNat 64 pointer := by
  have hb := ctrl.bit
  have hbase := ctrl.base
  have hp := ctrl.pointer
  change s.getMem 0x43070#64 = _ at hb
  change s.getMem 0x430c0#64 = _ at hbase
  change s.getMem 0x430a0#64 = _ at hp
  simp [setupState,schedule,setupCode,runSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,hb,hbase,hp]
  change BitVec.ofNat 64 (Levels.cacheBase location level) +
    (((BitVec.ofNat 64 bit ^^^ BitVec.ofNat 64 1) <<< 2) +
    ((BitVec.ofNat 64 bit ^^^ BitVec.ofNat 64 1) <<< 4)) = _
  rw [← BitVec.ofNat_xor]
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 (Levels.cacheBase location level) +
    (BitVec.ofNat 64 (bit ^^^ 1) * BitVec.ofNat 64 4 +
    BitVec.ofNat 64 (bit ^^^ 1) * BitVec.ofNat 64 16) = _
  rw [← BitVec.ofNat_mul,← BitVec.ofNat_mul,← BitVec.ofNat_add,← BitVec.ofNat_add]
  congr 1
  omega

theorem setup_frame (location : Fin 5) (s : MachineState) (a : Word) :
    (setupState location s).getMem a=s.getMem a := by
  simp [setupState,schedule,setupCode,runSchedule,execInstrBr]

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathSetup.setup_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setup_block

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathSetup.setup_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setup_regs

end SigGolfCandidate.SphincsMaskedSignOtsPathSetup
