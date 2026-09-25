import SigGolfCandidate.SphincsMaskedSignOtsPathSibling

namespace SigGolfCandidate.SphincsMaskedSignOtsPathFinish
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedSignOtsShift SphincsMaskedSignOtsParents SphincsMaskedSignOtsTree
open SphincsMaskedSignOtsPath SphincsMaskedSignOtsPathSetup
open SphincsVerifierFtsRootCopy SphincsMaskedKeygenPrefix SphincsMaskedSignForestTail
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def finishCode (location : Fin 5) : List (Word × Instr) := [
  (0x1998, .LUI .x28 67),
  (0x199c, .ADDI .x28 .x28 160),
  (0x19a0, .LD .x6 .x28 0),
  (0x19a4, .ADDI .x6 .x6 20),
  (0x19a8, .LUI .x28 67),
  (0x19ac, .ADDI .x28 .x28 160),
  (0x19b0, .SD .x28 .x6 0),
  (0x19b4, .LUI .x28 67),
  (0x19b8, .ADDI .x28 .x28 192),
  (0x19bc, .LD .x6 .x28 0),
  (0x19c0, .LUI .x28 67),
  (0x19c4, .ADDI .x28 .x28 144),
  (0x19c8, .LD .x7 .x28 0),
  (0x19cc, .SLLI .x10 .x7 2),
  (0x19d0, .SLLI .x11 .x7 4),
  (0x19d4, .ADD .x10 .x10 .x11),
  (0x19d8, .ADD .x6 .x6 .x10),
  (0x19dc, .LUI .x28 67),
  (0x19e0, .ADDI .x28 .x28 192),
  (0x19e4, .SD .x28 .x6 0),
  (0x19e8, .LUI .x28 67),
  (0x19ec, .ADDI .x28 .x28 144),
  (0x19f0, .LD .x6 .x28 0),
  (0x19f4, .SRLI .x6 .x6 1),
  (0x19f8, .LUI .x28 67),
  (0x19fc, .ADDI .x28 .x28 144),
  (0x1a00, .SD .x28 .x6 0),
  (0x1a04, .LUI .x28 67),
  (0x1a08, .ADDI .x28 .x28 112),
  (0x1a0c, .LD .x6 .x28 0),
  (0x1a10, .SRLI .x6 .x6 1),
  (0x1a14, .LUI .x28 67),
  (0x1a18, .ADDI .x28 .x28 112),
  (0x1a1c, .SD .x28 .x6 0),
  (0x1a20, .LUI .x28 67),
  (0x1a24, .ADDI .x28 .x28 72),
  (0x1a28, .LD .x6 .x28 0),
  (0x1a2c, .ADDI .x6 .x6 1),
  (0x1a30, .LUI .x28 67),
  (0x1a34, .ADDI .x28 .x28 72),
  (0x1a38, .SD .x28 .x6 0),
  (0x1a3c, .LUI .x28 67),
  (0x1a40, .ADDI .x28 .x28 72),
  (0x1a44, .LD .x6 .x28 0),
  (0x1a48, .ADDI .x7 .x0 (BitVec.ofNat 12 (Levels.height location))),
  (0x1a4c, .BNE .x6 .x7 (-276))]

def finishState (location : Fin 5) (s : MachineState) : MachineState := runSchedule (finishCode location) s

def finished (location : Fin 5) (s : MachineState) : MachineState :=
  shift (delta location) (finishState location (s.setPC 0x1998))

theorem finish_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (614+offset location) (finishCode location) := by
  fin_cases location <;> rfl

theorem finish_encoded (location : Fin 5) : ∀ e∈finishCode location,
    instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  apply encoded_of_block _ (614+offset location) _ _ (finish_image location)
  · have h := SphincsMaskedSignOtsParents.offset_bound location
    change 614+offset location+46≤11000
    omega
  · intro i
    have h : ∀ i : Fin (finishCode location).length,
        (finishCode location)[i.val].1=BitVec.ofNat 64 (0x1998+4*i.val) := by
      fin_cases location <;> decide
    rw [h i,delta,←BitVec.ofNat_add]
    congr 1
    omega

theorem finish_supported (location : Fin 5) : ∀ e∈finishCode location,Supported e.2 := by
  fin_cases location <;> decide

theorem finish_checked (location : Fin 5) (s : MachineState) (pc : s.pc=0x1998) :
    Checked (finishCode location) s := by
  fin_cases location <;>
    simp [finishCode,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
      accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem finish_length (location : Fin 5) : (finishCode location).length=46 := by
  fin_cases location <;> rfl

theorem finish_block (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x1998+delta location) :
    OrdinarySteps SphincsMaskedImages.sign s 46 (finished location s) := by
  have trace := block_shift SphincsMaskedImages.sign (delta location) (finishCode location)
    (finish_supported location) (finish_encoded location) (s.setPC 0x1998)
    (finish_checked location (s.setPC 0x1998) rfl)
  rw [SphincsMaskedSignOtsDomain.rebase_eq _ _ s pc] at trace
  simpa only [finished,finishState,finish_length] using trace

def controlWrites : List Word := [0x430a0#64,0x430c0#64,0x43090#64,0x43070#64,0x43048#64]

theorem finish_frame (location : Fin 5) (s : MachineState) (a : Word)
    (outside : a∉controlWrites) :
    (finished location s).getMem a=s.getMem a := by
  simp only [controlWrites,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4⟩:=outside
  simp [finished,finishState,finishCode,runSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    h0,h1,h2,h3,h4]

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathFinish.finish_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finish_block

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathFinish.finish_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finish_frame

/-- Advance the five loop controls after one exact sibling copy. -/
theorem finished_controls (location : Fin 5) (s : MachineState)
    (level : Fin (Levels.height location)) (bit pointer : Nat)
    (ctrl : PathControls location s level.val bit pointer)
    (bitBound : bit<32) :
    PathControls location (finished location s) (level.val+1) (bit/2) (pointer+20) := by
  have base:=ctrl.base
  have count:=ctrl.count
  have lev:=ctrl.level
  have bits:=ctrl.bit
  have ptr:=ctrl.pointer
  change s.getMem 0x430c0#64 = _ at base
  change s.getMem 0x43090#64 = _ at count
  change s.getMem 0x43048#64 = _ at lev
  change s.getMem 0x43070#64 = _ at bits
  change s.getMem 0x430a0#64 = _ at ptr
  rcases Levels.layout location level with ⟨hbase, _, _, _, _, _, _, _, _, hwidth, _, _⟩
  have shift4 (n : Nat) : (BitVec.ofNat 64 n <<< 2) = BitVec.ofNat 64 (n*4) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    simp [BitVec.twoPow, ← BitVec.ofNat_mul]
  have shift16 (n : Nat) : (BitVec.ofNat 64 n <<< 4) = BitVec.ofNat 64 (n*16) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    simp [BitVec.twoPow, ← BitVec.ofNat_mul]
  constructor <;>
    simp [finished,finishState,finishCode,runSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,base,count,lev,bits,ptr,
      ofNat_half bit (by omega),BitVec.ofNat_add]
  · rw [shift4, shift16, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    omega
  · rw [ofNat_half _ (by omega)]
    congr 1
    omega

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathFinish.finished_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finished_controls


/-- The path back-edge is taken exactly until the last sibling level. -/
theorem finished_pc (location : Fin 5) (s : MachineState)
    (level : Fin (Levels.height location))
    (lev : s.getMem 0x43048#64 = BitVec.ofNat 64 level.val) :
    (finished location s).pc =
      if level.val+1=Levels.height location then 0x1a50+delta location
      else 0x1938+delta location := by
  simp [finished,finishState,finishCode,runSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,lev,delta]
  have hh : Levels.height location = 5 ∨ Levels.height location = 4 := by
    fin_cases location <;> simp [Levels.height]
  have hext : BitVec.signExtend 64 (BitVec.ofNat 12 (Levels.height location)) =
      BitVec.ofNat 64 (Levels.height location) := by
    rcases hh with h | h <;> simp [h]
  rw [hext, ← BitVec.ofNat_add]
  have hsmall : level.val + 1 < 2^64 := by
    have := level.isLt
    rcases hh with h | h <;> omega
  have hsmall2 : Levels.height location < 2^64 := by
    rcases hh with h | h <;> omega
  have heq : (BitVec.ofNat 64 (level.val+1) = BitVec.ofNat 64 (Levels.height location)) ↔
      level.val+1=Levels.height location := by
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall,
        Nat.mod_eq_of_lt hsmall2] at h'
      exact h'
    · intro h
      rw [h]
  simp only [heq]
  split_ifs <;> rfl

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathFinish.finished_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finished_pc

end SigGolfCandidate.SphincsMaskedSignOtsPathFinish
