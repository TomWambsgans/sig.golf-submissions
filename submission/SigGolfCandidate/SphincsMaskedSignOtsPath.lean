import SigGolfCandidate.SphincsMaskedSignOtsParents

namespace SigGolfCandidate.SphincsMaskedSignOtsPath
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedSignOtsShift SphincsMaskedSignOtsTree SphincsMaskedSignOtsParents
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Output address of the authentication path, following the four-byte WOTS counter
and the 52 twenty-byte chain values. The five locations are layers one through five. -/
def pathPointer (location : Fin 5) : Nat :=
  if location.val = 0 then 0x21a80 else if location.val = 1 then 0x21ef8 else
  if location.val = 2 then 0x22370 else if location.val = 3 then 0x227e8 else 0x22c4c

def pointerHi (location : Fin 5) : Nat := if location.val = 4 then 35 else 34
def pointerLo (location : Fin 5) : Int :=
  if location.val = 0 then -1408 else if location.val = 1 then -264 else
  if location.val = 2 then 880 else if location.val = 3 then 2024 else -948

theorem pointer_parts (location : Fin 5) :
    BitVec.ofNat 64 (4096 * pointerHi location) +
      signExtend12 (BitVec.ofInt 12 (pointerLo location)) =
      BitVec.ofNat 64 (pathPointer location) := by
  fin_cases location <;> decide

theorem pointer_bound (location : Fin 5) :
    pathPointer location % 4 = 0 ∧ pathPointer location + 20 *
      SphincsMaskedSignOtsTree.Finish.width location ≤ 0x40000 := by
  fin_cases location <;> decide

/-- The entire24-instruction path prologue, starting at the proven subtree-root exit. -/
def initCode (location : Fin 5) : List (Word × Instr) := [
  (0x18d8, .LUI .x6 (BitVec.ofNat 20 (pointerHi location))),
  (0x18dc, .ADDI .x6 .x6 (BitVec.ofInt 12 (pointerLo location))),
  (0x18e0, .LUI .x28 67), (0x18e4, .ADDI .x28 .x28 160), (0x18e8, .SD .x28 .x6 0),
  (0x18ec, .LUI .x6 80), (0x18f0, .ADDI .x6 .x6 0),
  (0x18f4, .LUI .x28 67), (0x18f8, .ADDI .x28 .x28 192), (0x18fc, .SD .x28 .x6 0),
  (0x1900, .ADDI .x6 .x0 (BitVec.ofNat 12 (SphincsMaskedSignOtsTree.Finish.width location))),
  (0x1904, .LUI .x28 67), (0x1908, .ADDI .x28 .x28 144), (0x190c, .SD .x28 .x6 0),
  (0x1910, .ADDI .x6 .x0 0), (0x1914, .LUI .x28 67),
  (0x1918, .ADDI .x28 .x28 72), (0x191c, .SD .x28 .x6 0),
  (0x1920, .LUI .x28 67), (0x1924, .ADDI .x28 .x28 168), (0x1928, .LD .x6 .x28 0),
  (0x192c, .LUI .x28 67), (0x1930, .ADDI .x28 .x28 112), (0x1934, .SD .x28 .x6 0)]

def initialized (location : Fin 5) (s : MachineState) : MachineState := runSchedule (initCode location) s

theorem init_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (566+offset location) (initCode location) := by
  fin_cases location <;> rfl

theorem init_encoded (location : Fin 5) : ∀ e ∈ initCode location,
    instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  apply encoded_of_block _ (566+offset location) _ _ (init_image location)
  · have h := SphincsMaskedSignOtsParents.offset_bound location
    change 566+offset location+24≤11000
    omega
  · intro i
    have h : ∀ i : Fin (initCode location).length,
        (initCode location)[i.val].1=BitVec.ofNat 64 (0x18d8+4*i.val) := by
      fin_cases location <;> decide
    rw [h i,delta,←BitVec.ofNat_add]
    congr 1
    omega

theorem init_supported (location : Fin 5) : ∀ e ∈ initCode location, Supported e.2 := by
  fin_cases location <;> decide

theorem init_checked (location : Fin 5) (s : MachineState) (pc : s.pc=0x18d8) :
    Checked (initCode location) s := by
  fin_cases location <;>
    simp [initCode,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
      accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem init_block (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x18d8+delta location) :
    OrdinarySteps SphincsMaskedImages.sign s 24
      (shift (delta location) (initialized location (s.setPC 0x18d8))) := by
  have shifted := block_shift SphincsMaskedImages.sign (delta location) (initCode location)
    (init_supported location) (init_encoded location) (s.setPC 0x18d8)
    (init_checked location (s.setPC 0x18d8) rfl)
  rw [SphincsMaskedSignOtsDomain.rebase_eq _ _ s pc] at shifted
  exact shifted

theorem initialized_pc (location : Fin 5) (s : MachineState) (pc : s.pc=0x18d8) :
    (initialized location s).pc=0x1938 := by
  fin_cases location <;>
    simp [initialized,initCode,runSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

/-- The code's retained state is the actual source of all path-loop addresses. -/
structure PathControls (location : Fin 5) (s : MachineState) (level bit pointer : Nat) : Prop where
  base : s.getMem 0x430c0 = BitVec.ofNat 64 (SphincsMaskedSignOtsParents.Levels.cacheBase location level)
  count : s.getMem 0x43090 = BitVec.ofNat 64 (SphincsMaskedSignOtsParents.Levels.width location level)
  level : s.getMem 0x43048 = BitVec.ofNat 64 level
  bit : s.getMem 0x43070 = BitVec.ofNat 64 bit
  pointer : s.getMem 0x430a0 = BitVec.ofNat 64 pointer

theorem initialized_controls (location : Fin 5) (s : MachineState) (selected : Nat)
    (hs : s.getMem 0x430a8 = BitVec.ofNat 64 selected) :
    PathControls location (initialized location s) 0 selected (pathPointer location) := by
  fin_cases location <;> constructor <;>
    simp [initialized,initCode,runSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,hs,
      SphincsMaskedSignOtsParents.Levels.cacheBase,SphincsMaskedSignOtsParents.Levels.width,
      SphincsMaskedSignOtsParents.Levels.height,SphincsMaskedSignOtsTree.Finish.width,
      pointerHi,pointerLo,pathPointer]
  all_goals first | exact hs | decide


open SphincsVerifierMessageCopy SphincsVerifierFtsCopyAccess SphincsVerifierCopy
open SphincsMaskedSignForestParents

/-- The ten-word sibling copier is byte-for-byte identical in all five layers. -/
theorem copy_image (location : Fin 5) :
    (SphincsMaskedImages.sign.code.drop (604+offset location)).take 10 =
      (SphincsMaskedImages.sign.code.drop (604+offset (0 : Fin 5))).take 10 := by
  fin_cases location <;> rfl

theorem copy_word (location : Fin 5) (i : Fin 10) :
    SphincsMaskedImages.sign.code[604+offset location+i.val]? =
      SphincsMaskedImages.sign.code[604+offset (0 : Fin 5)+i.val]? := by
  have h := congrArg (fun words : List (BitVec 32) => words[i.val]?) (copy_image location)
  simpa only [List.getElem?_take_of_lt i.isLt,List.getElem?_drop] using h

theorem copy_code_zero : Copy20Code SphincsMaskedImages.sign (604+offset (0 : Fin 5)) := by
  constructor <;> intro i <;> fin_cases i <;> decide

theorem copy_code (location : Fin 5) : Copy20Code SphincsMaskedImages.sign (604+offset location) := by
  constructor
  · intro i
    have h := copy_word location ⟨2*i.val,by omega⟩
    have h0 := (copy_code_zero.load i)
    simpa [Nat.add_assoc] using (congrArg (fun w : Option (BitVec 32) => w.bind decodeInstruction) h).trans h0
  · intro i
    have h := copy_word location ⟨2*i.val+1,by omega⟩
    have h0 := (copy_code_zero.store i)
    simpa [Nat.add_assoc] using (congrArg (fun w : Option (BitVec 32) => w.bind decodeInstruction) h).trans h0

/-- One actual sibling copy: exact ten instructions and twenty copied bytes. -/
theorem copied_block (location : Fin 5) (s : MachineState) (source target : Nat)
    (pc : s.pc=0x1970+delta location)
    (src : s.getReg .x6=BitVec.ofNat 64 source)
    (dst : s.getReg .x7=BitVec.ofNat 64 target)
    (srcAlign : source%4=0) (srcBound : source+20≤0x60000)
    (dstAlign : target%4=0) (dstBound : target+20≤0x40000) :
    OrdinarySteps SphincsMaskedImages.sign s 10 (copyRootState s) := by
  have atIndex : s.pc=BitVec.ofNat 64 (0x1000+4*(604+offset location)) := by
    rw [pc,delta]
    change BitVec.ofNat 64 0x1970 + BitVec.ofNat 64 (4*offset location) = _
    rw [←BitVec.ofNat_add]
    congr 1
    omega
  exact copy20_block_general SphincsMaskedImages.sign (604+offset location) (copy_code location)
    s source target atIndex src dst srcAlign (by dsimp [MEMORY_BYTES];omega)
    dstAlign (by dsimp [MEMORY_BYTES];omega)
    (by have h := SphincsMaskedSignOtsParents.offset_bound location;omega)

theorem copied_word (s : MachineState) (source target : Nat)
    (src : s.getReg .x6=BitVec.ofNat 64 source)
    (dst : s.getReg .x7=BitVec.ofNat 64 target)
    (srcAlign : source%4=0) (srcBound : source+20≤0x60000)
    (dstAlign : target%4=0) (dstBound : target+20≤0x40000)
    (above : 0x50000≤source) (i : Fin 5) :
    (copyRootState s).getWord32 (BitVec.ofNat 64 (target+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (source+4*i.val)) := by
  exact SphincsMaskedSignForestParents.copy_data s source target
    (by omega) (by omega) srcAlign dstAlign (Or.inr (by omega)) src dst i

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPath.copied_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copied_block

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPath.copied_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copied_word

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPath.init_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms init_block

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPath.initialized_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initialized_controls

end SigGolfCandidate.SphincsMaskedSignOtsPath
