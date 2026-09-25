import SigGolfCandidate.SphincsMaskedSignHonestAuthentication

namespace SigGolfCandidate.SphincsMaskedSignNonceTrial
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsBridge SphincsSecurity SphincsMaskedMaskSemantics
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def initSchedule : List (Word × Instr) := [
  (0x1510, .ADDI .x6 .x0 0),
  (0x1514, .LUI .x28 67),
  (0x1518, .ADDI .x28 .x28 152),
  (0x151c, .SD .x28 .x6 0)]

def controlSchedule : List (Word × Instr) := [
  (0x1520, .LUI .x28 67),
  (0x1524, .ADDI .x28 .x28 152),
  (0x1528, .LD .x6 .x28 0),
  (0x152c, .LUI .x28 67),
  (0x1530, .ADDI .x28 .x28 16),
  (0x1534, .SD .x28 .x6 0),
  (0x1538, .ADDI .x6 .x0 0),
  (0x153c, .LUI .x28 67),
  (0x1540, .ADDI .x28 .x28 24),
  (0x1544, .SD .x28 .x6 0)]

def keySchedule : List (Word × Instr) := [
  (0x1548, .ADDI .x6 .x0 32),
  (0x154c, .LUI .x7 64),
  (0x1550, .ADDI .x7 .x7 40),
  (0x1554, .ADDI .x10 .x0 4),
  (0x1558, .LD .x11 .x6 0),
  (0x155c, .SD .x7 .x11 0),
  (0x1560, .ADDI .x6 .x6 8),
  (0x1564, .ADDI .x7 .x7 8),
  (0x1568, .ADDI .x10 .x10 (-1)),
  (0x156c, .BNE .x10 .x0 (-20)),
  (0x1558, .LD .x11 .x6 0),
  (0x155c, .SD .x7 .x11 0),
  (0x1560, .ADDI .x6 .x6 8),
  (0x1564, .ADDI .x7 .x7 8),
  (0x1568, .ADDI .x10 .x10 (-1)),
  (0x156c, .BNE .x10 .x0 (-20)),
  (0x1558, .LD .x11 .x6 0),
  (0x155c, .SD .x7 .x11 0),
  (0x1560, .ADDI .x6 .x6 8),
  (0x1564, .ADDI .x7 .x7 8),
  (0x1568, .ADDI .x10 .x10 (-1)),
  (0x156c, .BNE .x10 .x0 (-20)),
  (0x1558, .LD .x11 .x6 0),
  (0x155c, .SD .x7 .x11 0),
  (0x1560, .ADDI .x6 .x6 8),
  (0x1564, .ADDI .x7 .x7 8),
  (0x1568, .ADDI .x10 .x10 (-1)),
  (0x156c, .BNE .x10 .x0 (-20))]

def messageSchedule : List (Word × Instr) := [
  (0x1570, .ADDI .x6 .x0 0),
  (0x1574, .LUI .x7 64),
  (0x1578, .ADDI .x7 .x7 72),
  (0x157c, .ADDI .x10 .x0 4),
  (0x1580, .LD .x11 .x6 0),
  (0x1584, .SD .x7 .x11 0),
  (0x1588, .ADDI .x6 .x6 8),
  (0x158c, .ADDI .x7 .x7 8),
  (0x1590, .ADDI .x10 .x10 (-1)),
  (0x1594, .BNE .x10 .x0 (-20)),
  (0x1580, .LD .x11 .x6 0),
  (0x1584, .SD .x7 .x11 0),
  (0x1588, .ADDI .x6 .x6 8),
  (0x158c, .ADDI .x7 .x7 8),
  (0x1590, .ADDI .x10 .x10 (-1)),
  (0x1594, .BNE .x10 .x0 (-20)),
  (0x1580, .LD .x11 .x6 0),
  (0x1584, .SD .x7 .x11 0),
  (0x1588, .ADDI .x6 .x6 8),
  (0x158c, .ADDI .x7 .x7 8),
  (0x1590, .ADDI .x10 .x10 (-1)),
  (0x1594, .BNE .x10 .x0 (-20)),
  (0x1580, .LD .x11 .x6 0),
  (0x1584, .SD .x7 .x11 0),
  (0x1588, .ADDI .x6 .x6 8),
  (0x158c, .ADDI .x7 .x7 8),
  (0x1590, .ADDI .x10 .x10 (-1)),
  (0x1594, .BNE .x10 .x0 (-20))]

def headerSchedule : List (Word × Instr) := [
  (0x1598, .ADDI .x6 .x0 1793),
  (0x159c, .LUI .x28 67),
  (0x15a0, .ADDI .x28 .x28 0),
  (0x15a4, .LD .x7 .x28 0),
  (0x15a8, .SLLI .x7 .x7 16),
  (0x15ac, .ADD .x6 .x6 .x7),
  (0x15b0, .LUI .x7 64),
  (0x15b4, .ADDI .x7 .x7 0),
  (0x15b8, .SW .x7 .x6 0),
  (0x15bc, .LUI .x28 67),
  (0x15c0, .ADDI .x28 .x28 16),
  (0x15c4, .LD .x6 .x28 0),
  (0x15c8, .SW .x7 .x6 4),
  (0x15cc, .LUI .x28 67),
  (0x15d0, .ADDI .x28 .x28 8),
  (0x15d4, .LD .x6 .x28 0),
  (0x15d8, .SD .x7 .x6 8),
  (0x15dc, .LUI .x28 67),
  (0x15e0, .ADDI .x28 .x28 24),
  (0x15e4, .LD .x6 .x28 0),
  (0x15e8, .SW .x7 .x6 16),
  (0x15ec, .ADDI .x6 .x0 116),
  (0x15f0, .LUI .x7 64),
  (0x15f4, .ADDI .x7 .x7 20),
  (0x15f8, .LWU .x13 .x6 0),
  (0x15fc, .SW .x7 .x13 0),
  (0x1600, .LWU .x13 .x6 4),
  (0x1604, .SW .x7 .x13 4),
  (0x1608, .LWU .x13 .x6 8),
  (0x160c, .SW .x7 .x13 8),
  (0x1610, .LWU .x13 .x6 12),
  (0x1614, .SW .x7 .x13 12),
  (0x1618, .LWU .x13 .x6 16),
  (0x161c, .SW .x7 .x13 16),
  (0x1620, .LUI .x10 64),
  (0x1624, .ADDI .x10 .x10 0),
  (0x1628, .ADDI .x11 .x0 832),
  (0x162c, .LUI .x12 66),
  (0x1630, .ADDI .x12 .x12 0),
  (0x1634, .ADDI .x5 .x0 1)]

def init (s : MachineState) := runSchedule initSchedule s
def control (s : MachineState) := runSchedule controlSchedule s
def keyCopy (s : MachineState) := runSchedule keySchedule s
def messageCopy (s : MachineState) := runSchedule messageSchedule s
def header (s : MachineState) := runSchedule headerSchedule s
def noncePrepare (s : MachineState) := header (messageCopy (keyCopy (control s)))

theorem init_code : ∀ e ∈ initSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem init_checked (s : MachineState) (pc : s.pc = 0x1510) : Checked initSchedule s := by
  simp [Checked,initSchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem init_trace (s : MachineState) (pc : s.pc = 0x1510) :
    OrdinarySteps SphincsMaskedImages.sign s 4 (init s) :=
  checked_sound _ initSchedule init_code s (init_checked s pc)
theorem init_pc (s : MachineState) (pc : s.pc = 0x1510) : (init s).pc = 0x1520 := by
  simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem init_counter (s : MachineState) : (init s).getMem 0x43098#64 = 0 := by
  simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem control_code : ∀ e ∈ controlSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem control_checked (s : MachineState) (pc : s.pc = 0x1520) : Checked controlSchedule s := by
  simp [Checked,controlSchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]
theorem control_block (s : MachineState) (pc : s.pc = 0x1520) :
    OrdinarySteps SphincsMaskedImages.sign s 10 (control s) :=
  checked_sound _ controlSchedule control_code s (control_checked s pc)
theorem control_pc (s : MachineState) (pc : s.pc = 0x1520) : (control s).pc = 0x1548 := by
  simp [control,runSchedule,controlSchedule,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]

theorem keyCopy_code : ∀ e ∈ keySchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem keyCopy_checked (s : MachineState) (pc : s.pc = 0x1548) : Checked keySchedule s := by
  simp [Checked,keySchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]
theorem keyCopy_block (s : MachineState) (pc : s.pc = 0x1548) :
    OrdinarySteps SphincsMaskedImages.sign s 28 (keyCopy s) :=
  checked_sound _ keySchedule keyCopy_code s (keyCopy_checked s pc)
theorem keyCopy_pc (s : MachineState) (pc : s.pc = 0x1548) : (keyCopy s).pc = 0x1570 := by
  simp [keyCopy,runSchedule,keySchedule,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]

theorem messageCopy_code : ∀ e ∈ messageSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem messageCopy_checked (s : MachineState) (pc : s.pc = 0x1570) : Checked messageSchedule s := by
  simp [Checked,messageSchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]
theorem messageCopy_block (s : MachineState) (pc : s.pc = 0x1570) :
    OrdinarySteps SphincsMaskedImages.sign s 28 (messageCopy s) :=
  checked_sound _ messageSchedule messageCopy_code s (messageCopy_checked s pc)
theorem messageCopy_pc (s : MachineState) (pc : s.pc = 0x1570) : (messageCopy s).pc = 0x1598 := by
  simp [messageCopy,runSchedule,messageSchedule,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]

theorem header_code : ∀ e ∈ headerSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem header_checked (s : MachineState) (pc : s.pc = 0x1598) : Checked headerSchedule s := by
  simp [Checked,headerSchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]
theorem header_block (s : MachineState) (pc : s.pc = 0x1598) :
    OrdinarySteps SphincsMaskedImages.sign s 40 (header s) :=
  checked_sound _ headerSchedule header_code s (header_checked s pc)
theorem header_pc (s : MachineState) (pc : s.pc = 0x1598) : (header s).pc = 0x1638 := by
  simp [header,runSchedule,headerSchedule,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]

theorem nonce_block (s : MachineState) (pc : s.pc = 0x1520) :
    OrdinarySteps SphincsMaskedImages.sign s 106 (noncePrepare s) := by
  have a := control_pc s pc
  have b := keyCopy_pc _ a
  have c := messageCopy_pc _ b
  exact SphincsVerifierFtsRootCopy.ordinary_trans _ _ _ _ 10 96 (control_block s pc)
    (SphincsVerifierFtsRootCopy.ordinary_trans _ _ _ _ 28 68 (keyCopy_block _ a)
      (SphincsVerifierFtsRootCopy.ordinary_trans _ _ _ _ 28 40 (messageCopy_block _ b) (header_block _ c)))
theorem nonce_pc (s : MachineState) (pc : s.pc = 0x1520) : (noncePrepare s).pc = 0x1638 :=
  header_pc _ (messageCopy_pc _ (keyCopy_pc _ (control_pc s pc)))
theorem header_registers (s : MachineState) :
    (header s).getReg .x10 = 0x40000 ∧ (header s).getReg .x11 = 832 ∧
    (header s).getReg .x12 = 0x42000 ∧ (header s).getReg .x5 = 1 := by
  simp [header,runSchedule,headerSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,MachineState.setWord32]
theorem nonce_registers (s : MachineState) :
    (noncePrepare s).getReg .x10 = 0x40000 ∧ (noncePrepare s).getReg .x11 = 832 ∧
    (noncePrepare s).getReg .x12 = 0x42000 ∧ (noncePrepare s).getReg .x5 = 1 := header_registers _

/-- Reusable trial invariant. The stored 64-bit counter is bounded to match the
    specification's 32-bit trial and the bytecode's 2^20 exhaustion check. -/
structure Context (s : MachineState) (parameter : Digest) (seed : MasterSeed)
    (message : SphincsSecurity.Message) (trial : Nat) : Prop where
  layer : s.getMem 0x43000#64 = 0
  tree : s.getMem 0x43008#64 = 0
  counter : s.getMem 0x43098#64 = BitVec.ofNat 64 trial
  bounded : trial < 2^20
  parameterWords : Words20 s 0x74 parameter
  keyWords : Words32 s seed
  messageWords : ∀ i : Fin 8, s.getWord32 (BitVec.ofNat 64 (4*i.val)) = message.extractLsb' (32*i.val) 32

def queryWord (s : MachineState) (i : Fin 26) : BitVec 32 :=
  if i.val = 0 then (1793#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val = 1 then (s.getMem 0x43098).setWidth 32
  else if i.val = 2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val = 3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val = 4 then 0
  else if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x74 + 4*(i.val-5)))
  else if i.val < 18 then s.getWord32 (BitVec.ofNat 64 (0x20 + 4*(i.val-10)))
  else s.getWord32 (BitVec.ofNat 64 (4*(i.val-18)))

theorem keyCopy_frame (s : MachineState) (a : Word)
    (outside : a.toNat < 0x40028 ∨ 0x40048 ≤ a.toNat) :
    (keyCopy s).getMem a = s.getMem a := by
  have ne (b : Word) (lo : 0x40028 ≤ b.toNat) (hi : b.toNat < 0x40048) : a ≠ b := by
    intro eq; rw [eq] at outside; rcases outside with h | h <;> omega
  simp [keyCopy,runSchedule,keySchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,ne]

theorem messageCopy_frame (s : MachineState) (a : Word)
    (outside : a.toNat < 0x40048 ∨ 0x40068 ≤ a.toNat) :
    (messageCopy s).getMem a = s.getMem a := by
  have ne (b : Word) (lo : 0x40048 ≤ b.toNat) (hi : b.toNat < 0x40068) : a ≠ b := by
    intro eq; rw [eq] at outside; rcases outside with h | h <;> omega
  simp [messageCopy,runSchedule,messageSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,ne]

theorem header_frame (s : MachineState) (a : Word)
    (outside : a.toNat < 0x40000 ∨ 0x40028 ≤ a.toNat) :
    (header s).getMem a = s.getMem a := by
  have ne (b : Word) (lo : 0x40000 ≤ b.toNat) (hi : b.toNat < 0x40028) : a ≠ b := by
    intro eq; rw [eq] at outside; rcases outside with h | h <;> omega
  simp [header,runSchedule,headerSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,ne]

theorem control_mem (s : MachineState) (a : Word) :
    (control s).getMem a = if a = 0x43018#64 then 0 else
      if a = 0x43010#64 then s.getMem 0x43098 else s.getMem a := by
  by_cases h1 : a = 0x43018#64 <;> by_cases h2 : a = 0x43010#64 <;>
    simp [control,runSchedule,controlSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h1,h2]

def headerWord (s : MachineState) (i : Fin 26) : BitVec 32 :=
  if i.val = 0 then (1793#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val = 1 then (s.getMem 0x43010).setWidth 32
  else if i.val = 2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val = 3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val = 4 then (s.getMem 0x43018).setWidth 32
  else if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x74 + 4*(i.val-5)))
  else s.getWord32 (BitVec.ofNat 64 (0x40000+4*i.val))
def keyWord (s : MachineState) (i : Fin 26) : BitVec 32 :=
  if 10 ≤ i.val ∧ i.val < 18 then s.getWord32 (BitVec.ofNat 64 (0x20 + 4*(i.val-10)))
  else s.getWord32 (BitVec.ofNat 64 (0x40000+4*i.val))
def messageWord (s : MachineState) (i : Fin 26) : BitVec 32 :=
  if 18 ≤ i.val then s.getWord32 (BitVec.ofNat 64 (4*(i.val-18)))
  else s.getWord32 (BitVec.ofNat 64 (0x40000+4*i.val))

theorem header_words (s : MachineState) (i : Fin 26) :
    (header s).getWord32 (BitVec.ofNat 64 (0x40000+4*i.val)) = headerWord s i := by
  fin_cases i <;>
    simp [header,runSchedule,headerSchedule,execInstrBr,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,headerWord]

theorem keyCopy_words (s : MachineState) (i : Fin 26) :
    (keyCopy s).getWord32 (BitVec.ofNat 64 (0x40000+4*i.val)) = keyWord s i := by
  fin_cases i <;>
    simp [keyCopy,runSchedule,keySchedule,execInstrBr,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,keyWord]

theorem messageCopy_words (s : MachineState) (i : Fin 26) :
    (messageCopy s).getWord32 (BitVec.ofNat 64 (0x40000+4*i.val)) = messageWord s i := by
  fin_cases i <;>
    simp [messageCopy,runSchedule,messageSchedule,execInstrBr,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,messageWord]

theorem nonce_words (s : MachineState) (i : Fin 26) :
    (noncePrepare s).getWord32 (BitVec.ofNat 64 (0x40000+4*i.val)) = queryWord s i := by
  rw [noncePrepare,header_words]
  fin_cases i
  · simp [headerWord,messageCopy_words _ 0,messageWord,keyCopy_words _ 0,keyWord,queryWord,
      MachineState.getWord32,alignToDword,byteOffset,messageCopy_frame,keyCopy_frame,control_mem]
  · simp [headerWord,messageCopy_words _ 1,messageWord,keyCopy_words _ 1,keyWord,queryWord,
      MachineState.getWord32,alignToDword,byteOffset,messageCopy_frame,keyCopy_frame,control_mem]
  · simp [headerWord,messageCopy_words _ 2,messageWord,keyCopy_words _ 2,keyWord,queryWord,
      MachineState.getWord32,alignToDword,byteOffset,messageCopy_frame,keyCopy_frame,control_mem]
  · simp [headerWord,messageCopy_words _ 3,messageWord,keyCopy_words _ 3,keyWord,queryWord,
      MachineState.getWord32,alignToDword,byteOffset,messageCopy_frame,keyCopy_frame,control_mem]
  · simp [headerWord,messageCopy_words _ 4,messageWord,keyCopy_words _ 4,keyWord,queryWord,
      MachineState.getWord32,alignToDword,byteOffset,messageCopy_frame,keyCopy_frame,control_mem]
  · simp [headerWord,messageCopy_words _ 5,messageWord,keyCopy_words _ 5,keyWord,queryWord,
      MachineState.getWord32,alignToDword,byteOffset,messageCopy_frame,keyCopy_frame,control_mem]
  · simp [headerWord,messageCopy_words _ 6,messageWord,keyCopy_words _ 6,keyWord,queryWord,
      MachineState.getWord32,alignToDword,byteOffset,messageCopy_frame,keyCopy_frame,control_mem]
  · simp [headerWord,messageCopy_words _ 7,messageWord,keyCopy_words _ 7,keyWord,queryWord,
      MachineState.getWord32,alignToDword,byteOffset,messageCopy_frame,keyCopy_frame,control_mem]
  · simp [headerWord,messageCopy_words _ 8,messageWord,keyCopy_words _ 8,keyWord,queryWord,
      MachineState.getWord32,alignToDword,byteOffset,messageCopy_frame,keyCopy_frame,control_mem]
  · simp [headerWord,messageCopy_words _ 9,messageWord,keyCopy_words _ 9,keyWord,queryWord,
      MachineState.getWord32,alignToDword,byteOffset,messageCopy_frame,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262184) = _
    have hm := messageCopy_words (keyCopy (control s)) 10
    norm_num [messageWord] at hm
    rw [hm]
    have hk := keyCopy_words (control s) 10
    norm_num [keyWord] at hk
    rw [hk]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262188) = _
    have hm := messageCopy_words (keyCopy (control s)) 11
    norm_num [messageWord] at hm
    rw [hm]
    have hk := keyCopy_words (control s) 11
    norm_num [keyWord] at hk
    rw [hk]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262192) = _
    have hm := messageCopy_words (keyCopy (control s)) 12
    norm_num [messageWord] at hm
    rw [hm]
    have hk := keyCopy_words (control s) 12
    norm_num [keyWord] at hk
    rw [hk]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262196) = _
    have hm := messageCopy_words (keyCopy (control s)) 13
    norm_num [messageWord] at hm
    rw [hm]
    have hk := keyCopy_words (control s) 13
    norm_num [keyWord] at hk
    rw [hk]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262200) = _
    have hm := messageCopy_words (keyCopy (control s)) 14
    norm_num [messageWord] at hm
    rw [hm]
    have hk := keyCopy_words (control s) 14
    norm_num [keyWord] at hk
    rw [hk]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262204) = _
    have hm := messageCopy_words (keyCopy (control s)) 15
    norm_num [messageWord] at hm
    rw [hm]
    have hk := keyCopy_words (control s) 15
    norm_num [keyWord] at hk
    rw [hk]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262208) = _
    have hm := messageCopy_words (keyCopy (control s)) 16
    norm_num [messageWord] at hm
    rw [hm]
    have hk := keyCopy_words (control s) 16
    norm_num [keyWord] at hk
    rw [hk]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262212) = _
    have hm := messageCopy_words (keyCopy (control s)) 17
    norm_num [messageWord] at hm
    rw [hm]
    have hk := keyCopy_words (control s) 17
    norm_num [keyWord] at hk
    rw [hk]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262216) = _
    have hm := messageCopy_words (keyCopy (control s)) 18
    norm_num [messageWord] at hm
    rw [hm]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262220) = _
    have hm := messageCopy_words (keyCopy (control s)) 19
    norm_num [messageWord] at hm
    rw [hm]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262224) = _
    have hm := messageCopy_words (keyCopy (control s)) 20
    norm_num [messageWord] at hm
    rw [hm]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262228) = _
    have hm := messageCopy_words (keyCopy (control s)) 21
    norm_num [messageWord] at hm
    rw [hm]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262232) = _
    have hm := messageCopy_words (keyCopy (control s)) 22
    norm_num [messageWord] at hm
    rw [hm]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262236) = _
    have hm := messageCopy_words (keyCopy (control s)) 23
    norm_num [messageWord] at hm
    rw [hm]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262240) = _
    have hm := messageCopy_words (keyCopy (control s)) 24
    norm_num [messageWord] at hm
    rw [hm]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]
  · change (messageCopy (keyCopy (control s))).getWord32 (BitVec.ofNat 64 262244) = _
    have hm := messageCopy_words (keyCopy (control s)) 25
    norm_num [messageWord] at hm
    rw [hm]
    simp [queryWord,MachineState.getWord32,alignToDword,byteOffset,keyCopy_frame,control_mem]

def payload (parameter : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (trial : Nat) : List Byte :=
  (randomizerHashInput parameter seed message (BitVec.ofNat 32 trial)).map UInt8.toBitVec

theorem payload_length (parameter : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (trial : Nat) : (payload parameter seed message trial).length = 104 := by
  simp [payload,randomizerHashInput,fieldBytes,bytesLE]

theorem prepared_byte (s : MachineState) (i : Fin 104) :
    (noncePrepare s).getByte (BitVec.ofNat 64 (0x40000+i.val)) =
      (queryWord s ⟨i.val/4,by omega⟩).extractLsb' (8*(i.val%4)) 8 := by
  have h := SphincsVerifierFtsGenericBytes.variableWord_byte (noncePrepare s)
    (0x40000+4*(i.val/4)) (by omega) (by omega) 0 ⟨i.val%4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  rw [show 0x40000+4*(i.val/4)+i.val%4=0x40000+i.val by omega] at h
  rw [h,nonce_words s ⟨i.val/4,by omega⟩]

theorem context_byte (s : MachineState) (parameter : Digest) (seed : MasterSeed)
    (message : SphincsSecurity.Message) (trial : Nat)
    (ctx : Context s parameter seed message trial) (i : Fin 104) :
    (queryWord s ⟨i.val/4,by omega⟩).extractLsb' (8*(i.val%4)) 8 =
      (payload parameter seed message trial)[i.val]'(by rw [payload_length];exact i.isLt) := by
  obtain ⟨layer,tree,counter,bounded,par,key,msg⟩ := ctx
  have p0 := par 0
  have p1 := par 1
  have p2 := par 2
  have p3 := par 3
  have p4 := par 4
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  have k3 := key 3
  have k4 := key 4
  have k5 := key 5
  have k6 := key 6
  have k7 := key 7
  have m0 := msg 0
  have m1 := msg 1
  have m2 := msg 2
  have m3 := msg 3
  have m4 := msg 4
  have m5 := msg 5
  have m6 := msg 6
  have m7 := msg 7
  norm_num at p0 p1 p2 p3 p4 k0 k1 k2 k3 k4 k5 k6 k7 m0 m1 m2 m3 m4 m5 m6 m7
  fin_cases i <;>
    simp [queryWord,layer,tree,counter,p0,p1,p2,p3,p4,k0,k1,k2,k3,k4,k5,k6,k7,m0,m1,m2,m3,m4,m5,m6,m7,extractWord32,
      payload,randomizerHashInput,fieldBytes,bytesLE,protocolDomainSep]
  all_goals
    ext b hb
    interval_cases b <;> simp [BitVec.getLsbD_eq_getElem]
  all_goals exact BitVec.getLsbD_eq_getElem (by decide)

theorem query_eq (s : MachineState) (parameter : Digest) (seed : MasterSeed)
    (message : SphincsSecurity.Message) (trial : Nat)
    (ctx : Context s parameter seed message trial) :
    hashInput (noncePrepare s) =
      toQuery (randomizerHashInput parameter seed message (BitVec.ofNat 32 trial)) := by
  apply Serialization.hashInput_of_list (noncePrepare s) 0x40000 (payload parameter seed message trial)
  · exact (nonce_registers s).1
  · rw [payload_length,(nonce_registers s).2.1]; rfl
  · intro i hi
    have bound : i < 104 := by simpa only [payload_length] using hi
    rw [prepared_byte s ⟨i,bound⟩]
    exact context_byte s parameter seed message trial ctx ⟨i,bound⟩

def nonceAnswer (hash : Hash) (s : MachineState) : MachineState :=
  writeHash (noncePrepare s) (hash (hashInput (noncePrepare s)))

theorem nonce_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x1520) :
    Trace hash SphincsMaskedImages.sign s 107 122 1 2 (nonceAnswer hash s) := by
  obtain ⟨src,bits,dst,service⟩ := nonce_registers s
  have fetched : fetch SphincsMaskedImages.sign (noncePrepare s) = some (.base .ECALL) := by
    rw [SphincsVerifierFtsRootCopy.fetch_at,nonce_pc s pc]; decide
  have valid : hashArgumentsValid (noncePrepare s) = true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (noncePrepare s)).1 = 832 := by simp [hashInput,bits]
  have step := Trace.hash (hash := hash) (image := SphincsMaskedImages.sign)
    (noncePrepare s) _ 0 0 0 0 fetched service valid (Trace.refl _)
  have one : Trace hash SphincsMaskedImages.sign (noncePrepare s) 1 16 1 2 (nonceAnswer hash s) := by
    simpa [nonceAnswer,len,show compressions 832 = 2 from rfl] using step
  exact (nonce_block s pc).trace.trans one

theorem answer_words (hash : Hash) (s : MachineState) (i : Fin 5) :
    (nonceAnswer hash s).getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) =
      (hash (hashInput (noncePrepare s))).extractLsb' (32*i.val) 32 := by
  have dst := (nonce_registers s).2.2.1
  fin_cases i <;>
    simp [nonceAnswer,writeHash,dst,MachineState.writeWords,
      MachineState.getWord32,alignToDword,byteOffset,extractWord32]
  all_goals ext j hj; interval_cases j <;> simp

theorem answer_value (hash : Hash) (s : MachineState) (parameter : Digest) (seed : MasterSeed)
    (message : SphincsSecurity.Message) (trial : Nat)
    (ctx : Context s parameter seed message trial) :
    Words20 (nonceAnswer hash s) 0x42000
      (truncateHash (hash (toQuery (randomizerHashInput parameter seed message (BitVec.ofNat 32 trial))))) := by
  intro i
  rw [answer_words,query_eq s parameter seed message trial ctx]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

theorem init_frame (s : MachineState) (a : Word) (different : a ≠ 0x43098#64) :
    (init s).getMem a = s.getMem a := by
  simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,different]

theorem nonce_frame (s : MachineState) (a : Word)
    (outside : a.toNat < 0x40000 ∨ 0x43020 ≤ a.toNat ∨ a = 0x43000#64 ∨ a = 0x43008#64) :
    (noncePrepare s).getMem a = s.getMem a := by
  have h1 : a.toNat < 0x40000 ∨ 0x40028 ≤ a.toNat := by
    rcases outside with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
    · rw [h];decide
    · rw [h];decide
  have h2 : a.toNat < 0x40048 ∨ 0x40068 ≤ a.toNat := by
    rcases outside with h | h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
    · rw [h];decide
    · rw [h];decide
  have h3 : a.toNat < 0x40028 ∨ 0x40048 ≤ a.toNat := by
    rcases outside with h | h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
    · rw [h];decide
    · rw [h];decide
  have ne1 : a ≠ 0x43010#64 := by intro eq;rw [eq] at outside;revert outside;decide
  have ne2 : a ≠ 0x43018#64 := by intro eq;rw [eq] at outside;revert outside;decide
  rw [noncePrepare,header_frame _ _ h1,messageCopy_frame _ _ h2,keyCopy_frame _ _ h3,
    control_mem,if_neg ne2,if_neg ne1]

theorem answer_frame (hash : Hash) (s : MachineState) (a : Word)
    (outside : a.toNat < 0x40000 ∨ 0x43020 ≤ a.toNat ∨ a = 0x43000#64 ∨ a = 0x43008#64) :
    (nonceAnswer hash s).getMem a = s.getMem a := by
  have ne (b : Word) (lo : 0x42000 ≤ b.toNat) (hi : b.toNat < 0x42020) : a ≠ b := by
    intro eq; rw [eq] at outside
    rcases outside with h | h | h | h
    · omega
    · omega
    · rw [h] at hi; contradiction
    · rw [h] at hi; contradiction
  have dst := (nonce_registers s).2.2.1
  simp [nonceAnswer,writeHash,dst,MachineState.writeWords,ne,nonce_frame s a outside]

theorem answer_context (hash : Hash) (s : MachineState) (parameter : Digest) (seed : MasterSeed)
    (message : SphincsSecurity.Message) (trial : Nat)
    (ctx : Context s parameter seed message trial) :
    Context (nonceAnswer hash s) parameter seed message trial := by
  refine ⟨?_,?_,?_,ctx.bounded,?_,?_,?_⟩
  · rw [answer_frame _ _ _ (by simp)]; exact ctx.layer
  · rw [answer_frame _ _ _ (by simp)]; exact ctx.tree
  · rw [answer_frame _ _ _ (by simp)]; exact ctx.counter
  · exact SphincsMaskedSignHonestAuthentication.frame_words20 _ _
      (fun a h => answer_frame hash s a (Or.inl h)) 0x74 (by decide) _ ctx.parameterWords
  · exact SphincsMaskedSignHonestAuthentication.frame_words32 _ _
      (fun a h => answer_frame hash s a (Or.inl h)) seed ctx.keyWords
  · intro i
    rw [SphincsMaskedSignHonestAuthentication.frame_word _ _
      (fun a h => answer_frame hash s a (Or.inl h)) (4*i.val) (by have := i.isLt;omega)]
    exact ctx.messageWords i

theorem init_context (s : MachineState) (parameter : Digest) (seed : MasterSeed)
    (message : SphincsSecurity.Message)
    (layer : s.getMem 0x43000#64 = 0) (tree : s.getMem 0x43008#64 = 0)
    (par : Words20 s 0x74 parameter) (key : Words32 s seed)
    (msg : ∀ i : Fin 8, s.getWord32 (BitVec.ofNat 64 (4*i.val)) = message.extractLsb' (32*i.val) 32) :
    Context (init s) parameter seed message 0 := by
  have frame (a : Word) (low : a.toNat < 0x40000) : (init s).getMem a = s.getMem a :=
    init_frame s a (by intro eq; rw [eq] at low; contradiction)
  refine ⟨?_,?_,init_counter s,by decide,?_,?_,?_⟩
  · rw [init_frame _ _ (by decide)];exact layer
  · rw [init_frame _ _ (by decide)];exact tree
  · exact SphincsMaskedSignHonestAuthentication.frame_words20 _ _ frame 0x74 (by decide) _ par
  · exact SphincsMaskedSignHonestAuthentication.frame_words32 _ _ frame seed key
  · intro i
    rw [SphincsMaskedSignHonestAuthentication.frame_word _ _ frame (4*i.val) (by have := i.isLt;omega)]
    exact msg i

/-- The first nonce HASH, including trial initialization, with its exact abstract
    query and answer and the invariant needed to continue the same trial. -/
theorem first_nonce (hash : Hash) (s : MachineState) (pc : s.pc = 0x1510)
    (parameter : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (layer : s.getMem 0x43000#64 = 0) (tree : s.getMem 0x43008#64 = 0)
    (par : Words20 s 0x74 parameter) (key : Words32 s seed)
    (msg : ∀ i : Fin 8, s.getWord32 (BitVec.ofNat 64 (4*i.val)) = message.extractLsb' (32*i.val) 32) :
    Trace hash SphincsMaskedImages.sign s 111 126 1 2 (nonceAnswer hash (init s)) ∧
    (nonceAnswer hash (init s)).pc = 0x163c ∧
    hashInput (noncePrepare (init s)) = toQuery (randomizerHashInput parameter seed message 0) ∧
    Words20 (nonceAnswer hash (init s)) 0x42000
      (truncateHash (hash (toQuery (randomizerHashInput parameter seed message 0)))) ∧
    Context (nonceAnswer hash (init s)) parameter seed message 0 := by
  have ctx := init_context s parameter seed message layer tree par key msg
  refine ⟨(init_trace s pc).trace.trans (nonce_trace hash (init s) (init_pc s pc)),?_,
    query_eq _ parameter seed message 0 ctx,answer_value hash _ parameter seed message 0 ctx,
    answer_context hash _ parameter seed message 0 ctx⟩
  simp [nonceAnswer,writeHash,nonce_pc _ (init_pc s pc)]

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_eq

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.nonce_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonce_trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.answer_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms answer_context

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.first_nonce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_nonce

end SigGolfCandidate.SphincsMaskedSignNonceTrial

namespace SigGolfCandidate.SphincsMaskedSignNonceTrial
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsBridge SphincsSecurity SphincsMaskedMaskSemantics
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def digestInitSchedule : List (Word × Instr) := [
  (0x163c, .LUI .x6 66),
  (0x1640, .ADDI .x6 .x6 0),
  (0x1644, .LUI .x7 32),
  (0x1648, .ADDI .x7 .x7 136),
  (0x164c, .LWU .x13 .x6 0),
  (0x1650, .SW .x7 .x13 0),
  (0x1654, .LWU .x13 .x6 4),
  (0x1658, .SW .x7 .x13 4),
  (0x165c, .LWU .x13 .x6 8),
  (0x1660, .SW .x7 .x13 8),
  (0x1664, .LWU .x13 .x6 12),
  (0x1668, .SW .x7 .x13 12),
  (0x166c, .LWU .x13 .x6 16),
  (0x1670, .SW .x7 .x13 16),
  (0x1674, .ADDI .x6 .x0 0),
  (0x1678, .LUI .x28 67),
  (0x167c, .ADDI .x28 .x28 0),
  (0x1680, .SD .x28 .x6 0),
  (0x1684, .ADDI .x6 .x0 0),
  (0x1688, .LUI .x28 67),
  (0x168c, .ADDI .x28 .x28 8),
  (0x1690, .SD .x28 .x6 0),
  (0x1694, .ADDI .x6 .x0 0),
  (0x1698, .LUI .x28 67),
  (0x169c, .ADDI .x28 .x28 16),
  (0x16a0, .SD .x28 .x6 0),
  (0x16a4, .ADDI .x6 .x0 0),
  (0x16a8, .LUI .x28 67),
  (0x16ac, .ADDI .x28 .x28 24),
  (0x16b0, .SD .x28 .x6 0)]

def digestPayloadSchedule : List (Word × Instr) := [
  (0x16b4, .LUI .x6 32),
  (0x16b8, .ADDI .x6 .x6 136),
  (0x16bc, .LUI .x7 64),
  (0x16c0, .ADDI .x7 .x7 40),
  (0x16c4, .LWU .x13 .x6 0),
  (0x16c8, .SW .x7 .x13 0),
  (0x16cc, .LWU .x13 .x6 4),
  (0x16d0, .SW .x7 .x13 4),
  (0x16d4, .LWU .x13 .x6 8),
  (0x16d8, .SW .x7 .x13 8),
  (0x16dc, .LWU .x13 .x6 12),
  (0x16e0, .SW .x7 .x13 12),
  (0x16e4, .LWU .x13 .x6 16),
  (0x16e8, .SW .x7 .x13 16),
  (0x16ec, .LUI .x6 32),
  (0x16f0, .ADDI .x6 .x6 96),
  (0x16f4, .LUI .x7 64),
  (0x16f8, .ADDI .x7 .x7 60),
  (0x16fc, .LWU .x13 .x6 0),
  (0x1700, .SW .x7 .x13 0),
  (0x1704, .LWU .x13 .x6 4),
  (0x1708, .SW .x7 .x13 4),
  (0x170c, .LWU .x13 .x6 8),
  (0x1710, .SW .x7 .x13 8),
  (0x1714, .LWU .x13 .x6 12),
  (0x1718, .SW .x7 .x13 12),
  (0x171c, .LWU .x13 .x6 16),
  (0x1720, .SW .x7 .x13 16),
  (0x1724, .ADDI .x6 .x0 0),
  (0x1728, .LUI .x7 64),
  (0x172c, .ADDI .x7 .x7 80),
  (0x1730, .ADDI .x10 .x0 4),
  (0x1734, .LD .x11 .x6 0),
  (0x1738, .SD .x7 .x11 0),
  (0x173c, .ADDI .x6 .x6 8),
  (0x1740, .ADDI .x7 .x7 8),
  (0x1744, .ADDI .x10 .x10 (-1)),
  (0x1748, .BNE .x10 .x0 (-20)),
  (0x1734, .LD .x11 .x6 0),
  (0x1738, .SD .x7 .x11 0),
  (0x173c, .ADDI .x6 .x6 8),
  (0x1740, .ADDI .x7 .x7 8),
  (0x1744, .ADDI .x10 .x10 (-1)),
  (0x1748, .BNE .x10 .x0 (-20)),
  (0x1734, .LD .x11 .x6 0),
  (0x1738, .SD .x7 .x11 0),
  (0x173c, .ADDI .x6 .x6 8),
  (0x1740, .ADDI .x7 .x7 8),
  (0x1744, .ADDI .x10 .x10 (-1)),
  (0x1748, .BNE .x10 .x0 (-20)),
  (0x1734, .LD .x11 .x6 0),
  (0x1738, .SD .x7 .x11 0),
  (0x173c, .ADDI .x6 .x6 8),
  (0x1740, .ADDI .x7 .x7 8),
  (0x1744, .ADDI .x10 .x10 (-1)),
  (0x1748, .BNE .x10 .x0 (-20))]

def digestHeaderSchedule : List (Word × Instr) := [
  (0x174c, .LUI .x6 1),
  (0x1750, .ADDI .x6 .x6 (-1023)),
  (0x1754, .LUI .x28 67),
  (0x1758, .ADDI .x28 .x28 0),
  (0x175c, .LD .x7 .x28 0),
  (0x1760, .SLLI .x7 .x7 16),
  (0x1764, .ADD .x6 .x6 .x7),
  (0x1768, .LUI .x7 64),
  (0x176c, .ADDI .x7 .x7 0),
  (0x1770, .SW .x7 .x6 0),
  (0x1774, .LUI .x28 67),
  (0x1778, .ADDI .x28 .x28 16),
  (0x177c, .LD .x6 .x28 0),
  (0x1780, .SW .x7 .x6 4),
  (0x1784, .LUI .x28 67),
  (0x1788, .ADDI .x28 .x28 8),
  (0x178c, .LD .x6 .x28 0),
  (0x1790, .SD .x7 .x6 8),
  (0x1794, .LUI .x28 67),
  (0x1798, .ADDI .x28 .x28 24),
  (0x179c, .LD .x6 .x28 0),
  (0x17a0, .SW .x7 .x6 16),
  (0x17a4, .ADDI .x6 .x0 116),
  (0x17a8, .LUI .x7 64),
  (0x17ac, .ADDI .x7 .x7 20),
  (0x17b0, .LWU .x13 .x6 0),
  (0x17b4, .SW .x7 .x13 0),
  (0x17b8, .LWU .x13 .x6 4),
  (0x17bc, .SW .x7 .x13 4),
  (0x17c0, .LWU .x13 .x6 8),
  (0x17c4, .SW .x7 .x13 8),
  (0x17c8, .LWU .x13 .x6 12),
  (0x17cc, .SW .x7 .x13 12),
  (0x17d0, .LWU .x13 .x6 16),
  (0x17d4, .SW .x7 .x13 16),
  (0x17d8, .LUI .x10 64),
  (0x17dc, .ADDI .x10 .x10 0),
  (0x17e0, .ADDI .x11 .x0 896),
  (0x17e4, .LUI .x12 66),
  (0x17e8, .ADDI .x12 .x12 0),
  (0x17ec, .ADDI .x5 .x0 1)]

def digestInit (s : MachineState) := runSchedule digestInitSchedule s

theorem digestInit_code : ∀ e ∈ digestInitSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem digestInit_checked (s : MachineState) (pc : s.pc = 0x163c) : Checked digestInitSchedule s := by
  simp [Checked,digestInitSchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]
theorem digestInit_block (s : MachineState) (pc : s.pc = 0x163c) :
    OrdinarySteps SphincsMaskedImages.sign s 30 (digestInit s) :=
  checked_sound _ digestInitSchedule digestInit_code s (digestInit_checked s pc)
theorem digestInit_pc (s : MachineState) (pc : s.pc = 0x163c) : (digestInit s).pc = 0x16b4 := by
  simp [digestInit,runSchedule,digestInitSchedule,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]

def digestPayload (s : MachineState) := runSchedule digestPayloadSchedule s

theorem digestPayload_code : ∀ e ∈ digestPayloadSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem digestPayload_checked (s : MachineState) (pc : s.pc = 0x16b4) : Checked digestPayloadSchedule s := by
  simp [Checked,digestPayloadSchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]
theorem digestPayload_block (s : MachineState) (pc : s.pc = 0x16b4) :
    OrdinarySteps SphincsMaskedImages.sign s 56 (digestPayload s) :=
  checked_sound _ digestPayloadSchedule digestPayload_code s (digestPayload_checked s pc)
theorem digestPayload_pc (s : MachineState) (pc : s.pc = 0x16b4) : (digestPayload s).pc = 0x174c := by
  simp [digestPayload,runSchedule,digestPayloadSchedule,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]

def digestHeader (s : MachineState) := runSchedule digestHeaderSchedule s

theorem digestHeader_code : ∀ e ∈ digestHeaderSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem digestHeader_checked (s : MachineState) (pc : s.pc = 0x174c) : Checked digestHeaderSchedule s := by
  simp [Checked,digestHeaderSchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]
theorem digestHeader_block (s : MachineState) (pc : s.pc = 0x174c) :
    OrdinarySteps SphincsMaskedImages.sign s 41 (digestHeader s) :=
  checked_sound _ digestHeaderSchedule digestHeader_code s (digestHeader_checked s pc)
theorem digestHeader_pc (s : MachineState) (pc : s.pc = 0x174c) : (digestHeader s).pc = 0x17f0 := by
  simp [digestHeader,runSchedule,digestHeaderSchedule,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]

def digestPrepare (s : MachineState) := digestHeader (digestPayload (digestInit s))
def digestAnswer (hash : Hash) (s : MachineState) :=
  writeHash (digestPrepare s) (hash (hashInput (digestPrepare s)))
theorem digest_block (s : MachineState) (pc : s.pc = 0x163c) :
    OrdinarySteps SphincsMaskedImages.sign s 127 (digestPrepare s) := by
  have a := digestInit_pc s pc
  have b := digestPayload_pc _ a
  exact SphincsVerifierFtsRootCopy.ordinary_trans _ _ _ _ 30 97 (digestInit_block s pc)
    (SphincsVerifierFtsRootCopy.ordinary_trans _ _ _ _ 56 41
      (digestPayload_block _ a) (digestHeader_block _ b))
theorem digest_pc (s : MachineState) (pc : s.pc = 0x163c) : (digestPrepare s).pc = 0x17f0 :=
  digestHeader_pc _ (digestPayload_pc _ (digestInit_pc s pc))
theorem digestHeader_registers (s : MachineState) :
    (digestHeader s).getReg .x10 = 0x40000 ∧ (digestHeader s).getReg .x11 = 896 ∧
    (digestHeader s).getReg .x12 = 0x42000 ∧ (digestHeader s).getReg .x5 = 1 := by
  simp [digestHeader,runSchedule,digestHeaderSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,MachineState.setWord32]
theorem digest_registers (s : MachineState) :
    (digestPrepare s).getReg .x10 = 0x40000 ∧ (digestPrepare s).getReg .x11 = 896 ∧
    (digestPrepare s).getReg .x12 = 0x42000 ∧ (digestPrepare s).getReg .x5 = 1 := digestHeader_registers _
theorem digest_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x163c) :
    Trace hash SphincsMaskedImages.sign s 128 143 1 2 (digestAnswer hash s) := by
  obtain ⟨src,bits,dst,service⟩ := digest_registers s
  have fetched : fetch SphincsMaskedImages.sign (digestPrepare s) = some (.base .ECALL) := by
    rw [SphincsVerifierFtsRootCopy.fetch_at,digest_pc s pc]; decide
  have valid : hashArgumentsValid (digestPrepare s) = true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (digestPrepare s)).1 = 896 := by simp [hashInput,bits]
  have step := Trace.hash (hash := hash) (image := SphincsMaskedImages.sign)
    (digestPrepare s) _ 0 0 0 0 fetched service valid (Trace.refl _)
  have one : Trace hash SphincsMaskedImages.sign (digestPrepare s) 1 16 1 2 (digestAnswer hash s) := by
    simpa [digestAnswer,len,show compressions 896 = 2 from rfl] using step
  exact (digest_block s pc).trace.trans one

theorem digestPayload_frame (s : MachineState) (a : Word)
    (outside : a.toNat < 0x40028 ∨ 0x40070 ≤ a.toNat) :
    (digestPayload s).getMem a = s.getMem a := by
  have ne (b : Word) (lo : 0x40028 ≤ b.toNat) (hi : b.toNat < 0x40070) : a ≠ b := by
    intro eq; rw [eq] at outside; rcases outside with h | h <;> omega
  simp [digestPayload,runSchedule,digestPayloadSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,ne]

theorem digestHeader_frame (s : MachineState) (a : Word)
    (outside : a.toNat < 0x40000 ∨ 0x40028 ≤ a.toNat) :
    (digestHeader s).getMem a = s.getMem a := by
  have ne (b : Word) (lo : 0x40000 ≤ b.toNat) (hi : b.toNat < 0x40028) : a ≠ b := by
    intro eq; rw [eq] at outside; rcases outside with h | h <;> omega
  simp [digestHeader,runSchedule,digestHeaderSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,ne]

theorem digestInit_frame (s : MachineState) (a : Word)
    (outsideSignature : a.toNat < 0x20088 ∨ 0x200a0 ≤ a.toNat)
    (outsideControls : a.toNat < 0x43000 ∨ 0x43020 ≤ a.toNat) :
    (digestInit s).getMem a = s.getMem a := by
  have ne (b : Word) (inside : (0x20088 ≤ b.toNat ∧ b.toNat < 0x200a0) ∨
      (0x43000 ≤ b.toNat ∧ b.toNat < 0x43020)) : a ≠ b := by
    intro eq;rw [eq] at outsideSignature outsideControls
    rcases inside with h | h <;> rcases outsideSignature with h1 | h1 <;>
      rcases outsideControls with h2 | h2 <;> omega
  simp [digestInit,runSchedule,digestInitSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,ne]

theorem digestInit_controls (s : MachineState) (i : Fin 4) :
    (digestInit s).getMem (BitVec.ofNat 64 (0x43000+8*i.val)) = 0 := by
  fin_cases i <;>
    simp [digestInit,runSchedule,digestInitSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,alignToDword,byteOffset]
theorem digestInit_words (s : MachineState) (i : Fin 5) :
    (digestInit s).getWord32 (BitVec.ofNat 64 (0x20088+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) := by
  fin_cases i <;>
    simp [digestInit,runSchedule,digestInitSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

def digestHeaderWord (s : MachineState) (i : Fin 28) : BitVec 32 :=
  if i.val = 0 then (3073#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val = 1 then (s.getMem 0x43010).setWidth 32
  else if i.val = 2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val = 3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val = 4 then (s.getMem 0x43018).setWidth 32
  else if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x74+4*(i.val-5)))
  else s.getWord32 (BitVec.ofNat 64 (0x40000+4*i.val))
def digestPayloadWord (s : MachineState) (i : Fin 28) : BitVec 32 :=
  if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x40000+4*i.val))
  else if i.val < 15 then s.getWord32 (BitVec.ofNat 64 (0x20088+4*(i.val-10)))
  else if i.val < 20 then s.getWord32 (BitVec.ofNat 64 (0x20060+4*(i.val-15)))
  else s.getWord32 (BitVec.ofNat 64 (4*(i.val-20)))
def digestQueryWord (s : MachineState) (i : Fin 28) : BitVec 32 :=
  if i.val = 0 then 3073
  else if i.val < 5 then 0
  else if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x74+4*(i.val-5)))
  else if i.val < 15 then s.getWord32 (BitVec.ofNat 64 (0x42000+4*(i.val-10)))
  else if i.val < 20 then s.getWord32 (BitVec.ofNat 64 (0x20060+4*(i.val-15)))
  else s.getWord32 (BitVec.ofNat 64 (4*(i.val-20)))

theorem digestHeader_words (s : MachineState) (i : Fin 28) :
    (digestHeader s).getWord32 (BitVec.ofNat 64 (0x40000+4*i.val)) = digestHeaderWord s i := by
  fin_cases i <;>
    simp [digestHeader,runSchedule,digestHeaderSchedule,execInstrBr,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,digestHeaderWord]

theorem digestPayload_words (s : MachineState) (i : Fin 28) :
    (digestPayload s).getWord32 (BitVec.ofNat 64 (0x40000+4*i.val)) = digestPayloadWord s i := by
  fin_cases i <;>
    simp [digestPayload,runSchedule,digestPayloadSchedule,execInstrBr,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,digestPayloadWord]

theorem digest_words (s : MachineState) (i : Fin 28) :
    (digestPrepare s).getWord32 (BitVec.ofNat 64 (0x40000+4*i.val)) = digestQueryWord s i := by
  have z0 := digestInit_controls s 0
  have z1 := digestInit_controls s 1
  have z2 := digestInit_controls s 2
  have z3 := digestInit_controls s 3
  norm_num at z0 z1 z2 z3
  rw [digestPrepare,digestHeader_words]
  fin_cases i
  · simp [digestHeaderWord,digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,
      digestPayload_frame,digestInit_frame,z0,z1,z2,z3,extractWord32]
  · simp [digestHeaderWord,digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,
      digestPayload_frame,digestInit_frame,z0,z1,z2,z3,extractWord32]
  · simp [digestHeaderWord,digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,
      digestPayload_frame,digestInit_frame,z0,z1,z2,z3,extractWord32]
  · simp [digestHeaderWord,digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,
      digestPayload_frame,digestInit_frame,z0,z1,z2,z3,extractWord32]
  · simp [digestHeaderWord,digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,
      digestPayload_frame,digestInit_frame,z0,z1,z2,z3,extractWord32]
  · simp [digestHeaderWord,digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,
      digestPayload_frame,digestInit_frame,z0,z1,z2,z3,extractWord32]
  · simp [digestHeaderWord,digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,
      digestPayload_frame,digestInit_frame,z0,z1,z2,z3,extractWord32]
  · simp [digestHeaderWord,digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,
      digestPayload_frame,digestInit_frame,z0,z1,z2,z3,extractWord32]
  · simp [digestHeaderWord,digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,
      digestPayload_frame,digestInit_frame,z0,z1,z2,z3,extractWord32]
  · simp [digestHeaderWord,digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,
      digestPayload_frame,digestInit_frame,z0,z1,z2,z3,extractWord32]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262184) = _
    have hp := digestPayload_words (digestInit s) 10
    norm_num [digestPayloadWord] at hp
    rw [hp]
    have hn := digestInit_words s 0
    norm_num at hn
    rw [hn]
    simp [digestQueryWord]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262188) = _
    have hp := digestPayload_words (digestInit s) 11
    norm_num [digestPayloadWord] at hp
    rw [hp]
    have hn := digestInit_words s 1
    norm_num at hn
    rw [hn]
    simp [digestQueryWord]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262192) = _
    have hp := digestPayload_words (digestInit s) 12
    norm_num [digestPayloadWord] at hp
    rw [hp]
    have hn := digestInit_words s 2
    norm_num at hn
    rw [hn]
    simp [digestQueryWord]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262196) = _
    have hp := digestPayload_words (digestInit s) 13
    norm_num [digestPayloadWord] at hp
    rw [hp]
    have hn := digestInit_words s 3
    norm_num at hn
    rw [hn]
    simp [digestQueryWord]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262200) = _
    have hp := digestPayload_words (digestInit s) 14
    norm_num [digestPayloadWord] at hp
    rw [hp]
    have hn := digestInit_words s 4
    norm_num at hn
    rw [hn]
    simp [digestQueryWord]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262204) = _
    have hp := digestPayload_words (digestInit s) 15
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262208) = _
    have hp := digestPayload_words (digestInit s) 16
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262212) = _
    have hp := digestPayload_words (digestInit s) 17
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262216) = _
    have hp := digestPayload_words (digestInit s) 18
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262220) = _
    have hp := digestPayload_words (digestInit s) 19
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262224) = _
    have hp := digestPayload_words (digestInit s) 20
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262228) = _
    have hp := digestPayload_words (digestInit s) 21
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262232) = _
    have hp := digestPayload_words (digestInit s) 22
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262236) = _
    have hp := digestPayload_words (digestInit s) 23
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262240) = _
    have hp := digestPayload_words (digestInit s) 24
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262244) = _
    have hp := digestPayload_words (digestInit s) 25
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262248) = _
    have hp := digestPayload_words (digestInit s) 26
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]
  · change (digestPayload (digestInit s)).getWord32 (BitVec.ofNat 64 262252) = _
    have hp := digestPayload_words (digestInit s) 27
    norm_num [digestPayloadWord] at hp
    rw [hp]
    simp [digestQueryWord,MachineState.getWord32,alignToDword,byteOffset,digestInit_frame]

def digestBytes (parameter root randomness : Digest) (message : SphincsSecurity.Message) : List Byte :=
  (tweakableHashInput parameter .message (Concrete.messageDigestPayload root message randomness)).map UInt8.toBitVec

theorem digestBytes_length (parameter root randomness : Digest) (message : SphincsSecurity.Message) :
    (digestBytes parameter root randomness message).length = 112 := by
  simp [digestBytes,tweakableHashInput,tweakBytes,hashDomainFields,tweakFields,
    Concrete.messageDigestPayload,fieldBytes,bytesLE]

theorem digest_prepared_byte (s : MachineState) (i : Fin 112) :
    (digestPrepare s).getByte (BitVec.ofNat 64 (0x40000+i.val)) =
      (digestQueryWord s ⟨i.val/4,by omega⟩).extractLsb' (8*(i.val%4)) 8 := by
  have h := SphincsVerifierFtsGenericBytes.variableWord_byte (digestPrepare s)
    (0x40000+4*(i.val/4)) (by omega) (by omega) 0 ⟨i.val%4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  rw [show 0x40000+4*(i.val/4)+i.val%4=0x40000+i.val by omega] at h
  rw [h,digest_words s ⟨i.val/4,by omega⟩]

theorem digest_context_byte (s : MachineState) (parameter root randomness : Digest)
    (message : SphincsSecurity.Message)
    (par : Words20 s 0x74 parameter) (rootWords : Words20 s 0x20060 root)
    (randomWords : Words20 s 0x42000 randomness)
    (msg : ∀ i : Fin 8, s.getWord32 (BitVec.ofNat 64 (4*i.val)) = message.extractLsb' (32*i.val) 32)
    (i : Fin 112) :
    (digestQueryWord s ⟨i.val/4,by omega⟩).extractLsb' (8*(i.val%4)) 8 =
      (digestBytes parameter root randomness message)[i.val]'(by rw [digestBytes_length];exact i.isLt) := by
  have p0 := par 0
  have p1 := par 1
  have p2 := par 2
  have p3 := par 3
  have p4 := par 4
  have r0 := rootWords 0
  have r1 := rootWords 1
  have r2 := rootWords 2
  have r3 := rootWords 3
  have r4 := rootWords 4
  have n0 := randomWords 0
  have n1 := randomWords 1
  have n2 := randomWords 2
  have n3 := randomWords 3
  have n4 := randomWords 4
  have m0 := msg 0
  have m1 := msg 1
  have m2 := msg 2
  have m3 := msg 3
  have m4 := msg 4
  have m5 := msg 5
  have m6 := msg 6
  have m7 := msg 7
  norm_num at p0 p1 p2 p3 p4 r0 r1 r2 r3 r4 n0 n1 n2 n3 n4 m0 m1 m2 m3 m4 m5 m6 m7
  fin_cases i <;>
    simp [digestQueryWord,p0,p1,p2,p3,p4,r0,r1,r2,r3,r4,n0,n1,n2,n3,n4,m0,m1,m2,m3,m4,m5,m6,m7,extractWord32,digestBytes,tweakableHashInput,
      tweakBytes,hashDomainFields,tweakFields,Concrete.messageDigestPayload,fieldBytes,bytesLE,protocolDomainSep]
  all_goals
    ext b hb
    interval_cases b <;> simp [BitVec.getLsbD_eq_getElem]
  all_goals exact BitVec.getLsbD_eq_getElem (by decide)

theorem digest_query_eq (s : MachineState) (parameter root randomness : Digest)
    (message : SphincsSecurity.Message)
    (par : Words20 s 0x74 parameter) (rootWords : Words20 s 0x20060 root)
    (randomWords : Words20 s 0x42000 randomness)
    (msg : ∀ i : Fin 8, s.getWord32 (BitVec.ofNat 64 (4*i.val)) = message.extractLsb' (32*i.val) 32) :
    hashInput (digestPrepare s) =
      toQuery (tweakableHashInput parameter .message (Concrete.messageDigestPayload root message randomness)) := by
  apply Serialization.hashInput_of_list (digestPrepare s) 0x40000 (digestBytes parameter root randomness message)
  · exact (digest_registers s).1
  · rw [digestBytes_length,(digest_registers s).2.1];rfl
  · intro i hi
    have bound : i < 112 := by simpa only [digestBytes_length] using hi
    rw [digest_prepared_byte s ⟨i,bound⟩]
    exact digest_context_byte s parameter root randomness message par rootWords randomWords msg ⟨i,bound⟩

end SigGolfCandidate.SphincsMaskedSignNonceTrial

namespace SigGolfCandidate.SphincsMaskedSignNonceTrial
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsBridge SphincsSecurity SphincsMaskedMaskSemantics
open SphincsVerifierLeavesTrace SphincsVerifierLeafCode
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def decodeHeadSchedule : List (Word × Instr) := [
  (0x17f4, .LUI .x6 66),
  (0x17f8, .ADDI .x6 .x6 0),
  (0x17fc, .LD .x10 .x6 0),
  (0x1800, .SLLI .x10 .x10 30),
  (0x1804, .SRLI .x10 .x10 30),
  (0x1808, .LUI .x28 67),
  (0x180c, .ADDI .x28 .x28 24),
  (0x1810, .SD .x28 .x10 0),
  (0x1814, .LUI .x28 67),
  (0x1818, .ADDI .x28 .x28 120),
  (0x181c, .SD .x28 .x10 0),
  (0x1820, .LUI .x6 66),
  (0x1824, .ADDI .x6 .x6 0),
  (0x1828, .LBU .x10 .x6 28),
  (0x182c, .LBU .x11 .x6 29),
  (0x1830, .SRLI .x10 .x10 2),
  (0x1834, .SLLI .x11 .x11 6),
  (0x1838, .ADD .x10 .x10 .x11),
  (0x183c, .ANDI .x10 .x10 255),
  (0x1840, .LUI .x28 67),
  (0x1844, .ADDI .x28 .x28 176),
  (0x1848, .SD .x28 .x10 0)]

def decodeHead (s : MachineState) := runSchedule decodeHeadSchedule s

theorem decodeHead_code : ∀ e ∈ decodeHeadSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem decodeHead_checked (s : MachineState) (pc : s.pc = 0x17f4) : Checked decodeHeadSchedule s := by
  simp [Checked,decodeHeadSchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,signExtend21,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]
theorem decodeHead_block (s : MachineState) (pc : s.pc = 0x17f4) :
    OrdinarySteps SphincsMaskedImages.sign s 22 (decodeHead s) :=
  checked_sound _ decodeHeadSchedule decodeHead_code s (decodeHead_checked s pc)

def dispatchSchedule : List (Word × Instr) := [
  (0x184c, .LUI .x28 67),
  (0x1850, .ADDI .x28 .x28 176),
  (0x1854, .LD .x6 .x28 0),
  (0x1858, .BEQ .x6 .x0 8)]

def dispatch (s : MachineState) := runSchedule dispatchSchedule s

theorem dispatch_code : ∀ e ∈ dispatchSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem dispatch_checked (s : MachineState) (pc : s.pc = 0x184c) : Checked dispatchSchedule s := by
  simp [Checked,dispatchSchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,signExtend21,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]
theorem dispatch_block (s : MachineState) (pc : s.pc = 0x184c) :
    OrdinarySteps SphincsMaskedImages.sign s 4 (dispatch s) :=
  checked_sound _ dispatchSchedule dispatch_code s (dispatch_checked s pc)

def skipLeavesSchedule : List (Word × Instr) := [
  (0x185c, .JAL .x0 1060)]

def skipLeaves (s : MachineState) := runSchedule skipLeavesSchedule s

theorem skipLeaves_code : ∀ e ∈ skipLeavesSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem skipLeaves_checked (s : MachineState) (pc : s.pc = 0x185c) : Checked skipLeavesSchedule s := by
  simp [Checked,skipLeavesSchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,signExtend21,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]
theorem skipLeaves_block (s : MachineState) (pc : s.pc = 0x185c) :
    OrdinarySteps SphincsMaskedImages.sign s 1 (skipLeaves s) :=
  checked_sound _ skipLeavesSchedule skipLeaves_code s (skipLeaves_checked s pc)

def finishTrialSchedule : List (Word × Instr) := [
  (0x1c80, .LUI .x28 67),
  (0x1c84, .ADDI .x28 .x28 176),
  (0x1c88, .LD .x6 .x28 0),
  (0x1c8c, .BEQ .x6 .x0 60)]

def finishTrial (s : MachineState) := runSchedule finishTrialSchedule s

theorem finishTrial_code : ∀ e ∈ finishTrialSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem finishTrial_checked (s : MachineState) (pc : s.pc = 0x1c80) : Checked finishTrialSchedule s := by
  simp [Checked,finishTrialSchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,signExtend21,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]
theorem finishTrial_block (s : MachineState) (pc : s.pc = 0x1c80) :
    OrdinarySteps SphincsMaskedImages.sign s 4 (finishTrial s) :=
  checked_sound _ finishTrialSchedule finishTrial_code s (finishTrial_checked s pc)

def retrySchedule : List (Word × Instr) := [
  (0x1c90, .LUI .x28 67),
  (0x1c94, .ADDI .x28 .x28 152),
  (0x1c98, .LD .x6 .x28 0),
  (0x1c9c, .ADDI .x6 .x6 1),
  (0x1ca0, .LUI .x28 67),
  (0x1ca4, .ADDI .x28 .x28 152),
  (0x1ca8, .SD .x28 .x6 0),
  (0x1cac, .LUI .x28 67),
  (0x1cb0, .ADDI .x28 .x28 152),
  (0x1cb4, .LD .x6 .x28 0),
  (0x1cb8, .LUI .x7 256),
  (0x1cbc, .ADDI .x7 .x7 0),
  (0x1cc0, .BNE .x6 .x7 (-1952))]

def retry (s : MachineState) := runSchedule retrySchedule s

theorem retry_code : ∀ e ∈ retrySchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by decide
theorem retry_checked (s : MachineState) (pc : s.pc = 0x1c90) : Checked retrySchedule s := by
  simp [Checked,retrySchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,signExtend21,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset]
theorem retry_block (s : MachineState) (pc : s.pc = 0x1c90) :
    OrdinarySteps SphincsMaskedImages.sign s 13 (retry s) :=
  checked_sound _ retrySchedule retry_code s (retry_checked s pc)

theorem decodeHead_pc (s : MachineState) (pc : s.pc = 0x17f4) : (decodeHead s).pc = 0x184c := by
  simp [decodeHead,runSchedule,decodeHeadSchedule,execInstrBr,signExtend12,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem skipLeaves_pc (s : MachineState) (pc : s.pc = 0x185c) : (skipLeaves s).pc = 0x1c80 := by
  simp [skipLeaves,runSchedule,skipLeavesSchedule,execInstrBr,signExtend21,pc]
theorem dispatch_accept_pc (s : MachineState) (pc : s.pc = 0x184c)
    (zero : s.getMem 0x430b0#64 = 0) : (dispatch s).pc = 0x1860 := by
  simp [dispatch,runSchedule,dispatchSchedule,execInstrBr,signExtend12,signExtend13,pc,zero,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem dispatch_reject_pc (s : MachineState) (pc : s.pc = 0x184c)
    (nonzero : s.getMem 0x430b0#64 ≠ 0#64) : (dispatch s).pc = 0x185c := by
  simp [dispatch,runSchedule,dispatchSchedule,execInstrBr,signExtend12,signExtend13,pc,nonzero,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem finishTrial_accept_pc (s : MachineState) (pc : s.pc = 0x1c80)
    (zero : s.getMem 0x430b0#64 = 0) : (finishTrial s).pc = 0x1cc8 := by
  simp [finishTrial,runSchedule,finishTrialSchedule,execInstrBr,signExtend12,signExtend13,pc,zero,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem finishTrial_reject_pc (s : MachineState) (pc : s.pc = 0x1c80)
    (nonzero : s.getMem 0x430b0#64 ≠ 0#64) : (finishTrial s).pc = 0x1c90 := by
  simp [finishTrial,runSchedule,finishTrialSchedule,execInstrBr,signExtend12,signExtend13,pc,nonzero,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem decodeHead_last (s : MachineState) :
    (decodeHead s).getMem 0x430b0#64 = (SphincsVerifierLastLeaf.lastTailState s).getReg .x10 := by
  simp [decodeHead,runSchedule,decodeHeadSchedule,SphincsVerifierLastLeaf.lastTailState,
    execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getByte,alignToDword,byteOffset]
theorem decodeHead_admissible (s : MachineState) (answer : BitVec 256)
    (bytes : AnswerBytes s answer) :
    (decodeHead s).getMem 0x430b0#64 = 0 ↔ Concrete.Admissible (truncateMessageDigest answer) := by
  rw [decodeHead_last,← BitVec.toNat_inj,SphincsVerifierLastLeaf.lastTail_digest s answer bytes]
  change (Concrete.digestLeaves (truncateMessageDigest answer) Concrete.lastIndexGroup).val = 0 ↔ _
  unfold Concrete.Admissible
  exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩

theorem dispatch_mem (s : MachineState) (a : Word) : (dispatch s).getMem a = s.getMem a := by
  simp [dispatch,runSchedule,dispatchSchedule,execInstrBr]

theorem skipLeaves_mem (s : MachineState) (a : Word) : (skipLeaves s).getMem a = s.getMem a := by
  simp [skipLeaves,runSchedule,skipLeavesSchedule,execInstrBr]

theorem finishTrial_mem (s : MachineState) (a : Word) : (finishTrial s).getMem a = s.getMem a := by
  simp [finishTrial,runSchedule,finishTrialSchedule,execInstrBr]

def selectorSchedule (tree : Fin 24) : List (Word × Instr) := [
  (BitVec.ofNat 64 (0x1860+44*tree.val),.LUI .x6 66),
  (BitVec.ofNat 64 (0x1864+44*tree.val),.ADDI .x6 .x6 0),
  (BitVec.ofNat 64 (0x1868+44*tree.val),.LBU .x10 .x6 (4+tree.val)),
  (BitVec.ofNat 64 (0x186c+44*tree.val),.LBU .x11 .x6 (5+tree.val)),
  (BitVec.ofNat 64 (0x1870+44*tree.val),.SRLI .x10 .x10 2),
  (BitVec.ofNat 64 (0x1874+44*tree.val),.SLLI .x11 .x11 6),
  (BitVec.ofNat 64 (0x1878+44*tree.val),.ADD .x10 .x10 .x11),
  (BitVec.ofNat 64 (0x187c+44*tree.val),.ANDI .x10 .x10 255),
  (BitVec.ofNat 64 (0x1880+44*tree.val),.LUI .x7 69),
  (BitVec.ofNat 64 (0x1884+44*tree.val),.ADDI .x7 .x7 (-2048+tree.val)),
  (BitVec.ofNat 64 (0x1888+44*tree.val),.SB .x7 .x10 0)]

theorem selector_code (tree : Fin 24) : ∀ e ∈ selectorSchedule tree,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 = some (.base e.2) := by
  fin_cases tree <;> decide

theorem selector_checked (tree : Fin 24) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (0x1860+44*tree.val)) : Checked (selectorSchedule tree) s := by
  fin_cases tree <;>
    simp [Checked,selectorSchedule,execInstrBr,ordinaryStep,memoryArgumentsValid,
      accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,pc,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setByte,alignToDword,byteOffset]
theorem selector_state (tree : Fin 24) (s : MachineState) :
    runSchedule (selectorSchedule tree) s = leafState tree s := rfl
theorem selector_block (tree : Fin 24) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (0x1860+44*tree.val)) :
    OrdinarySteps SphincsMaskedImages.sign s 11 (leafState tree s) := by
  exact checked_sound _ (selectorSchedule tree) (selector_code tree) s (selector_checked tree s pc)
theorem selector_pc (tree : Fin 24) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (0x1860+44*tree.val)) :
    (leafState tree s).pc = BitVec.ofNat 64 (0x1860+44*(tree.val+1)) := by
  simp [leafState,execInstrBr,pc,BitVec.ofNat_add_ofNat]
  congr 1

theorem selectors_contract (s : MachineState) (pc : s.pc = 0x1860) :
    ∀ n (bound : n ≤ 24),
      OrdinarySteps SphincsMaskedImages.sign s (11*n) (leafStates s n bound) ∧
      (leafStates s n bound).pc = BitVec.ofNat 64 (0x1860+44*n) := by
  intro n
  induction n with
  | zero => intro bound;exact ⟨OrdinarySteps.refl s,pc⟩
  | succ n ih =>
    intro bound
    obtain ⟨run,loc⟩ := ih (by omega)
    have next := selector_block ⟨n,by omega⟩ _ loc
    have endPc := selector_pc ⟨n,by omega⟩ _ loc
    exact ⟨by simpa [leafStates,Nat.mul_add] using run.append next,endPc⟩

theorem digest_answer_bytes (hash : Hash) (s : MachineState) :
    AnswerBytes (digestAnswer hash s) (hash (hashInput (digestPrepare s))) := by
  intro i
  rw [SphincsVerifierFtsRootCopyBytes.getByte_word _ 0x42000 i.val (by decide) (by omega)]
  change extractByte ((writeHash (digestPrepare s) (hash (hashInput (digestPrepare s)))).getMem
    (BitVec.ofNat 64 (0x42000+8*(i.val/8)))) (i.val%8) = _
  rw [SphincsVerifierMessageAnswer.writeHash_word _ _ (digest_registers s).2.2.1 ⟨i.val/8,by omega⟩]
  generalize hash (hashInput (digestPrepare s)) = value
  ext j hj
  have hb : i.val % 8 * 8 + j < 64 := by omega
  have he : 64 * (i.val / 8) + (i.val % 8 * 8 + j) = 8 * i.val + j := by omega
  simp [extractByte,hb,he]

def PreservedAddress (a : Word) : Prop :=
  (a.toNat < 0x20088 ∨ 0x200a0 ≤ a.toNat) ∧ (a.toNat < 0x40000 ∨ 0x43020 ≤ a.toNat)

theorem digestPrepare_frame (s : MachineState) (a : Word) (outside : PreservedAddress a) :
    (digestPrepare s).getMem a = s.getMem a := by
  have h1 : a.toNat < 0x40000 ∨ 0x40028 ≤ a.toNat := by rcases outside.2 with h | h <;> omega
  have h2 : a.toNat < 0x40028 ∨ 0x40070 ≤ a.toNat := by rcases outside.2 with h | h <;> omega
  have h3 : a.toNat < 0x43000 ∨ 0x43020 ≤ a.toNat := by rcases outside.2 with h | h <;> omega
  rw [digestPrepare,digestHeader_frame _ _ h1,digestPayload_frame _ _ h2,
    digestInit_frame _ _ outside.1 h3]

theorem digestAnswer_frame (hash : Hash) (s : MachineState) (a : Word) (outside : PreservedAddress a) :
    (digestAnswer hash s).getMem a = s.getMem a := by
  have ne (b : Word) (lo : 0x42000 ≤ b.toNat) (hi : b.toNat < 0x42020) : a ≠ b := by
    intro eq; have ha := outside.2;rw [eq] at ha;rcases ha with h | h <;> omega
  have dst := (digest_registers s).2.2.1
  simp [digestAnswer,writeHash,dst,MachineState.writeWords,ne,digestPrepare_frame s a outside]

theorem digest_word_frame (hash : Hash) (s : MachineState) (a : Nat) (low : a < 0x20088) :
    (digestAnswer hash s).getWord32 (BitVec.ofNat 64 a) = s.getWord32 (BitVec.ofNat 64 a) := by
  have small : (alignToDword (BitVec.ofNat 64 a)).toNat ≤ a := by
    unfold alignToDword;rw [BitVec.toNat_and]
    apply le_trans Nat.and_le_left
    simp only [BitVec.toNat_ofNat];exact Nat.mod_le _ _
  simp only [MachineState.getWord32,digestAnswer_frame hash s (alignToDword (BitVec.ofNat 64 a)) ⟨Or.inl (by omega),Or.inl (by omega)⟩]

theorem digestAnswer_controls (hash : Hash) (s : MachineState) (i : Fin 4) :
    (digestAnswer hash s).getMem (BitVec.ofNat 64 (0x43000+8*i.val)) = 0 := by
  have dst := (digest_registers s).2.2.1
  have zero := digestInit_controls s i
  have frame : (digestAnswer hash s).getMem (BitVec.ofNat 64 (0x43000+8*i.val)) =
      (digestPrepare s).getMem (BitVec.ofNat 64 (0x43000+8*i.val)) := by
    fin_cases i <;> simp [digestAnswer,writeHash,dst,MachineState.writeWords]
  rw [frame]
  fin_cases i <;>
    simpa [digestPrepare,digestHeader_frame,digestPayload_frame] using zero

theorem digestAnswer_context (hash : Hash) (s : MachineState) (parameter : Digest) (seed : MasterSeed)
    (message : SphincsSecurity.Message) (trial : Nat) (ctx : Context s parameter seed message trial) :
    Context (digestAnswer hash s) parameter seed message trial := by
  refine ⟨digestAnswer_controls hash s 0,digestAnswer_controls hash s 1,?_,ctx.bounded,?_,?_,?_⟩
  · rw [digestAnswer_frame _ _ _ (by constructor <;> simp [PreservedAddress])];exact ctx.counter
  · intro i
    rw [digest_word_frame _ _ _ (by have := i.isLt;omega)];exact ctx.parameterWords i
  · intro i
    rw [digest_word_frame _ _ _ (by have := i.isLt;omega)];exact ctx.keyWords i
  · intro i
    rw [digest_word_frame _ _ _ (by have := i.isLt;omega)];exact ctx.messageWords i

def randomizerValue (hash : Hash) (parameter : Digest) (seed : MasterSeed)
    (message : SphincsSecurity.Message) (trial : Nat) : Digest :=
  truncateHash (hash (toQuery (randomizerHashInput parameter seed message (BitVec.ofNat 32 trial))))
def messageAnswer (hash : Hash) (parameter root : Digest) (seed : MasterSeed)
    (message : SphincsSecurity.Message) (trial : Nat) : BitVec 256 :=
  hash (toQuery (tweakableHashInput parameter .message
    (Concrete.messageDigestPayload root message (randomizerValue hash parameter seed message trial))))
def trialAnswer (hash : Hash) (s : MachineState) : MachineState := digestAnswer hash (nonceAnswer hash s)

theorem trialAnswer_contract (hash : Hash) (s : MachineState) (pc : s.pc = 0x1520)
    (parameter root : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (trial : Nat) (ctx : Context s parameter seed message trial) (rootWords : Words20 s 0x20060 root) :
    Trace hash SphincsMaskedImages.sign s 235 265 2 4 (trialAnswer hash s) ∧
    (trialAnswer hash s).pc = 0x17f4 ∧
    Context (trialAnswer hash s) parameter seed message trial ∧
    AnswerBytes (trialAnswer hash s) (messageAnswer hash parameter root seed message trial) := by
  have npc : (nonceAnswer hash s).pc = 0x163c := by simp [nonceAnswer,writeHash,nonce_pc s pc]
  have nc := answer_context hash s parameter seed message trial ctx
  have nr := SphincsMaskedSignHonestAuthentication.frame_words20 _ _
    (fun a h => answer_frame hash s a (Or.inl h)) 0x20060 (by decide) root rootWords
  have nq := answer_value hash s parameter seed message trial ctx
  have input := digest_query_eq (nonceAnswer hash s) parameter root
    (randomizerValue hash parameter seed message trial) message nc.parameterWords nr nq nc.messageWords
  refine ⟨(nonce_trace hash s pc).trans (digest_trace hash _ npc),?_,
    digestAnswer_context hash _ parameter seed message trial nc,?_⟩
  · simp [trialAnswer,digestAnswer,writeHash,digest_pc _ npc]
  · have bytes := digest_answer_bytes hash (nonceAnswer hash s)
    rw [input] at bytes
    exact bytes

def TrialAddress (a : Word) : Prop := a.toNat < 0x20088 ∨
  a = 0x43000#64 ∨ a = 0x43008#64 ∨ a = 0x43098#64

theorem decodeHead_frame (s : MachineState) (a : Word)
    (outside : a ≠ 0x43018#64 ∧ a ≠ 0x43078#64 ∧ a ≠ 0x430b0#64) :
    (decodeHead s).getMem a = s.getMem a := by
  simp [decodeHead,runSchedule,decodeHeadSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,outside.1,outside.2.1,outside.2.2]

theorem decodeHead_trial_frame (s : MachineState) (a : Word) (ha : TrialAddress a) :
    (decodeHead s).getMem a = s.getMem a := by
  apply decodeHead_frame
  have ne (b : Word) (bad : ¬ TrialAddress b) : a ≠ b := by intro eq;subst a;exact bad ha
  exact ⟨ne _ (by unfold TrialAddress;decide),ne _ (by unfold TrialAddress;decide),ne _ (by unfold TrialAddress;decide)⟩

theorem selector_low_frame (tree : Fin 24) (s : MachineState) (a : Word)
    (low : a.toNat < 0x44800) : (leafState tree s).getMem a = s.getMem a := by
  have ne (b : Word) (high : 0x44800 ≤ b.toNat) : a ≠ b := by intro eq;rw [eq] at low;omega
  fin_cases tree <;>
    simp [leafState,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,MachineState.setByte,alignToDword,byteOffset,ne]

theorem selectors_low_frame (s : MachineState) (a : Word) (low : a.toNat < 0x44800) :
    ∀ n (bound : n ≤ 24), (leafStates s n bound).getMem a = s.getMem a := by
  intro n;induction n with
  | zero => intro bound;rfl
  | succ n ih =>
    intro bound
    rw [leafStates,selector_low_frame _ _ _ low]
    exact ih (by omega)

theorem decodeHead_answer (s : MachineState) (answer : BitVec 256) (bytes : AnswerBytes s answer) :
    AnswerBytes (decodeHead s) answer := by
  intro i
  have ne (b : Word) (high : 0x43000 ≤ b.toNat) :
      alignToDword (BitVec.ofNat 64 (0x42000+i.val)) ≠ b := by
    intro eq
    have small : (alignToDword (BitVec.ofNat 64 (0x42000+i.val))).toNat < 0x43000 := by
      unfold alignToDword;rw [BitVec.toNat_and]
      apply lt_of_le_of_lt Nat.and_le_left
      simp only [BitVec.toNat_ofNat];omega
    rw [eq] at small;omega
  change extractByte ((decodeHead s).getMem _) _ = _
  rw [decodeHead_frame _ _ ⟨ne _ (by decide),ne _ (by decide),ne _ (by decide)⟩]
  exact bytes i

theorem memory_answer (before after : MachineState)
    (frame : ∀ a, after.getMem a = before.getMem a)
    (answer : BitVec 256) (bytes : AnswerBytes before answer) : AnswerBytes after answer := by
  intro i
  change extractByte (after.getMem _) _ = _
  rw [frame];exact bytes i

theorem trial_word_frame (before after : MachineState)
    (frame : ∀ a, TrialAddress a → after.getMem a = before.getMem a)
    (a : Nat) (low : a < 0x20088) :
    after.getWord32 (BitVec.ofNat 64 a) = before.getWord32 (BitVec.ofNat 64 a) := by
  have small : (alignToDword (BitVec.ofNat 64 a)).toNat ≤ a := by
    unfold alignToDword;rw [BitVec.toNat_and]
    apply le_trans Nat.and_le_left
    simp only [BitVec.toNat_ofNat];exact Nat.mod_le _ _
  simp only [MachineState.getWord32,frame (alignToDword (BitVec.ofNat 64 a)) (Or.inl (by omega))]

theorem context_frame (before after : MachineState)
    (frame : ∀ a, TrialAddress a → after.getMem a = before.getMem a)
    (parameter : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (trial : Nat) (ctx : Context before parameter seed message trial) :
    Context after parameter seed message trial := by
  refine ⟨?_,?_,?_,ctx.bounded,?_,?_,?_⟩
  · rw [frame _ (by simp [TrialAddress])];exact ctx.layer
  · rw [frame _ (by simp [TrialAddress])];exact ctx.tree
  · rw [frame _ (by simp [TrialAddress])];exact ctx.counter
  · intro i;rw [trial_word_frame _ _ frame _ (by have := i.isLt;omega)];exact ctx.parameterWords i
  · intro i;rw [trial_word_frame _ _ frame _ (by have := i.isLt;omega)];exact ctx.keyWords i
  · intro i;rw [trial_word_frame _ _ frame _ (by have := i.isLt;omega)];exact ctx.messageWords i

def accepted (s : MachineState) : MachineState := finishTrial (leafStates (dispatch (decodeHead s)) 24 (by decide))
def rejected (s : MachineState) : MachineState := finishTrial (skipLeaves (dispatch (decodeHead s)))

theorem accepted_contract (s : MachineState) (pc : s.pc = 0x17f4)
    (answer : BitVec 256) (bytes : AnswerBytes s answer)
    (admissible : Concrete.Admissible (truncateMessageDigest answer)) :
    OrdinarySteps SphincsMaskedImages.sign s 294 (accepted s) ∧
    (accepted s).pc = 0x1cc8 ∧
    (∀ a, TrialAddress a → (accepted s).getMem a = s.getMem a) ∧
    (∀ tree : Fin 24, ((accepted s).getByte (BitVec.ofNat 64 (0x44800+tree.val))).toNat =
      abstractLeaf answer tree) := by
  have headPc := decodeHead_pc s pc
  have zero := (decodeHead_admissible s answer bytes).2 admissible
  have dispatchPc := dispatch_accept_pc _ headPc zero
  obtain ⟨leaves,leavesPc⟩ := selectors_contract _ dispatchPc 24 (by decide)
  have leafZero : (leafStates (dispatch (decodeHead s)) 24 (by decide)).getMem 0x430b0#64 = 0 := by
    rw [selectors_low_frame _ _ (by decide),dispatch_mem,zero]
  have front := (decodeHead_block s pc).append (dispatch_block _ headPc)
  have full := (front.append leaves).append (finishTrial_block _ leavesPc)
  refine ⟨full,finishTrial_accept_pc _ leavesPc leafZero,?_,?_⟩
  · intro a ha
    have low : a.toNat < 0x44800 := by
      rcases ha with h | h | h | h
      · omega
      all_goals rw [h];decide
    rw [accepted,finishTrial_mem,selectors_low_frame _ _ low,dispatch_mem]
    exact decodeHead_trial_frame s a ha
  · intro tree
    have b := memory_answer _ _ (dispatch_mem (decodeHead s)) answer (decodeHead_answer s answer bytes)
    have selectors := leafStates_selectors _ answer b 24 (by decide) tree (by omega)
    simpa only [accepted,MachineState.getByte,finishTrial_mem] using selectors

theorem rejected_contract (s : MachineState) (pc : s.pc = 0x17f4)
    (answer : BitVec 256) (bytes : AnswerBytes s answer)
    (inadmissible : ¬ Concrete.Admissible (truncateMessageDigest answer)) :
    OrdinarySteps SphincsMaskedImages.sign s 31 (rejected s) ∧
    (rejected s).pc = 0x1c90 ∧
    (∀ a, TrialAddress a → (rejected s).getMem a = s.getMem a) := by
  have headPc := decodeHead_pc s pc
  have nonzero : (decodeHead s).getMem 0x430b0#64 ≠ 0#64 :=
    fun h => inadmissible ((decodeHead_admissible s answer bytes).1 h)
  have dispatchPc := dispatch_reject_pc _ headPc nonzero
  have skipPc := skipLeaves_pc _ dispatchPc
  have stillNonzero : (skipLeaves (dispatch (decodeHead s))).getMem 0x430b0#64 ≠ 0#64 := by
    simpa only [skipLeaves_mem,dispatch_mem] using nonzero
  have full := (((decodeHead_block s pc).append (dispatch_block _ headPc)).append
    (skipLeaves_block _ dispatchPc)).append (finishTrial_block _ skipPc)
  refine ⟨full,finishTrial_reject_pc _ skipPc stillNonzero,?_⟩
  intro a ha
  rw [rejected,finishTrial_mem,skipLeaves_mem,dispatch_mem]
  exact decodeHead_trial_frame s a ha

theorem retry_counter (s : MachineState) :
    (retry s).getMem 0x43098#64 = s.getMem 0x43098#64 + 1 := by
  simp [retry,runSchedule,retrySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem retry_mem (s : MachineState) (a : Word) (different : a ≠ 0x43098#64) :
    (retry s).getMem a = s.getMem a := by
  simp [retry,runSchedule,retrySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,different]

theorem retry_pc (s : MachineState) (pc : s.pc = 0x1c90) (trial : Nat)
    (counter : s.getMem 0x43098#64 = BitVec.ofNat 64 trial) (bound : trial+1 < 2^20) :
    (retry s).pc = 0x1520 := by
  have unequal : BitVec.ofNat 64 trial + 1#64 ≠ 0x100000#64 := by
    intro equal
    have h := congrArg BitVec.toNat equal
    simp [BitVec.toNat_add] at h
    omega
  simp [retry,runSchedule,retrySchedule,execInstrBr,signExtend12,signExtend13,pc,counter,unequal,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem retry_exhausted_pc (s : MachineState) (pc : s.pc = 0x1c90)
    (counter : s.getMem 0x43098#64 = 1048575#64) : (retry s).pc = 0x1cc4 := by
  simp [retry,runSchedule,retrySchedule,execInstrBr,signExtend12,signExtend13,pc,counter,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem retry_context (s : MachineState) (parameter : Digest) (seed : MasterSeed)
    (message : SphincsSecurity.Message) (trial : Nat) (ctx : Context s parameter seed message trial)
    (bound : trial+1 < 2^20) : Context (retry s) parameter seed message (trial+1) := by
  have frame (a : Word) (low : a.toNat < 0x40000) : (retry s).getMem a = s.getMem a :=
    retry_mem s a (by intro eq;rw [eq] at low;contradiction)
  refine ⟨?_,?_,?_,bound,?_,?_,?_⟩
  · rw [retry_mem _ _ (by decide)];exact ctx.layer
  · rw [retry_mem _ _ (by decide)];exact ctx.tree
  · rw [retry_counter,ctx.counter]
    change BitVec.ofNat 64 trial + BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_add_ofNat]
  · exact SphincsMaskedSignHonestAuthentication.frame_words20 _ _ frame 0x74 (by decide) _ ctx.parameterWords
  · exact SphincsMaskedSignHonestAuthentication.frame_words32 _ _ frame seed ctx.keyWords
  · intro i
    rw [SphincsMaskedSignHonestAuthentication.frame_word _ _ frame (4*i.val) (by have := i.isLt;omega)]
    exact ctx.messageWords i

def acceptedTrial (hash : Hash) (s : MachineState) := accepted (trialAnswer hash s)
def rejectedTrial (hash : Hash) (s : MachineState) := retry (rejected (trialAnswer hash s))

theorem accepted_trial (hash : Hash) (s : MachineState) (pc : s.pc = 0x1520)
    (parameter root : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (trial : Nat) (ctx : Context s parameter seed message trial) (rootWords : Words20 s 0x20060 root)
    (admissible : Concrete.Admissible (truncateMessageDigest (messageAnswer hash parameter root seed message trial))) :
    Trace hash SphincsMaskedImages.sign s 529 559 2 4 (acceptedTrial hash s) ∧
    (acceptedTrial hash s).pc = 0x1cc8 ∧
    Context (acceptedTrial hash s) parameter seed message trial ∧
    (∀ tree : Fin 24, ((acceptedTrial hash s).getByte (BitVec.ofNat 64 (0x44800+tree.val))).toNat =
      abstractLeaf (messageAnswer hash parameter root seed message trial) tree) := by
  obtain ⟨run,loc,core,bytes⟩ := trialAnswer_contract hash s pc parameter root seed message trial ctx rootWords
  obtain ⟨back,endPc,frame,selectors⟩ := accepted_contract _ loc _ bytes admissible
  exact ⟨run.trans back.trace,endPc,context_frame _ _ frame parameter seed message trial core,selectors⟩

theorem rejected_trial (hash : Hash) (s : MachineState) (pc : s.pc = 0x1520)
    (parameter root : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (trial : Nat) (ctx : Context s parameter seed message trial) (rootWords : Words20 s 0x20060 root)
    (inadmissible : ¬ Concrete.Admissible (truncateMessageDigest (messageAnswer hash parameter root seed message trial)))
    (remaining : trial+1 < 2^20) :
    Trace hash SphincsMaskedImages.sign s 279 309 2 4 (rejectedTrial hash s) ∧
    (rejectedTrial hash s).pc = 0x1520 ∧
    Context (rejectedTrial hash s) parameter seed message (trial+1) := by
  obtain ⟨run,loc,core,bytes⟩ := trialAnswer_contract hash s pc parameter root seed message trial ctx rootWords
  obtain ⟨back,endPc,frame⟩ := rejected_contract _ loc _ bytes inadmissible
  have core' := context_frame _ _ frame parameter seed message trial core
  exact ⟨(run.trans back.trace).trans (retry_block _ endPc).trace,
    retry_pc _ endPc trial core'.counter remaining,retry_context _ parameter seed message trial core' remaining⟩

theorem trialAnswer_root (hash : Hash) (s : MachineState) (root : Digest)
    (words : Words20 s 0x20060 root) : Words20 (trialAnswer hash s) 0x20060 root := by
  intro i
  rw [trialAnswer,digest_word_frame _ _ _ (by have := i.isLt;omega)]
  rw [SphincsMaskedSignHonestAuthentication.frame_word _ _
    (fun a h => answer_frame hash s a (Or.inl h)) (0x20060+4*i.val) (by have := i.isLt;omega)]
  exact words i

theorem accepted_trial_root (hash : Hash) (s : MachineState) (pc : s.pc = 0x1520)
    (parameter root : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (trial : Nat) (ctx : Context s parameter seed message trial) (rootWords : Words20 s 0x20060 root)
    (admissible : Concrete.Admissible (truncateMessageDigest (messageAnswer hash parameter root seed message trial))) :
    Words20 (acceptedTrial hash s) 0x20060 root := by
  obtain ⟨_,loc,_,bytes⟩ := trialAnswer_contract hash s pc parameter root seed message trial ctx rootWords
  have frame := (accepted_contract _ loc _ bytes admissible).2.2.1
  have words := trialAnswer_root hash s root rootWords
  intro i
  exact (trial_word_frame _ _ frame (0x20060+4*i.val) (by have := i.isLt;omega)).trans (words i)

theorem rejected_trial_root (hash : Hash) (s : MachineState) (pc : s.pc = 0x1520)
    (parameter root : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (trial : Nat) (ctx : Context s parameter seed message trial) (rootWords : Words20 s 0x20060 root)
    (inadmissible : ¬ Concrete.Admissible (truncateMessageDigest (messageAnswer hash parameter root seed message trial))) :
    Words20 (rejectedTrial hash s) 0x20060 root := by
  obtain ⟨_,loc,_,bytes⟩ := trialAnswer_contract hash s pc parameter root seed message trial ctx rootWords
  have frame := (rejected_contract _ loc _ bytes inadmissible).2.2
  have words := trialAnswer_root hash s root rootWords
  intro i
  have retryFrame (a : Word) (low : a.toNat < 0x40000) :
      (retry (rejected (trialAnswer hash s))).getMem a = (rejected (trialAnswer hash s)).getMem a :=
    retry_mem _ a (by intro eq;rw [eq] at low;contradiction)
  exact (SphincsMaskedSignHonestAuthentication.frame_word _ _ retryFrame
    (0x20060+4*i.val) (by have := i.isLt;omega)).trans
      ((trial_word_frame _ _ frame (0x20060+4*i.val) (by have := i.isLt;omega)).trans (words i))

theorem answer_first_word (s : MachineState) (answer : BitVec 256) (bytes : AnswerBytes s answer) :
    s.getMem 0x42000 = answer.extractLsb' 0 64 := by
  ext j hj
  have byte := bytes ⟨j/8,by omega⟩
  rw [SphincsVerifierFtsRootCopyBytes.getByte_word s 0x42000 (j/8) (by decide) (by omega)] at byte
  have hdiv : j/8/8 = 0 := by omega
  have hmod : j/8%8 = j/8 := by omega
  simp only [hdiv,hmod,Nat.mul_zero,Nat.add_zero] at byte
  have bit := congrArg (fun x : BitVec 8 => x.getLsbD (j%8)) byte
  rw [← BitVec.getLsbD_eq_getElem]
  simpa [extractByte,BitVec.getLsbD_extractLsb',show j%8<8 by omega,
    show 8*(j/8)+j%8=j by omega,show j/8*8+j%8=j by omega,
    SphincsVerifierFtsRootCopy.wordAddress] using bit

theorem decodeHead_index (s : MachineState) :
    (decodeHead s).getMem 0x43078 = (SphincsVerifierIndexPrefix.indexValueState s).getReg .x10 := by
  simp [decodeHead,runSchedule,decodeHeadSchedule,SphincsVerifierIndexPrefix.indexValueState,
    execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem accepted_index (s : MachineState) (answer : BitVec 256) (bytes : AnswerBytes s answer) :
    ((accepted s).getMem 0x43078).toNat = (Concrete.digestIndex (truncateMessageDigest answer)).val := by
  rw [accepted,finishTrial_mem,leafStates_msgIndex,dispatch_mem,decodeHead_index]
  exact SphincsVerifierIndexPrefix.indexValue_eq_digestIndex s answer (answer_first_word s answer bytes)

theorem accepted_trial_index (hash : Hash) (s : MachineState) (pc : s.pc = 0x1520)
    (parameter root : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (trial : Nat) (ctx : Context s parameter seed message trial) (rootWords : Words20 s 0x20060 root) :
    ((acceptedTrial hash s).getMem 0x43078).toNat =
      (Concrete.digestIndex (truncateMessageDigest (messageAnswer hash parameter root seed message trial))).val := by
  have bytes := (trialAnswer_contract hash s pc parameter root seed message trial ctx rootWords).2.2.2
  exact accepted_index _ _ bytes

/-- One actual grind trial from the post-signature-prefix PC, with both branch
    costs, abstract success predicate, and the invariant needed for a retry. -/
theorem first_trial (hash : Hash) (s : MachineState) (pc : s.pc = 0x1510)
    (parameter root : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (layer : s.getMem 0x43000#64 = 0) (tree : s.getMem 0x43008#64 = 0)
    (par : Words20 s 0x74 parameter) (key : Words32 s seed)
    (rootWords : Words20 s 0x20060 root)
    (msg : ∀ i : Fin 8, s.getWord32 (BitVec.ofNat 64 (4*i.val)) = message.extractLsb' (32*i.val) 32) :
    let admissible := Concrete.Admissible (truncateMessageDigest (messageAnswer hash parameter root seed message 0))
    (admissible ∧
      Trace hash SphincsMaskedImages.sign s 533 563 2 4 (acceptedTrial hash (init s)) ∧
      (acceptedTrial hash (init s)).pc = 0x1cc8 ∧
      Context (acceptedTrial hash (init s)) parameter seed message 0 ∧
      Words20 (acceptedTrial hash (init s)) 0x20060 root) ∨
    (¬admissible ∧
      Trace hash SphincsMaskedImages.sign s 283 313 2 4 (rejectedTrial hash (init s)) ∧
      (rejectedTrial hash (init s)).pc = 0x1520 ∧
      Context (rejectedTrial hash (init s)) parameter seed message 1 ∧
      Words20 (rejectedTrial hash (init s)) 0x20060 root) := by
  dsimp
  have ctx := init_context s parameter seed message layer tree par key msg
  have roots : Words20 (init s) 0x20060 root := by
    apply SphincsMaskedSignHonestAuthentication.frame_words20 _ _ ?_ 0x20060 (by decide) root rootWords
    intro a low
    exact init_frame s a (by intro eq;rw [eq] at low;contradiction)
  by_cases admissible : Concrete.Admissible (truncateMessageDigest (messageAnswer hash parameter root seed message 0))
  · obtain ⟨run,loc,core,_⟩ := accepted_trial hash (init s) (init_pc s pc) parameter root seed message 0 ctx roots admissible
    exact Or.inl ⟨admissible,(init_trace s pc).trace.trans run,loc,core,
      accepted_trial_root hash (init s) (init_pc s pc) parameter root seed message 0 ctx roots admissible⟩
  · obtain ⟨run,loc,core⟩ := rejected_trial hash (init s) (init_pc s pc) parameter root seed message 0 ctx roots admissible (by decide)
    exact Or.inr ⟨admissible,(init_trace s pc).trace.trans run,loc,core,
      rejected_trial_root hash (init s) (init_pc s pc) parameter root seed message 0 ctx roots admissible⟩

theorem digestAnswer_afterInit_frame (hash : Hash) (s : MachineState) (a : Word) (low : a.toNat < 0x40000) :
    (digestAnswer hash s).getMem a = (digestInit s).getMem a := by
  have ne (b : Word) (high : 0x42000 ≤ b.toNat) : a ≠ b := by intro eq;rw [eq] at low;omega
  have dst := (digest_registers s).2.2.1
  have hashFrame : (digestAnswer hash s).getMem a = (digestPrepare s).getMem a := by
    simp [digestAnswer,writeHash,dst,MachineState.writeWords,ne]
  rw [hashFrame,digestPrepare,digestHeader_frame _ _ (Or.inl low),
    digestPayload_frame _ _ (Or.inl (by omega))]

theorem accepted_low_frame (s : MachineState) (a : Word) (low : a.toNat < 0x40000) :
    (accepted s).getMem a = s.getMem a := by
  have ne (b : Word) (high : 0x43000 ≤ b.toNat) : a ≠ b := by intro eq;rw [eq] at low;omega
  rw [accepted,finishTrial_mem,selectors_low_frame _ _ (by omega),dispatch_mem,
    decodeHead_frame _ _ ⟨ne _ (by decide),ne _ (by decide),ne _ (by decide)⟩]

theorem trial_randomizer_words (hash : Hash) (s : MachineState) (parameter : Digest) (seed : MasterSeed)
    (message : SphincsSecurity.Message) (trial : Nat) (ctx : Context s parameter seed message trial) :
    Words20 (trialAnswer hash s) 0x20088 (randomizerValue hash parameter seed message trial) := by
  have initial : Words20 (digestInit (nonceAnswer hash s)) 0x20088
      (randomizerValue hash parameter seed message trial) := by
    intro i
    exact (digestInit_words _ i).trans (answer_value hash s parameter seed message trial ctx i)
  exact SphincsMaskedSignHonestAuthentication.frame_words20 _ _
    (digestAnswer_afterInit_frame hash (nonceAnswer hash s)) 0x20088 (by decide) _ initial

theorem accepted_randomizer_words (hash : Hash) (s : MachineState) (parameter : Digest) (seed : MasterSeed)
    (message : SphincsSecurity.Message) (trial : Nat) (ctx : Context s parameter seed message trial) :
    Words20 (acceptedTrial hash s) 0x20088 (randomizerValue hash parameter seed message trial) :=
  SphincsMaskedSignHonestAuthentication.frame_words20 _ _ (accepted_low_frame (trialAnswer hash s))
    0x20088 (by decide) _ (trial_randomizer_words hash s parameter seed message trial ctx)

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.trialAnswer_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trialAnswer_contract

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.accepted_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted_trial

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.rejected_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rejected_trial

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.first_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_trial

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.accepted_trial_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted_trial_index

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.accepted_randomizer_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted_randomizer_words

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.retry_exhausted_pc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms retry_exhausted_pc

def retryStates (hash : Hash) (s : MachineState) : Nat → MachineState
  | 0 => s
  | n+1 => rejectedTrial hash (retryStates hash s n)

/-- Parameterized retry induction. The retained root and input words make the
    next trial's abstract queries independent of transient machine registers. -/
theorem retries_contract (hash : Hash) (s : MachineState) (pc : s.pc = 0x1520)
    (parameter root : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (trial : Nat) (ctx : Context s parameter seed message trial) (rootWords : Words20 s 0x20060 root) :
    ∀ n, trial+n < 2^20 →
      (∀ j, j < n → ¬ Concrete.Admissible
        (truncateMessageDigest (messageAnswer hash parameter root seed message (trial+j)))) →
      Trace hash SphincsMaskedImages.sign s (279*n) (309*n) (2*n) (4*n) (retryStates hash s n) ∧
      (retryStates hash s n).pc = 0x1520 ∧
      Context (retryStates hash s n) parameter seed message (trial+n) ∧
      Words20 (retryStates hash s n) 0x20060 root := by
  intro n
  induction n with
  | zero =>
    intro bound failed
    exact ⟨Trace.refl s,pc,ctx,rootWords⟩
  | succ n ih =>
    intro bound failed
    obtain ⟨run,loc,core,roots⟩ := ih (by omega) (fun j hj => failed j (by omega))
    have bad := failed n (by omega)
    obtain ⟨step,endPc,nextCore⟩ := rejected_trial hash _ loc parameter root seed message
      (trial+n) core roots bad (by omega)
    have nextRoot := rejected_trial_root hash _ loc parameter root seed message (trial+n) core roots bad
    refine ⟨?_,endPc,?_,nextRoot⟩
    · simpa [retryStates,Nat.mul_add] using run.trans step
    · simpa [retryStates,Nat.add_assoc] using nextCore

-- Keep large concrete retry counts symbolic during later resource proofs.
attribute [irreducible] retryStates

/-- The last failed trial does not wrap or retry: the exact bytecode reaches
    its common rejection jump after the same two HASH calls. -/
theorem exhausted_trial (hash : Hash) (s : MachineState) (pc : s.pc = 0x1520)
    (parameter root : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (ctx : Context s parameter seed message 1048575) (rootWords : Words20 s 0x20060 root)
    (inadmissible : ¬ Concrete.Admissible
      (truncateMessageDigest (messageAnswer hash parameter root seed message 1048575))) :
    Trace hash SphincsMaskedImages.sign s 279 309 2 4 (rejectedTrial hash s) ∧
    (rejectedTrial hash s).pc = 0x1cc4 := by
  obtain ⟨run,loc,core,bytes⟩ := trialAnswer_contract hash s pc parameter root seed message 1048575 ctx rootWords
  obtain ⟨back,endPc,frame⟩ := rejected_contract _ loc _ bytes inadmissible
  have core' := context_frame _ _ frame parameter seed message 1048575 core
  exact ⟨(run.trans back.trace).trans (retry_block _ endPc).trace,
    retry_exhausted_pc _ endPc core'.counter⟩

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.retries_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms retries_contract

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.exhausted_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exhausted_trial

/-- Closed resource counts when trial `n` is the first admissible trial. -/
theorem grind_success (hash : Hash) (s : MachineState) (pc : s.pc = 0x1520)
    (parameter root : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (ctx : Context s parameter seed message 0) (rootWords : Words20 s 0x20060 root)
    (n : Nat) (bound : n < 2^20)
    (prior : ∀ j, j < n → ¬ Concrete.Admissible
      (truncateMessageDigest (messageAnswer hash parameter root seed message j)))
    (success : Concrete.Admissible
      (truncateMessageDigest (messageAnswer hash parameter root seed message n))) :
    Trace hash SphincsMaskedImages.sign s (279*n+529) (309*n+559) (2*(n+1)) (4*(n+1))
      (acceptedTrial hash (retryStates hash s n)) ∧
    (acceptedTrial hash (retryStates hash s n)).pc = 0x1cc8 := by
  obtain ⟨run,loc,core,roots⟩ := retries_contract hash s pc parameter root seed message 0 ctx rootWords
    n (by simpa using bound) (by simpa using prior)
  obtain ⟨last,endPc,_,_⟩ := accepted_trial hash _ loc parameter root seed message n (by simpa using core) roots success
  exact ⟨by simpa [Nat.mul_add] using run.trans last,endPc⟩

/-- The cap bounds the complete failed grind without assumptions on the oracle:
    exactly 2^20 trials reach the rejection jump, with four compressions per trial. -/
theorem grind_exhaustion (hash : Hash) (s : MachineState) (pc : s.pc = 0x1520)
    (parameter root : Digest) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (ctx : Context s parameter seed message 0) (rootWords : Words20 s 0x20060 root)
    (failed : ∀ j, j < 2^20 → ¬ Concrete.Admissible
      (truncateMessageDigest (messageAnswer hash parameter root seed message j))) :
    Trace hash SphincsMaskedImages.sign s 292552704 324009984 2097152 4194304
      (rejectedTrial hash (retryStates hash s 1048575)) ∧
    (rejectedTrial hash (retryStates hash s 1048575)).pc = 0x1cc4 := by
  obtain ⟨run,loc,core,roots⟩ := retries_contract hash s pc parameter root seed message 0 ctx rootWords
    1048575 (by decide) (by intro j hj;simpa only [Nat.zero_add] using failed j (by omega))
  obtain ⟨last,endPc⟩ := exhausted_trial hash _ loc parameter root seed message core roots (failed 1048575 (by decide))
  exact ⟨run.trans last,endPc⟩

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.grind_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms grind_success

/-- info: 'SigGolfCandidate.SphincsMaskedSignNonceTrial.grind_exhaustion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms grind_exhaustion

end SigGolfCandidate.SphincsMaskedSignNonceTrial
