import SigGolfCandidate.SphincsMaskedParentCode

namespace SigGolfCandidate.SphincsMaskedParentNode
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedParentCode
open SphincsVerifierFtsRootCopy SphincsVerifierCopy SphincsVerifierCopyMemory
open SphincsVerifierMessageCopy SphincsVerifierFtsCopyAccess SphincsVerifierFtsPriorRoots SphincsVerifierFtsGenericCopyData
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem leftSetup_registers (s : MachineState) (base node : Nat)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node) :
    (leftSetup s).getReg .x6 = BitVec.ofNat 64 (base + 40 * node) ∧
      (leftSetup s).getReg .x7 = 0x40028 := by
  change s.getMem 0x43068#64 = BitVec.ofNat 64 base at hb
  change s.getMem 0x43088#64 = BitVec.ofNat 64 node at hn
  simp [leftSetup,runSchedule,leftSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,hb,hn]
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 base + (BitVec.ofNat 64 node * BitVec.ofNat 64 8 +
    BitVec.ofNat 64 node * BitVec.ofNat 64 32) = _
  rw [← BitVec.ofNat_mul,← BitVec.ofNat_mul,← BitVec.ofNat_add,← BitVec.ofNat_add]
  congr 1;omega

theorem leftSetup_frame (s : MachineState) (a : Word) : (leftSetup s).getMem a = s.getMem a := by
  simp [leftSetup,runSchedule,leftSetupSchedule,execInstrBr]

theorem rightSetup_frame (s : MachineState) (a : Word) : (rightSetup s).getMem a = s.getMem a := by
  simp [rightSetup,runSchedule,rightSetupSchedule,execInstrBr]

theorem rightSetup_registers (s : MachineState) (source : Nat) (hs : s.getReg .x6 = BitVec.ofNat 64 source) :
    (rightSetup s).getReg .x6 = BitVec.ofNat 64 (source + 20) ∧ (rightSetup s).getReg .x7 = 0x4003c := by
  simp [rightSetup,runSchedule,rightSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,hs,BitVec.ofNat_add]

def leftCopied (s : MachineState) := copyRootState (leftSetup s)
def children (s : MachineState) := copyRootState (rightSetup (leftCopied s))

theorem copyRoot_pc (s : MachineState) : (copyRootState s).pc = s.pc + 40 := by
  simp [copyRootState,copyWordState,execInstrBr,BitVec.add_assoc]

theorem copyRoot_registers (s : MachineState) :
    (copyRootState s).getReg .x6 = s.getReg .x6 ∧ (copyRootState s).getReg .x7 = s.getReg .x7 := by
  simp [copyRootState,copyWordState,execInstrBr,MachineState.getReg_setReg_ne,MachineState.setWord32]

theorem leftCopied_pc (s : MachineState) (pc : s.pc = 0x1620) : (leftCopied s).pc = 0x1678 := by
  rw [leftCopied,copyRoot_pc,leftSetup_pc s pc];rfl

theorem children_pc (s : MachineState) (pc : s.pc = 0x1620) : (children s).pc = 0x16ac := by
  rw [children,copyRoot_pc,rightSetup_pc _ (leftCopied_pc s pc)];rfl

theorem left_copy_code : Copy20Code SphincsMaskedImages.keygen 404 := by
  constructor <;> intro i <;> fin_cases i <;> decide

theorem right_copy_code : Copy20Code SphincsMaskedImages.keygen 417 := by
  constructor <;> intro i <;> fin_cases i <;> decide

theorem children_block (s : MachineState) (base node : Nat) (pc : s.pc = 0x1620)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : base + 40 * node + 40 ≤ 0x40000) (aligned : base % 4 = 0) :
    OrdinarySteps SphincsMaskedImages.keygen s 35 (children s) := by
  have left := leftSetup_registers s base node hb hn
  have lcopy := copy20_block_general SphincsMaskedImages.keygen 404 left_copy_code
    (leftSetup s) (base + 40 * node) 0x40028 (leftSetup_pc s pc) left.1 left.2
    (by omega) (by dsimp [MEMORY_BYTES];omega) (by decide) (by decide) (by decide)
  have source : (leftCopied s).getReg .x6 = BitVec.ofNat 64 (base + 40 * node) :=
    (copyRoot_registers (leftSetup s)).1.trans left.1
  have right := rightSetup_registers (leftCopied s) (base + 40 * node) source
  have rcopy := copy20_block_general SphincsMaskedImages.keygen 417 right_copy_code
    (rightSetup (leftCopied s)) (base + 40 * node + 20) 0x4003c
    (rightSetup_pc _ (leftCopied_pc s pc)) right.1 right.2
    (by omega) (by dsimp [MEMORY_BYTES];omega) (by decide) (by decide) (by decide)
  exact ordinary_trans _ _ _ _ 12 23 (leftSetup_block s pc)
    (ordinary_trans _ _ _ _ 10 13 lcopy (ordinary_trans _ _ _ _ 3 10
      (rightSetup_block _ (leftCopied_pc s pc)) rcopy))

def payloadWrites : List Word := [0x40028#64,0x40030#64,0x40038#64,0x40040#64,0x40048#64]

theorem children_frame (s : MachineState) (a : Word) (outside : a ∉ payloadWrites) :
    (children s).getMem a = s.getMem a := by
  have left : (leftSetup s).getReg .x7 = 0x40028 := by
    simp [leftSetup,runSchedule,leftSetupSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have right : (rightSetup (leftCopied s)).getReg .x7 = 0x4003c := by
    simp [rightSetup,runSchedule,rightSetupSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  change (copyRootState (rightSetup (leftCopied s))).getMem a = _
  rw [copyRoot_mem_frame]
  · rw [rightSetup_frame]
    change (copyRootState (leftSetup s)).getMem a = _
    rw [copyRoot_mem_frame]
    · exact leftSetup_frame s a
    · intro i;rw [left]
      fin_cases i <;> simp_all [payloadWrites,signExtend12,alignToDword]
  · intro i;rw [right]
    fin_cases i <;> simp_all [payloadWrites,signExtend12,alignToDword]

def headerWrites : List Word := [0x43010#64,0x43018#64,0x40000#64,0x40008#64,0x40010#64,0x40018#64,0x40020#64]

theorem hashPrepare_frame (s : MachineState) (a : Word) (outside : a ∉ headerWrites) :
    (hashPrepare s).getMem a = s.getMem a := by
  simp only [headerWrites,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := outside
  simp [hashPrepare,runSchedule,hashPrepareSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,h0,h1,h2,h3,h4,h5,h6]

theorem hashPrepare_registers (s : MachineState) :
    (hashPrepare s).getReg .x10 = 0x40000 ∧ (hashPrepare s).getReg .x11 = 640 ∧
      (hashPrepare s).getReg .x12 = 0x42000 ∧ (hashPrepare s).getReg .x5 = 1 := by
  simp [hashPrepare,runSchedule,hashPrepareSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

def answer (hash : Hash) (s : MachineState) :=
  writeHash (hashPrepare (children s)) (hash (hashInput (hashPrepare (children s))))

theorem answer_pc (hash : Hash) (s : MachineState) (pc : s.pc = 0x1620) :
    (answer hash s).pc = 0x1780 := by
  simp [answer,writeHash,hashPrepare_pc _ (children_pc s pc)]

def answerWrites : List Word := [0x42000#64,0x42008#64,0x42010#64,0x42018#64]
def preWrites := payloadWrites ++ headerWrites ++ answerWrites

theorem answer_frame (hash : Hash) (s : MachineState) (a : Word) (outside : a ∉ preWrites) :
    (answer hash s).getMem a = s.getMem a := by
  have split : (a ∉ payloadWrites ∧ a ∉ headerWrites) ∧ a ∉ answerWrites := by
    simpa only [preWrites,List.mem_append,not_or] using outside
  obtain ⟨⟨payload,header⟩,ans⟩ := split
  simp only [answerWrites,List.mem_cons,List.not_mem_nil,not_or] at ans
  obtain ⟨h0,h1,h2,h3⟩ := ans
  have dst := (hashPrepare_registers (children s)).2.2.1
  simp [answer,writeHash,dst,MachineState.writeWords,h0,h1,h2,h3]
  rw [hashPrepare_frame _ a header,children_frame s a payload]

theorem answer_trace (hash : Hash) (s : MachineState) (base node : Nat) (pc : s.pc = 0x1620)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : base + 40 * node + 40 ≤ 0x40000) (aligned : base % 4 = 0) :
    Trace hash SphincsMaskedImages.keygen s 88 103 1 2 (answer hash s) := by
  obtain ⟨src,bits,dst,service⟩ := hashPrepare_registers (children s)
  have fetch : fetch SphincsMaskedImages.keygen (hashPrepare (children s)) = some (.base .ECALL) := by
    rw [fetch_at,hashPrepare_pc _ (children_pc s pc)];decide
  have valid : hashArgumentsValid (hashPrepare (children s)) = true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (hashPrepare (children s))).1 = 640 := by simp [hashInput,bits]
  have step := Trace.hash (hash := hash) (image := SphincsMaskedImages.keygen)
    (hashPrepare (children s)) _ 0 0 0 0 fetch service valid (Trace.refl _)
  have hstep : Trace hash SphincsMaskedImages.keygen (hashPrepare (children s)) 1 16 1 2 (answer hash s) := by
    simp only [len] at step;exact step
  exact (children_block s base node pc hb hn bounded aligned).trace.trans
    ((hashPrepare_block _ (children_pc s pc)).trace.trans hstep)

/-- info: 'SigGolfCandidate.SphincsMaskedParentNode.answer_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms answer_trace


theorem storeSetup_frame (s : MachineState) (a : Word) : (storeSetup s).getMem a = s.getMem a := by
  simp [storeSetup,runSchedule,storeSetupSchedule,execInstrBr]

theorem storeSetup_registers (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node) :
    (storeSetup s).getReg .x6 = 0x42000 ∧
      (storeSetup s).getReg .x7 = BitVec.ofNat 64 (target + 20 * node) := by
  change s.getMem 0x43080#64 = BitVec.ofNat 64 target at ht
  change s.getMem 0x43088#64 = BitVec.ofNat 64 node at hn
  simp [storeSetup,runSchedule,storeSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ht,hn]
  simp only [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 target + (BitVec.ofNat 64 node * BitVec.ofNat 64 4 +
    BitVec.ofNat 64 node * BitVec.ofNat 64 16) = _
  rw [← BitVec.ofNat_mul,← BitVec.ofNat_mul,← BitVec.ofNat_add,← BitVec.ofNat_add]
  congr 1;omega

def stored (s : MachineState) := copyRootState (storeSetup s)
def next (hash : Hash) (s : MachineState) := nodeFinish (stored (answer hash s))

theorem store_code : Copy20Code SphincsMaskedImages.keygen 492 := by
  constructor <;> intro i <;> fin_cases i <;> decide

theorem stored_pc (s : MachineState) (pc : s.pc = 0x1780) : (stored s).pc = 0x17d8 := by
  rw [stored,copyRoot_pc,storeSetup_pc s pc];rfl

theorem stored_control (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : target + 20 * node + 20 ≤ 0x40000) (a : Word) (high : 0x40000 ≤ a.toNat) :
    (stored s).getMem a = s.getMem a := by
  change (copyRootState (storeSetup s)).getMem a = _
  rw [copyRoot_mem_frame]
  · exact storeSetup_frame s a
  · intro i
    rw [(storeSetup_registers s target node ht hn).2]
    have address : BitVec.ofNat 64 (target + 20 * node) + signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
        BitVec.ofNat 64 (target + 20 * node + 4 * i.val) := by
      fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [address]
    intro eq
    have low : (alignToDword (BitVec.ofNat 64 (target + 20 * node + 4 * i.val))).toNat < 0x40000 := by
      unfold alignToDword
      rw [BitVec.toNat_and]
      apply lt_of_le_of_lt Nat.and_le_left
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [← eq] at low;omega

theorem nodeFinish_counter (s : MachineState) :
    (nodeFinish s).getMem 0x43088 = s.getMem 0x43088 + 1 := by
  simp [nodeFinish,runSchedule,nodeFinishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem nodeFinish_frame (s : MachineState) (a : Word) (ha : a ≠ 0x43088#64) :
    (nodeFinish s).getMem a = s.getMem a := by
  simp [nodeFinish,runSchedule,nodeFinishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ha]

theorem nodeFinish_pc (s : MachineState) (pc : s.pc = 0x17d8) :
    (nodeFinish s).pc = if s.getMem 0x43088 + 1 = s.getMem 0x43090 then 0x1810 else 0x1620 := by
  simp [nodeFinish,runSchedule,nodeFinishSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem node_trace (hash : Hash) (s : MachineState) (base target node count : Nat) (pc : s.pc = 0x1620)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (ht : s.getMem 0x43080 = BitVec.ofNat 64 target)
    (hn : s.getMem 0x43088 = BitVec.ofNat 64 node) (hc : s.getMem 0x43090 = BitVec.ofNat 64 count)
    (sourceBound : base + 40 * node + 40 ≤ 0x40000) (sourceAlign : base % 4 = 0)
    (targetBound : target + 20 * node + 20 ≤ 0x40000) (targetAlign : target % 4 = 0)
    (countBound : count < 2048) :
    Trace hash SphincsMaskedImages.keygen s 124 139 1 2 (next hash s) ∧
      (next hash s).getMem 0x43088 = BitVec.ofNat 64 (node + 1) ∧
      (next hash s).pc = if node + 1 = count then 0x1810 else 0x1620 := by
  have atarget : (answer hash s).getMem 0x43080 = BitVec.ofNat 64 target :=
    (answer_frame hash s _ (by decide)).trans ht
  have anode : (answer hash s).getMem 0x43088 = BitVec.ofNat 64 node :=
    (answer_frame hash s _ (by decide)).trans hn
  have acount : (answer hash s).getMem 0x43090 = BitVec.ofNat 64 count :=
    (answer_frame hash s _ (by decide)).trans hc
  have regs := storeSetup_registers (answer hash s) target node atarget anode
  have apc := answer_pc hash s pc
  have copied := copy20_block_general SphincsMaskedImages.keygen 492 store_code
    (storeSetup (answer hash s)) 0x42000 (target + 20 * node)
    (storeSetup_pc _ apc) regs.1 regs.2 (by decide) (by decide)
    (by omega) (by dsimp [MEMORY_BYTES];omega) (by decide)
  have storedNode := (stored_control (answer hash s) target node atarget anode targetBound 0x43088 (by decide)).trans anode
  have storedCount := (stored_control (answer hash s) target node atarget anode targetBound 0x43090 (by decide)).trans acount
  refine ⟨?_,?_,?_⟩
  · exact (answer_trace hash s base node pc hb hn sourceBound sourceAlign).trans
      ((storeSetup_block _ apc).trace.trans (copied.trace.trans (nodeFinish_block _ (stored_pc _ apc)).trace))
  · change (nodeFinish (stored (answer hash s))).getMem _ = _
    rw [nodeFinish_counter,storedNode]
    exact (BitVec.ofNat_add _ _).symm
  · change (nodeFinish (stored (answer hash s))).pc = _
    rw [nodeFinish_pc _ (stored_pc _ apc),storedNode,storedCount]
    rw [show BitVec.ofNat 64 node + 1 = BitVec.ofNat 64 (node + 1) from (BitVec.ofNat_add _ _).symm]
    have eq : (BitVec.ofNat 64 (node + 1) : Word) = BitVec.ofNat 64 count ↔ node + 1 = count := by
      constructor
      · intro h
        have h := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show node + 1 < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show count < 2 ^ 64 by omega)] at h
        exact h
      · intro h;rw [h]
    simp only [eq]

/-- info: 'SigGolfCandidate.SphincsMaskedParentNode.node_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms node_trace

end SigGolfCandidate.SphincsMaskedParentNode
