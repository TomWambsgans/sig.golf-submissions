import SigGolfCandidate.SphincsMaskedMaskCode

namespace SigGolfCandidate.SphincsMaskedMaskNode
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedMaskCode SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsVerifierFtsRootCopy SphincsVerifierFtsCopyAccess SphincsBridge SphincsSecurity
open SphincsCacheSecretDomains
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem prepare_registers (s : MachineState) :
    (prepare s).getReg .x10 = 0x40000 ∧ (prepare s).getReg .x11 = 576 ∧
      (prepare s).getReg .x12 = 0x42000 ∧ (prepare s).getReg .x5 = 1 := by
  simp [prepare,runSchedule,prepareSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

def prepareWrites : List Word := [0x43010#64,0x40000#64,0x40008#64,0x40010#64,0x40018#64,
  0x40020#64,0x40028#64,0x40030#64,0x40038#64,0x40040#64]

theorem prepare_frame (s : MachineState) (a : Word) (outside : a ∉ prepareWrites) :
    (prepare s).getMem a = s.getMem a := by
  simp only [prepareWrites,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := outside
  simp [prepare,runSchedule,prepareSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]

def answer (hash : Hash) (s : MachineState) := writeHash (prepare s) (hash (hashInput (prepare s)))

theorem answer_pc (hash : Hash) (s : MachineState) (pc : s.pc = 0x1a78) :
    (answer hash s).pc = 0x1b60 := by simp [answer,writeHash,prepare_pc s pc]

theorem answer_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x1a78) :
    Trace hash SphincsMaskedImages.keygen s 76 91 1 2 (answer hash s) := by
  obtain ⟨src,bits,dst,service⟩ := prepare_registers s
  have fetch : fetch SphincsMaskedImages.keygen (prepare s) = some (.base .ECALL) := by
    rw [fetch_at,prepare_pc s pc];decide
  have valid : hashArgumentsValid (prepare s) = true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (prepare s)).1 = 576 := by simp [hashInput,bits]
  have h := Trace.hash (hash := hash) (image := SphincsMaskedImages.keygen) (prepare s) _ 0 0 0 0 fetch service valid (Trace.refl _)
  have hs : Trace hash SphincsMaskedImages.keygen (prepare s) 1 16 1 2 (answer hash s) := by
    simp only [len] at h;exact h
  exact (prepare_block s pc).trace.trans hs

def answerWrites := prepareWrites ++ [0x42000#64,0x42008#64,0x42010#64,0x42018#64]

theorem answer_frame (hash : Hash) (s : MachineState) (a : Word) (outside : a ∉ answerWrites) :
    (answer hash s).getMem a = s.getMem a := by
  have split : a ∉ prepareWrites ∧ a ∉ [0x42000#64,0x42008#64,0x42010#64,0x42018#64] := by
    simpa only [answerWrites,List.mem_append,not_or] using outside
  obtain ⟨prep,ans⟩ := split
  simp only [List.mem_cons,List.not_mem_nil,not_or] at ans
  obtain ⟨h0,h1,h2,h3⟩ := ans
  have dst := (prepare_registers s).2.2.1
  simp [answer,writeHash,dst,MachineState.writeWords,h0,h1,h2,h3,prepare_frame s a prep]

theorem xorSetup_frame (s : MachineState) (a : Word) : (xorSetup s).getMem a = s.getMem a := by
  simp [xorSetup,runSchedule,xorSetupSchedule,execInstrBr]

theorem xorSetup_registers (s : MachineState) :
    (xorSetup s).getReg .x6 = s.getMem 0x430d8 ∧ (xorSetup s).getReg .x12 = 0x42000 := by
  simp [xorSetup,runSchedule,xorSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem xor_checked (s : MachineState) (base : Nat) (pc : s.pc = 0x1b74)
    (ptr : s.getReg .x6 = BitVec.ofNat 64 base) (pad : s.getReg .x12 = 0x42000)
    (aligned : base % 4 = 0) (bounded : base+20 ≤ MEMORY_BYTES) : Checked xorSchedule s := by
  simp [xorSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    signExtend12,signExtend13,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    pc,ptr,pad,accessValid,rangeValid,MEMORY_BYTES]
  dsimp [MEMORY_BYTES] at bounded
  omega

theorem xor_block (s : MachineState) (base : Nat) (pc : s.pc = 0x1b74)
    (ptr : s.getReg .x6 = BitVec.ofNat 64 base) (pad : s.getReg .x12 = 0x42000)
    (aligned : base % 4 = 0) (bounded : base+20 ≤ MEMORY_BYTES) :
    OrdinarySteps SphincsMaskedImages.keygen s 20 (applyXor s) :=
  checked_sound _ xorSchedule xor_code s (xor_checked s base pc ptr pad aligned bounded)

theorem xor_pc (s : MachineState) (pc : s.pc = 0x1b74) : (applyXor s).pc = 0x1bc4 := by
  simp [applyXor,runSchedule,xorSchedule,execInstrBr,MachineState.setWord32,pc]

def Context (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (node : BitVec 32) : Prop :=
  s.getMem 0x43000#64 = 0 ∧ s.getMem 0x43008#64 = 0 ∧ s.getMem 0x43018#64 = 0 ∧
    s.getMem 0x430d0#64 = node.zeroExtend 64 ∧ Words20 s 0x74 parameter ∧ Words32 s seed

def queryWord (s : MachineState) (i : Fin 18) : BitVec 32 :=
  if i.val = 0 then (3585#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val = 1 then (s.getMem 0x430d0).setWidth 32
  else if i.val = 2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val = 3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val = 4 then (s.getMem 0x43018).setWidth 32
  else if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * (i.val - 5)))
  else s.getWord32 (BitVec.ofNat 64 (0x20 + 4 * (i.val - 10)))

theorem prepare_words (s : MachineState) (i : Fin 18) :
    (prepare s).getWord32 (BitVec.ofNat 64 (0x40000 + 4 * i.val)) = queryWord s i := by
  fin_cases i <;>
    simp [prepare,runSchedule,prepareSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,queryWord]

def payload (parameter : BitVec 160) (seed : MasterSeed) (node : BitVec 32) : List Byte :=
  (padInput parameter seed node).map UInt8.toBitVec

theorem payload_length (parameter : BitVec 160) (seed : MasterSeed) (node : BitVec 32) :
    (payload parameter seed node).length = 72 := by
  simp [payload,padInput,tweakFields,fieldBytes,bytesLE]

theorem prepared_byte (s : MachineState) (i : Fin 72) :
    (prepare s).getByte (BitVec.ofNat 64 (0x40000 + i.val)) =
      (queryWord s ⟨i.val / 4,by omega⟩).extractLsb' (8 * (i.val % 4)) 8 := by
  have h := SphincsVerifierFtsGenericBytes.variableWord_byte (prepare s)
    (0x40000 + 4 * (i.val / 4)) (by omega) (by omega) 0 ⟨i.val % 4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  rw [show 0x40000 + 4 * (i.val / 4) + i.val % 4 = 0x40000 + i.val by omega] at h
  rw [h,prepare_words s ⟨i.val / 4,by omega⟩]

theorem context_byte (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (node : BitVec 32) (ctx : Context s parameter seed node) (i : Fin 72) :
    (queryWord s ⟨i.val / 4,by omega⟩).extractLsb' (8 * (i.val % 4)) 8 =
      (payload parameter seed node)[i.val]'(by rw [payload_length];exact i.isLt) := by
  obtain ⟨layer,tree,index,counter,par,key⟩ := ctx
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
  norm_num at p0 p1 p2 p3 p4 k0 k1 k2 k3 k4 k5 k6 k7
  fin_cases i <;>
    simp [queryWord,layer,tree,index,counter,p0,p1,p2,p3,p4,k0,k1,k2,k3,k4,k5,k6,k7,extractWord32,
      payload,padInput,tweakFields,fieldBytes,bytesLE,
      protocolDomainSep]
  all_goals
    ext b hb
    interval_cases b <;> simp

theorem query_eq (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (node : BitVec 32) (ctx : Context s parameter seed node) :
    hashInput (prepare s) = toQuery (padInput parameter seed node) := by
  apply Serialization.hashInput_of_list (prepare s) 0x40000 (payload parameter seed node)
  · exact (prepare_registers s).1
  · rw [payload_length,(prepare_registers s).2.1];rfl
  · intro i hi
    have bound : i < 72 := by simpa only [payload_length] using hi
    rw [prepared_byte s ⟨i,bound⟩]
    exact context_byte s parameter seed node ctx ⟨i,bound⟩


/-- info: 'SigGolfCandidate.SphincsMaskedMaskNode.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_eq

/-- info: 'SigGolfCandidate.SphincsMaskedMaskNode.answer_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms answer_trace

end SigGolfCandidate.SphincsMaskedMaskNode
