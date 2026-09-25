import SigGolfCandidate.SphincsMaskedSignRootPad

namespace SigGolfCandidate.SphincsMaskedSignRootPadDomain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedSignRootPad SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsVerifierFtsRootCopy SphincsVerifierFtsRootCopyBytes SphincsBridge SphincsSecurity
open SphincsCacheSecretDomains
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def Context (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (node : BitVec 32) : Prop :=
  s.getMem 0x43000#64 = 0 ∧ s.getMem 0x43008#64 = 0 ∧ s.getMem 0x43018#64 = 0 ∧
    s.getMem 0x43010#64 = node.zeroExtend 64 ∧ Words20 s 0x74 parameter ∧ Words32 s seed

def queryWord (s : MachineState) (i : Fin 18) : BitVec 32 :=
  if i.val = 0 then (3585#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val = 1 then (s.getMem 0x43010).setWidth 32
  else if i.val = 2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val = 3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val = 4 then (s.getMem 0x43018).setWidth 32
  else if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * (i.val - 5)))
  else s.getWord32 (BitVec.ofNat 64 (0x20 + 4 * (i.val - 10)))

theorem prepare_words (s : MachineState) (i : Fin 18) :
    (padPrepare s).getWord32 (BitVec.ofNat 64 (0x40000 + 4 * i.val)) = queryWord s i := by
  fin_cases i <;>
    simp [padPrepare,runSchedule,padSchedule,SphincsMaskedMaskCode.prepareSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,queryWord]

def payload (parameter : BitVec 160) (seed : MasterSeed) (node : BitVec 32) : List Byte :=
  (padInput parameter seed node).map UInt8.toBitVec

theorem payload_length (parameter : BitVec 160) (seed : MasterSeed) (node : BitVec 32) :
    (payload parameter seed node).length = 72 := by
  simp [payload,padInput,tweakFields,fieldBytes,bytesLE]

theorem prepared_byte (s : MachineState) (i : Fin 72) :
    (padPrepare s).getByte (BitVec.ofNat 64 (0x40000 + i.val)) =
      (queryWord s ⟨i.val / 4,by omega⟩).extractLsb' (8 * (i.val % 4)) 8 := by
  have h := SphincsVerifierFtsGenericBytes.variableWord_byte (padPrepare s)
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
    hashInput (padPrepare s) = toQuery (padInput parameter seed node) := by
  apply Serialization.hashInput_of_list (padPrepare s) 0x40000 (payload parameter seed node)
  · exact (pad_registers s).1
  · rw [payload_length,(pad_registers s).2.1];rfl
  · intro i hi
    have bound : i < 72 := by simpa only [payload_length] using hi
    rw [prepared_byte s ⟨i,bound⟩]
    exact context_byte s parameter seed node ctx ⟨i,bound⟩


/-- The signer header selects the top-tree root and leaves its input words intact. -/
theorem init_context (s : MachineState) (parameter : BitVec 160)
    (seed : MasterSeed) (par : Words20 s 0x74 parameter)
    (key : Words32 s seed) :
    Context (init s) parameter seed 4094 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · intro i
    have h := par i
    fin_cases i <;>
      simpa [init,runSchedule,initSchedule,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
        MachineState.getWord32,alignToDword,byteOffset] using h
  · intro i
    have h := key i
    fin_cases i <;>
      simpa [init,runSchedule,initSchedule,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
        MachineState.getWord32,alignToDword,byteOffset] using h

/-- The signer's root-unmasking HASH uses exactly the top-root pad domain. -/
theorem root_query (s : MachineState) (parameter : BitVec 160)
    (seed : MasterSeed) (par : Words20 s 0x74 parameter)
    (key : Words32 s seed) :
    hashInput (padPrepare (init s)) =
      toQuery (padInput parameter seed 4094) :=
  query_eq (init s) parameter seed 4094 (init_context s parameter seed par key)

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootPadDomain.root_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms root_query

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootPadDomain.init_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms init_context

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootPadDomain.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_eq

end SigGolfCandidate.SphincsMaskedSignRootPadDomain
