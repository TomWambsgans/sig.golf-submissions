import SigGolfCandidate.SphincsMaskedChainDomain

namespace SigGolfCandidate.SphincsMaskedSecretDomain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedChainStep SphincsMaskedChainLoop
open SphincsMaskedChainDomain SphincsBridge SphincsSecurity
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def Words32 (s : MachineState) (seed : MasterSeed) : Prop :=
  ∀ i : Fin 8, s.getWord32 (BitVec.ofNat 64 (0x20 + 4 * i.val)) = seed.extractLsb' (32 * i.val) 32

def Context (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (leaf : LeafIndex) (chain : ChainIndex) : Prop :=
  s.getMem 0x43000#64 = 0 ∧ s.getMem 0x43008#64 = 0 ∧
  s.getMem 0x43020#64 = BitVec.ofNat 64 leaf.val ∧
  s.getMem 0x43050#64 = BitVec.ofNat 64 chain.val ∧ Words20 s 0x74 parameter ∧ Words32 s seed

def queryWord (s : MachineState) (i : Fin 18) : BitVec 32 :=
  if i.val = 0 then (1#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val = 1 then (s.getMem 0x43050).setWidth 32
  else if i.val = 2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val = 3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val = 4 then (s.getMem 0x43020).setWidth 32
  else if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * (i.val - 5)))
  else s.getWord32 (BitVec.ofNat 64 (0x20 + 4 * (i.val - 10)))

theorem prepare_words (s : MachineState) (i : Fin 18) :
    (secretPrepare s).getWord32 (BitVec.ofNat 64 (0x40000 + 4 * i.val)) = queryWord s i := by
  fin_cases i <;>
    simp [secretPrepare,runSchedule,secretPrepareSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,queryWord]

def payload (parameter : BitVec 160) (seed : MasterSeed) (leaf : LeafIndex) (chain : ChainIndex) : List Byte :=
  (keygenHashInput parameter (.ots topLayer Concrete.rootTree leaf chain) seed).map UInt8.toBitVec

theorem payload_length (parameter : BitVec 160) (seed : MasterSeed) (leaf : LeafIndex) (chain : ChainIndex) :
    (payload parameter seed leaf chain).length = 72 := by
  simp [payload,keygenHashInput,keygenDomainFields,tweakFields,fieldBytes,bytesLE]

theorem prepared_byte (s : MachineState) (i : Fin 72) :
    (secretPrepare s).getByte (BitVec.ofNat 64 (0x40000 + i.val)) =
      (queryWord s ⟨i.val / 4,by omega⟩).extractLsb' (8 * (i.val % 4)) 8 := by
  have h := SphincsVerifierFtsGenericBytes.variableWord_byte (secretPrepare s)
    (0x40000 + 4 * (i.val / 4)) (by omega) (by omega) 0 ⟨i.val % 4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  rw [show 0x40000 + 4 * (i.val / 4) + i.val % 4 = 0x40000 + i.val by omega] at h
  rw [h,prepare_words s ⟨i.val / 4,by omega⟩]

theorem context_byte (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (leaf : LeafIndex) (chain : ChainIndex) (ctx : Context s parameter seed leaf chain) (i : Fin 72) :
    (queryWord s ⟨i.val / 4,by omega⟩).extractLsb' (8 * (i.val % 4)) 8 =
      (payload parameter seed leaf chain)[i.val]'(by rw [payload_length];exact i.isLt) := by
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
      payload,keygenHashInput,keygenDomainFields,tweakFields,fieldBytes,bytesLE,
      protocolDomainSep,topLayer,Concrete.rootTree]
  all_goals
    ext b hb
    interval_cases b <;> simp

theorem query_eq (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (leaf : LeafIndex) (chain : ChainIndex) (ctx : Context s parameter seed leaf chain) :
    hashInput (secretPrepare s) = toQuery (keygenHashInput parameter (.ots topLayer Concrete.rootTree leaf chain) seed) := by
  apply Serialization.hashInput_of_list (secretPrepare s) 0x40000 (payload parameter seed leaf chain)
  · exact (secretPrepare_registers s).1
  · rw [payload_length,(secretPrepare_registers s).2.1];rfl
  · intro i hi
    have bound : i < 72 := by simpa only [payload_length] using hi
    rw [prepared_byte s ⟨i,bound⟩]
    exact context_byte s parameter seed leaf chain ctx ⟨i,bound⟩


theorem finish_words (s : MachineState) (i : Fin 5) :
    (secretFinish s).getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) := by
  fin_cases i <;>
    simp [secretFinish,runSchedule,secretFinishSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

theorem initial_words (hash : Hash) (s : MachineState) (i : Fin 5) :
    (initialChain hash s).getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * i.val)) =
      (hash (hashInput (secretPrepare s))).extractLsb' (32 * i.val) 32 := by
  rw [initialChain,finish_words]
  have dst := (secretPrepare_registers s).2.2.1
  fin_cases i <;>
    simp [secretAnswer,writeHash,dst,MachineState.writeWords,
      MachineState.getWord32,alignToDword,byteOffset,extractWord32]
  all_goals
    ext j hj
    interval_cases j <;> simp

theorem initial_value (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (leaf : LeafIndex) (chain : ChainIndex) (ctx : Context s parameter seed leaf chain) :
    Words20 (initialChain hash s) 0x44b00
      (truncateHash (hash (toQuery (keygenHashInput parameter (.ots topLayer Concrete.rootTree leaf chain) seed)))) := by
  intro i
  rw [initial_words,query_eq s parameter seed leaf chain ctx]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

theorem prepare_index (s : MachineState) : (secretPrepare s).getMem 0x43018 = s.getMem 0x43020 := by
  simp [secretPrepare,runSchedule,secretPrepareSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

theorem initial_index (hash : Hash) (s : MachineState) :
    (initialChain hash s).getMem 0x43018 = s.getMem 0x43020 := by
  rw [initialChain,secretFinish_frame _ _ (by decide)]
  have dst := (secretPrepare_registers s).2.2.1
  simp [secretAnswer,writeHash,dst,MachineState.writeWords]
  exact prepare_index s

theorem initial_fixed (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (leaf : LeafIndex) (chain : ChainIndex) (ctx : Context s parameter seed leaf chain) :
    FixedContext (initialChain hash s) parameter leaf chain := by
  obtain ⟨layer,tree,index,counter,par,key⟩ := ctx
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (initialChain_frame hash s _ (by decide)).trans layer
  · exact (initialChain_frame hash s _ (by decide)).trans tree
  · exact (initial_index hash s).trans index
  · exact (initialChain_frame hash s _ (by decide)).trans counter
  · intro i
    have frame : (initialChain hash s).getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val)) := by
      simp only [MachineState.getWord32]
      rw [initialChain_frame hash s _ (by fin_cases i <;> decide)]
    exact frame.trans (par i)

theorem eval_derive (hash : Hash) (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
      (deriveKey parameter domain seed : OracleComp SphincsSecurity.HashSpec Digest) =
        truncateHash (hash (toQuery (keygenHashInput parameter domain seed))) := by
  have evalOracle (input : HashInput) :
      evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Concrete.oracleHash input : OracleComp SphincsSecurity.HashSpec HashOutput) = adaptOracle hash input := by
    simp only [Concrete.oracleHash,HasQuery.query]
    exact simulateQ_spec_query (spec := SphincsSecurity.HashSpec) (r := Id) (adaptOracle hash) input
  simp only [deriveKey,evalWithAnswerFn_bind,evalWithAnswerFn_pure,evalOracle]
  rfl

/-- A whole machine chain starts with the correct seeded secret and follows all seven abstract hashes. -/
theorem endpoint_value (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (leaf : LeafIndex) (chain : ChainIndex) (ctx : Context s parameter seed leaf chain)
    (pc : s.pc = 0x112c) :
    Words20 (chainValue hash s) 0x44b00
      (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (do let secret ← deriveKey parameter (.ots topLayer Concrete.rootTree leaf chain) seed
            Concrete.chainWalk parameter topLayer Concrete.rootTree leaf chain 0 7 secret :
          OracleComp SphincsSecurity.HashSpec Digest)) := by
  rw [evalWithAnswerFn_bind,eval_derive]
  exact walk_value hash (initialChain hash s) parameter _ leaf chain
    (initial_fixed hash s parameter seed leaf chain ctx)
    (initialChain_pc hash s pc) (initialChain_step_zero hash s)
    (initial_value hash s parameter seed leaf chain ctx) 7 (by decide)

/-- info: 'SigGolfCandidate.SphincsMaskedSecretDomain.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_eq

/-- info: 'SigGolfCandidate.SphincsMaskedSecretDomain.initial_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initial_value

/-- info: 'SigGolfCandidate.SphincsMaskedSecretDomain.endpoint_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms endpoint_value

end SigGolfCandidate.SphincsMaskedSecretDomain
