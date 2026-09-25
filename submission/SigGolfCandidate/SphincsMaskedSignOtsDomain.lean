import SigGolfCandidate.SphincsMaskedSignOtsShift

namespace SigGolfCandidate.SphincsMaskedSignOtsDomain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedChainStep SphincsMaskedChainLoop
open SphincsMaskedChainEndpoints SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsMaskedPublicKeyDomain SphincsBridge SphincsSecurity
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Chain
def Context (s : MachineState) (parameter value : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) : Prop :=
  s.getMem 0x43000#64 = BitVec.ofNat 64 lay.val ∧ s.getMem 0x43008#64 = BitVec.ofNat 64 treeIdx.val ∧
  s.getMem 0x43018#64 = BitVec.ofNat 64 leaf.val ∧
  s.getMem 0x43050#64 = BitVec.ofNat 64 chain.val ∧
  s.getMem 0x43058#64 = BitVec.ofNat 64 step.val ∧
  Words20 s 0x74 parameter ∧ Words20 s 0x44b00 value

def payload (parameter value : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep) : List Byte :=
  (tweakableHashInput parameter (.chain lay treeIdx leaf chain step) (bytesLE 20 value)).map UInt8.toBitVec

theorem payload_length (parameter value : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep) :
    (payload parameter value lay treeIdx leaf chain step).length = 60 := by
  simp [payload,tweakableHashInput,tweakBytes,hashDomainFields,tweakFields,fieldBytes,bytesLE]

theorem context_byte (s : MachineState) (parameter value : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) (ctx : Context s parameter value lay treeIdx leaf chain step) (i : Fin 60) :
    (queryWord32 s ⟨i.val / 4,by omega⟩).extractLsb' (8 * (i.val % 4)) 8 =
      (payload parameter value lay treeIdx leaf chain step)[i.val]'(by rw [payload_length]; exact i.isLt) := by
  obtain ⟨layer,tree,index,counter,position,par,val⟩ := ctx
  have shift : (BitVec.ofNat 64 chain.val <<< 3) + BitVec.ofNat 64 step.val =
      BitVec.ofNat 64 (8 * chain.val + step.val) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 chain.val * BitVec.ofNat 64 8 + BitVec.ofNat 64 step.val = _
    rw [← BitVec.ofNat_mul,← BitVec.ofNat_add]
    congr 1; omega
  have p0 := par 0
  have p1 := par 1
  have p2 := par 2
  have p3 := par 3
  have p4 := par 4
  have v0 := val 0
  have v1 := val 1
  have v2 := val 2
  have v3 := val 3
  have v4 := val 4
  norm_num at p0 p1 p2 p3 p4 v0 v1 v2 v3 v4
  have treeWidth : (BitVec.ofNat 64 treeIdx.val).setWidth 32=BitVec.ofNat 32 treeIdx.val := by simp
  fin_cases i <;>
    simp [queryWord32,layer,tree,index,counter,position,shift,p0,p1,p2,p3,p4,v0,v1,v2,v3,v4,extractWord32,
      payload,tweakableHashInput,tweakBytes,hashDomainFields,tweakFields,fieldBytes,bytesLE,
      chainLength,winternitzBits,protocolDomainSep]
  all_goals first
    | (fin_cases lay <;> decide)
    | (rw [←treeWidth]; exact BitVec.extractLsb'_setWidth_of_le (by decide))
    | (solve | simp [BitVec.setWidth_ushiftRight_eq_extractLsb,SphincsMaskedSignForestDomain.nested_extract])


theorem query_eq (s : MachineState) (parameter value : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) (ctx : Context s parameter value lay treeIdx leaf chain step) :
    hashInput (prepareState s) = toQuery
      (tweakableHashInput parameter (.chain lay treeIdx leaf chain step) (bytesLE 20 value)) := by
  apply Serialization.hashInput_of_list (prepareState s) 0x40000 (payload parameter value lay treeIdx leaf chain step)
  · exact (prepare_registers s).1
  · rw [payload_length,(prepare_registers s).2.1]; rfl
  · intro i hi
    have bound : i < 60 := by simpa only [payload_length] using hi
    rw [prepared_byte s ⟨i,bound⟩]
    exact context_byte s parameter value lay treeIdx leaf chain step ctx ⟨i,bound⟩

theorem step_value (hash : Hash) (s : MachineState) (parameter value : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) (ctx : Context s parameter value lay treeIdx leaf chain step) :
    Words20 (stepState hash s) 0x44b00
      (truncateHash (hash (toQuery
        (tweakableHashInput parameter (.chain lay treeIdx leaf chain step) (bytesLE 20 value))))) := by
  intro i
  rw [step_value_words,query_eq s parameter value lay treeIdx leaf chain step ctx]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

def FixedContext (s : MachineState) (parameter : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) : Prop :=
  s.getMem 0x43000#64 = BitVec.ofNat 64 lay.val ∧ s.getMem 0x43008#64 = BitVec.ofNat 64 treeIdx.val ∧
  s.getMem 0x43018#64 = BitVec.ofNat 64 leaf.val ∧
  s.getMem 0x43050#64 = BitVec.ofNat 64 chain.val ∧ Words20 s 0x74 parameter

theorem walk_fixed (hash : Hash) (s : MachineState) (n : Nat) (parameter : BitVec 160)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (ctx : FixedContext s parameter lay treeIdx leaf chain) :
    FixedContext (walk hash n s) parameter lay treeIdx leaf chain := by
  obtain ⟨layer,tree,index,counter,par⟩ := ctx
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [walk_frame hash n s _ (by decide)]; exact layer
  · rw [walk_frame hash n s _ (by decide)]; exact tree
  · rw [walk_frame hash n s _ (by decide)]; exact index
  · rw [walk_frame hash n s _ (by decide)]; exact counter
  · intro i
    have frame : (walk hash n s).getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val)) := by
      simp only [MachineState.getWord32]
      rw [walk_frame hash n s _ (by fin_cases i <;> decide)]
    exact frame.trans (par i)

/-- The exact seven-step machine loop agrees with the abstract WOTS chain function. -/
theorem walk_value (hash : Hash) (s : MachineState) (parameter value : BitVec 160)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (ctx : FixedContext s parameter lay treeIdx leaf chain)
    (pc : s.pc = 0x1270) (zero : s.getMem 0x43058 = 0) (initial : Words20 s 0x44b00 value)
    (n : Nat) (hn : n ≤ 7) :
    Words20 (walk hash n s) 0x44b00
      (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Concrete.chainWalk parameter lay treeIdx leaf chain 0 n value :
          OracleComp SphincsSecurity.HashSpec Digest)) := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    obtain ⟨layer,tree,index,counter,par⟩ := walk_fixed hash s n parameter lay treeIdx leaf chain ctx
    have count := (walk_trace hash s pc zero n (by omega)).2.1
    have ns : n < chainLength - 1 := by change n < 7; omega
    have stepCtx : Context (walk hash n s) parameter
        (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
          (Concrete.chainWalk parameter lay treeIdx leaf chain 0 n value :
            OracleComp SphincsSecurity.HashSpec Digest)) lay treeIdx leaf chain ⟨n,ns⟩ :=
      ⟨layer,tree,index,counter,count,par,ih (by omega)⟩
    have result := step_value hash (walk hash n s) parameter _ lay treeIdx leaf chain ⟨n,ns⟩ stepCtx
    simp only [Concrete.chainWalk]
    change Words20 (stepState hash (walk hash n s)) 0x44b00
      (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        ((Concrete.chainWalk parameter lay treeIdx leaf chain 0 n value :
          OracleComp SphincsSecurity.HashSpec Digest) >>= fun previous =>
          if h : 0 + n < chainLength - 1 then
            Concrete.tweakableHash parameter (.chain lay treeIdx leaf chain ⟨0 + n,h⟩)
              (bytesLE 20 previous) else pure 0))
    rw [evalWithAnswerFn_bind]
    have h : 0 + n < chainLength - 1 := by omega
    have choose : (if h : 0 + n < chainLength - 1 then
        (Concrete.tweakableHash parameter (.chain lay treeIdx leaf chain ⟨0 + n,h⟩)
          (bytesLE 20 (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
            (Concrete.chainWalk parameter lay treeIdx leaf chain 0 n value :
              OracleComp SphincsSecurity.HashSpec Digest))) : OracleComp SphincsSecurity.HashSpec Digest)
        else pure 0) =
      Concrete.tweakableHash parameter (.chain lay treeIdx leaf chain ⟨0 + n,h⟩)
        (bytesLE 20 (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
          (Concrete.chainWalk parameter lay treeIdx leaf chain 0 n value :
            OracleComp SphincsSecurity.HashSpec Digest))) := dif_pos h
    erw [choose,eval_hash]
    have stepEq : (⟨0 + n,h⟩ : ChainStep) = ⟨n,ns⟩ := Fin.ext (Nat.zero_add n)
    rw [stepEq]
    exact result


end Chain

namespace Secret
def Context (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) : Prop :=
  s.getMem 0x43000#64 = BitVec.ofNat 64 lay.val ∧ s.getMem 0x43008#64 = BitVec.ofNat 64 treeIdx.val ∧
  s.getMem 0x43020#64 = BitVec.ofNat 64 leaf.val ∧
  s.getMem 0x43050#64 = BitVec.ofNat 64 chain.val ∧ Words20 s 0x74 parameter ∧ Words32 s seed

def payload (parameter : BitVec 160) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) : List Byte :=
  (keygenHashInput parameter (.ots lay treeIdx leaf chain) seed).map UInt8.toBitVec

theorem payload_length (parameter : BitVec 160) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) :
    (payload parameter seed lay treeIdx leaf chain).length = 72 := by
  simp [payload,keygenHashInput,keygenDomainFields,tweakFields,fieldBytes,bytesLE]

theorem context_byte (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (ctx : Context s parameter seed lay treeIdx leaf chain) (i : Fin 72) :
    (queryWord s ⟨i.val / 4,by omega⟩).extractLsb' (8 * (i.val % 4)) 8 =
      (payload parameter seed lay treeIdx leaf chain)[i.val]'(by rw [payload_length];exact i.isLt) := by
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
  have treeWidth : (BitVec.ofNat 64 treeIdx.val).setWidth 32=BitVec.ofNat 32 treeIdx.val := by simp
  fin_cases i <;>
    simp [queryWord,layer,tree,index,counter,p0,p1,p2,p3,p4,k0,k1,k2,k3,k4,k5,k6,k7,extractWord32,
      payload,keygenHashInput,keygenDomainFields,tweakFields,fieldBytes,bytesLE,
      protocolDomainSep]
  all_goals first
    | (fin_cases lay <;> decide)
    | (rw [←treeWidth]; exact BitVec.extractLsb'_setWidth_of_le (by decide))
    | (solve | simp [BitVec.setWidth_ushiftRight_eq_extractLsb,SphincsMaskedSignForestDomain.nested_extract])

theorem query_eq (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (ctx : Context s parameter seed lay treeIdx leaf chain) :
    hashInput (secretPrepare s) = toQuery (keygenHashInput parameter (.ots lay treeIdx leaf chain) seed) := by
  apply Serialization.hashInput_of_list (secretPrepare s) 0x40000 (payload parameter seed lay treeIdx leaf chain)
  · exact (secretPrepare_registers s).1
  · rw [payload_length,(secretPrepare_registers s).2.1];rfl
  · intro i hi
    have bound : i < 72 := by simpa only [payload_length] using hi
    rw [prepared_byte s ⟨i,bound⟩]
    exact context_byte s parameter seed lay treeIdx leaf chain ctx ⟨i,bound⟩


theorem initial_value (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (ctx : Context s parameter seed lay treeIdx leaf chain) :
    Words20 (initialChain hash s) 0x44b00
      (truncateHash (hash (toQuery (keygenHashInput parameter (.ots lay treeIdx leaf chain) seed)))) := by
  intro i
  rw [initial_words,query_eq s parameter seed lay treeIdx leaf chain ctx]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

theorem initial_fixed (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (ctx : Context s parameter seed lay treeIdx leaf chain) :
    Chain.FixedContext (initialChain hash s) parameter lay treeIdx leaf chain := by
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

/-- A whole machine chain starts with the correct seeded secret and follows all seven abstract hashes. -/
theorem endpoint_value (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (ctx : Context s parameter seed lay treeIdx leaf chain)
    (pc : s.pc = 0x112c) :
    Words20 (chainValue hash s) 0x44b00
      (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (do let secret ← deriveKey parameter (.ots lay treeIdx leaf chain) seed
            Concrete.chainWalk parameter lay treeIdx leaf chain 0 7 secret :
          OracleComp SphincsSecurity.HashSpec Digest)) := by
  rw [evalWithAnswerFn_bind,eval_derive]
  exact Chain.walk_value hash (initialChain hash s) parameter _ lay treeIdx leaf chain
    (initial_fixed hash s parameter seed lay treeIdx leaf chain ctx)
    (initialChain_pc hash s pc) (initialChain_step_zero hash s)
    (initial_value hash s parameter seed lay treeIdx leaf chain ctx) 7 (by decide)


end Secret

namespace PublicKey
/-- Each iteration retains the seed and parameter and selects precisely its own chain index. -/
theorem chains_context (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (ctx : Secret.Context s parameter seed lay treeIdx leaf ⟨0,by decide⟩)
    (pc : s.pc = 0x112c) (c : ChainIndex) :
    Secret.Context (chains hash c.val s) parameter seed lay treeIdx leaf c := by
  obtain ⟨layer,tree,index,counter,par,key⟩ := ctx
  have zero : s.getMem 0x43050 = 0 := counter
  have bound : c.val ≤ 52 := by have := c.isLt; change c.val < 52 at this; omega
  refine ⟨?_,?_,?_,(chains_trace hash s pc zero c.val bound).2.1,?_,?_⟩
  · exact (chains_control hash s pc zero c.val bound _ (Or.inl rfl)).trans layer
  · exact (chains_control hash s pc zero c.val bound _ (Or.inr rfl)).trans tree
  · exact (SphincsMaskedChainFrame.chains_frame hash s pc zero c.val bound _ (Or.inr rfl)).trans index
  · intro i
    have frame : (chains hash c.val s).getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val)) := by
      simp only [MachineState.getWord32]
      rw [SphincsMaskedChainFrame.chains_frame hash s pc zero c.val bound _
        (Or.inl (by fin_cases i <;> decide))]
    exact frame.trans (par i)
  · intro i
    have frame : (chains hash c.val s).getWord32 (BitVec.ofNat 64 (0x20 + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x20 + 4 * i.val)) := by
      simp only [MachineState.getWord32]
      rw [SphincsMaskedChainFrame.chains_frame hash s pc zero c.val bound _
        (Or.inl (by fin_cases i <;> decide))]
    exact frame.trans (key i)

/-- The full 52-chain endpoint buffer is the seeded abstract WOTS public key. -/
theorem publicKey_words (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (ctx : Secret.Context s parameter seed lay treeIdx leaf ⟨0,by decide⟩)
    (pc : s.pc = 0x112c) (c : ChainIndex) :
    Words20 (chains hash 52 s) (0x44300 + 20 * c.val)
      ((evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.oneTimePublicKey parameter lay treeIdx leaf seed :
          OracleComp SphincsSecurity.HashSpec (ChainIndex → Digest))) c) := by
  have counter : s.getMem 0x43050 = 0 := ctx.2.2.2.1
  have bound : c.val < 52 := c.isLt
  have location : (chains hash c.val s).pc = 0x112c := by
    rw [(chains_trace hash s pc counter c.val (by omega)).2.2,if_neg (by omega)]
  have value := Secret.endpoint_value hash (chains hash c.val s) parameter seed lay treeIdx leaf c
    (chains_context hash s parameter seed lay treeIdx leaf ctx pc c) location
  intro i
  rw [chains_data hash s pc counter 52 (by decide) c bound i]
  simpa only [Seeded.oneTimePublicKey,Concrete.evalWithAnswerFn_sequenceFin,show chainLength - 1 = 7 by rfl] using value i

theorem publicKey_bytes (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (ctx : Secret.Context s parameter seed lay treeIdx leaf ⟨0,by decide⟩)
    (pc : s.pc = 0x112c) (c : ChainIndex) (j : Fin 20) :
    (chains hash 52 s).getByte (BitVec.ofNat 64 (0x44300 + 20 * c.val + j.val)) =
      ((evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.oneTimePublicKey parameter lay treeIdx leaf seed :
          OracleComp SphincsSecurity.HashSpec (ChainIndex → Digest))) c).extractLsb' (8 * j.val) 8 := by
  have bound : c.val < 52 := c.isLt
  exact words20_byte _ _ _ (by omega) (by omega)
    (publicKey_words hash s parameter seed lay treeIdx leaf ctx pc c) j


end PublicKey

namespace Leaf
open SphincsMaskedLeafLoop SphincsMaskedLeafDomain
def HeaderContext (s : MachineState) (parameter : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) : Prop :=
  s.getMem 0x43000#64 = BitVec.ofNat 64 lay.val ∧ s.getMem 0x43008#64 = BitVec.ofNat 64 treeIdx.val ∧
  s.getMem 0x43018#64 = BitVec.ofNat 64 leaf.val ∧ s.getMem 0x43010#64 = 0 ∧ Words20 s 0x74 parameter

def header (parameter : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) : List Byte :=
  ((fieldBytes (hashDomainFields (.leaf lay treeIdx leaf))) ++ bytesLE 20 parameter).map UInt8.toBitVec

theorem header_length (parameter : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) : (header parameter lay treeIdx leaf).length = 40 := by
  simp [header,hashDomainFields,tweakFields,fieldBytes,bytesLE]

theorem header_byte (s : MachineState) (parameter : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex)
    (ctx : HeaderContext s parameter lay treeIdx leaf) (i : Fin 40) :
    (hashPrepare s).getByte (BitVec.ofNat 64 (0x40000 + i.val)) =
      (header parameter lay treeIdx leaf)[i.val]'(by rw [header_length];exact i.isLt) := by
  have h := SphincsVerifierFtsGenericBytes.variableWord_byte (hashPrepare s)
    (0x40000 + 4 * (i.val / 4)) (by omega) (by omega) 0 ⟨i.val % 4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  rw [show 0x40000 + 4 * (i.val / 4) + i.val % 4 = 0x40000 + i.val by omega] at h
  rw [h,header_words s ⟨i.val / 4,by omega⟩]
  obtain ⟨layer,tree,index,position,par⟩ := ctx
  have p0 := par 0
  have p1 := par 1
  have p2 := par 2
  have p3 := par 3
  have p4 := par 4
  norm_num at p0 p1 p2 p3 p4
  have treeWidth : (BitVec.ofNat 64 treeIdx.val).setWidth 32=BitVec.ofNat 32 treeIdx.val := by simp
  fin_cases i <;>
    simp [headerWord,layer,tree,index,position,p0,p1,p2,p3,p4,extractWord32,
      header,hashDomainFields,tweakFields,fieldBytes,bytesLE,protocolDomainSep]
  all_goals first
    | (fin_cases lay <;> decide)
    | (rw [←treeWidth]; exact BitVec.extractLsb'_setWidth_of_le (by decide))
    | (solve | simp [BitVec.setWidth_ushiftRight_eq_extractLsb,SphincsMaskedSignForestDomain.nested_extract])

def input (parameter : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (endpoints : ChainIndex → Digest) : HashInput :=
  tweakableHashInput parameter (.leaf lay treeIdx leaf) (Concrete.leafPayload endpoints)

theorem input_split (parameter : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (endpoints : ChainIndex → Digest) :
    (input parameter lay treeIdx leaf endpoints).map UInt8.toBitVec =
      header parameter lay treeIdx leaf ++ (Concrete.leafPayload endpoints).map UInt8.toBitVec := by
  simp [input,tweakableHashInput,tweakBytes,header,List.append_assoc]

theorem query_eq (s : MachineState) (parameter : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) (ctx : HeaderContext s parameter lay treeIdx leaf)
    (payload : ∀ i : Fin 1040, s.getByte (BitVec.ofNat 64 (0x40028 + i.val)) =
      (endpoints ⟨i.val / 20,by change i.val / 20 < 52;omega⟩).extractLsb' (8 * (i.val % 20)) 8) :
    hashInput (hashPrepare s) = toQuery (input parameter lay treeIdx leaf endpoints) := by
  apply Serialization.hashInput_of_list (hashPrepare s) 0x40000 ((input parameter lay treeIdx leaf endpoints).map UInt8.toBitVec)
  · exact (hashPrepare_registers s).1
  · rw [input_split,List.length_append,header_length,List.length_map,leafPayload_length,
      (hashPrepare_registers s).2.1];rfl
  · intro i hi
    simp only [input_split] at hi ⊢
    have bound : i < 1080 := by simpa only [List.length_append,header_length,List.length_map,leafPayload_length] using hi
    by_cases h : i < 40
    · rw [List.getElem_append_left (by simpa only [header_length] using h)]
      exact header_byte s parameter lay treeIdx leaf ctx ⟨i,h⟩
    · rw [List.getElem_append_right (by simpa only [header_length] using Nat.le_of_not_gt h)]
      simp only [header_length]
      have offset : 0x40000 + i = 0x40028 + (i - 40) := by omega
      rw [offset,hashPrepare_payload s ⟨i-40,by omega⟩,payload ⟨i-40,by omega⟩]
      simp only [leafPayload_flat,List.map_ofFn,List.getElem_ofFn,Function.comp_apply,UInt8.toBitVec_ofBitVec]


/-- The actual tag-two HASH answer equals the abstract leaf hash of all endpoints. -/
theorem answer_value (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) (endpoints : ChainIndex → Digest)
    (ctx : HeaderContext s parameter lay treeIdx leaf)
    (payload : ∀ i : Fin 1040, s.getByte (BitVec.ofNat 64 (0x40028+i.val))=
      (endpoints ⟨i.val/20,by change i.val/20<52;omega⟩).extractLsb' (8*(i.val%20)) 8) :
    Words20 (SphincsMaskedLeafLoop.answerState hash s) 0x42000
      (evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
        (Concrete.leafHash parameter lay treeIdx leaf endpoints : OracleComp SphincsSecurity.HashSpec Digest)) := by
  intro i
  rw [SphincsMaskedLeafDomain.answer_words,query_eq s parameter lay treeIdx leaf endpoints ctx payload]
  rw [Concrete.leafHash,SphincsMaskedChainDomain.eval_hash]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

end Leaf

set_option backward.isDefEq.respectTransparency true

open SphincsMaskedSignOtsShift SphincsVerifierFtsRootCopy

/-- PC rebasing leaves all live data unchanged. -/
theorem rebase_eq (delta p : Word) (s : MachineState) (pc : s.pc=p+delta) :
    shift delta (s.setPC p)=s := by
  unfold shift
  rw [show (s.setPC p).pc=p from rfl,←pc,setPC_twice]
  cases s;rfl

/-- The exact signer endpoint loop produces the seeded WOTS public key at
    any live layer/tree address, with all 416 actual HASH calls accounted for. -/
theorem signer_endpoints (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex)
    (leaf : LeafIndex) (ctx : Secret.Context s parameter seed lay treeIdx leaf ⟨0,by decide⟩)
    (pc : s.pc=0x112c+chainDelta location) :
    Trace hash SphincsMaskedImages.sign s 40352 43680 416 468
      (shift (chainDelta location) (chains hash 52 (s.setPC 0x112c))) ∧
    (∀ c : ChainIndex, Words20 (shift (chainDelta location) (chains hash 52 (s.setPC 0x112c)))
      (0x44300+20*c.val)
      ((evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.oneTimePublicKey parameter lay treeIdx leaf seed :
          OracleComp SphincsSecurity.HashSpec (ChainIndex → Digest))) c)) := by
  refine ⟨endpoint_array location hash s pc ctx.2.2.2.1,?_⟩
  intro c i
  rw [SphincsMaskedSignOtsShift.shift_word]
  exact PublicKey.publicKey_words hash (s.setPC 0x112c) parameter seed lay treeIdx leaf ctx rfl c i

/-- Byte-level form of the same actual endpoint array. -/
theorem signer_endpoint_bytes (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex)
    (leaf : LeafIndex) (ctx : Secret.Context s parameter seed lay treeIdx leaf ⟨0,by decide⟩)
    (pc : s.pc=0x112c+chainDelta location) (c : ChainIndex) (j : Fin 20) :
    (shift (chainDelta location) (chains hash 52 (s.setPC 0x112c))).getByte
      (BitVec.ofNat 64 (0x44300+20*c.val+j.val))=
      ((evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.oneTimePublicKey parameter lay treeIdx leaf seed :
          OracleComp SphincsSecurity.HashSpec (ChainIndex → Digest))) c).extractLsb' (8*j.val) 8 := by
  exact words20_byte _ _ _ (by have := c.isLt;change c.val<52 at this;omega) (by omega)
    ((signer_endpoints location hash s parameter seed lay treeIdx leaf ctx pc).2 c) j

/-- Transfer the shared tag-two header and HASH instruction into each signer layer. -/
theorem leaf_hash_trace (location : Fin 5) (hash : Hash) (s : MachineState) (pc : s.pc=0x14a0) :
    Trace hash SphincsMaskedImages.sign (shift (chainDelta location) s) 42 177 1 17
      (shift (chainDelta location) (SphincsMaskedLeafLoop.answerState hash s)) := by
  open SphincsMaskedLeafLoop in
  have block:=block_shift SphincsMaskedImages.sign (chainDelta location) hashPrepareSchedule (by decide)
    (encoded_of location hashPrepareSchedule (by decide) hashPrepare_code) s (hashPrepare_checked s pc)
  obtain ⟨src,bits,dst,service⟩:=SphincsMaskedLeafLoop.hashPrepare_registers s
  have fetched : fetch SphincsMaskedImages.sign (shift (chainDelta location) (SphincsMaskedLeafLoop.hashPrepare s))=
      some (.base .ECALL) := by
    rw [fetch_at,shift_pc,SphincsMaskedLeafLoop.hashPrepare_pc s pc]
    rw [instruction_transfer location 0x1544 (by decide) (by decide) (by decide)]
    decide
  have valid : hashArgumentsValid (SphincsMaskedLeafLoop.hashPrepare s)=true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (SphincsMaskedLeafLoop.hashPrepare s)).1=8640 := by simp [hashInput,bits]
  have one:=hash_block_shift (chainDelta location) hash SphincsMaskedImages.sign
    (SphincsMaskedLeafLoop.hashPrepare s) fetched service valid
  have hashing : Trace hash SphincsMaskedImages.sign
      (shift (chainDelta location) (SphincsMaskedLeafLoop.hashPrepare s)) 1 136 1 17
      (shift (chainDelta location) (SphincsMaskedLeafLoop.answerState hash s)) := by
    simpa only [len,SphincsMaskedLeafLoop.answerState,show compressions 8640=17 from by decide,Nat.reduceMul] using one
  exact block.trace.trans hashing

/-- Actual signer tag-two execution, including its semantic answer. -/
theorem signer_leaf_hash (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) (ctx : Leaf.HeaderContext s parameter lay treeIdx leaf)
    (pc : s.pc=0x14a0+chainDelta location)
    (payload : ∀ i : Fin 1040, s.getByte (BitVec.ofNat 64 (0x40028+i.val))=
      (endpoints ⟨i.val/20,by change i.val/20<52;omega⟩).extractLsb' (8*(i.val%20)) 8) :
    Trace hash SphincsMaskedImages.sign s 42 177 1 17
      (shift (chainDelta location) (SphincsMaskedLeafLoop.answerState hash (s.setPC 0x14a0))) ∧
    Words20 (shift (chainDelta location) (SphincsMaskedLeafLoop.answerState hash (s.setPC 0x14a0))) 0x42000
      (evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
        (Concrete.leafHash parameter lay treeIdx leaf endpoints : OracleComp SphincsSecurity.HashSpec Digest)) := by
  constructor
  · have trace:=leaf_hash_trace location hash (s.setPC 0x14a0) rfl
    rw [rebase_eq _ _ s pc] at trace
    exact trace
  · intro i
    rw [SphincsMaskedSignOtsShift.shift_word]
    exact Leaf.answer_value hash (s.setPC 0x14a0) parameter lay treeIdx leaf endpoints ctx payload i

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsDomain.Chain.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chain.query_eq

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsDomain.Chain.walk_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chain.walk_value

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsDomain.Secret.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Secret.query_eq

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsDomain.PublicKey.publicKey_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PublicKey.publicKey_words

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsDomain.Leaf.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Leaf.query_eq

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsDomain.signer_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_endpoints

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsDomain.signer_leaf_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_leaf_hash

end SigGolfCandidate.SphincsMaskedSignOtsDomain
