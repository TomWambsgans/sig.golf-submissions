import SigGolfCandidate.SphincsMaskedLeafCache

namespace SigGolfCandidate.SphincsMaskedChainDomain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedChainStep SphincsBridge SphincsSecurity
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Five little-endian lanes encode a 160-bit parameter or chain value. -/
def Words20 (s : MachineState) (base : Nat) (value : BitVec 160) : Prop :=
  ∀ i : Fin 5, s.getWord32 (BitVec.ofNat 64 (base + 4 * i.val)) = value.extractLsb' (32 * i.val) 32

def Context (s : MachineState) (parameter value : BitVec 160) (leaf : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) : Prop :=
  s.getMem 0x43000#64 = 0 ∧ s.getMem 0x43008#64 = 0 ∧
  s.getMem 0x43018#64 = BitVec.ofNat 64 leaf.val ∧
  s.getMem 0x43050#64 = BitVec.ofNat 64 chain.val ∧
  s.getMem 0x43058#64 = BitVec.ofNat 64 step.val ∧
  Words20 s 0x74 parameter ∧ Words20 s 0x44b00 value

def payload (parameter value : BitVec 160) (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep) : List Byte :=
  (tweakableHashInput parameter (.chain topLayer Concrete.rootTree leaf chain step) (bytesLE 20 value)).map UInt8.toBitVec

theorem payload_length (parameter value : BitVec 160) (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep) :
    (payload parameter value leaf chain step).length = 60 := by
  simp [payload,tweakableHashInput,tweakBytes,hashDomainFields,tweakFields,fieldBytes,bytesLE,topLayer,Concrete.rootTree]

theorem prepared_byte (s : MachineState) (i : Fin 60) :
    (prepareState s).getByte (BitVec.ofNat 64 (0x40000 + i.val)) =
      (queryWord32 s ⟨i.val / 4,by omega⟩).extractLsb' (8 * (i.val % 4)) 8 := by
  have h := SphincsVerifierFtsGenericBytes.variableWord_byte (prepareState s)
    (0x40000 + 4 * (i.val / 4)) (by omega) (by omega) 0 ⟨i.val % 4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  rw [show 0x40000 + 4 * (i.val / 4) + i.val % 4 = 0x40000 + i.val by omega] at h
  rw [h,prepare_words s ⟨i.val / 4,by omega⟩]

theorem context_byte (s : MachineState) (parameter value : BitVec 160) (leaf : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) (ctx : Context s parameter value leaf chain step) (i : Fin 60) :
    (queryWord32 s ⟨i.val / 4,by omega⟩).extractLsb' (8 * (i.val % 4)) 8 =
      (payload parameter value leaf chain step)[i.val]'(by rw [payload_length]; exact i.isLt) := by
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
  fin_cases i <;>
    simp [queryWord32,layer,tree,index,counter,position,shift,p0,p1,p2,p3,p4,v0,v1,v2,v3,v4,extractWord32,
      payload,tweakableHashInput,tweakBytes,hashDomainFields,tweakFields,fieldBytes,bytesLE,
      chainLength,winternitzBits,protocolDomainSep,topLayer,Concrete.rootTree]
  all_goals
    ext b hb
    interval_cases b <;> simp


theorem query_eq (s : MachineState) (parameter value : BitVec 160) (leaf : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) (ctx : Context s parameter value leaf chain step) :
    hashInput (prepareState s) = toQuery
      (tweakableHashInput parameter (.chain topLayer Concrete.rootTree leaf chain step) (bytesLE 20 value)) := by
  apply Serialization.hashInput_of_list (prepareState s) 0x40000 (payload parameter value leaf chain step)
  · exact (prepare_registers s).1
  · rw [payload_length,(prepare_registers s).2.1]; rfl
  · intro i hi
    have bound : i < 60 := by simpa only [payload_length] using hi
    rw [prepared_byte s ⟨i,bound⟩]
    exact context_byte s parameter value leaf chain step ctx ⟨i,bound⟩

theorem step_value (hash : Hash) (s : MachineState) (parameter value : BitVec 160) (leaf : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) (ctx : Context s parameter value leaf chain step) :
    Words20 (stepState hash s) 0x44b00
      (truncateHash (hash (toQuery
        (tweakableHashInput parameter (.chain topLayer Concrete.rootTree leaf chain step) (bytesLE 20 value))))) := by
  intro i
  rw [step_value_words,query_eq s parameter value leaf chain step ctx]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

theorem eval_hash (hash : Hash) (parameter : PublicParameter) (domain : HashDomain) (input : HashInput) :
    evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
      (Concrete.tweakableHash parameter domain input : OracleComp SphincsSecurity.HashSpec Digest) =
        truncateHash (hash (toQuery (tweakableHashInput parameter domain input))) := by
  have evalOracle (input : HashInput) :
      evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Concrete.oracleHash input : OracleComp SphincsSecurity.HashSpec HashOutput) = adaptOracle hash input := by
    simp only [Concrete.oracleHash, HasQuery.query]
    exact simulateQ_spec_query (spec := SphincsSecurity.HashSpec) (r := Id) (adaptOracle hash) input
  simp only [Concrete.tweakableHash,evalWithAnswerFn_bind,evalWithAnswerFn_pure,evalOracle]
  rfl

def FixedContext (s : MachineState) (parameter : BitVec 160) (leaf : LeafIndex) (chain : ChainIndex) : Prop :=
  s.getMem 0x43000#64 = 0 ∧ s.getMem 0x43008#64 = 0 ∧
  s.getMem 0x43018#64 = BitVec.ofNat 64 leaf.val ∧
  s.getMem 0x43050#64 = BitVec.ofNat 64 chain.val ∧ Words20 s 0x74 parameter

theorem walk_fixed (hash : Hash) (s : MachineState) (n : Nat) (parameter : BitVec 160)
    (leaf : LeafIndex) (chain : ChainIndex) (ctx : FixedContext s parameter leaf chain) :
    FixedContext (walk hash n s) parameter leaf chain := by
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
    (leaf : LeafIndex) (chain : ChainIndex) (ctx : FixedContext s parameter leaf chain)
    (pc : s.pc = 0x1270) (zero : s.getMem 0x43058 = 0) (initial : Words20 s 0x44b00 value)
    (n : Nat) (hn : n ≤ 7) :
    Words20 (walk hash n s) 0x44b00
      (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Concrete.chainWalk parameter topLayer Concrete.rootTree leaf chain 0 n value :
          OracleComp SphincsSecurity.HashSpec Digest)) := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    obtain ⟨layer,tree,index,counter,par⟩ := walk_fixed hash s n parameter leaf chain ctx
    have count := (walk_trace hash s pc zero n (by omega)).2.1
    have ns : n < chainLength - 1 := by change n < 7; omega
    have stepCtx : Context (walk hash n s) parameter
        (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
          (Concrete.chainWalk parameter topLayer Concrete.rootTree leaf chain 0 n value :
            OracleComp SphincsSecurity.HashSpec Digest)) leaf chain ⟨n,ns⟩ :=
      ⟨layer,tree,index,counter,count,par,ih (by omega)⟩
    have result := step_value hash (walk hash n s) parameter _ leaf chain ⟨n,ns⟩ stepCtx
    simp only [Concrete.chainWalk]
    change Words20 (stepState hash (walk hash n s)) 0x44b00
      (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        ((Concrete.chainWalk parameter topLayer Concrete.rootTree leaf chain 0 n value :
          OracleComp SphincsSecurity.HashSpec Digest) >>= fun previous =>
          if h : 0 + n < chainLength - 1 then
            Concrete.tweakableHash parameter (.chain topLayer Concrete.rootTree leaf chain ⟨0 + n,h⟩)
              (bytesLE 20 previous) else pure 0))
    rw [evalWithAnswerFn_bind]
    have h : 0 + n < chainLength - 1 := by omega
    have choose : (if h : 0 + n < chainLength - 1 then
        (Concrete.tweakableHash parameter (.chain topLayer Concrete.rootTree leaf chain ⟨0 + n,h⟩)
          (bytesLE 20 (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
            (Concrete.chainWalk parameter topLayer Concrete.rootTree leaf chain 0 n value :
              OracleComp SphincsSecurity.HashSpec Digest))) : OracleComp SphincsSecurity.HashSpec Digest)
        else pure 0) =
      Concrete.tweakableHash parameter (.chain topLayer Concrete.rootTree leaf chain ⟨0 + n,h⟩)
        (bytesLE 20 (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
          (Concrete.chainWalk parameter topLayer Concrete.rootTree leaf chain 0 n value :
            OracleComp SphincsSecurity.HashSpec Digest))) := dif_pos h
    erw [choose,eval_hash]
    have stepEq : (⟨0 + n,h⟩ : ChainStep) = ⟨n,ns⟩ := Fin.ext (Nat.zero_add n)
    rw [stepEq]
    exact result

/-- info: 'SigGolfCandidate.SphincsMaskedChainDomain.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_eq

/-- info: 'SigGolfCandidate.SphincsMaskedChainDomain.step_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_value

/-- info: 'SigGolfCandidate.SphincsMaskedChainDomain.walk_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walk_value

end SigGolfCandidate.SphincsMaskedChainDomain
