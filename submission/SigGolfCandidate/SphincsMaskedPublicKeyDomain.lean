import SigGolfCandidate.SphincsMaskedSecretDomain
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Eval

namespace SigGolfCandidate.SphincsMaskedPublicKeyDomain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedChainStep SphincsMaskedChainLoop SphincsMaskedChainEndpoints
open SphincsMaskedChainDomain SphincsMaskedSecretDomain SphincsBridge SphincsSecurity
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The layer and tree fields are unchanged by endpoint production and storage. -/
theorem chainNext_control (hash : Hash) (s : MachineState) (c : Fin 52)
    (chain : s.getMem 0x43050 = BitVec.ofNat 64 c.val) (a : Word)
    (ha : a = 0x43000#64 ∨ a = 0x43008#64) :
    (chainNext hash s).getMem a = s.getMem a := by
  have value : (chainValue hash s).getMem a = s.getMem a := by
    rw [chainValue,walk_frame hash 7 _ a (by rcases ha with rfl | rfl <;> decide)]
    exact initialChain_frame hash s a (by rcases ha with rfl | rfl <;> decide)
  change (endpointFinish (endpointStored (chainValue hash s))).getMem a = _
  rw [endpointFinish_frame _ a (by rcases ha with rfl | rfl <;> decide)]
  change (SphincsVerifierCopy.copyRootState (endpointSetup (chainValue hash s))).getMem a = _
  rw [SphincsVerifierCopyMemory.copyRoot_mem_frame]
  · exact (endpointSetup_frame _ a).trans value
  · intro i
    rw [(endpointSetup_registers (chainValue hash s) c.val ((chainValue_counter hash s).trans chain)).2]
    rcases ha with rfl | rfl <;> fin_cases c <;> fin_cases i <;> decide

theorem chains_control (hash : Hash) (s : MachineState) (pc : s.pc = 0x112c)
    (counter : s.getMem 0x43050 = 0) (n : Nat) (hn : n ≤ 52) (a : Word)
    (ha : a = 0x43000#64 ∨ a = 0x43008#64) :
    (chains hash n s).getMem a = s.getMem a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [chains,chainNext_control hash _ ⟨n,by omega⟩
      (chains_trace hash s pc counter n (by omega)).2.1 a ha]
    exact ih (by omega)

/-- Each iteration retains the seed and parameter and selects precisely its own chain index. -/
theorem chains_context (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (leaf : LeafIndex) (ctx : SphincsMaskedSecretDomain.Context s parameter seed leaf ⟨0,by decide⟩)
    (pc : s.pc = 0x112c) (c : ChainIndex) :
    SphincsMaskedSecretDomain.Context (chains hash c.val s) parameter seed leaf c := by
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
    (leaf : LeafIndex) (ctx : SphincsMaskedSecretDomain.Context s parameter seed leaf ⟨0,by decide⟩)
    (pc : s.pc = 0x112c) (c : ChainIndex) :
    Words20 (chains hash 52 s) (0x44300 + 20 * c.val)
      ((evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.oneTimePublicKey parameter topLayer Concrete.rootTree leaf seed :
          OracleComp SphincsSecurity.HashSpec (ChainIndex → Digest))) c) := by
  have counter : s.getMem 0x43050 = 0 := ctx.2.2.2.1
  have bound : c.val < 52 := c.isLt
  have location : (chains hash c.val s).pc = 0x112c := by
    rw [(chains_trace hash s pc counter c.val (by omega)).2.2,if_neg (by omega)]
  have value := endpoint_value hash (chains hash c.val s) parameter seed leaf c
    (chains_context hash s parameter seed leaf ctx pc c) location
  intro i
  rw [chains_data hash s pc counter 52 (by decide) c bound i]
  simpa only [Seeded.oneTimePublicKey,Concrete.evalWithAnswerFn_sequenceFin,show chainLength - 1 = 7 by rfl] using value i

/-- Five lane equalities expose all twenty little-endian bytes of an abstract digest. -/
theorem words20_byte (s : MachineState) (base : Nat) (value : BitVec 160)
    (bounded : base + 20 ≤ 0x50000) (aligned : base % 4 = 0)
    (words : Words20 s base value) (j : Fin 20) :
    s.getByte (BitVec.ofNat 64 (base + j.val)) = value.extractLsb' (8 * j.val) 8 := by
  have lane := SphincsVerifierFtsGenericBytes.variableWord_byte s base bounded aligned
    ⟨j.val / 4,by omega⟩ ⟨j.val % 4,Nat.mod_lt _ (by decide)⟩
  rw [words] at lane
  have address : base + 4 * (j.val / 4) + j.val % 4 = base + j.val := by omega
  simp only [address] at lane
  rw [lane]
  fin_cases j <;> ext b hb <;> interval_cases b <;> simp

theorem publicKey_bytes (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (leaf : LeafIndex) (ctx : SphincsMaskedSecretDomain.Context s parameter seed leaf ⟨0,by decide⟩)
    (pc : s.pc = 0x112c) (c : ChainIndex) (j : Fin 20) :
    (chains hash 52 s).getByte (BitVec.ofNat 64 (0x44300 + 20 * c.val + j.val)) =
      ((evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.oneTimePublicKey parameter topLayer Concrete.rootTree leaf seed :
          OracleComp SphincsSecurity.HashSpec (ChainIndex → Digest))) c).extractLsb' (8 * j.val) 8 := by
  have bound : c.val < 52 := c.isLt
  exact words20_byte _ _ _ (by omega) (by omega)
    (publicKey_words hash s parameter seed leaf ctx pc c) j

/-- info: 'SigGolfCandidate.SphincsMaskedPublicKeyDomain.publicKey_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms publicKey_words

/-- info: 'SigGolfCandidate.SphincsMaskedPublicKeyDomain.publicKey_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms publicKey_bytes

end SigGolfCandidate.SphincsMaskedPublicKeyDomain
