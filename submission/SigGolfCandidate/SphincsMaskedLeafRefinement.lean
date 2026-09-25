import SigGolfCandidate.SphincsMaskedLeafDomain

namespace SigGolfCandidate.SphincsMaskedLeafRefinement
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedChainStep SphincsMaskedChainLoop
open SphincsMaskedChainEndpoints SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsMaskedPublicKeyDomain SphincsMaskedLeafLoop SphincsMaskedLeafDomain
open SphincsVerifierFtsRootCopy SphincsVerifierCopyMemory SphincsBridge SphincsSecurity
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Stable key material and the top-layer tree selection. -/
def KeyContext (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed) : Prop :=
  s.getMem 0x43000#64 = 0 ∧ s.getMem 0x43008#64 = 0 ∧ Words20 s 0x74 parameter ∧ Words32 s seed

def Protected (a : Word) : Prop :=
  a.toNat < 0x40000 ∨ a = 0x43000#64 ∨ a = 0x43008#64 ∨ a = 0x43018#64 ∨ a = 0x43020#64

theorem protected_ne (a : Word) (ha : Protected a) (b : Word)
    (hb : 0x40000 ≤ b.toNat ∧ b ≠ 0x43000#64 ∧ b ≠ 0x43008#64 ∧ b ≠ 0x43018#64 ∧ b ≠ 0x43020#64) : a ≠ b := by
  intro eq; subst b
  rcases ha with h | h | h | h | h
  · omega
  · exact hb.2.1 h
  · exact hb.2.2.1 h
  · exact hb.2.2.2.1 h
  · exact hb.2.2.2.2 h

theorem context_transport (s t : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (ctx : KeyContext s parameter seed)
    (frame : ∀ a, a.toNat < 0x88 ∨ a = 0x43000#64 ∨ a = 0x43008#64 → t.getMem a = s.getMem a) :
    KeyContext t parameter seed := by
  obtain ⟨layer,tree,par,key⟩ := ctx
  refine ⟨(frame _ (Or.inr (Or.inl rfl))).trans layer,
    (frame _ (Or.inr (Or.inr rfl))).trans tree,?_,?_⟩
  · intro i
    simp only [MachineState.getWord32]
    rw [frame _ (Or.inl (by fin_cases i <;> decide))]
    exact par i
  · intro i
    simp only [MachineState.getWord32]
    rw [frame _ (Or.inl (by fin_cases i <;> decide))]
    exact key i

theorem entry_frame (s : MachineState) (a : Word) (ha : a ≠ 0x43050#64) :
    (entry s).getMem a = s.getMem a := by
  simp [entry,runSchedule,entrySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ha]

theorem entry_context (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (ctx : KeyContext s parameter seed) : KeyContext (entry s) parameter seed := by
  apply context_transport s _ parameter seed ctx
  intro a ha
  apply entry_frame
  exact protected_ne a (by rcases ha with h | h | h; exact Or.inl (by omega); exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h))) _ (by decide)

theorem chains_context (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (ctx : KeyContext s parameter seed) (pc : s.pc = 0x112c) (counter : s.getMem 0x43050 = 0)
    (n : Nat) (hn : n ≤ 52) : KeyContext (chains hash n s) parameter seed := by
  apply context_transport s _ parameter seed ctx
  intro a ha
  rcases ha with low | layer | tree
  · exact SphincsMaskedChainFrame.chains_frame hash s pc counter n hn a (Or.inl (by omega))
  · exact chains_control hash s pc counter n hn a (Or.inl layer)
  · exact chains_control hash s pc counter n hn a (Or.inr tree)

theorem chainNext_index (hash : Hash) (s : MachineState) (c : Fin 52)
    (counter : s.getMem 0x43050 = BitVec.ofNat 64 c.val) :
    (chainNext hash s).getMem 0x43018 = s.getMem 0x43020 := by
  change (endpointFinish (endpointStored (chainValue hash s))).getMem _ = _
  rw [endpointFinish_frame _ _ (by decide)]
  change (SphincsVerifierCopy.copyRootState (endpointSetup (chainValue hash s))).getMem _ = _
  rw [copyRoot_mem_frame]
  · rw [endpointSetup_frame,chainValue,walk_frame hash 7 _ _ (by decide)]
    exact initial_index hash s
  · intro i
    rw [(endpointSetup_registers (chainValue hash s) c.val ((chainValue_counter hash s).trans counter)).2]
    fin_cases c <;> fin_cases i <;> decide

theorem endpoints_index (hash : Hash) (s : MachineState) (pc : s.pc = 0x112c)
    (counter : s.getMem 0x43050 = 0) :
    (chains hash 52 s).getMem 0x43018 = s.getMem 0x43020 := by
  change (chainNext hash (chains hash 51 s)).getMem _ = _
  rw [chainNext_index hash _ ⟨51,by decide⟩ (chains_trace hash s pc counter 51 (by decide)).2.1]
  exact SphincsMaskedChainFrame.chains_frame hash s pc counter 51 (by decide) _ (Or.inr rfl)

theorem copySetup_frame (s : MachineState) (a : Word) (ha : a ≠ 0x43010#64) :
    (copySetup s).getMem a = s.getMem a := by
  simp [copySetup,runSchedule,copySetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ha]

theorem copySetup_position (s : MachineState) : (copySetup s).getMem 0x43010 = 0 := by
  simp [copySetup,runSchedule,copySetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem payload_outside (a : Word) (ha : Protected a) (i : Nat) (hi : i < 130) :
    a ≠ wordAddress 0x40028 i := by
  apply protected_ne a ha
  simp only [wordAddress,BitVec.toNat_ofNat]
  have small : 0x40028 + 8 * i < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt small]
  refine ⟨by omega,?_,?_,?_,?_⟩
  all_goals intro eq; have h := congrArg BitVec.toNat eq; simp only [BitVec.toNat_ofNat] at h; omega

/-- Copy all 1,040 bytes while retaining every low-memory cache cell and keygen control. -/
theorem payload_copy_full (s : MachineState) (pc : s.pc = 0x1464) :
    ∃ t, OrdinarySteps SphincsMaskedImages.keygen s 789 t ∧ t.pc = 0x14a0 ∧
      t.getMem 0x43010 = 0 ∧
      (∀ i : Fin 1040, t.getByte (BitVec.ofNat 64 (0x40028 + i.val)) = s.getByte (BitVec.ofNat 64 (0x44300 + i.val))) ∧
      (∀ a, Protected a → t.getMem a = s.getMem a) := by
  have regs := copySetup_registers s
  have inv : CopyInvariant 0x1488 0x44300 0x40028 130 130 (copySetup s) :=
    ⟨by decide,by decide,copySetup_pc s pc,regs.1,regs.2.1,regs.2.2⟩
  obtain ⟨t,trace,done,copied,frame⟩ := copy_all SphincsMaskedImages.keygen 0x1488
    payload_copy_code 0x44300 0x40028 130 (copySetup s) inv
    (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))
  refine ⟨t,ordinary_trans _ _ _ _ 9 780 (copySetup_block s pc) trace,done.2.2.1,?_,?_,?_⟩
  · rw [frame,copySetup_position]
    intro i hi eq
    have h := congrArg BitVec.toNat eq
    change 0x43010 = (0x40028 + 8 * i) % 2 ^ 64 at h
    omega
  · intro i
    apply SphincsVerifierFtsRootCopyBytes.bytes_eq_of_words s t 0x44300 0x40028 1040
      (by decide) (by decide) (by decide) (by decide) _ i.val i.isLt
    intro j hj
    rw [copied j hj,copySetup_frame]
    intro eq; have h := congrArg BitVec.toNat eq
    simp only [wordAddress,BitVec.toNat_ofNat] at h
    omega
  · intro a ha
    rw [frame a (payload_outside a ha),copySetup_frame s a (protected_ne a ha _ (by decide))]

theorem hash_frame (hash : Hash) (s : MachineState) (a : Word) (ha : Protected a) :
    (SphincsMaskedLeafLoop.answerState hash s).getMem a = s.getMem a := by
  have dst := (hashPrepare_registers s).2.2.1
  have h0 := protected_ne a ha 0x42000#64 (by decide)
  have h1 := protected_ne a ha 0x42008#64 (by decide)
  have h2 := protected_ne a ha 0x42010#64 (by decide)
  have h3 := protected_ne a ha 0x42018#64 (by decide)
  simp [SphincsMaskedLeafLoop.answerState,writeHash,dst,MachineState.writeWords,h0,h1,h2,h3]
  apply hashPrepare_frame
  simp only [headerWrites,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true]
  exact ⟨protected_ne a ha _ (by decide),protected_ne a ha _ (by decide),
    protected_ne a ha _ (by decide),protected_ne a ha _ (by decide),protected_ne a ha _ (by decide)⟩

theorem nextLeaf_key_frame (s : MachineState) (leaf : Fin 2048)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) (a : Word)
    (ha : a.toNat < 0x88 ∨ a = 0x43000#64 ∨ a = 0x43008#64) :
    (nextLeaf s).getMem a = s.getMem a := by
  change (finish (SphincsVerifierCopy.copyRootState (storeSetup s))).getMem a = _
  rw [SphincsMaskedLeafCache.finish_frame _ a]
  · rw [copyRoot_mem_frame]
    · exact SphincsMaskedLeafCache.storeSetup_frame s a
    · intro i
      rw [(storeSetup_registers s leaf.val counter).2]
      have address : BitVec.ofNat 64 (0x88 + 20 * leaf.val) +
          signExtend12 (4#12 * BitVec.ofNat 12 i.val) = BitVec.ofNat 64 (0x88 + 20 * leaf.val + 4 * i.val) := by
        fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
      rw [address]
      intro eq
      have bound := SphincsMaskedLeafCache.cache_word_bounded leaf i
      have lower : 0x88 ≤ (alignToDword (BitVec.ofNat 64 (0x88 + 20 * leaf.val + 4 * i.val))).toNat := by
        have aligned : alignToDword (BitVec.ofNat 64 (0x88 + 20 * leaf.val + 4 * i.val)) =
            BitVec.ofNat 64 (0x88 + 8 * ((20 * leaf.val + 4 * i.val) / 8)) := by
          have ha : (BitVec.ofNat 64 0x88).toNat % 8 = 0 := by decide
          have hover : (BitVec.ofNat 64 0x88).toNat + (20 * leaf.val + 4 * i.val) < 2 ^ 64 := by
            change 0x88 + (20 * leaf.val + 4 * i.val) < 2 ^ 64; omega
          simpa only [BitVec.ofNat_add,Nat.add_assoc] using alignToDword_add_ofNat_of_aligned ha hover
        rw [aligned,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
        omega
      rw [← eq] at bound lower
      rcases ha with h | rfl | rfl <;> norm_num at * <;> omega
  · intro eq
    rcases ha with h | h | h
    · rw [eq] at h; contradiction
    · rw [h] at eq; contradiction
    · rw [h] at eq; contradiction

/-- info: 'SigGolfCandidate.SphincsMaskedLeafRefinement.payload_copy_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms payload_copy_full


theorem protected_of_key_address (a : Word)
    (h : a.toNat < 0x88 ∨ a = 0x43000#64 ∨ a = 0x43008#64) : Protected a := by
  rcases h with h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

def leafValue (hash : Hash) (parameter : BitVec 160) (seed : MasterSeed) (leaf : LeafIndex) : Digest :=
  evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
    (do let endpoints ← Seeded.oneTimePublicKey parameter topLayer Concrete.rootTree leaf seed
        Concrete.leafHash parameter topLayer Concrete.rootTree leaf endpoints : OracleComp SphincsSecurity.HashSpec Digest)

theorem nextLeaf_position (s : MachineState) (leaf : Fin 2048) (pc : s.pc = 0x1548)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) :
    (nextLeaf s).getMem 0x43020 = BitVec.ofNat 64 (leaf.val + 1) ∧
    (nextLeaf s).pc = if leaf.val + 1 = 2048 then 0x15cc else 0x111c := by
  have next : BitVec.ofNat 64 leaf.val + 1 = BitVec.ofNat 64 (leaf.val + 1) := (BitVec.ofNat_add _ _).symm
  constructor
  · change (finish (stored s)).getMem _ = _
    rw [finish_leaf,stored_leaf s leaf counter,counter,next]
  · change (finish (stored s)).pc = _
    rw [finish_pc _ (stored_pc s pc),stored_leaf s leaf counter,counter,next]
    have eq : (BitVec.ofNat 64 (leaf.val + 1) : Word) = 2048 ↔ leaf.val + 1 = 2048 := by
      constructor
      · intro h
        have hh := congrArg BitVec.toNat h
        change (leaf.val + 1) % 2 ^ 64 = 2048 at hh
        rw [Nat.mod_eq_of_lt (by omega)] at hh
        exact hh
      · intro h; rw [h];rfl
    simp only [eq]

/-- One actual leaf iteration computes its seeded abstract leaf and preserves every other cache slot. -/
theorem leaf_contract (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (leaf : LeafIndex) (ctx : KeyContext s parameter seed) (pc : s.pc = 0x111c)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) :
    ∃ final, Trace hash SphincsMaskedImages.keygen s 41220 44683 417 485 final ∧
      final.getMem 0x43020 = BitVec.ofNat 64 (leaf.val + 1) ∧
      final.pc = (if leaf.val + 1 = 2048 then 0x15cc else 0x111c) ∧
      KeyContext final parameter seed ∧
      Words20 final (0x88 + 20 * leaf.val) (leafValue hash parameter seed leaf) ∧
      (∀ other : LeafIndex, other ≠ leaf → ∀ i : Fin 5,
        final.getWord32 (BitVec.ofNat 64 (0x88 + 20 * other.val + 4 * i.val)) =
          s.getWord32 (BitVec.ofNat 64 (0x88 + 20 * other.val + 4 * i.val))) := by
  let endpoints := chains hash 52 (entry s)
  let values := evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
    (Seeded.oneTimePublicKey parameter topLayer Concrete.rootTree leaf seed : OracleComp SphincsSecurity.HashSpec (ChainIndex → Digest))
  have entryCtx := entry_context s parameter seed ctx
  have epc := entry_pc s pc
  have entrySecret : SphincsMaskedSecretDomain.Context (entry s) parameter seed leaf ⟨0,by decide⟩ :=
    ⟨entryCtx.1,entryCtx.2.1,(entry_leaf s).trans counter,entry_counter s,entryCtx.2.2⟩
  obtain ⟨chainTrace,_,chainPc⟩ := fifty_two_chains hash (entry s) epc (entry_counter s)
  have endCtx := chains_context hash (entry s) parameter seed entryCtx epc (entry_counter s) 52 (by decide)
  have endCount : endpoints.getMem 0x43020 = BitVec.ofNat 64 leaf.val :=
    (SphincsMaskedChainFrame.chains_frame hash (entry s) epc (entry_counter s) 52 (by decide) _ (Or.inr rfl)).trans
      ((entry_leaf s).trans counter)
  have endIndex : endpoints.getMem 0x43018 = BitVec.ofNat 64 leaf.val :=
    (endpoints_index hash (entry s) epc (entry_counter s)).trans ((entry_leaf s).trans counter)
  obtain ⟨copied,copyTrace,copyPc,copyPos,copyBytes,copyFrame⟩ := payload_copy_full endpoints chainPc
  have copiedCtx : KeyContext copied parameter seed := by
    apply context_transport endpoints copied parameter seed endCtx
    intro a ha; exact copyFrame a (protected_of_key_address a ha)
  have copiedCount : copied.getMem 0x43020 = BitVec.ofNat 64 leaf.val :=
    (copyFrame _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans endCount
  have headerCtx : HeaderContext copied parameter leaf :=
    ⟨copiedCtx.1,copiedCtx.2.1,
      (copyFrame _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans endIndex,copyPos,copiedCtx.2.2.1⟩
  have payload : ∀ i : Fin 1040, copied.getByte (BitVec.ofNat 64 (0x40028 + i.val)) =
      (values ⟨i.val / 20,by change i.val / 20 < 52;omega⟩).extractLsb' (8 * (i.val % 20)) 8 := by
    intro i
    rw [copyBytes i]
    have bytes := publicKey_bytes hash (entry s) parameter seed leaf entrySecret epc
      ⟨i.val / 20,by change i.val / 20 < 52;omega⟩ ⟨i.val % 20,Nat.mod_lt _ (by decide)⟩
    have address : 0x44300 + 20 * (i.val / 20) + i.val % 20 = 0x44300 + i.val := by omega
    simpa only [address] using bytes
  let answer := SphincsMaskedLeafLoop.answerState hash copied
  have answerCount : answer.getMem 0x43020 = BitVec.ofNat 64 leaf.val := (answer_leaf hash copied).trans copiedCount
  have apc := answer_pc hash copied copyPc
  have answerCtx : KeyContext answer parameter seed := by
    apply context_transport copied answer parameter seed copiedCtx
    intro a ha; exact hash_frame hash copied a (protected_of_key_address a ha)
  have finalCtx : KeyContext (nextLeaf answer) parameter seed := by
    apply context_transport answer _ parameter seed answerCtx
    exact nextLeaf_key_frame answer leaf answerCount
  obtain ⟨nextCount,nextPc⟩ := nextLeaf_position answer leaf apc answerCount
  refine ⟨nextLeaf answer,?_,nextCount,nextPc,finalCtx,?_,?_⟩
  · exact (entry_block s pc).trace.trans (chainTrace.trans (copyTrace.trace.trans
      ((hash_trace hash copied copyPc).trans (store_block answer leaf apc answerCount).trace)))
  · have result := cache_value hash copied parameter leaf values headerCtx copiedCount payload
    simpa only [leafValue,evalWithAnswerFn_bind] using result
  · intro other ne i
    rw [SphincsMaskedLeafCache.nextLeaf_other answer leaf other (Ne.symm ne) answerCount i]
    simp only [MachineState.getWord32]
    have low := SphincsMaskedLeafCache.cache_word_bounded other i
    rw [hash_frame hash copied _ (Or.inl low),copyFrame _ (Or.inl low)]
    rw [SphincsMaskedChainFrame.chains_frame hash (entry s) epc (entry_counter s) 52 (by decide) _ (Or.inl low)]
    rw [entry_frame _ _ (protected_ne _ (Or.inl low) _ (by decide))]

/-- info: 'SigGolfCandidate.SphincsMaskedLeafRefinement.leaf_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_contract


/-- Inductively fill the cache with abstract seeded leaf values, without unrolling the loop. -/
theorem leaves_contract (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (ctx : KeyContext s parameter seed) (pc : s.pc = 0x111c) (counter : s.getMem 0x43020 = 0)
    (n : Nat) (hn : n ≤ 2048) :
    ∃ final, Trace hash SphincsMaskedImages.keygen s (41220 * n) (44683 * n) (417 * n) (485 * n) final ∧
      final.getMem 0x43020 = BitVec.ofNat 64 n ∧ final.pc = (if n = 2048 then 0x15cc else 0x111c) ∧
      KeyContext final parameter seed ∧
      (∀ leaf : LeafIndex, leaf.val < n → Words20 final (0x88 + 20 * leaf.val) (leafValue hash parameter seed leaf)) := by
  induction n with
  | zero => exact ⟨s,Trace.refl _,counter,pc,ctx,by intro leaf h;omega⟩
  | succ n ih =>
    obtain ⟨mid,first,count,loc,keyCtx,values⟩ := ih (by omega)
    have npc : mid.pc = 0x111c := by rw [loc,if_neg (by omega)]
    let current : LeafIndex := ⟨n,by change n < 2048;omega⟩
    obtain ⟨final,last,nextCount,nextPc,finalCtx,newValue,frame⟩ :=
      leaf_contract hash mid parameter seed current keyCtx npc count
    refine ⟨final,?_,nextCount,nextPc,finalCtx,?_⟩
    · simpa only [Nat.mul_succ] using first.trans last
    · intro leaf hl
      by_cases eq : leaf = current
      · subst leaf;exact newValue
      · intro i
        rw [frame leaf eq i]
        have ne : leaf.val ≠ n := fun h => eq (Fin.ext h)
        exact values leaf (by omega) i

/-- Every cache byte after the 2,048-leaf loop equals the corresponding abstract seeded leaf. -/
theorem all_leaves_contract (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (ctx : KeyContext s parameter seed) (pc : s.pc = 0x111c) (counter : s.getMem 0x43020 = 0) :
    ∃ final, Trace hash SphincsMaskedImages.keygen s 84418560 91510784 854016 993280 final ∧
      final.getMem 0x43020 = 2048 ∧ final.pc = 0x15cc ∧ KeyContext final parameter seed ∧
      (∀ leaf : LeafIndex, ∀ j : Fin 20,
        final.getByte (BitVec.ofNat 64 (0x88 + 20 * leaf.val + j.val)) =
          (leafValue hash parameter seed leaf).extractLsb' (8 * j.val) 8) := by
  obtain ⟨final,trace,count,loc,keyCtx,values⟩ := leaves_contract hash s parameter seed ctx pc counter 2048 (by decide)
  refine ⟨final,trace,count,?_,keyCtx,?_⟩
  · simpa using loc
  · intro leaf j
    have bound : leaf.val < 2048 := leaf.isLt
    exact words20_byte final _ _ (by omega) (by omega) (values leaf bound) j

/-- info: 'SigGolfCandidate.SphincsMaskedLeafRefinement.leaves_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaves_contract

/-- info: 'SigGolfCandidate.SphincsMaskedLeafRefinement.all_leaves_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms all_leaves_contract

end SigGolfCandidate.SphincsMaskedLeafRefinement
