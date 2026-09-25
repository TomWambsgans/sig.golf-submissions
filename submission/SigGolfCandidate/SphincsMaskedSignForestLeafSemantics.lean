import SigGolfCandidate.SphincsSecurity.Completeness.Recovery
import SigGolfCandidate.SphincsMaskedSignForestLeafDomain
import SigGolfCandidate.SphincsMaskedSignForestExecution

namespace SigGolfCandidate.SphincsMaskedSignForestLeafSemantics
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsSecurity SphincsBridge SphincsMaskedChainDomain
open SphincsMaskedKeygenPrefix SphincsMaskedSignForestEntry
open SphincsMaskedSignForestExecution SphincsVerifierFtsRootCopy
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev HeaderRetained (a : Word) : Prop := a.toNat<0x40000 ∨ 0x43000≤a.toNat

/-- The first HASH does not change live tweak fields or parameter/key memory. -/
theorem first_frame (hash : Hash) (s : MachineState) (a : Word)
    (outside : HeaderRetained a) : (leafAnswer hash s).getMem a=s.getMem a := by
  have ne (b : Word) (hb : b=0x40000#64 ∨ b=0x40008#64 ∨ b=0x40010#64 ∨
      b=0x40018#64 ∨ b=0x40020#64 ∨ b=0x42000#64 ∨ b=0x42008#64 ∨
      b=0x42010#64 ∨ b=0x42018#64) : a≠b := by
    intro eq;subst b
    rcases hb with h|h|h|h|h|h|h|h|h <;> subst a <;> norm_num [HeaderRetained] at outside
  have dst := (leafHash_registers s).2.2.1
  simp [leafAnswer,writeHash,dst,MachineState.writeWords,
    leafHashReady,runSchedule,leafHashSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,
    ne (0x40000#64) (by simp),ne (0x40008#64) (by simp),ne (0x40010#64) (by simp),
    ne (0x40018#64) (by simp),ne (0x40020#64) (by simp),ne (0x42000#64) (by simp),
    ne (0x42008#64) (by simp),ne (0x42010#64) (by simp),ne (0x42018#64) (by simp)]

/-- The low 160 bits of the first actual HASH answer are the seeded FORS secret. -/
theorem secret_value (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (ctx : SphincsMaskedSignForestDomain.Context s parameter seed index tree leaf) :
    Words20 (leafAnswer hash s) 0x42000
      (Completeness.ftsSecret (adaptOracle hash) parameter index tree leaf seed) := by
  have query := SphincsMaskedSignForestDomain.query_eq s parameter seed index tree leaf ctx
  unfold Completeness.ftsSecret
  rw [SphincsMaskedSecretDomain.eval_derive]
  intro i
  have dst := (leafHash_registers s).2.2.1
  have words : (leafAnswer hash s).getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) =
      (hash (hashInput (leafHashReady s))).extractLsb' (32*i.val) 32 := by
    fin_cases i <;>
      simp [leafAnswer,writeHash,dst,MachineState.writeWords,
        MachineState.getWord32,alignToDword,byteOffset,extractWord32]
    all_goals ext j hj; interval_cases j <;> simp
  rw [words,query]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

abbrev PayloadRetained (a : Word) : Prop := a.toNat<0x40000 ∨
  (0x43000≤a.toNat ∧ a.toNat<0x44b00) ∨ 0x44b18≤a.toNat

theorem payload_kept (s : MachineState) (a : Word) (outside : PayloadRetained a) :
    (SphincsMaskedSignForestLoop.payload s).getMem a=s.getMem a := by
  apply SphincsMaskedSignForestLoop.payload_frame
  repeat' apply And.intro
  all_goals intro eq;subst a;norm_num [PayloadRetained] at outside

/-- The first answer and unchanged tweak fields meet the second query's exact context. -/
theorem second_context (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (ctx : SphincsMaskedSignForestDomain.Context s parameter seed index tree leaf) :
    SphincsMaskedSignForestLeafDomain.Context (leafAnswer hash s) parameter
      (Completeness.ftsSecret (adaptOracle hash) parameter index tree leaf seed) index tree leaf := by
  obtain ⟨ht,hi,hp,hl,par,key⟩ := ctx
  refine ⟨?_,?_,?_,?_,?_,secret_value hash s parameter seed index tree leaf ⟨ht,hi,hp,hl,par,key⟩⟩
  · rw [payload_kept _ _ (by decide),first_frame _ _ _ (by decide)];exact ht
  · rw [payload_kept _ _ (by decide),first_frame _ _ _ (by decide)];exact hi
  · rw [payload_kept _ _ (by decide),first_frame _ _ _ (by decide)];exact hp
  · rw [payload_kept _ _ (by decide),first_frame _ _ _ (by decide)];exact hl
  · intro i
    have frame : (SphincsMaskedSignForestLoop.payload (leafAnswer hash s)).getWord32
        (BitVec.ofNat 64 (0x74+4*i.val)) = s.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) := by
      simp only [MachineState.getWord32]
      rw [payload_kept _ _ (by fin_cases i <;> decide),first_frame _ _ _ (by fin_cases i <;> decide)]
    exact frame.trans (par i)

/-- The second actual HASH query has the abstract tag-9 domain and the derived secret. -/
theorem second_query (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (ctx : SphincsMaskedSignForestDomain.Context s parameter seed index tree leaf) :
    hashInput (SphincsMaskedSignForestLeafDomain.ready (leafAnswer hash s)) =
      toQuery (tweakableHashInput parameter (.ftsLeaf index tree leaf)
        (bytesLE 20 (Completeness.ftsSecret (adaptOracle hash) parameter index tree leaf seed))) :=
  SphincsMaskedSignForestLeafDomain.query_eq _ _ _ _ _ _
    (second_context hash s parameter seed index tree leaf ctx)

/-- An abstract leaf, evaluated under the same oracle as the concrete image. -/
def leafValue (hash : Hash) (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) : Digest :=
  evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
    (Concrete.ftsLeafHash parameter index tree leaf
      (Completeness.ftsSecret (adaptOracle hash) parameter index tree leaf seed))

theorem leafValue_eq_node (hash : Hash) (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) :
    leafValue hash parameter seed index tree leaf =
      Completeness.ftsNodeValue (adaptOracle hash) parameter index tree seed 0 leaf.val :=
  (Completeness.ftsNodeValue_zero _ _ _ _ _ _).symm

/-- Both HASH answers and the cache store realize the abstract seeded leaf. -/
theorem stored_value (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (ctx : SphincsMaskedSignForestDomain.Context s parameter seed index tree leaf)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    Words20 (SphincsMaskedSignForestLoop.nextLeaf
      (SphincsMaskedSignForestLoop.answer hash (leafAnswer hash s)))
      (0x50000+20*leaf.val) (leafValue hash parameter seed index tree leaf) := by
  have count := (first_frame hash s 0x43020 (by decide)).trans counter
  have value := SphincsMaskedSignForestLoop.leaf_suffix_value hash (leafAnswer hash s) leaf count
  change Words20 _ _ (truncateHash (hash (hashInput
    (SphincsMaskedSignForestLeafDomain.ready (leafAnswer hash s))))) at value
  rw [second_query hash s parameter seed index tree leaf ctx] at value
  simpa only [leafValue,Concrete.ftsLeafHash,SphincsMaskedChainDomain.eval_hash] using value


/-- Persistent semantic context at the start of each FORS leaf iteration. -/
def Context (s : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) : Prop :=
  s.getMem 0x43000=BitVec.ofNat 64 tree.val ∧
  s.getMem 0x43008=BitVec.ofNat 64 index.val ∧
  Words20 s 0x74 parameter ∧ SphincsMaskedSecretDomain.Words32 s seed

abbrev StableAddress (a : Word) : Prop := a.toNat<0x40000 ∨
  (0x43000≤a.toNat ∧ a.toNat<0x44b00 ∧ a≠0x43010#64 ∧ a≠0x43018#64 ∧ a≠0x43020#64)

theorem setup_frame (s : MachineState) (a : Word)
    (h0 : a≠0x43010#64) (h1 : a≠0x43018#64) :
    (leafSetup s).getMem a=s.getMem a := by
  simp [leafSetup,runSchedule,leafSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1]

theorem setup_fields (s : MachineState) :
    (leafSetup s).getMem 0x43010=0 ∧ (leafSetup s).getMem 0x43018=s.getMem 0x43020 := by
  simp [leafSetup,runSchedule,leafSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

/-- The exact four-word seed copy also establishes the first query's context. -/
theorem prepare (s : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (ctx : Context s parameter seed index tree) (pc : s.pc=0x1d54)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    ∃ t, OrdinarySteps SphincsMaskedImages.sign s 38 t ∧ t.pc=0x1da4 ∧
      SphincsMaskedSignForestDomain.Context t parameter seed index tree leaf ∧
      ∀ a, HeaderRetained a → t.getMem a=(leafSetup s).getMem a := by
  obtain ⟨t,run,inv,data,frame⟩ := copy_all SphincsMaskedImages.sign 0x1d8c leafCopy_code
    0x20 0x40028 4 (leafSetup s) (leafSetup_copyInvariant s pc)
    (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
  have kept (a : Word) (ha : HeaderRetained a) : t.getMem a=(leafSetup s).getMem a := by
    apply frame
    intro i hi eq
    have val := congrArg BitVec.toNat eq
    simp only [wordAddress,BitVec.toNat_ofNat] at val
    rw [Nat.mod_eq_of_lt (by omega)] at val
    rcases ha with low|high <;> omega
  obtain ⟨ht,hi,par,key⟩ := ctx
  refine ⟨t,ordinary_trans _ s (leafSetup s) t 14 24 (leafSetup_block s pc) run,
    by simpa [CopyInvariant] using inv.2.2.1,?_,kept⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [kept _ (by decide),setup_frame _ _ (by decide) (by decide)];exact ht
  · rw [kept _ (by decide),setup_frame _ _ (by decide) (by decide)];exact hi
  · rw [kept _ (by decide)];exact (setup_fields s).1
  · rw [kept _ (by decide),(setup_fields s).2,counter]
  · intro i
    have eq : t.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) := by
      simp only [MachineState.getWord32]
      rw [kept _ (by fin_cases i <;> decide),setup_frame _ _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact eq.trans (par i)
  · intro i
    have d0 := (data 0 (by decide)).trans (leafSetup_secretWord s 0)
    have d1 := (data 1 (by decide)).trans (leafSetup_secretWord s 1)
    have d2 := (data 2 (by decide)).trans (leafSetup_secretWord s 2)
    have d3 := (data 3 (by decide)).trans (leafSetup_secretWord s 3)
    norm_num [wordAddress] at d0 d1 d2 d3
    have eq : t.getWord32 (BitVec.ofNat 64 (0x40028+4*i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) := by
      fin_cases i <;> simp [MachineState.getWord32,alignToDword,byteOffset,d0,d1,d2,d3]
    exact eq.trans (key i)

theorem stable_header (a : Word) (ha : StableAddress a) : HeaderRetained a := by
  rcases ha with low|high
  · exact Or.inl low
  · exact Or.inr high.1

theorem stable_excluded (a : Word) (ha : StableAddress a) :
    a≠0x43010#64 ∧ a≠0x43018#64 ∧ a≠0x43020#64 := by
  rcases ha with low|high
  · repeat' apply And.intro
    all_goals intro eq;subst a;norm_num at low
  · exact high.2.2

/-- The full iteration stores the abstract leaf and preserves all surrounding
    forest controls and previously stored endpoints. -/
theorem leaf_semantics (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (ctx : Context s parameter seed index tree) (pc : s.pc=0x1d54)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 183 205 2 3 t ∧
      t.pc=(if leaf.val+1=256 then 0x1fe8 else 0x1d54) ∧
      t.getMem 0x43020=BitVec.ofNat 64 (leaf.val+1) ∧
      Words20 t (0x50000+20*leaf.val) (leafValue hash parameter seed index tree leaf) ∧
      (∀ a, StableAddress a → t.getMem a=s.getMem a) ∧
      ∀ prior : Fin 256, prior≠leaf → ∀ i : Fin 5,
        t.getWord32 (BitVec.ofNat 64 (0x50000+20*prior.val+4*i.val)) =
          s.getWord32 (BitVec.ofNat 64 (0x50000+20*prior.val+4*i.val)) := by
  obtain ⟨prepared,prep,prepPc,prepCtx,copyFrame⟩ := prepare s parameter seed index tree leaf ctx pc counter
  have preCount : prepared.getMem 0x43020=BitVec.ofNat 64 leaf.val := by
    rw [copyFrame _ (by decide),setup_frame _ _ (by decide) (by decide),counter]
  have midCount := (first_frame hash prepared 0x43020 (by decide)).trans preCount
  have midPc := leafAnswer_pc hash prepared prepPc
  obtain ⟨last,done,loc⟩ := SphincsMaskedSignForestLoop.leaf_suffix hash (leafAnswer hash prepared) leaf midPc midCount
  refine ⟨SphincsMaskedSignForestLoop.nextLeaf (SphincsMaskedSignForestLoop.answer hash (leafAnswer hash prepared)),
    prep.trace.trans ((leafHash_trace hash prepared prepPc).trans last),loc,done,
    stored_value hash prepared parameter seed index tree leaf prepCtx preCount,?_,?_⟩
  · intro a ha
    have retained : a.toNat<0x40000 ∨ (0x43000≤a.toNat ∧ a.toNat<0x44b00 ∧ a≠0x43020#64) := by
      rcases ha with low|high
      · exact Or.inl low
      · exact Or.inr ⟨high.1,high.2.1,high.2.2.2.2⟩
    rw [SphincsMaskedSignForestLoop.leaf_suffix_frame _ _ _ midCount a retained,
      first_frame _ _ _ (stable_header a ha),copyFrame _ (stable_header a ha),
      setup_frame _ _ (stable_excluded a ha).1 (stable_excluded a ha).2.1]
  · intro prior different i
    rw [SphincsMaskedSignForestLoop.leaf_suffix_prior _ _ leaf prior (Ne.symm different) midCount i]
    simp only [MachineState.getWord32]
    have high := SphincsMaskedSignForestLoop.cache_cell_lower prior i
    rw [first_frame _ _ _ (Or.inr (by omega)),copyFrame _ (Or.inr (by omega)),
      setup_frame _ _ (by intro eq;rw [eq] at high;norm_num at high)
        (by intro eq;rw [eq] at high;norm_num at high)]


/-- Semantic key/parameter/tweak context depends only on retained memory. -/
theorem context_preserved (s t : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree)
    (frame : ∀ a, StableAddress a → t.getMem a=s.getMem a)
    (ctx : Context s parameter seed index tree) : Context t parameter seed index tree := by
  obtain ⟨ht,hi,par,key⟩ := ctx
  refine ⟨(frame _ (by decide)).trans ht,(frame _ (by decide)).trans hi,?_,?_⟩
  · intro i
    have eq : t.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) := by
      simp only [MachineState.getWord32]
      rw [frame _ (by fin_cases i <;> decide)]
    exact eq.trans (par i)
  · intro i
    have eq : t.getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) := by
      simp only [MachineState.getWord32]
      rw [frame _ (by fin_cases i <;> decide)]
    exact eq.trans (key i)

/-- Optional enclosing invariants can mention retained signature memory, T,
    SIG_PTR, SELECTED, MSG_INDEX, or selector bytes without constraining HASH. -/
def FrameStable (extra : MachineState → Prop) : Prop :=
  ∀ s t, (∀ a, StableAddress a → t.getMem a=s.getMem a) → extra s → extra t

/-- Discharge the generic 256-leaf induction's complete semantic contract. -/
theorem leaf_contract (hash : Hash) (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) (extra : MachineState → Prop)
    (stable : FrameStable extra) :
    SphincsMaskedSignForestLoop.LeafContract hash
      (fun s => Context s parameter seed index tree ∧ extra s)
      (leafValue hash parameter seed index tree) := by
  intro leaf s ctx pc counter
  obtain ⟨t,run,loc,count,value,frame,prior⟩ :=
    leaf_semantics hash s parameter seed index tree leaf ctx.1 pc counter
  refine ⟨t,run,⟨context_preserved s t parameter seed index tree frame ctx.1,
    stable s t frame ctx.2⟩,loc,count,value,?_⟩
  intro previous before known i
  rw [prior previous (by intro eq;subst previous;omega) i]
  exact known i

/-- All 256 abstract leaf values follow from the discharged local contract. -/
theorem leaves_semantics (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree) (extra : MachineState → Prop)
    (stable : FrameStable extra) (ctx : Context s parameter seed index tree)
    (extraCtx : extra s) (pc : s.pc=0x1d54) (counter : s.getMem 0x43020=0) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 46848 52480 512 768 t ∧
      (Context t parameter seed index tree ∧ extra t) ∧ t.pc=0x1fe8 ∧
      t.getMem 0x43020=256 ∧ ∀ leaf : FtsLeaf,
        Words20 t (0x50000+20*leaf.val) (leafValue hash parameter seed index tree leaf) :=
  SphincsMaskedSignForestLoop.leaves_complete hash _ _
    (leaf_contract hash parameter seed index tree extra stable) s ⟨ctx,extraCtx⟩ pc counter

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLeafSemantics.first_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_frame

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLeafSemantics.secret_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms secret_value

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLeafSemantics.second_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms second_context

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLeafSemantics.second_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms second_query

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLeafSemantics.stored_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stored_value

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLeafSemantics.prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prepare

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLeafSemantics.leaf_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_semantics

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLeafSemantics.context_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms context_preserved

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLeafSemantics.leaf_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_contract

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLeafSemantics.leaves_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaves_semantics

end SigGolfCandidate.SphincsMaskedSignForestLeafSemantics
