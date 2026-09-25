import SigGolfCandidate.SphincsMaskedKeygenRefinement

namespace SigGolfCandidate.SphincsMaskedKeygenPadding
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedChainDomain SphincsMaskedSecretDomain SphincsMaskedLeafRefinement
open SphincsVerifierFtsRootCopy SphincsBridge SphincsSecurity
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Equal-length exact traces in the deterministic VM have the same final state. -/
theorem trace_unique {hash : Hash} {image : Image} {s t u : MachineState}
    {steps cycles calls blocks cycles' calls' blocks' : Nat}
    (left : Trace hash image s steps cycles calls blocks t)
    (right : Trace hash image s steps cycles' calls' blocks' u) : t=u := by
  induction left generalizing u cycles' calls' blocks' with
  | refl state => cases right;rfl
  | ordinary state next final instruction steps cycles calls blocks hf hs tail ih =>
    cases right with
    | ordinary _ next' _ instruction' _ _ _ _ hf' hs' tail' =>
      have instr : instruction=instruction' := Option.some.inj (hf.symm.trans hf')
      subst instruction'
      have states : next=next' := Option.some.inj (hs.symm.trans hs')
      subst next'
      exact ih tail'
    | hash _ _ _ _ _ _ hf' hs' hv' tail' =>
      have instr : instruction=.base .ECALL := Option.some.inj (hf.symm.trans hf')
      simp [instr,ordinaryStep] at hs
  | hash state final steps cycles calls blocks hf hs hv tail ih =>
    cases right with
    | ordinary _ next' _ instruction' _ _ _ _ hf' hs' tail' =>
      have instr : instruction'=.base .ECALL := Option.some.inj (hf'.symm.trans hf)
      simp [instr,ordinaryStep] at hs'
    | hash _ _ _ _ _ _ hf' hs' hv' tail' => exact ih tail'

/-- The unused cache suffix, after the root node and before its authentication tag. -/
def PaddingAddress (a : Nat) : Prop := 0x14074≤a ∧ a<0x2004c ∧ a%4=0

def PaddingFrame (before after : MachineState) : Prop :=
  ∀ a, PaddingAddress a → after.getWord32 (BitVec.ofNat 64 a)=before.getWord32 (BitVec.ofNat 64 a)

theorem padding_low (a : Nat) (padding : PaddingAddress a) :
    (alignToDword (BitVec.ofNat 64 a)).toNat<0x40000 :=
  SphincsMaskedMaskSemantics.low_cell a (by rcases padding with ⟨_,h,_⟩;omega)

theorem nextLeaf_padding (s : MachineState) (leaf : Fin 2048)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    PaddingFrame s (SphincsMaskedLeafLoop.nextLeaf s) := by
  intro a padding
  have low := padding_low a padding
  rw [SphincsMaskedLeafLoop.nextLeaf]
  simp only [MachineState.getWord32,SphincsMaskedLeafCache.finish_frame _ _
    (SphincsMaskedMaskSemantics.low_ne a (by rcases padding with ⟨_,h,_⟩;omega) _ (by decide))]
  change (SphincsVerifierCopy.copyRootState (SphincsMaskedLeafLoop.storeSetup s)).getWord32 _ = _
  rw [SphincsVerifierFtsPriorRoots.copyRoot_word_frame]
  · simp only [MachineState.getWord32,SphincsMaskedLeafCache.storeSetup_frame]
  · intro i
    rw [(SphincsMaskedLeafLoop.storeSetup_registers s leaf.val counter).2]
    have address : BitVec.ofNat 64 (0x88+20*leaf.val)+signExtend12 (4#12*BitVec.ofNat 12 i.val)=
        BitVec.ofNat 64 (0x88+20*leaf.val+4*i.val) := by fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [address]
    rcases padding with ⟨lower,upper,aligned⟩
    exact SphincsVerifierFtsPriorRoots.wordLaneDistinct _ _ (by omega) (by omega) (by omega) aligned (by omega)

theorem leaf_padding (hash : Hash) (s t : MachineState) (leaf : Fin 2048)
    (pc : s.pc=0x111c) (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val)
    (run : Trace hash SphincsMaskedImages.keygen s 41220 44683 417 485 t) : PaddingFrame s t := by
  let endpoints := SphincsMaskedChainLoop.chains hash 52 (SphincsMaskedLeafLoop.entry s)
  have epc := SphincsMaskedLeafLoop.entry_pc s pc
  obtain ⟨chainTrace,_,chainPc⟩ := SphincsMaskedChainLoop.fifty_two_chains hash (SphincsMaskedLeafLoop.entry s)
    epc (SphincsMaskedLeafLoop.entry_counter s)
  have count : endpoints.getMem 0x43020=BitVec.ofNat 64 leaf.val :=
    (SphincsMaskedChainFrame.chains_frame hash _ epc (SphincsMaskedLeafLoop.entry_counter s) 52 (by decide)
      0x43020 (Or.inr rfl)).trans ((SphincsMaskedLeafLoop.entry_leaf s).trans counter)
  obtain ⟨copied,copyTrace,copyPc,copyPos,copyBytes,copyFrame⟩ := payload_copy_full endpoints chainPc
  have copiedCount : copied.getMem 0x43020=BitVec.ofNat 64 leaf.val :=
    (copyFrame _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans count
  let answer := SphincsMaskedLeafLoop.answerState hash copied
  have answerCount := (SphincsMaskedLeafLoop.answer_leaf hash copied).trans copiedCount
  have apc := SphincsMaskedLeafLoop.answer_pc hash copied copyPc
  have whole : Trace hash SphincsMaskedImages.keygen s 41220 44683 417 485 (SphincsMaskedLeafLoop.nextLeaf answer) :=
    (SphincsMaskedLeafLoop.entry_block s pc).trace.trans (chainTrace.trans (copyTrace.trace.trans
      ((SphincsMaskedLeafLoop.hash_trace hash copied copyPc).trans (SphincsMaskedLeafLoop.store_block answer leaf apc answerCount).trace)))
  have equal := trace_unique run whole
  rw [equal]
  intro a padding
  rw [nextLeaf_padding answer leaf answerCount a padding]
  simp only [MachineState.getWord32]
  have low := padding_low a padding
  rw [hash_frame hash copied _ (Or.inl low),copyFrame _ (Or.inl low),
    SphincsMaskedChainFrame.chains_frame hash _ epc (SphincsMaskedLeafLoop.entry_counter s) 52 (by decide) _ (Or.inl low),
    entry_frame _ _ (protected_ne _ (Or.inl low) _ (by decide))]

theorem leaves_padding (hash : Hash) (s t : MachineState) (pc : s.pc=0x111c)
    (counter : s.getMem 0x43020=0) (n : Nat) (bound : n≤2048)
    (run : Trace hash SphincsMaskedImages.keygen s (41220*n) (44683*n) (417*n) (485*n) t) :
    PaddingFrame s t := by
  induction n generalizing t with
  | zero => cases run;intro a h;rfl
  | succ n ih =>
    obtain ⟨mid,first,count,loc⟩ := SphincsMaskedLeafLoop.leaves_trace hash s pc counter n (by omega)
    have npc : mid.pc=0x111c := by rw [loc,if_neg (by omega)]
    let leaf : Fin 2048 := ⟨n,by omega⟩
    obtain ⟨last,lastTrace,lastCount,lastPc⟩ := SphincsMaskedLeafLoop.leaf_trace hash mid leaf npc count
    have whole : Trace hash SphincsMaskedImages.keygen s (41220*(n+1)) (44683*(n+1)) (417*(n+1)) (485*(n+1)) last := by
      simpa only [Nat.mul_succ] using first.trans lastTrace
    rw [trace_unique run whole]
    intro a padding
    rw [leaf_padding hash mid last leaf npc count lastTrace a padding,ih mid (by omega) first a padding]

section Parents
open SphincsMaskedParentLevels SphincsMaskedParentCode

theorem parent_nodes_padding (hash : Hash) (s : MachineState) (target count n : Nat)
    (bound : n≤count) (targetBound : target+20*count≤0x14074) (aligned : target%4=0)
    (controls : ∀ k, k<n →
      (nodes hash k s).getMem 0x43080=BitVec.ofNat 64 target ∧
      (nodes hash k s).getMem 0x43088=BitVec.ofNat 64 k) :
    PaddingFrame s (nodes hash n s) := by
  induction n with
  | zero => intro a h;rfl
  | succ n ih =>
    intro a padding
    obtain ⟨targetAt,nodeAt⟩ := controls n (by omega)
    rcases padding with ⟨lower,upper,align⟩
    rw [nodes,SphincsMaskedParentDomain.next_other_word hash (nodes hash n s) target n a
      targetAt nodeAt (by omega) aligned (by omega) align (by intro j;omega)]
    exact ih (by omega) (fun k hk => controls k (by omega)) a ⟨lower,upper,align⟩

theorem level_padding (hash : Hash) (s t : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (k : Fin 11) (pc : s.pc=0x1610) (ctx : KeyContext s parameter seed) (ctrl : LevelControls s k.val)
    (source : ∀ node, node<width k.val → Words20 s (cacheBase k.val+20*node) (treeValue hash parameter seed k.val node))
    (run : Trace hash SphincsMaskedImages.keygen s (39+124*width (k.val+1))
      (39+139*width (k.val+1)) (width (k.val+1)) (2*width (k.val+1)) t) : PaddingFrame s t := by
  obtain ⟨sourceEnd,targetEnd,targetBound,baseAlign,targetAlign,above,positive,small,half,total⟩ := layout k
  have countTwice : 2*width (k.val+1)=width k.val := by fin_cases k <;> decide
  have entryKey := loop_key s (levelEntry s) parameter seed ctx (by
    intro a ha;apply levelEntry_frame
    intro eq;exact ha (by simp [loopWrites,eq]))
  have entryValues : ∀ j, j<2*width (k.val+1) → Words20 (levelEntry s)
      (cacheBase k.val+20*j) (treeValue hash parameter seed k.val j) := by
    intro j hj i
    simp only [MachineState.getWord32]
    rw [levelEntry_frame _ _ (SphincsMaskedMaskSemantics.low_ne _ (by omega) _ (by decide))]
    exact source j (by omega) i
  have nodeFacts (n : Nat) (hn : n≤width (k.val+1)) := nodes_contract hash (levelEntry s) parameter seed
    (cacheBase k.val) (cacheBase (k.val+1)) (k.val+1) (width (k.val+1))
    (treeValue hash parameter seed k.val) (levelEntry_pc s pc) entryKey (levelEntry_controls s k.val ctrl)
    entryValues (by omega) (by omega) baseAlign targetAlign above positive small n hn
  obtain ⟨nodeTrace,nodeCtrl,nodeKey,nodePc,values,frame⟩ := nodeFacts (width (k.val+1)) (by omega)
  let mid := nodes hash (width (k.val+1)) (levelEntry s)
  have midPc : mid.pc=0x1810 := by simpa using nodePc
  have whole : Trace hash SphincsMaskedImages.keygen s (39+124*width (k.val+1))
      (39+139*width (k.val+1)) (width (k.val+1)) (2*width (k.val+1)) (levelFinish mid) := by
    have trace := (levelEntry_block s pc).trace.trans (nodeTrace.trans (levelFinish_block mid midPc).trace)
    convert trace using 1 <;> omega
  rw [trace_unique run whole]
  have within : cacheBase (k.val+1)+20*width (k.val+1)≤0x14074 := by
    fin_cases k <;> decide
  have frameNodes := parent_nodes_padding hash (levelEntry s) (cacheBase (k.val+1))
    (width (k.val+1)) (width (k.val+1)) (by omega) within targetAlign (by
      intro n hn
      have ctl := (nodeFacts n (by omega)).2.1
      exact ⟨ctl.target,ctl.node⟩)
  intro a padding
  simp only [MachineState.getWord32]
  rw [levelFinish_frame _ _ (low_outside _ (padding_low a padding))]
  change mid.getWord32 _ = _
  rw [frameNodes a padding]
  simp only [MachineState.getWord32]
  rw [levelEntry_frame _ _ (SphincsMaskedMaskSemantics.low_ne _ (by rcases padding with ⟨_,h,_⟩;omega) _ (by decide))]

theorem levels_padding (hash : Hash) (s t : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (pc : s.pc=0x1610) (ctx : KeyContext s parameter seed) (ctrl : LevelControls s 0)
    (leaves : ∀ node, node<width 0 → Words20 s (cacheBase 0+20*node) (treeValue hash parameter seed 0 node))
    (n : Nat) (bound : n≤11)
    (run : Trace hash SphincsMaskedImages.keygen s (39*n+124*totalNodes n) (39*n+139*totalNodes n)
      (totalNodes n) (2*totalNodes n) t) : PaddingFrame s t := by
  induction n generalizing t with
  | zero => cases run;intro a h;rfl
  | succ n ih =>
    obtain ⟨mid,first,midCtrl,midKey,midPc,old⟩ := levels_contract hash s parameter seed pc ctx ctrl leaves n (by omega)
    have npc : mid.pc=0x1610 := by rw [midPc,if_neg (by omega)]
    let k : Fin 11 := ⟨n,by omega⟩
    obtain ⟨last,lastTrace,lastCtrl,lastKey,lastPc,new,frame⟩ :=
      level_contract hash mid parameter seed k npc midKey midCtrl (old n (by omega))
    have total : totalNodes (n+1)=totalNodes n+width (n+1) := (layout k).2.2.2.2.2.2.2.2.2
    have whole : Trace hash SphincsMaskedImages.keygen s (39*(n+1)+124*totalNodes (n+1))
        (39*(n+1)+139*totalNodes (n+1)) (totalNodes (n+1)) (2*totalNodes (n+1)) last := by
      have trace := first.trans lastTrace
      dsimp [k] at trace
      rw [total]
      convert trace using 1 <;> omega
    rw [trace_unique run whole]
    intro a padding
    rw [level_padding hash mid last parameter seed k npc midKey midCtrl (old n (by omega)) lastTrace a padding,
      ih mid (by omega) first a padding]

theorem parents_padding (hash : Hash) (s t : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (pc : s.pc=0x15cc) (ctx : KeyContext s parameter seed)
    (leaves : ∀ leaf : LeafIndex, Words20 s (0x88+20*leaf.val) (leafValue hash parameter seed leaf))
    (run : Trace hash SphincsMaskedImages.keygen s 254274 284979 2047 4094 t) : PaddingFrame s t := by
  have key := loop_key s (init s) parameter seed ctx (init_frame s)
  have initial : ∀ node, node<width 0 → Words20 (init s) (cacheBase 0+20*node)
      (treeValue hash parameter seed 0 node) := by
    intro node hn i
    change node<2048 at hn
    let leaf : LeafIndex := ⟨node,hn⟩
    have value := leaves leaf i
    rw [leafValue_treeValue] at value
    change (init s).getWord32 (BitVec.ofNat 64 (0x88+20*node+4*i.val)) = _
    simp only [MachineState.getWord32]
    rw [init_frame _ _ (low_outside _ (SphincsMaskedMaskSemantics.low_cell _ (by omega)))]
    exact value
  obtain ⟨last,lastTrace,lastCtrl,lastKey,lastPc,values⟩ := levels_contract hash (init s) parameter seed
    (init_pc s pc) key (init_controls s) initial 11 (by decide)
  have whole : Trace hash SphincsMaskedImages.keygen s 254274 284979 2047 4094 last :=
    (init_block s pc).trace.trans lastTrace
  rw [trace_unique run whole]
  intro a padding
  rw [levels_padding hash (init s) last parameter seed (init_pc s pc) key (init_controls s) initial 11
    (by decide) lastTrace a padding]
  simp only [MachineState.getWord32]
  rw [init_frame _ _ (low_outside _ (padding_low a padding))]

end Parents

theorem firstHash_low_frame (s : MachineState) (a : Word) (low : a.toNat<0x40000) :
    (firstHashState s).getMem a=s.getMem a := by
  have ne (b : Word) (high : 0x40000≤b.toNat) : a≠b := by intro eq;rw [eq] at low;omega
  simp [firstHashState,runSchedule,prefixSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,ne]

theorem afterHash_low_frame (hash : Hash) (s : MachineState) (seed : MasterSeed) (a : Word) (low : a.toNat<0x40000) :
    (afterHashState hash s seed).getMem a=s.getMem a := by
  have ne (b : Word) (high : 0x40000≤b.toNat) : a≠b := by intro eq;rw [eq] at low;omega
  have dst := (firstHash_registers s).2.2.1
  simp [afterHashState,writeHash,dst,MachineState.writeWords,ne,firstHash_low_frame s a low]

theorem ready_frame (s : MachineState) (a : Word) (lower : 0x88≤a.toNat) (upper : a.toNat<0x40000) :
    (SphincsMaskedKeygenRefinement.ready s).getMem a=s.getMem a := by
  have ne (b : Word) (outside : b.toNat<0x88 ∨ 0x40000≤b.toNat) : a≠b := by
    intro eq;rw [eq] at lower upper;rcases outside with h|h <;> omega
  simp [SphincsMaskedKeygenRefinement.ready,runSchedule,SphincsMaskedKeygenRefinement.readySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,ne]

def ZeroPadding (s : MachineState) : Prop := ∀ a, PaddingAddress a → s.getWord32 (BitVec.ofNat 64 a)=0

theorem leavesEntry_zero (hash : Hash) (seed : MasterSeed) :
    ZeroPadding (SphincsMaskedKeygenRefinement.leavesEntry hash seed) := by
  intro a padding
  have lower := SphincsMaskedKeygenCommitment.cache_cell_lower a (by rcases padding with ⟨h,_,_⟩;omega)
    (by rcases padding with ⟨_,h,_⟩;omega)
  have upper := padding_low a padding
  simp only [SphincsMaskedKeygenRefinement.leavesEntry,MachineState.getWord32]
  rw [ready_frame _ _ lower upper,afterHash_low_frame _ _ _ _ upper]
  simp only [entryState,MachineState.getMem_setReg]
  rw [Memory.write_preserves _ 0x20 (SigGolf.bytes (n:=32) seed) _ (by simp [SigGolf.bytes]) (Or.inr (by simp [SigGolf.bytes];omega))]
  simp [extractWord32,MachineState.getMem]

theorem keygen_executes_zero (hash : Hash) (seed : MasterSeed) :
    ∃ final, Executes hash SphincsMaskedImages.keygen (entryState seed) 85168809
      ⟨.success,final,92369576,860161,1007616⟩ ∧ ZeroPadding final := by
  let parameter := SphincsMaskedKeygenRefinement.parameter hash seed
  obtain ⟨firstTrace,pc,count⟩ := SphincsMaskedKeygenRefinement.leavesEntry_trace hash seed
  obtain ⟨leaves,leafTrace,leafCount,leafPc,leafKey,leafValues⟩ := leaves_contract hash
    (SphincsMaskedKeygenRefinement.leavesEntry hash seed) parameter seed
    (SphincsMaskedKeygenRefinement.leavesEntry_context hash seed) pc count 2048 (by decide)
  have leafLocation : leaves.pc=0x15cc := by simpa using leafPc
  obtain ⟨parents,parentTrace,parentPc,parentBase,parentKey,parentValues⟩ :=
    SphincsMaskedParentLevels.parents_contract hash leaves parameter seed leafLocation leafKey
      (fun leaf => leafValues leaf leaf.isLt)
  have rootValue : Words20 parents 0x14060 (SphincsMaskedKeygenRefinement.root hash seed) :=
    parentValues 11 (by decide) 0 (by decide)
  obtain ⟨committed,commitTrace,commitPc,commitKey,commitRoot,commitPublic,commitFrame⟩ :=
    SphincsMaskedKeygenCommitment.commitment_contract hash parents parameter
      (SphincsMaskedKeygenRefinement.root hash seed) seed parentPc parentBase parentKey rootValue
  let final := SphincsMaskedKeygenTail.final hash committed
  have done := SphincsMaskedKeygenTail.tail_executes hash committed commitPc
  have trace := firstTrace.trans (leafTrace.trans (parentTrace.trans commitTrace))
  refine ⟨final,?_,?_⟩
  · simpa [Execution.charge] using trace.then_executes done
  intro a padding
  rcases padding with ⟨lower,upper,aligned⟩
  change (SphincsMaskedKeygenTail.final hash committed).getWord32 _=0
  rw [SphincsMaskedMaskSemantics.final_protected_word hash committed commitPc a upper aligned
    (Or.inr lower) (Or.inr (by omega)),commitFrame a (by omega) (by omega) aligned,
    parents_padding hash leaves parents parameter seed leafLocation leafKey
      (fun leaf => leafValues leaf leaf.isLt) parentTrace a ⟨lower,upper,aligned⟩,
    leaves_padding hash (SphincsMaskedKeygenRefinement.leavesEntry hash seed) leaves pc count 2048
      (by decide) leafTrace a ⟨lower,upper,aligned⟩]
  exact leavesEntry_zero hash seed a ⟨lower,upper,aligned⟩

def CacheZeroPadding (cache : SigGolf.Cache) : Prop :=
  ∀ (i : Nat), 81940 ≤ i → i < 131052 → cache.extractLsb' (8*i) 8 = 0

theorem read_zeroPadding (s : MachineState) (zero : ZeroPadding s) :
    CacheZeroPadding (readBuffer s 0x60 CACHE_BYTES) := by
  intro i lower upper
  rw [SphincsReadBufferBytes.readBuffer_byte s 0x60 CACHE_BYTES i (by dsimp [CACHE_BYTES];omega)]
  have byte := SphincsVerifierFtsGenericBytes.variableWord_byte s (0x60+4*(i/4))
    (by omega) (by omega) 0 ⟨i%4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at byte
  rw [show 0x60+4*(i/4)+i%4=0x60+i by omega] at byte
  rw [byte,zero _ ⟨by omega,by omega,by omega⟩]
  simp

/-- The actual returned cache satisfies the complete semantic fields and canonical zero padding. -/
theorem keygen_runWith_canonical (submission : Submission) (hash : Hash) (seed : MasterSeed)
    (image : submission.image .keygen=SphincsMaskedImages.keygen)
    (valid : (submission.image .keygen).Valid submission.sizes submission.layout)
    (secretAddress : submission.layout.secretKey=0x20)
    (publicAddress : submission.layout.publicKey=0x40) (cacheAddress : submission.layout.cache=0x60) :
    ∃ cache : SigGolf.Cache,
      submission.runWith hash .keygen seed=⟨some (SphincsMaskedKeygenRefinement.publicKey hash seed,cache),true,92369576,860161,1007616⟩ ∧
      SphincsMaskedKeygenRefinement.CacheSemantics hash seed cache ∧ CacheZeroPadding cache := by
  obtain ⟨cache,value,sem⟩ := SphincsMaskedKeygenRefinement.keygen_runWith submission hash seed image valid secretAddress publicAddress cacheAddress
  obtain ⟨final,run,zero⟩ := keygen_executes_zero hash seed
  have loaded := entry_loaded submission seed image valid secretAddress
  have exactRun : Executes hash (submission.image .keygen) (entryState seed) 85168809
      ⟨.success,final,92369576,860161,1007616⟩ := by rw [image];exact run
  have result := runWith_of_executes submission hash .keygen seed (entryState seed) 85168809
    ⟨.success,final,92369576,860161,1007616⟩ loaded exactRun (by decide)
  have output := congrArg RunResult.value (value.symm.trans result)
  simp only [readOutput,publicAddress,cacheAddress,if_true] at output
  have same := congrArg Prod.snd (Option.some.inj output)
  change cache=readBuffer final 0x60 CACHE_BYTES at same
  refine ⟨cache,value,sem,?_⟩
  rw [same]
  exact read_zeroPadding final zero

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenPadding.leaves_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaves_padding

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenPadding.parents_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parents_padding

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenPadding.leavesEntry_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leavesEntry_zero

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenPadding.keygen_runWith_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygen_runWith_canonical

end SigGolfCandidate.SphincsMaskedKeygenPadding
