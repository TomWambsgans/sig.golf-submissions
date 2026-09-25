import SigGolfCandidate.SphincsMaskedSignForestLeafSemantics

namespace SigGolfCandidate.SphincsMaskedSignForestParentSemantics
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsSecurity SphincsBridge SphincsMaskedChainDomain
open SphincsMaskedKeygenPrefix SphincsMaskedSignForestParents
open SphincsVerifierFtsGenericBytes
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def QueryContext (s : MachineState) (parameter left right : Digest)
    (index : Index) (tree : FtsTree) (level node : Nat) : Prop :=
  s.getMem 0x43000=BitVec.ofNat 64 tree.val ∧
  s.getMem 0x43008=BitVec.ofNat 64 index.val ∧
  s.getMem 0x43048=BitVec.ofNat 64 level ∧
  s.getMem 0x43088=BitVec.ofNat 64 node ∧
  Words20 s 0x74 parameter ∧ Words20 s 0x40028 left ∧ Words20 s 0x4003c right

def payload (parameter left right : Digest) (index : Index) (tree : FtsTree)
    (level node : Nat) : List Byte :=
  (tweakableHashInput parameter (.ftsNode index tree level node)
    (Concrete.nodePayload left right)).map UInt8.toBitVec

theorem payload_length (parameter left right : Digest) (index : Index) (tree : FtsTree)
    (level node : Nat) : (payload parameter left right index tree level node).length=80 := by
  simp [payload,tweakableHashInput,tweakBytes,hashDomainFields,tweakFields,fieldBytes,bytesLE,Concrete.nodePayload]

theorem prepared_byte (s : MachineState) (i : Fin 80) :
    (hashPrepare s).getByte (BitVec.ofNat 64 (0x40000+i.val)) =
      (queryWord s ⟨i.val/4,by omega⟩).extractLsb' (8*(i.val%4)) 8 := by
  have h := variableWord_byte (hashPrepare s) (0x40000+4*(i.val/4)) (by omega) (by omega)
    0 ⟨i.val%4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  rw [show 0x40000+4*(i.val/4)+i.val%4=0x40000+i.val by omega] at h
  rw [h,prepare_words s ⟨i.val/4,by omega⟩]

theorem context_byte (s : MachineState) (parameter left right : Digest)
    (index : Index) (tree : FtsTree) (level node : Nat)
    (ctx : QueryContext s parameter left right index tree level node) (i : Fin 80) :
    (queryWord s ⟨i.val/4,by omega⟩).extractLsb' (8*(i.val%4)) 8 =
      (payload parameter left right index tree level node)[i.val]'(by rw [payload_length];exact i.isLt) := by
  obtain ⟨htree,hindex,hlevel,hnode,par,hl,hr⟩ := ctx
  have p0 := par 0
  have p1 := par 1
  have p2 := par 2
  have p3 := par 3
  have p4 := par 4
  have l0 := hl 0
  have l1 := hl 1
  have l2 := hl 2
  have l3 := hl 3
  have l4 := hl 4
  have r0 := hr 0
  have r1 := hr 1
  have r2 := hr 2
  have r3 := hr 3
  have r4 := hr 4
  norm_num at p0 p1 p2 p3 p4 l0 l1 l2 l3 l4 r0 r1 r2 r3 r4
  have treeSmall : tree.val<2^8 := by have h:=tree.isLt;norm_num [ftsTrees] at h ⊢;omega
  have treeZext : (BitVec.ofNat 8 tree.val).setWidth 64=BitVec.ofNat 64 tree.val :=
    BitVec.setWidth_ofNat_of_le_of_lt (by omega) treeSmall
  rw [← treeZext] at htree
  have htree' : s.getMem 0x43000#64=(BitVec.ofNat 8 tree.val).setWidth 64 := by simpa using htree
  have hindex' : s.getMem 0x43008#64=BitVec.ofNat 64 index.val := by simpa using hindex
  have hlevel' : s.getMem 0x43048#64=BitVec.ofNat 64 level := by simpa using hlevel
  have hnode' : s.getMem 0x43088#64=BitVec.ofNat 64 node := by simpa using hnode
  by_cases hi : i.val<20
  · fin_cases i <;> simp [queryWord,htree,hindex,hlevel,hnode,p0,p1,p2,p3,p4,l0,l1,l2,l3,l4,r0,r1,r2,r3,r4,payload,tweakableHashInput,tweakBytes,hashDomainFields,tweakFields,fieldBytes,bytesLE,protocolDomainSep,extractWord32,Concrete.nodePayload] at hi ⊢
    all_goals first
      | (rw [hindex'];exact BitVec.extractLsb'_setWidth_of_le (by decide))
      | (rw [hindex'];simp [BitVec.setWidth_ushiftRight_eq_extractLsb,SphincsMaskedSignForestDomain.nested_extract])
      | (rw [hlevel'];simp)
      | (rw [hnode'];simp)
      | (rw [htree'];fin_cases tree <;> decide)
  · fin_cases i <;> simp [queryWord,htree,hindex,hlevel,hnode,p0,p1,p2,p3,p4,l0,l1,l2,l3,l4,r0,r1,r2,r3,r4,payload,tweakableHashInput,tweakBytes,hashDomainFields,tweakFields,fieldBytes,bytesLE,protocolDomainSep,extractWord32,Concrete.nodePayload] at hi ⊢
    all_goals exact SphincsMaskedSignForestDomain.nested_extract _ _ _ _ _ (by decide)

theorem query_eq (s : MachineState) (parameter left right : Digest)
    (index : Index) (tree : FtsTree) (level node : Nat)
    (ctx : QueryContext s parameter left right index tree level node) :
    hashInput (hashPrepare s)=toQuery (tweakableHashInput parameter (.ftsNode index tree level node)
      (Concrete.nodePayload left right)) := by
  apply Serialization.hashInput_of_list (hashPrepare s) 0x40000 (payload parameter left right index tree level node)
  · exact (hashPrepare_registers s).1
  · rw [payload_length,(hashPrepare_registers s).2.1];rfl
  · intro i hi
    have bound : i<80 := by simpa only [payload_length] using hi
    rw [prepared_byte s ⟨i,bound⟩]
    exact context_byte s parameter left right index tree level node ctx ⟨i,bound⟩


abbrev Context := SphincsMaskedSignForestLeafSemantics.Context

theorem children_context (s : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) (left right : Digest) (k : Fin 8) (node : Nat)
    (bound : node<width (k.val+1)) (ctx : Context s parameter seed index tree)
    (ctrl : Controls s k.val node)
    (hl : Words20 s (cacheBase k.val+20*(2*node)) left)
    (hr : Words20 s (cacheBase k.val+20*(2*node+1)) right) :
    QueryContext (children s) parameter left right index tree (k.val+1) node := by
  obtain ⟨ht,hi,par,key⟩ := ctx
  obtain ⟨sourceEnd,targetEnd,targetBound,baseAlign,targetAlign,baseAbove,targetAbove,positive,small,twice,half,total⟩ := layout k
  have sourceBound : cacheBase k.val+40*node+40≤0x60000 := by omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [children_frame _ _ (by decide)];exact ht
  · rw [children_frame _ _ (by decide)];exact hi
  · rw [children_frame _ _ (by decide)];exact ctrl.level
  · rw [children_frame _ _ (by decide)];exact ctrl.node
  · intro i
    have eq : (children s).getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) := by
      simp only [MachineState.getWord32]
      rw [children_frame _ _ (by fin_cases i <;> decide)]
    exact eq.trans (par i)
  · intro i
    rw [children_left s _ node ctrl.base ctrl.node baseAbove sourceBound baseAlign i]
    convert hl i using 1 <;> congr 2 <;> omega
  · intro i
    rw [children_right s _ node ctrl.base ctrl.node baseAbove sourceBound baseAlign i]
    convert hr i using 1 <;> congr 2 <;> omega

theorem context_node_stable (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) : NodeStable (fun s => Context s parameter seed index tree) := by
  intro s t ctx frame
  obtain ⟨ht,hi,par,key⟩ := ctx
  refine ⟨(frame _ (by decide) (by decide) (by decide)).trans ht,
    (frame _ (by decide) (by decide) (by decide)).trans hi,?_,?_⟩
  · intro i
    have eq : t.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) := by
      simp only [MachineState.getWord32]
      rw [frame _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact eq.trans (par i)
  · intro i
    have eq : t.getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) := by
      simp only [MachineState.getWord32]
      rw [frame _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact eq.trans (key i)

theorem context_loop_stable (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) : LoopStable (fun s => Context s parameter seed index tree) := by
  intro s t ctx frame
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

/-- Actual tag-10 queries discharge every node's semantic contract. -/
theorem node_contract (hash : Hash) (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) (extra : MachineState → Prop)
    (stable : NodeStable extra) :
    NodeContract hash (fun s => Context s parameter seed index tree ∧ extra s)
      (Completeness.ftsNodeValue (adaptOracle hash) parameter index tree seed) := by
  apply node_contract_of_query
  · intro s t ctx frame
    exact ⟨context_node_stable parameter seed index tree s t ctx.1 frame,stable s t ctx.2 frame⟩
  · intro k node bound s ctx ctrl left right
    have query := query_eq (children s) parameter _ _ index tree (k.val+1) node
      (children_context s parameter seed index tree _ _ k node bound ctx.1 ctrl left right)
    rw [query,Completeness.ftsNodeValue_succ]
    rfl

/-- All 255 parent nodes agree with the abstract seeded tree. -/
theorem parents_semantics (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree) (extra : MachineState → Prop)
    (stableNode : NodeStable extra) (stableLoop : LoopStable extra)
    (ctx : Context s parameter seed index tree) (extraCtx : extra s) (pc : s.pc=0x1fe8)
    (leaves : ∀ leaf : FtsLeaf, Words20 s (0x50000+20*leaf.val)
      (SphincsMaskedSignForestLeafSemantics.leafValue hash parameter seed index tree leaf)) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 32205 36030 255 510 t ∧
      (Context t parameter seed index tree ∧ extra t) ∧ t.pc=0x22c0 ∧
      t.getMem 0x43068=0x527d8 ∧
      TreeValues (Completeness.ftsNodeValue (adaptOracle hash) parameter index tree seed) t 8 ∧
      Words20 t 0x527d8 (Completeness.ftsNodeValue (adaptOracle hash) parameter index tree seed 8 0) := by
  have stable : LoopStable (fun s => Context s parameter seed index tree ∧ extra s) := by
    intro s t ctx frame
    exact ⟨context_loop_stable parameter seed index tree s t ctx.1 frame,stableLoop s t ctx.2 frame⟩
  apply parents_complete hash _ stable _ (node_contract hash parameter seed index tree extra stableNode) s pc ⟨ctx,extraCtx⟩
  intro leaf
  rw [← SphincsMaskedSignForestLeafSemantics.leafValue_eq_node hash parameter seed index tree leaf]
  exact leaves leaf

/-- A complete leaf/parent body computes its abstract root with no assumed
    query or execution contracts. Optional invariants are memory-frame predicates. -/
theorem body_semantics (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree) (extra : MachineState → Prop)
    (stableLeaf : SphincsMaskedSignForestLeafSemantics.FrameStable extra)
    (stableNode : NodeStable extra) (stableLoop : LoopStable extra)
    (ctx : Context s parameter seed index tree) (extraCtx : extra s)
    (pc : s.pc=0x1d54) (counter : s.getMem 0x43020=0) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 79053 88510 767 1278 t ∧
      (Context t parameter seed index tree ∧ extra t) ∧ t.pc=0x22c0 ∧
      t.getMem 0x43068=0x527d8 ∧
      TreeValues (Completeness.ftsNodeValue (adaptOracle hash) parameter index tree seed) t 8 ∧
      Words20 t 0x527d8 (Completeness.ftsNodeValue (adaptOracle hash) parameter index tree seed 8 0) := by
  obtain ⟨mid,first,midCtx,midPc,_,leaves⟩ :=
    SphincsMaskedSignForestLeafSemantics.leaves_semantics hash s parameter seed index tree extra
      stableLeaf ctx extraCtx pc counter
  obtain ⟨t,last,done,loc,base,values,root⟩ := parents_semantics hash mid parameter seed index tree extra
    stableNode stableLoop midCtx.1 midCtx.2 midPc leaves
  exact ⟨t,first.trans last,done,loc,base,values,root⟩

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParentSemantics.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_eq

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParentSemantics.children_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms children_context

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParentSemantics.node_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms node_contract

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParentSemantics.parents_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parents_semantics

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestParentSemantics.body_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms body_semantics

end SigGolfCandidate.SphincsMaskedSignForestParentSemantics
