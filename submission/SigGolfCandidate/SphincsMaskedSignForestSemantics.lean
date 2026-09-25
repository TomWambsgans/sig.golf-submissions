import SigGolfCandidate.SphincsMaskedSignForestParentSemantics

namespace SigGolfCandidate.SphincsMaskedSignForestSemantics
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsSecurity SphincsBridge SphincsMaskedChainDomain
open SphincsMaskedKeygenPrefix SphincsMaskedSignForestTail
open SphincsVerifierFtsRootCopy SphincsVerifierCopy SphincsVerifierCopyMemory
open SphincsVerifierMessageCopy SphincsVerifierFtsCopyAccess SphincsVerifierFtsPriorRoots
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev signatureBase (n : Nat) := 0x2009c+180*n

abbrev WidePathRetained (a : Word) : Prop :=
  (a.toNat<0x20000 ∨ 0x40000≤a.toNat) ∧ a∉pathWrites

theorem pathInit_wide (s : MachineState) (a : Word) (ha : a∉pathWrites) :
    (pathInit s).getMem a=s.getMem a := by
  simp only [pathWrites,List.mem_cons,List.not_mem_nil,not_or] at ha
  obtain ⟨h0,h1,h2,h3,h4⟩ := ha
  simp [pathInit,runSchedule,pathInitSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3,h4]

theorem pathNext_wide (s : MachineState) (level bit pointer : Nat)
    (ctrl : PathControls s level bit pointer) (lower : 0x20000≤pointer)
    (bounded : pointer+20≤0x40000) (a : Word) (ha : WidePathRetained a) :
    (pathNext s).getMem a=s.getMem a := by
  rw [pathNext,pathFinish_memory _ a ha.2]
  have regs := pathSetup_registers s level bit pointer ctrl
  rw [pathCopied,copy_memory_frame _ pointer 0x20000 0x40000 regs.2 (by decide)
    lower bounded (by decide) a ha.1]
  simp [pathSetup,runSchedule,pathSetupSchedule,execInstrBr]

/-- Strengthened path induction preserves the key/parameter region as well as roots. -/
theorem paths_wide (s : MachineState) (selected : Fin 256) (pointer : Nat)
    (pc : s.pc=0x24b4) (ctrl : PathControls s 0 selected.val pointer)
    (lower : 0x20000≤pointer) (pointerBound : pointer+160≤0x40000) (aligned : pointer%4=0)
    (n : Nat) (bound : n≤8) :
    ∃ t, OrdinarySteps SphincsMaskedImages.sign s (70*n) t ∧
      PathControls t n (selected.val/2^n) (pointer+20*n) ∧
      t.pc=(if n=8 then 0x25cc else 0x24b4) ∧
      ∀ a, WidePathRetained a → t.getMem a=s.getMem a := by
  induction n with
  | zero => exact ⟨s,OrdinarySteps.refl _,by simpa using ctrl,pc,by intro _ _;rfl⟩
  | succ n ih =>
    obtain ⟨mid,first,midCtrl,midPc,frame⟩ := ih (by omega)
    have here : mid.pc=0x24b4 := by simpa only [if_neg (show n≠8 by omega)] using midPc
    let level : Fin 8 := ⟨n,by omega⟩
    obtain ⟨step,done,loc⟩ := path_step mid level (selected.val/2^n) (pointer+20*n)
      here midCtrl (divided_selector_bound selected level) (by omega) (by omega)
    refine ⟨pathNext mid,?_,?_,loc,?_⟩
    · simpa only [Nat.mul_add,Nat.mul_one,Nat.add_comm] using first.append step
    · convert done using 1
      · simp [level,Nat.pow_succ,Nat.div_div_eq_div_mul]
      · omega
    · intro a ha
      rw [pathNext_wide mid n (selected.val/2^n) (pointer+20*n) midCtrl (by omega) (by omega) a ha,frame a ha]

theorem signatureSaved_wide (s : MachineState) (pointer : Nat)
    (hp : s.getMem 0x430a0=BitVec.ofNat 64 pointer) (lower : 0x20000≤pointer)
    (bounded : pointer+20≤0x40000) (a : Word)
    (outside : a.toNat<0x20000 ∨ 0x40000≤a.toNat) (ne : a≠0x430a0#64) :
    (signatureSaved s).getMem a=s.getMem a := by
  rw [signatureSaved,signatureAdvance_frame _ a ne]
  have regs := signatureSetup_registers s pointer hp
  rw [signatureCopied,copy_memory_frame _ pointer 0x20000 0x40000 regs.2 (by decide)
    lower bounded (by decide) a outside]
  simp [signatureSetup,runSchedule,signatureSetupSchedule,execInstrBr]

/-- Everything after root storage preserves the low key region, all root slots,
    the message index, and the digest-selector bytes. -/
abbrev TailRetained (a : Word) : Prop := a.toNat<0x20000 ∨
  (0x44100≤a.toNat ∧ a.toNat<0x44300) ∨ ForestRetained a

theorem tail_retained_values (a : Word) (ha : TailRetained a) :
    a.toNat<0x20000 ∨ (0x44100≤a.toNat ∧ a.toNat<0x44300) ∨
      a.toNat=0x43078 ∨ (0x44800≤a.toNat ∧ a.toNat<0x44818) := by
  rcases ha with low|roots|eq|sels
  · exact Or.inl low
  · exact Or.inr (Or.inl roots)
  · rw [eq];exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr sels))

theorem tail_path (a : Word) (ha : TailRetained a) : WidePathRetained a := by
  have h := tail_retained_values a ha
  refine ⟨by omega,?_⟩
  simp only [pathWrites,List.mem_cons,List.not_mem_nil,or_false]
  intro eq
  rcases eq with eq|eq|eq|eq|eq <;>
    have val:=congrArg BitVec.toNat eq <;> norm_num at val <;> omega

theorem tail_secret (a : Word) (ha : TailRetained a) : SecretRetained a := by
  have h := tail_retained_values a ha
  change a.toNat<0x40000 ∨ 0x43020≤a.toNat
  omega

/-- Root-preserving remainder of the tree, beginning after the root store. -/
theorem after_root (hash : Hash) (s : MachineState) (tree : Fin 24) (selected : Fin 256)
    (pc : s.pc=0x2318) (counter : s.getMem 0x43040=BitVec.ofNat 64 tree.val)
    (pointer : s.getMem 0x430a0=BitVec.ofNat 64 (signatureBase tree.val))
    (selector : s.getMem 0x430a8=BitVec.ofNat 64 selected.val) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 693 708 1 2 t ∧
      t.pc=(if tree.val+1=24 then 0x25fc else 0x1cec) ∧
      t.getMem 0x43040=BitVec.ofNat 64 (tree.val+1) ∧
      t.getMem 0x430a0=BitVec.ofNat 64 (signatureBase (tree.val+1)) ∧
      ∀ a, TailRetained a → t.getMem a=s.getMem a := by
  obtain ⟨hashed,hashTrace,hashPc,hashFrame⟩ := secret_execution hash s pc
  have hp := (hashFrame 0x430a0 (by decide)).trans pointer
  have hc := (hashFrame 0x43040 (by decide)).trans counter
  have hs := (hashFrame 0x430a8 (by decide)).trans selector
  have ptrBound : signatureBase tree.val+20≤0x40000 := by dsimp [signatureBase];omega
  have ptrLower : 0x20000≤signatureBase tree.val := by dsimp [signatureBase];omega
  obtain ⟨storeTrace,storePc,storePointer⟩ := signature_saved hashed (signatureBase tree.val) hashPc hp ptrBound (by dsimp [signatureBase];omega)
  have storedSelector : (signatureSaved hashed).getMem 0x430a8=BitVec.ofNat 64 selected.val :=
    (signatureSaved_frame hashed _ hp ptrBound _ (by decide) (by decide)).trans hs
  have storedCounter : (signatureSaved hashed).getMem 0x43040=BitVec.ofNat 64 tree.val :=
    (signatureSaved_frame hashed _ hp ptrBound _ (by decide) (by decide)).trans hc
  have initial := pathInit_controls (signatureSaved hashed) selected.val (signatureBase tree.val+20) storedSelector storePointer
  obtain ⟨pathed,pathTrace,pathCtrl,pathPc,pathFrame⟩ := paths_wide
    (pathInit (signatureSaved hashed)) selected (signatureBase tree.val+20)
    (pathInit_pc _ storePc) initial (by omega) (by dsimp [signatureBase];omega)
    (by dsimp [signatureBase];omega) 8 (by decide)
  have here : pathed.pc=0x25cc := by simpa using pathPc
  have pathCounter : pathed.getMem 0x43040=BitVec.ofNat 64 tree.val :=
    (pathFrame _ (by decide)).trans ((pathInit_frame _ _ (by decide)).trans storedCounter)
  refine ⟨treeFinish pathed,?_,treeFinish_pc pathed tree here pathCounter,?_,?_,?_⟩
  · exact hashTrace.trans (storeTrace.trace.trans ((pathInit_block _ storePc).trace.trans
      (pathTrace.trace.trans (treeFinish_block pathed here).trace)))
  · rw [treeFinish_counter,pathCounter];exact (BitVec.ofNat_add _ _).symm
  · rw [treeFinish_frame _ _ (by decide),pathCtrl.pointer]
    congr 1 <;> dsimp [signatureBase] <;> omega
  · intro a ha
    have h:=tail_retained_values a ha
    have neTree : a≠0x43040#64 := by intro eq;have val:=congrArg BitVec.toNat eq;norm_num at val;omega
    have nePtr : a≠0x430a0#64 := by intro eq;have val:=congrArg BitVec.toNat eq;norm_num at val;omega
    have retained := tail_path a ha
    rw [treeFinish_frame _ a neTree,pathFrame a retained,pathInit_wide _ a retained.2,
      signatureSaved_wide hashed _ hp ptrLower ptrBound a retained.1 nePtr,hashFrame a (tail_secret a ha)]


/-- The root store preserves every other root at word granularity. -/
theorem root_saved_other (s : MachineState) (tree prior : Fin 24) (ne : tree≠prior)
    (base : s.getMem 0x43068=0x527d8) (counter : s.getMem 0x43040=BitVec.ofNat 64 tree.val)
    (i : Fin 5) :
    (rootSaved s).getWord32 (BitVec.ofNat 64 (0x44100+20*prior.val+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x44100+20*prior.val+4*i.val)) := by
  have regs := rootSetup_registers s tree base counter
  rw [rootSaved,copyRoot_word_frame]
  · simp [MachineState.getWord32,rootSetup,runSchedule,rootSetupSchedule,execInstrBr]
  · intro j
    rw [regs.2]
    have addr : BitVec.ofNat 64 (0x44100+20*tree.val)+signExtend12 (4#12*BitVec.ofNat 12 j.val)=
        BitVec.ofNat 64 (0x44100+20*tree.val+4*j.val) := by
      fin_cases j <;> simp [signExtend12,←BitVec.ofNat_add]
    rw [addr]
    have different : tree.val≠prior.val := fun eq => ne (Fin.ext eq)
    exact wordLaneDistinct _ _ (by omega) (by omega) (by omega) (by omega) (by omega)

abbrev rootValue (hash : Hash) (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) : Digest :=
  Completeness.ftsNodeValue (adaptOracle hash) parameter index tree seed 8 0

def Roots (hash : Hash) (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (n : Nat) (s : MachineState) : Prop :=
  ∀ tree : FtsTree, tree.val<n → Words20 s (0x44100+20*tree.val)
    (rootValue hash parameter seed index tree)

theorem root_cell (tree : FtsTree) (i : Fin 5) :
    0x44100≤(alignToDword (BitVec.ofNat 64 (0x44100+20*tree.val+4*i.val))).toNat ∧
    (alignToDword (BitVec.ofNat 64 (0x44100+20*tree.val+4*i.val))).toNat<0x44300 :=
  cell_bounds _ 0x44100 0x44300 (by decide) (by omega) (by have h:=tree.isLt;norm_num [ftsTrees] at h;omega) (by decide)

def Context (s : MachineState) (parameter : PublicParameter) (seed : MasterSeed) (index : Index) : Prop :=
  Words20 s 0x74 parameter ∧ SphincsMaskedSecretDomain.Words32 s seed ∧
    s.getMem 0x43078=BitVec.ofNat 64 index.val

theorem context_frame (s t : MachineState) (parameter : PublicParameter) (seed : MasterSeed) (index : Index)
    (frame : ∀ a, TailRetained a → t.getMem a=s.getMem a)
    (ctx : Context s parameter seed index) : Context t parameter seed index := by
  obtain ⟨par,key,msg⟩ := ctx
  refine ⟨?_,?_,(frame _ (by decide)).trans msg⟩
  · intro i
    have eq : t.getWord32 (BitVec.ofNat 64 (0x74+4*i.val))=s.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) := by
      simp only [MachineState.getWord32];rw [frame _ (by fin_cases i <;> decide)]
    exact eq.trans (par i)
  · intro i
    have eq : t.getWord32 (BitVec.ofNat 64 (0x20+4*i.val))=s.getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) := by
      simp only [MachineState.getWord32];rw [frame _ (by fin_cases i <;> decide)]
    exact eq.trans (key i)

theorem roots_frame (hash : Hash) (s t : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (n : Nat) (frame : ∀ a, TailRetained a → t.getMem a=s.getMem a)
    (roots : Roots hash parameter seed index n s) : Roots hash parameter seed index n t := by
  intro tree bound i
  simp only [MachineState.getWord32]
  rw [frame _ (Or.inr (Or.inl (root_cell tree i)))]
  exact roots tree bound i

/-- One root is committed to the persistent roots array and retained by its tail. -/
theorem tail_semantics (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree) (selected : Fin 256)
    (pc : s.pc=0x22c0) (base : s.getMem 0x43068=0x527d8)
    (counter : s.getMem 0x43040=BitVec.ofNat 64 tree.val)
    (pointer : s.getMem 0x430a0=BitVec.ofNat 64 (signatureBase tree.val))
    (selector : s.getMem 0x430a8=BitVec.ofNat 64 selected.val)
    (ctx : Context s parameter seed index) (old : Roots hash parameter seed index tree.val s)
    (root : Words20 s 0x527d8 (rootValue hash parameter seed index tree)) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 715 730 1 2 t ∧
      t.pc=(if tree.val+1=24 then 0x25fc else 0x1cec) ∧
      t.getMem 0x43040=BitVec.ofNat 64 (tree.val+1) ∧
      t.getMem 0x430a0=BitVec.ofNat 64 (signatureBase (tree.val+1)) ∧
      Context t parameter seed index ∧ Roots hash parameter seed index (tree.val+1) t := by
  obtain ⟨first,firstPc⟩ := root_saved s tree pc base counter
  have hc := (root_saved_frame s tree base counter 0x43040 (by decide)).trans counter
  have hp := (root_saved_frame s tree base counter 0x430a0 (by decide)).trans pointer
  have hs := (root_saved_frame s tree base counter 0x430a8 (by decide)).trans selector
  obtain ⟨t,last,loc,count,ptr,frame⟩ := after_root hash (rootSaved s) tree selected firstPc hc hp hs
  have roots : Roots hash parameter seed index (tree.val+1) (rootSaved s) := by
    intro prior before i
    by_cases eq : tree=prior
    · subst prior;rw [root_saved_word s tree base counter i];exact root i
    · rw [root_saved_other s tree prior eq base counter i]
      exact old prior (by have ne : tree.val≠prior.val := fun h => eq (Fin.ext h);omega) i
  refine ⟨t,first.trace.trans last,loc,count,ptr,?_,roots_frame hash _ _ parameter seed index _ frame roots⟩
  apply context_frame _ _ parameter seed index frame
  obtain ⟨par,key,msg⟩ := ctx
  refine ⟨?_,?_,(root_saved_frame s tree base counter _ (by decide)).trans msg⟩
  · intro i
    have eq : (rootSaved s).getWord32 (BitVec.ofNat 64 (0x74+4*i.val))=s.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) := by
      simp only [MachineState.getWord32];rw [root_saved_frame s tree base counter _ (by fin_cases i <;> decide)]
    exact eq.trans (par i)
  · intro i
    have eq : (rootSaved s).getWord32 (BitVec.ofNat 64 (0x20+4*i.val))=s.getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) := by
      simp only [MachineState.getWord32];rw [root_saved_frame s tree base counter _ (by fin_cases i <;> decide)]
    exact eq.trans (key i)

abbrev BodyRetained (a : Word) : Prop := TailRetained a ∨
  a=0x43040#64 ∨ a=0x430a0#64 ∨ a=0x430a8#64

theorem body_values (a : Word) (ha : BodyRetained a) :
    a.toNat<0x20000 ∨ (0x44100≤a.toNat ∧ a.toNat<0x44300) ∨
    a.toNat=0x43078 ∨ (0x44800≤a.toNat ∧ a.toNat<0x44818) ∨
    a.toNat=0x43040 ∨ a.toNat=0x430a0 ∨ a.toNat=0x430a8 := by
  rcases ha with tail|eq|eq|eq
  · have h:=tail_retained_values a tail;omega
  all_goals have val:=congrArg BitVec.toNat eq;norm_num at val;omega

theorem body_leaf_safe (a : Word) (ha : BodyRetained a) :
    SphincsMaskedSignForestLeafSemantics.StableAddress a := by
  have h:=body_values a ha
  by_cases low : a.toNat<0x40000
  · exact Or.inl low
  · refine Or.inr ⟨by omega,by omega,?_,?_,?_⟩
    all_goals intro eq;have val:=congrArg BitVec.toNat eq;norm_num at val;omega

theorem body_node_safe (a : Word) (ha : BodyRetained a) :
    a.toNat<0x50000 ∧ a∉SphincsMaskedSignForestParents.preWrites ∧ a≠0x43088#64 := by
  have h:=body_values a ha
  refine ⟨by omega,?_,?_⟩
  · simp only [SphincsMaskedSignForestParents.preWrites,SphincsMaskedSignForestParents.payloadWrites,
      SphincsMaskedSignForestParents.headerWrites,SphincsMaskedSignForestParents.answerWrites,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    intro bad
    rcases bad with ((bad|bad|bad|bad|bad)|(bad|bad|bad|bad|bad|bad|bad))|(bad|bad|bad|bad)
    all_goals have val:=congrArg BitVec.toNat bad;norm_num at val;omega
  · intro eq;have val:=congrArg BitVec.toNat eq;norm_num at val;omega

theorem body_loop_safe (a : Word) (ha : BodyRetained a) : a∉SphincsMaskedSignForestParents.loopWrites := by
  have h:=body_values a ha
  simp only [SphincsMaskedSignForestParents.loopWrites,List.mem_cons,List.not_mem_nil,or_false]
  intro bad
  rcases bad with bad|bad|bad|bad|bad
  all_goals have val:=congrArg BitVec.toNat bad;norm_num at val;omega

/-- Specialize the body proof to the concrete enclosing memory frame. -/
theorem body_semantics (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree)
    (ctx : SphincsMaskedSignForestLeafSemantics.Context s parameter seed index tree)
    (pc : s.pc=0x1d54) (counter : s.getMem 0x43020=0) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 79053 88510 767 1278 t ∧
      t.pc=0x22c0 ∧ t.getMem 0x43068=0x527d8 ∧
      Words20 t 0x527d8 (rootValue hash parameter seed index tree) ∧
      ∀ a, BodyRetained a → t.getMem a=s.getMem a := by
  let extra (t : MachineState) := ∀ a, BodyRetained a → t.getMem a=s.getMem a
  have leafStable : SphincsMaskedSignForestLeafSemantics.FrameStable extra := by
    intro u v frame old a ha;exact (frame a (body_leaf_safe a ha)).trans (old a ha)
  have nodeStable : SphincsMaskedSignForestParents.NodeStable extra := by
    intro u v old frame a ha
    have safe:=body_node_safe a ha
    exact (frame a safe.1 safe.2.1 safe.2.2).trans (old a ha)
  have loopStable : SphincsMaskedSignForestParents.LoopStable extra := by
    intro u v old frame a ha;exact (frame a (body_loop_safe a ha)).trans (old a ha)
  obtain ⟨t,run,done,loc,base,_,root⟩ := SphincsMaskedSignForestParentSemantics.body_semantics hash s
    parameter seed index tree extra leafStable nodeStable loopStable ctx (by intro _ _;rfl) pc counter
  exact ⟨t,run,loc,base,root,done.2⟩


theorem entry_frame (s : MachineState) (a : Word) (ha : TailRetained a) :
    (treeEntry s).getMem a=s.getMem a := by
  have h:=tail_retained_values a ha
  have ne (b : Word) (hb : b=0x43000#64 ∨ b=0x43008#64 ∨ b=0x430a8#64 ∨ b=0x43020#64) : a≠b := by
    intro eq;subst b
    rcases hb with eq|eq|eq|eq
    all_goals have val:=congrArg BitVec.toNat eq;norm_num at val;omega
  simp [treeEntry,runSchedule,treeEntrySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    ne (0x43000#64) (by simp),ne (0x43008#64) (by simp),ne (0x430a8#64) (by simp),ne (0x43020#64) (by simp)]

theorem entry_fields (s : MachineState) :
    (treeEntry s).getMem 0x43000=s.getMem 0x43040 ∧
    (treeEntry s).getMem 0x43008=s.getMem 0x43078 := by
  simp [treeEntry,runSchedule,treeEntrySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem entry_context (s : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) (ctx : Context s parameter seed index)
    (counter : s.getMem 0x43040=BitVec.ofNat 64 tree.val) :
    SphincsMaskedSignForestLeafSemantics.Context (treeEntry s) parameter seed index tree := by
  have kept:=context_frame s (treeEntry s) parameter seed index (entry_frame s) ctx
  exact ⟨(entry_fields s).1.trans counter,(entry_fields s).2.trans ctx.2.2,kept.1,kept.2.1⟩

/-- A whole FORS-tree iteration stores the correct root and retains earlier roots. -/
theorem tree_semantics (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree)
    (pc : s.pc=0x1cec) (ctx : Context s parameter seed index)
    (counter : s.getMem 0x43040=BitVec.ofNat 64 tree.val)
    (pointer : s.getMem 0x430a0=BitVec.ofNat 64 (signatureBase tree.val))
    (old : Roots hash parameter seed index tree.val s) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 79794 89266 768 1280 t ∧
      t.pc=(if tree.val+1=24 then 0x25fc else 0x1cec) ∧
      t.getMem 0x43040=BitVec.ofNat 64 (tree.val+1) ∧
      t.getMem 0x430a0=BitVec.ofNat 64 (signatureBase (tree.val+1)) ∧
      Context t parameter seed index ∧ Roots hash parameter seed index (tree.val+1) t := by
  have entered := entry_context s parameter seed index tree ctx counter
  have controls:=treeEntry_controls s
  obtain ⟨mid,body,midPc,base,root,frame⟩ := body_semantics hash (treeEntry s) parameter seed index tree
    entered (treeEntry_pc s pc) controls.2.2
  have kept (a : Word) (ha : TailRetained a) : mid.getMem a=s.getMem a :=
    (frame a (Or.inl ha)).trans (entry_frame s a ha)
  have bodyCounter := (frame 0x43040 (by decide)).trans (controls.1.trans counter)
  have bodyPointer := (frame 0x430a0 (by decide)).trans (controls.2.1.trans pointer)
  let selected : Fin 256 := ⟨((treeEntry s).getMem 0x430a8).toNat,treeEntry_selector_bound s⟩
  have bodySelector : mid.getMem 0x430a8=BitVec.ofNat 64 selected.val := by
    rw [frame _ (by decide)];simp [selected]
  obtain ⟨t,last,loc,count,ptr,done,roots⟩ := tail_semantics hash mid parameter seed index tree selected
    midPc base bodyCounter bodyPointer bodySelector (context_frame _ _ parameter seed index kept ctx)
    (roots_frame hash _ _ parameter seed index _ kept old) root
  exact ⟨t,(treeEntry_block s tree pc counter).trace.trans (body.trans last),loc,count,ptr,done,roots⟩

/-- The enclosing induction proves all 24 roots, with exact linear cost. -/
theorem trees_semantics (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (pc : s.pc=0x1cec)
    (ctx : Context s parameter seed index) (counter : s.getMem 0x43040=0)
    (pointer : s.getMem 0x430a0=BitVec.ofNat 64 (signatureBase 0)) (n : Nat) (bound : n≤24) :
    ∃ t, Trace hash SphincsMaskedImages.sign s (79794*n) (89266*n) (768*n) (1280*n) t ∧
      t.pc=(if n=24 then 0x25fc else 0x1cec) ∧ t.getMem 0x43040=BitVec.ofNat 64 n ∧
      t.getMem 0x430a0=BitVec.ofNat 64 (signatureBase n) ∧
      Context t parameter seed index ∧ Roots hash parameter seed index n t := by
  induction n with
  | zero => exact ⟨s,Trace.refl _,pc,counter,pointer,ctx,by intro tree before;omega⟩
  | succ n ih =>
    obtain ⟨mid,first,midPc,count,ptr,midCtx,old⟩ := ih (by omega)
    have here : mid.pc=0x1cec := by simpa only [if_neg (show n≠24 by omega)] using midPc
    let tree : FtsTree := ⟨n,by change n<24;omega⟩
    obtain ⟨t,last,loc,next,nextPtr,done,roots⟩ := tree_semantics hash mid parameter seed index tree here midCtx count ptr old
    refine ⟨t,?_,loc,next,nextPtr,done,roots⟩
    simpa only [Nat.mul_add,Nat.mul_one] using first.trans last

theorem init_frame (s : MachineState) (a : Word) (ha : TailRetained a) :
    (treeInit s).getMem a=s.getMem a := by
  have h:=tail_retained_values a ha
  have h0 : a≠0x43040#64 := by intro eq;have val:=congrArg BitVec.toNat eq;norm_num at val;omega
  have h1 : a≠0x430a0#64 := by intro eq;have val:=congrArg BitVec.toNat eq;norm_num at val;omega
  simp [treeInit,runSchedule,treeInitSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1]

/-- From successful grinding to all 24 abstract FORS roots in the root array. -/
theorem forest_roots (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (pc : s.pc=0x1cc8) (ctx : Context s parameter seed index) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 1915065 2142393 18432 30720 t ∧
      t.pc=0x25fc ∧ Context t parameter seed index ∧ Roots hash parameter seed index 24 t := by
  have initial:=treeInit_controls s
  obtain ⟨t,run,loc,_,_,done,roots⟩ := trees_semantics hash (treeInit s) parameter seed index
    (treeInit_pc s pc) (context_frame _ _ parameter seed index (init_frame s) ctx)
    initial.1 initial.2 24 (by decide)
  exact ⟨t,(treeInit_block s pc).trace.trans run,by simpa using loc,done,roots⟩


open SphincsVerifierFtsRootsPayload

def HeaderContext (s : MachineState) (parameter : PublicParameter) (index : Index) : Prop :=
  s.getMem 0x43000=0 ∧ s.getMem 0x43008=BitVec.ofNat 64 index.val ∧
  s.getMem 0x43010=0 ∧ s.getMem 0x43018=0 ∧ Words20 s 0x74 parameter

def headerPayload (parameter : PublicParameter) (index : Index) : List Byte :=
  ((tweakBytes (.ftsRoots index))++bytesLE 20 parameter).map UInt8.toBitVec

theorem headerPayload_length (parameter : PublicParameter) (index : Index) :
    (headerPayload parameter index).length=40 := by
  simp [headerPayload,tweakBytes,hashDomainFields,fieldBytes,bytesLE]

def combineWord (s : MachineState) (i : Fin 10) : BitVec 32 :=
  if i.val=0 then (2817#64+(s.getMem 0x43000 <<<16)).setWidth 32
  else if i.val=1 then (s.getMem 0x43010).setWidth 32
  else if i.val=2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val=3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val=4 then (s.getMem 0x43018).setWidth 32
  else s.getWord32 (BitVec.ofNat 64 (0x74+4*(i.val-5)))

theorem combine_words (s : MachineState) (i : Fin 10) :
    (combineHeader s).getWord32 (BitVec.ofNat 64 (0x40000+4*i.val))=combineWord s i := by
  fin_cases i <;> simp [combineHeader,runSchedule,combineHeaderSchedule,combineWord,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,MachineState.setWord32,
    MachineState.getWord32,alignToDword,byteOffset,
    SphincsMaskedChainStep.extract_replace_low,SphincsMaskedChainStep.extract_replace_high,
    SphincsMaskedChainStep.extract_replace_low_other,SphincsMaskedChainStep.extract_replace_high_other]

theorem combine_header_byte (s : MachineState) (parameter : PublicParameter) (index : Index)
    (ctx : HeaderContext s parameter index) (i : Fin 40) :
    (combineHeader s).getByte (BitVec.ofNat 64 (0x40000+i.val)) =
      (headerPayload parameter index)[i.val]'(by rw [headerPayload_length];exact i.isLt) := by
  have h:=SphincsVerifierFtsGenericBytes.variableWord_byte (combineHeader s)
    (0x40000+4*(i.val/4)) (by omega) (by omega) 0 ⟨i.val%4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  rw [show 0x40000+4*(i.val/4)+i.val%4=0x40000+i.val by omega] at h
  rw [h,combine_words s ⟨i.val/4,by omega⟩]
  obtain ⟨layer,idx,pos,node,par⟩ := ctx
  change s.getMem 0x43000#64=0 at layer
  change s.getMem 0x43010#64=0 at pos
  change s.getMem 0x43018#64=0 at node
  have p0:=par 0;have p1:=par 1;have p2:=par 2;have p3:=par 3;have p4:=par 4
  norm_num at p0 p1 p2 p3 p4
  have idx' : s.getMem 0x43008#64=BitVec.ofNat 64 index.val := by simpa using idx
  fin_cases i <;> simp [combineWord,layer,idx,pos,node,p0,p1,p2,p3,p4,
    headerPayload,tweakBytes,hashDomainFields,tweakFields,fieldBytes,bytesLE,protocolDomainSep,extractWord32]
  all_goals first
    | (rw [idx'];exact BitVec.extractLsb'_setWidth_of_le (by decide))
    | (rw [idx'];simp [BitVec.setWidth_ushiftRight_eq_extractLsb,SphincsMaskedSignForestDomain.nested_extract])
    | exact SphincsMaskedSignForestDomain.nested_extract _ _ _ _ _ (by decide)

theorem combineHeader_frame (s : MachineState) (a : Word)
    (outside : a.toNat<0x40000 ∨ 0x40028≤a.toNat) :
    (combineHeader s).getMem a=s.getMem a := by
  have ne (b : Word) (hb : b=0x40000#64 ∨ b=0x40008#64 ∨ b=0x40010#64 ∨ b=0x40018#64 ∨ b=0x40020#64) : a≠b := by
    intro eq;subst b
    rcases hb with eq|eq|eq|eq|eq
    all_goals have val:=congrArg BitVec.toNat eq;norm_num at val;omega
  simp [combineHeader,runSchedule,combineHeaderSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,MachineState.setWord32,alignToDword,byteOffset,
    ne (0x40000#64) (by simp),ne (0x40008#64) (by simp),ne (0x40010#64) (by simp),
    ne (0x40018#64) (by simp),ne (0x40020#64) (by simp)]

theorem combine_payload_byte (s : MachineState) (i : Fin 480) :
    (combineHeader s).getByte (BitVec.ofNat 64 (0x40028+i.val)) =
      s.getByte (BitVec.ofNat 64 (0x40028+i.val)) := by
  simp only [MachineState.getByte]
  rw [combineHeader_frame _ _ (Or.inr (cell_bounds _ 0x40028 0x40208
    (by decide) (by omega) (by omega) (by decide)).1)]

/-- Exact identification of the final520-byte forest-compression query. -/
theorem combine_query (s : MachineState) (parameter : PublicParameter) (index : Index)
    (roots : FtsTree → Digest) (ctx : HeaderContext s parameter index)
    (payload : ∀ i : Fin 480, s.getByte (BitVec.ofNat 64 (0x40028+i.val))=
      ((Concrete.ftsRootsPayload roots).map UInt8.toBitVec)[i.val]'(by rw [rootsPayload_flat,List.length_map,List.length_ofFn];exact i.isLt)) :
    hashInput (combineHeader s)=toQuery (tweakableHashInput parameter (.ftsRoots index) (Concrete.ftsRootsPayload roots)) := by
  have input : (tweakableHashInput parameter (.ftsRoots index) (Concrete.ftsRootsPayload roots)).map UInt8.toBitVec =
      headerPayload parameter index++(Concrete.ftsRootsPayload roots).map UInt8.toBitVec := by
    simp [tweakableHashInput,headerPayload,List.map_append]
  apply Serialization.hashInput_of_list (combineHeader s) 0x40000
    ((tweakableHashInput parameter (.ftsRoots index) (Concrete.ftsRootsPayload roots)).map UInt8.toBitVec)
  · exact (combine_registers s).1
  · rw [input,List.length_append,headerPayload_length,rootsPayload_flat,List.length_map,List.length_ofFn,(combine_registers s).2.1];rfl
  · intro i hi
    have length : ((tweakableHashInput parameter (.ftsRoots index) (Concrete.ftsRootsPayload roots)).map UInt8.toBitVec).length=520 := by
      rw [input,List.length_append,headerPayload_length,rootsPayload_flat,List.length_map,List.length_ofFn]
    have bound : i<520 := by simpa only [length] using hi
    simp only [input]
    by_cases early : i<40
    · rw [List.getElem_append_left (by rw [headerPayload_length];exact early)]
      exact combine_header_byte s parameter index ctx ⟨i,early⟩
    · have rightBound : (headerPayload parameter index).length ≤ i := by rw [headerPayload_length];omega
      simp only [List.getElem_append_right rightBound,headerPayload_length]
      have eq : 0x40000+i=0x40028+(i-40) := by omega
      rw [eq,combine_payload_byte s ⟨i-40,by omega⟩]
      exact payload ⟨i-40,by omega⟩

theorem combineSetup_frame (s : MachineState) (a : Word)
    (outside : a.toNat<0x43000 ∨ 0x43020≤a.toNat) :
    (combineSetup s).getMem a=s.getMem a := by
  have ne (b : Word) (hb : b=0x43000#64 ∨ b=0x43008#64 ∨ b=0x43010#64 ∨ b=0x43018#64) : a≠b := by
    intro eq;subst b
    rcases hb with eq|eq|eq|eq
    all_goals have val:=congrArg BitVec.toNat eq;norm_num at val;omega
  simp [combineSetup,runSchedule,combineSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    ne (0x43000#64) (by simp),ne (0x43008#64) (by simp),ne (0x43010#64) (by simp),ne (0x43018#64) (by simp)]

theorem combineSetup_context (s : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (ctx : Context s parameter seed index) : HeaderContext (combineSetup s) parameter index := by
  obtain ⟨par,key,msg⟩ := ctx
  change s.getMem 0x43078#64=BitVec.ofNat 64 index.val at msg
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [combineSetup,runSchedule,combineSetupSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [combineSetup,runSchedule,combineSetupSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,msg]
  · simp [combineSetup,runSchedule,combineSetupSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [combineSetup,runSchedule,combineSetupSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · intro i
    have eq : (combineSetup s).getWord32 (BitVec.ofNat 64 (0x74+4*i.val))=s.getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) := by
      simp only [MachineState.getWord32];rw [combineSetup_frame _ _ (by fin_cases i <;> decide)]
    exact eq.trans (par i)

/-- The copy setup preserves the actual root bytes and establishes the header fields. -/
theorem combine_prepare (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (pc : s.pc=0x25fc)
    (ctx : Context s parameter seed index) (roots : Roots hash parameter seed index 24 s) :
    ∃ t, OrdinarySteps SphincsMaskedImages.sign s 387 t ∧ t.pc=0x2680 ∧
      HeaderContext t parameter index ∧
      (∀ i : Fin 480, t.getByte (BitVec.ofNat 64 (0x40028+i.val))=
        ((Concrete.ftsRootsPayload (rootValue hash parameter seed index)).map UInt8.toBitVec)[i.val]'(by
          rw [rootsPayload_flat,List.length_map,List.length_ofFn];exact i.isLt)) ∧
      ∀ a, TailRetained a → t.getMem a=s.getMem a := by
  obtain ⟨t,run,inv,data,frame⟩ := copy_all SphincsMaskedImages.sign 0x2668 combine_copy_code
    0x44100 0x40028 60 (combineSetup s) (combine_copyInvariant s pc)
    (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))
  have kept (a : Word) (ha : a.toNat<0x40000 ∨ 0x43000≤a.toNat) : t.getMem a=(combineSetup s).getMem a := by
    apply frame
    intro i hi eq
    have val:=congrArg BitVec.toNat eq
    simp only [wordAddress,BitVec.toNat_ofNat] at val
    rw [Nat.mod_eq_of_lt (by omega)] at val
    omega
  have setup:=combineSetup_context s parameter seed index ctx
  refine ⟨t,ordinary_trans _ _ _ _ 27 360 (combineSetup_block s pc) run,
    by simpa [CopyInvariant] using inv.2.2.1,?_,?_,?_⟩
  · refine ⟨(kept _ (by decide)).trans setup.1,(kept _ (by decide)).trans setup.2.1,
      (kept _ (by decide)).trans setup.2.2.1,(kept _ (by decide)).trans setup.2.2.2.1,?_⟩
    intro i
    have eq : t.getWord32 (BitVec.ofNat 64 (0x74+4*i.val))=(combineSetup s).getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) := by
      simp only [MachineState.getWord32];rw [kept _ (by fin_cases i <;> decide)]
    exact eq.trans (setup.2.2.2.2 i)
  · intro i
    have copied := SphincsVerifierFtsRootCopyBytes.bytes_eq_of_words s t 0x44100 0x40028 480
      (by decide) (by decide) (by decide) (by decide) (by
        intro j hj
        rw [data j hj,combineSetup_frame]
        right;simp only [wordAddress,BitVec.toNat_ofNat];rw [Nat.mod_eq_of_lt (by omega)];omega) i.val i.isLt
    rw [copied]
    let tree : FtsTree := ⟨i.val/20,by change i.val/20<24;omega⟩
    let byte : Fin 20 := ⟨i.val%20,Nat.mod_lt _ (by decide)⟩
    have actual := SphincsMaskedPublicKeyDomain.words20_byte s (0x44100+20*tree.val)
      (rootValue hash parameter seed index tree) (by have h:=tree.isLt;change tree.val<24 at h;omega)
      (by omega) (roots tree tree.isLt) byte
    have expected := rootsPayload_byte (rootValue hash parameter seed index) tree byte.val byte.isLt
    have split : 20*tree.val+byte.val=i.val := by dsimp [tree,byte];omega
    have addr : 0x44100+20*tree.val+byte.val=0x44100+i.val := by omega
    rw [addr] at actual
    simpa only [split] using actual.trans expected.symm

  · intro a ha
    have h:=tail_retained_values a ha
    rw [kept _ (by omega),combineSetup_frame _ _ (by omega)]


theorem combineStore_frame (s : MachineState) (a : Word)
    (h0 : a≠0x44a00#64) (h1 : a≠0x44a08#64) (h2 : a≠0x44a10#64) :
    (combineStore s).getMem a=s.getMem a := by
  simp [combineStore,runSchedule,combineStoreSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,MachineState.setWord32,
    alignToDword,byteOffset,h0,h1,h2]

/-- Header preparation, HASH response and digest storage preserve the
    key/parameter region and every saved root. -/
theorem combine_result_frame (hash : Hash) (s : MachineState) (a : Word) (ha : TailRetained a) :
    (combineStore (combined hash s)).getMem a=s.getMem a := by
  have h:=tail_retained_values a ha
  have ne (b : Word) (hb : b=0x42000#64 ∨ b=0x42008#64 ∨ b=0x42010#64 ∨ b=0x42018#64 ∨
      b=0x44a00#64 ∨ b=0x44a08#64 ∨ b=0x44a10#64) : a≠b := by
    intro eq;subst b
    rcases hb with eq|eq|eq|eq|eq|eq|eq
    all_goals have val:=congrArg BitVec.toNat eq;norm_num at val;omega
  rw [combineStore_frame _ a (ne _ (by simp)) (ne _ (by simp)) (ne _ (by simp))]
  have dst:=(combine_registers s).2.2.1
  simp only [combined,writeHash,dst,MachineState.writeWords,MachineState.getMem_setPC]
  norm_num only [BitVec.reduceAdd]
  rw [MachineState.getMem_setMem_ne (ne _ (by simp)),MachineState.getMem_setMem_ne (ne _ (by simp)),
    MachineState.getMem_setMem_ne (ne _ (by simp)),MachineState.getMem_setMem_ne (ne _ (by simp))]
  exact combineHeader_frame s a (by omega)

theorem ftsKey_value (hash : Hash) (parameter : PublicParameter) (seed : MasterSeed) (index : Index) :
    evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash) (Seeded.ftsKey parameter index seed) =
      truncateHash (hash (toQuery (tweakableHashInput parameter (.ftsRoots index)
        (Concrete.ftsRootsPayload (rootValue hash parameter seed index))))) := by
  simp only [Seeded.ftsKey,evalWithAnswerFn_bind,Completeness.eval_sequenceFin]
  exact SphincsMaskedChainDomain.eval_hash hash parameter (.ftsRoots index)
    (Concrete.ftsRootsPayload (rootValue hash parameter seed index))

/-- Final forest digest equals the abstract scheme's seeded few-time key. -/
theorem combine_semantics (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (pc : s.pc=0x25fc)
    (ctx : Context s parameter seed index) (roots : Roots hash parameter seed index 24 s) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 444 515 1 9 t ∧ t.pc=0x2764 ∧
      Words20 t 0x44a00 (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.ftsKey parameter index seed)) ∧ Context t parameter seed index ∧
      Roots hash parameter seed index 24 t := by
  obtain ⟨prepared,prep,prepPc,header,bytes,prepFrame⟩ := combine_prepare hash s parameter seed index pc ctx roots
  have query:=combine_query prepared parameter index (rootValue hash parameter seed index) header bytes
  have value:=combined_value hash prepared
  rw [query] at value
  have frame (a : Word) (ha : TailRetained a) :
      (combineStore (combined hash prepared)).getMem a=s.getMem a :=
    (combine_result_frame hash prepared a ha).trans (prepFrame a ha)
  refine ⟨combineStore (combined hash prepared),prep.trace.trans
    ((combine_hash hash prepared prepPc).trans (combineStore_block _ (combined_pc hash prepared prepPc)).trace),
    combineStore_pc _ (combined_pc hash prepared prepPc),?_,
    context_frame _ _ parameter seed index frame ctx,roots_frame hash _ _ parameter seed index _ frame roots⟩
  rw [ftsKey_value]
  exact value

/-- The final machine state retains all roots and key/parameter words. -/
theorem forest_complete (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (pc : s.pc=0x1cc8) (ctx : Context s parameter seed index) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 1915509 2142908 18433 30729 t ∧ t.pc=0x2764 ∧
      Context t parameter seed index ∧ Roots hash parameter seed index 24 t ∧
      Words20 t 0x44a00 (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.ftsKey parameter index seed)) := by
  obtain ⟨mid,first,midPc,midCtx,roots⟩ := forest_roots hash s parameter seed index pc ctx
  obtain ⟨t,last,done,value,tCtx,tRoots⟩ := combine_semantics hash mid parameter seed index midPc midCtx roots
  exact ⟨t,first.trans last,done,tCtx,tRoots,value⟩

/-- Exact complete forest trace with all roots and the final digest justified by
    the real oracle calls. The semantic assumptions are only the incoming key,
    parameter and message-index words after successful grinding. -/
theorem forest_semantics (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (pc : s.pc=0x1cc8) (ctx : Context s parameter seed index) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 1915509 2142908 18433 30729 t ∧ t.pc=0x2764 ∧
      ∀ i : Fin 20, t.getByte (BitVec.ofNat 64 (0x44a00+i.val))=
        (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
          (Seeded.ftsKey parameter index seed)).extractLsb' (8*i.val) 8 := by
  obtain ⟨mid,first,midPc,midCtx,roots⟩ := forest_roots hash s parameter seed index pc ctx
  obtain ⟨t,last,done,value,_,_⟩ := combine_semantics hash mid parameter seed index midPc midCtx roots
  exact ⟨t,first.trans last,done,SphincsMaskedPublicKeyDomain.words20_byte t 0x44a00 _ (by decide) (by decide) value⟩


/-- Byte-for-byte refinement of every saved FORS root and the final forest digest. -/
theorem forest_bytes (hash : Hash) (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (pc : s.pc=0x1cc8) (ctx : Context s parameter seed index) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 1915509 2142908 18433 30729 t ∧ t.pc=0x2764 ∧
      Context t parameter seed index ∧
      (∀ tree : FtsTree, ∀ i : Fin 20,
        t.getByte (BitVec.ofNat 64 (0x44100+20*tree.val+i.val))=
          (rootValue hash parameter seed index tree).extractLsb' (8*i.val) 8) ∧
      ∀ i : Fin 20, t.getByte (BitVec.ofNat 64 (0x44a00+i.val))=
        (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
          (Seeded.ftsKey parameter index seed)).extractLsb' (8*i.val) 8 := by
  obtain ⟨t,run,done,tCtx,roots,value⟩ := forest_complete hash s parameter seed index pc ctx
  refine ⟨t,run,done,tCtx,?_,SphincsMaskedPublicKeyDomain.words20_byte t 0x44a00 _ (by decide) (by decide) value⟩
  intro tree i
  exact SphincsMaskedPublicKeyDomain.words20_byte t (0x44100+20*tree.val) _
    (by have h:=tree.isLt;change tree.val<24 at h;omega) (by omega) (roots tree tree.isLt) i

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.paths_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paths_wide

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.tail_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tail_semantics

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.body_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms body_semantics

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.tree_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tree_semantics

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.trees_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trees_semantics

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.forest_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forest_roots

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.combine_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combine_query

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.combine_prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combine_prepare

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.combine_result_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combine_result_frame

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.ftsKey_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ftsKey_value

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.combine_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combine_semantics

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.forest_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forest_complete

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.forest_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forest_semantics

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestSemantics.forest_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forest_bytes

end SigGolfCandidate.SphincsMaskedSignForestSemantics
