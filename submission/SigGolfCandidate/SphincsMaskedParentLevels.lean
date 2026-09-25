import SigGolfCandidate.SphincsMaskedParentDomain

namespace SigGolfCandidate.SphincsMaskedParentLevels
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedParentCode SphincsMaskedParentNode SphincsMaskedParentDomain
open SphincsMaskedChainDomain SphincsMaskedSecretDomain SphincsMaskedLeafRefinement
open SphincsBridge SphincsSecurity
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

structure Controls (s : MachineState) (base target level count node : Nat) : Prop where
  base : s.getMem 0x43068 = BitVec.ofNat 64 base
  target : s.getMem 0x43080 = BitVec.ofNat 64 target
  level : s.getMem 0x43048 = BitVec.ofNat 64 level
  count : s.getMem 0x43090 = BitVec.ofNat 64 count
  node : s.getMem 0x43088 = BitVec.ofNat 64 node

theorem next_control (hash : Hash) (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : target + 20 * node + 20 ≤ 0x40000) (a : Word)
    (high : 0x40000 ≤ a.toNat) (outside : a ∉ preWrites) (notNode : a ≠ 0x43088#64) :
    (next hash s).getMem a = s.getMem a := by
  have atarget := (answer_frame hash s _ (by decide)).trans ht
  have anode := (answer_frame hash s _ (by decide)).trans hn
  change (nodeFinish (stored (answer hash s))).getMem a = _
  rw [nodeFinish_frame _ a notNode,stored_control _ target node atarget anode bounded a high,
    answer_frame hash s a outside]

theorem next_key (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (target node : Nat) (ctx : KeyContext s parameter seed)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : target + 20 * node + 20 ≤ 0x40000) (aligned : target % 4 = 0) (above : 0x88 ≤ target) :
    KeyContext (next hash s) parameter seed := by
  obtain ⟨layer,tree,par,key⟩ := ctx
  refine ⟨?_,?_,?_,?_⟩
  · exact (next_control hash s target node ht hn bounded _ (by decide) (by decide) (by decide)).trans layer
  · exact (next_control hash s target node ht hn bounded _ (by decide) (by decide) (by decide)).trans tree
  · intro i
    rw [next_other_word hash s target node (0x74 + 4 * i.val) ht hn bounded aligned (by omega) (by omega) (by intro j;omega)]
    exact par i
  · intro i
    rw [next_other_word hash s target node (0x20 + 4 * i.val) ht hn bounded aligned (by omega) (by omega) (by intro j;omega)]
    exact key i

def nodes (hash : Hash) : Nat → MachineState → MachineState
  | 0,s => s
  | n+1,s => next hash (nodes hash n s)

def parentValue (hash : Hash) (parameter : BitVec 160) (level node : Nat) (left right : Digest) : Digest :=
  truncateHash (hash (toQuery (SphincsMaskedParentDomain.input parameter left right level node)))

/-- The node loop computes all parents while retaining every lower cache address. -/
theorem nodes_contract (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (base target level count : Nat) (values : Nat → Digest)
    (pc : s.pc = 0x1620) (ctx : KeyContext s parameter seed) (controls : Controls s base target level count 0)
    (source : ∀ j, j < 2 * count → Words20 s (base + 20 * j) (values j))
    (sourceBound : base + 40 * count ≤ target) (targetBound : target + 20 * count ≤ 0x40000)
    (baseAlign : base % 4 = 0) (targetAlign : target % 4 = 0) (above : 0x88 ≤ target)
    (positive : 0 < count) (small : count < 2048) (n : Nat) (hn : n ≤ count) :
    Trace hash SphincsMaskedImages.keygen s (124 * n) (139 * n) n (2 * n) (nodes hash n s) ∧
      Controls (nodes hash n s) base target level count n ∧ KeyContext (nodes hash n s) parameter seed ∧
      (nodes hash n s).pc = (if n = count then 0x1810 else 0x1620) ∧
      (∀ j, j < n → Words20 (nodes hash n s) (target + 20 * j)
        (parentValue hash parameter level j (values (2 * j)) (values (2 * j + 1)))) ∧
      (∀ address, address < target → address % 4 = 0 →
        (nodes hash n s).getWord32 (BitVec.ofNat 64 address) = s.getWord32 (BitVec.ofNat 64 address)) := by
  induction n with
  | zero =>
    refine ⟨Trace.refl _,controls,ctx,?_,?_,?_⟩
    · simpa only [nodes,if_neg (show 0 ≠ count by omega)] using pc
    · intro j h;omega
    · intro _ _ _;rfl
  | succ n ih =>
    obtain ⟨trace,ctrl,key,loc,done,frame⟩ := ih (by omega)
    let mid := nodes hash n s
    have npc : mid.pc = 0x1620 := by rw [loc,if_neg (by omega)]
    have sb : base + 40 * n + 40 ≤ 0x40000 := by omega
    have tb : target + 20 * n + 20 ≤ 0x40000 := by omega
    obtain ⟨last,nextCount,nextPc⟩ := node_trace hash mid base target n count npc ctrl.base ctrl.target ctrl.node ctrl.count sb baseAlign tb targetAlign small
    have newControls : Controls (next hash mid) base target level count (n+1) := by
      refine ⟨?_,?_,?_,?_,nextCount⟩
      · exact (next_control hash mid target n ctrl.target ctrl.node tb _ (by decide) (by decide) (by decide)).trans ctrl.base
      · exact (next_control hash mid target n ctrl.target ctrl.node tb _ (by decide) (by decide) (by decide)).trans ctrl.target
      · exact (next_control hash mid target n ctrl.target ctrl.node tb _ (by decide) (by decide) (by decide)).trans ctrl.level
      · exact (next_control hash mid target n ctrl.target ctrl.node tb _ (by decide) (by decide) (by decide)).trans ctrl.count
    have left : Words20 mid (base + 40 * n) (values (2 * n)) := by
      intro i
      rw [frame _ (by omega) (by omega)]
      convert source (2*n) (by omega) i using 1 <;> congr 2 <;> omega
    have right : Words20 mid (base + 40 * n + 20) (values (2 * n + 1)) := by
      intro i
      rw [frame _ (by omega) (by omega)]
      convert source (2*n+1) (by omega) i using 1 <;> congr 2 <;> omega
    have newValue := node_value hash mid parameter _ _ base target level n key.1 key.2.1
      ctrl.level ctrl.node ctrl.base ctrl.target sb tb targetAlign key.2.2.1 left right
    refine ⟨?_,newControls,next_key hash mid parameter seed target n key ctrl.target ctrl.node tb targetAlign above,nextPc,?_,?_⟩
    · simpa only [nodes,Nat.mul_succ,Nat.succ_eq_add_one] using trace.trans last
    · intro j hj
      by_cases eq : j = n
      · subst j;exact newValue
      · intro i
        rw [nodes,next_other_word hash mid target n (target + 20 * j + 4 * i.val)
          ctrl.target ctrl.node tb targetAlign (by omega) (by omega) (by intro k;omega)]
        exact done j (by omega) i
    · intro address ha halign
      rw [nodes,next_other_word hash mid target n address ctrl.target ctrl.node tb targetAlign
        (by omega) halign (by intro j;omega)]
      exact frame address ha halign

/-- info: 'SigGolfCandidate.SphincsMaskedParentLevels.nodes_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodes_contract


def width (level : Nat) : Nat := if level ≤ 11 then 2 ^ (11 - level) else 0
def cacheBase (level : Nat) : Nat := 0x88 + 20 * (4096 - 2 ^ (12 - level))
def totalNodes (levels : Nat) : Nat := 2048 - 2 ^ (11 - levels)

theorem layout : ∀ k : Fin 11,
    cacheBase k.val + 40 * width (k.val+1) = cacheBase (k.val+1) ∧
    cacheBase (k.val+1) + 20 * width (k.val+1) = cacheBase (k.val+2) ∧
    cacheBase (k.val+2) ≤ 0x40000 ∧
    cacheBase k.val % 4 = 0 ∧ cacheBase (k.val+1) % 4 = 0 ∧
    0x88 ≤ cacheBase (k.val+1) ∧ 0 < width (k.val+1) ∧ width (k.val+1) < 2048 ∧
    width (k.val+1) / 2 = width (k.val+2) ∧
    totalNodes (k.val+1) = totalNodes k.val + width (k.val+1) := by decide

theorem earlier_layout : ∀ (k : Fin 11) (l : Fin 12), l.val ≤ k.val →
    cacheBase l.val + 20 * width l.val ≤ cacheBase (k.val+1) ∧ cacheBase l.val % 4 = 0 := by decide

structure LevelControls (s : MachineState) (k : Nat) : Prop where
  base : s.getMem 0x43068 = BitVec.ofNat 64 (cacheBase k)
  target : s.getMem 0x43080 = BitVec.ofNat 64 (cacheBase (k+1))
  level : s.getMem 0x43048 = BitVec.ofNat 64 (k+1)
  count : s.getMem 0x43090 = BitVec.ofNat 64 (width (k+1))

theorem init_controls (s : MachineState) : LevelControls (init s) 0 := by
  constructor <;> simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,cacheBase,width]

def loopWrites : List Word := [0x43048#64,0x43068#64,0x43080#64,0x43088#64,0x43090#64]

theorem init_frame (s : MachineState) (a : Word) (outside : a ∉ loopWrites) :
    (init s).getMem a = s.getMem a := by
  simp only [loopWrites,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4⟩ := outside
  simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3,h4]

theorem levelEntry_frame (s : MachineState) (a : Word) (outside : a ≠ 0x43088#64) :
    (levelEntry s).getMem a = s.getMem a := by
  simp [levelEntry,runSchedule,levelEntrySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,outside]

theorem levelEntry_controls (s : MachineState) (k : Nat) (ctx : LevelControls s k) :
    Controls (levelEntry s) (cacheBase k) (cacheBase (k+1)) (k+1) (width (k+1)) 0 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (levelEntry_frame s _ (by decide)).trans ctx.base
  · exact (levelEntry_frame s _ (by decide)).trans ctx.target
  · exact (levelEntry_frame s _ (by decide)).trans ctx.level
  · exact (levelEntry_frame s _ (by decide)).trans ctx.count
  · simp [levelEntry,runSchedule,levelEntrySchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem levelFinish_frame (s : MachineState) (a : Word) (outside : a ∉ loopWrites) :
    (levelFinish s).getMem a = s.getMem a := by
  simp only [loopWrites,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4⟩ := outside
  simp [levelFinish,runSchedule,levelFinishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3,h4]

theorem low_outside (a : Word) (ha : a.toNat < 0x40000) : a ∉ loopWrites := by
  intro member
  have high : ∀ b ∈ loopWrites, 0x40000 ≤ b.toNat := by simp [loopWrites]
  exact (low_ne a a ha (high a member)) rfl

theorem loop_key (s t : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (ctx : KeyContext s parameter seed) (frame : ∀ a, a ∉ loopWrites → t.getMem a = s.getMem a) :
    KeyContext t parameter seed := by
  apply context_transport s t parameter seed ctx
  intro a ha
  apply frame
  rcases ha with low | rfl | rfl
  · exact low_outside a (by omega)
  · decide
  · decide

theorem levelFinish_controls (s : MachineState) (k : Fin 11)
    (ctx : Controls s (cacheBase k.val) (cacheBase (k.val+1)) (k.val+1) (width (k.val+1)) (width (k.val+1))) :
    LevelControls (levelFinish s) (k.val+1) := by
  have target := ctx.target
  have count := ctx.count
  have level := ctx.level
  change s.getMem 0x43080#64 = _ at target
  change s.getMem 0x43090#64 = _ at count
  change s.getMem 0x43048#64 = _ at level
  constructor <;>
    simp [levelFinish,runSchedule,levelFinishSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,target,count,level]
  all_goals fin_cases k <;> decide

theorem levelFinish_pc (s : MachineState) (k : Fin 11) (pc : s.pc = 0x1810)
    (level : s.getMem 0x43048 = BitVec.ofNat 64 (k.val+1)) :
    (levelFinish s).pc = if k.val+1 = 11 then 0x189c else 0x1610 := by
  change s.getMem 0x43048#64 = _ at level
  simp [levelFinish,runSchedule,levelFinishSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc,level]
  fin_cases k <;> decide

def treeValue (hash : Hash) (parameter : BitVec 160) (seed : MasterSeed) (level node : Nat) : Digest :=
  evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
    (Seeded.treeNode parameter topLayer Concrete.rootTree seed level node : OracleComp SphincsSecurity.HashSpec Digest)

theorem treeValue_succ (hash : Hash) (parameter : BitVec 160) (seed : MasterSeed) (level node : Nat) :
    treeValue hash parameter seed (level+1) node =
      parentValue hash parameter (level+1) node (treeValue hash parameter seed level (2*node))
        (treeValue hash parameter seed level (2*node+1)) := by
  simp only [treeValue,Seeded.treeNode,evalWithAnswerFn_bind,SphincsMaskedChainDomain.eval_hash]
  rfl

/-- One complete level, including resetting its node index and advancing all tree-layout controls. -/
theorem level_contract (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (k : Fin 11) (pc : s.pc = 0x1610) (ctx : KeyContext s parameter seed) (ctrl : LevelControls s k.val)
    (source : ∀ node, node < width k.val → Words20 s (cacheBase k.val + 20 * node) (treeValue hash parameter seed k.val node)) :
    ∃ final, Trace hash SphincsMaskedImages.keygen s (39 + 124 * width (k.val+1))
      (39 + 139 * width (k.val+1)) (width (k.val+1)) (2 * width (k.val+1)) final ∧
      LevelControls final (k.val+1) ∧ KeyContext final parameter seed ∧
      final.pc = (if k.val+1 = 11 then 0x189c else 0x1610) ∧
      (∀ node, node < width (k.val+1) → Words20 final (cacheBase (k.val+1) + 20 * node)
        (treeValue hash parameter seed (k.val+1) node)) ∧
      (∀ address, address < cacheBase (k.val+1) → address % 4 = 0 →
        final.getWord32 (BitVec.ofNat 64 address) = s.getWord32 (BitVec.ofNat 64 address)) := by
  obtain ⟨sourceEnd,targetEnd,targetBound,baseAlign,targetAlign,above,positive,small,half,total⟩ := layout k
  have countTwice : 2 * width (k.val+1) = width k.val := by fin_cases k <;> decide
  have entryKey := loop_key s (levelEntry s) parameter seed ctx (by
    intro a ha;apply levelEntry_frame
    intro eq;exact ha (by simp [loopWrites,eq]))
  have entryValues : ∀ j, j < 2 * width (k.val+1) → Words20 (levelEntry s)
      (cacheBase k.val + 20*j) (treeValue hash parameter seed k.val j) := by
    intro j hj i
    simp only [MachineState.getWord32]
    rw [levelEntry_frame _ _ (low_ne _ _ (low_cell _ (by omega)) (by decide))]
    exact source j (by omega) i
  obtain ⟨nodeTrace,nodeCtrl,nodeKey,nodePc,values,frame⟩ := nodes_contract hash (levelEntry s) parameter seed
    (cacheBase k.val) (cacheBase (k.val+1)) (k.val+1) (width (k.val+1))
    (treeValue hash parameter seed k.val) (levelEntry_pc s pc) entryKey (levelEntry_controls s k.val ctrl)
    entryValues (by omega) (by omega) baseAlign targetAlign above positive small (width (k.val+1)) (by omega)
  let mid := nodes hash (width (k.val+1)) (levelEntry s)
  have midPc : mid.pc = 0x1810 := by simpa using nodePc
  refine ⟨levelFinish mid,?_,levelFinish_controls mid k nodeCtrl,
    loop_key mid _ parameter seed nodeKey (levelFinish_frame mid),levelFinish_pc mid k midPc nodeCtrl.level,?_,?_⟩
  · have trace := (levelEntry_block s pc).trace.trans (nodeTrace.trans (levelFinish_block mid midPc).trace)
    convert trace using 1 <;> omega
  · intro node hn i
    simp only [MachineState.getWord32]
    rw [levelFinish_frame _ _ (low_outside _ (low_cell _ (by omega)))]
    rw [treeValue_succ]
    exact values node hn i
  · intro address ha halign
    simp only [MachineState.getWord32]
    rw [levelFinish_frame _ _ (low_outside _ (low_cell _ (by omega)))]
    change mid.getWord32 _ = _
    rw [frame address ha halign]
    simp only [MachineState.getWord32]
    rw [levelEntry_frame _ _ (low_ne _ _ (low_cell _ (by omega)) (by decide))]

/-- info: 'SigGolfCandidate.SphincsMaskedParentLevels.level_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms level_contract


/-- Compose all tree levels while retaining the abstract meaning of every earlier cache node. -/
theorem levels_contract (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (pc : s.pc = 0x1610) (ctx : KeyContext s parameter seed) (ctrl : LevelControls s 0)
    (leaves : ∀ node, node < width 0 → Words20 s (cacheBase 0 + 20 * node) (treeValue hash parameter seed 0 node))
    (n : Nat) (hn : n ≤ 11) :
    ∃ final, Trace hash SphincsMaskedImages.keygen s (39*n + 124*totalNodes n) (39*n + 139*totalNodes n)
      (totalNodes n) (2*totalNodes n) final ∧ LevelControls final n ∧ KeyContext final parameter seed ∧
      final.pc = (if n = 11 then 0x189c else 0x1610) ∧
      (∀ level, level ≤ n → ∀ node, node < width level →
        Words20 final (cacheBase level + 20*node) (treeValue hash parameter seed level node)) := by
  induction n with
  | zero =>
    refine ⟨s,?_,ctrl,ctx,pc,?_⟩
    · exact Trace.refl _
    · intro level hl node hn
      have eq : level = 0 := by omega
      subst level;exact leaves node hn
  | succ n ih =>
    obtain ⟨mid,first,midCtrl,midKey,midPc,old⟩ := ih (by omega)
    have npc : mid.pc = 0x1610 := by rw [midPc,if_neg (by omega)]
    let k : Fin 11 := ⟨n,by omega⟩
    obtain ⟨final,last,finalCtrl,finalKey,finalPc,new,frame⟩ :=
      level_contract hash mid parameter seed k npc midKey midCtrl (old n (by omega))
    refine ⟨final,?_,finalCtrl,finalKey,finalPc,?_⟩
    · have total : totalNodes (n+1) = totalNodes n + width (n+1) := (layout k).2.2.2.2.2.2.2.2.2
      have trace := first.trans last
      dsimp [k] at trace
      rw [total]
      convert trace using 1 <;> omega
    · intro level hl node hnode
      by_cases eq : level = n+1
      · subst level;exact new node hnode
      · have le : level ≤ n := by omega
        have before := earlier_layout k ⟨level,by omega⟩ le
        change cacheBase level + 20 * width level ≤ cacheBase (n+1) ∧ cacheBase level % 4 = 0 at before
        dsimp only [k] at frame
        intro i
        rw [frame _ (by omega) (by omega)]
        exact old level le node hnode i

theorem leafValue_treeValue (hash : Hash) (parameter : BitVec 160) (seed : MasterSeed) (leaf : LeafIndex) :
    leafValue hash parameter seed leaf = treeValue hash parameter seed 0 leaf.val := by
  have leafEq : Concrete.leafOfNat leaf.val = leaf := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt leaf.isLt
  simp only [treeValue,Seeded.treeNode,leafEq,leafValue]

/-- All 2,047 internal nodes are exact abstract seeded-tree values, with exact aggregate cost. -/
theorem parents_contract (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (pc : s.pc = 0x15cc) (ctx : KeyContext s parameter seed)
    (leaves : ∀ leaf : LeafIndex, Words20 s (0x88 + 20*leaf.val) (leafValue hash parameter seed leaf)) :
    ∃ final, Trace hash SphincsMaskedImages.keygen s 254274 284979 2047 4094 final ∧
      final.pc = 0x189c ∧ final.getMem 0x43068 = 0x14060 ∧ KeyContext final parameter seed ∧
      (∀ level, level ≤ 11 → ∀ node, node < width level →
        Words20 final (cacheBase level + 20*node) (treeValue hash parameter seed level node)) := by
  have key := loop_key s (init s) parameter seed ctx (init_frame s)
  have initial : ∀ node, node < width 0 → Words20 (init s) (cacheBase 0 + 20*node)
      (treeValue hash parameter seed 0 node) := by
    intro node hn i
    have bound : node < 2048 := hn
    let leaf : LeafIndex := ⟨node,bound⟩
    have val := leaves leaf i
    rw [leafValue_treeValue] at val
    change (init s).getWord32 (BitVec.ofNat 64 (0x88 + 20*node + 4*i.val)) = _
    simp only [MachineState.getWord32]
    rw [init_frame _ _ (low_outside _ (low_cell _ (by omega)))]
    exact val
  obtain ⟨final,trace,control,key,loc,values⟩ := levels_contract hash (init s) parameter seed
    (init_pc s pc) key (init_controls s) initial 11 (by decide)
  refine ⟨final,?_,?_,control.base,key,values⟩
  · exact (init_block s pc).trace.trans trace
  · simpa using loc

/-- The exact root slot equals the abstract top-tree root. -/
theorem parents_root (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (pc : s.pc = 0x15cc) (ctx : KeyContext s parameter seed)
    (leaves : ∀ leaf : LeafIndex, Words20 s (0x88 + 20*leaf.val) (leafValue hash parameter seed leaf)) :
    ∃ final, Trace hash SphincsMaskedImages.keygen s 254274 284979 2047 4094 final ∧
      final.pc = 0x189c ∧ final.getMem 0x43068 = 0x14060 ∧ KeyContext final parameter seed ∧
      Words20 final 0x14060
        (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
          (Seeded.treeRoot parameter topLayer Concrete.rootTree seed : OracleComp SphincsSecurity.HashSpec Digest)) := by
  obtain ⟨final,trace,loc,base,key,values⟩ := parents_contract hash s parameter seed pc ctx leaves
  refine ⟨final,trace,loc,base,key,?_⟩
  exact values 11 (by decide) 0 (by decide)

/-- info: 'SigGolfCandidate.SphincsMaskedParentLevels.parents_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parents_contract

/-- info: 'SigGolfCandidate.SphincsMaskedParentLevels.parents_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parents_root

end SigGolfCandidate.SphincsMaskedParentLevels
