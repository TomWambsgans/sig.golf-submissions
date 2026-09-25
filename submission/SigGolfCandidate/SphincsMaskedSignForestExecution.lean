import SigGolfCandidate.SphincsMaskedSignForestTail
import SigGolfCandidate.SphincsMaskedSignForestEntry

namespace SigGolfCandidate.SphincsMaskedSignForestExecution
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
open SphincsMaskedSignForestEntry
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev Retained (a : Word) : Prop := a.toNat<0x40000 ∨ 0x43020≤a.toNat

def leafAnswer (hash : Hash) (s : MachineState) :=
  writeHash (leafHashReady s) (hash (hashInput (leafHashReady s)))

theorem leafAnswer_pc (hash : Hash) (s : MachineState) (pc : s.pc=0x1da4) :
    (leafAnswer hash s).pc=0x1e4c := by
  simp [leafAnswer,writeHash,leafHash_pc s pc]

theorem leafSetup_frame (s : MachineState) (a : Word) (outside : Retained a) :
    (leafSetup s).getMem a=s.getMem a := by
  have h0 : a ≠ 0x43010#64 := by intro eq;subst a;norm_num [Retained] at outside
  have h1 : a ≠ 0x43018#64 := by intro eq;subst a;norm_num [Retained] at outside
  simp [leafSetup,runSchedule,leafSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1]

theorem leafHashReady_frame (s : MachineState) (a : Word) (outside : Retained a) :
    (leafHashReady s).getMem a=s.getMem a := by
  have ne (b : Word) (hb : b=0x40000#64 ∨ b=0x40008#64 ∨ b=0x40010#64 ∨ b=0x40018#64 ∨ b=0x40020#64) : a≠b := by
    intro eq;subst b
    rcases hb with h|h|h|h|h <;> subst a <;> norm_num [Retained] at outside
  simp [leafHashReady,runSchedule,leafHashSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,alignToDword,byteOffset,
    ne (0x40000#64) (by simp),ne (0x40008#64) (by simp),ne (0x40010#64) (by simp),ne (0x40018#64) (by simp),ne (0x40020#64) (by simp)]

theorem leafAnswer_frame (hash : Hash) (s : MachineState) (a : Word) (outside : Retained a) :
    (leafAnswer hash s).getMem a=s.getMem a := by
  have ne (b : Word) (hb : b=0x42000#64 ∨ b=0x42008#64 ∨ b=0x42010#64 ∨ b=0x42018#64) : a≠b := by
    intro eq;subst b
    rcases hb with h|h|h|h <;> subst a <;> norm_num [Retained] at outside
  have dst := (leafHash_registers s).2.2.1
  simp [leafAnswer,writeHash,dst,MachineState.writeWords,
    ne (0x42000#64) (by simp),ne (0x42008#64) (by simp),ne (0x42010#64) (by simp),ne (0x42018#64) (by simp)]
  exact leafHashReady_frame s a outside

/-- The selected secret derivation always completes and retains the forest controls. -/
theorem leaf_prefix (hash : Hash) (s : MachineState) (pc : s.pc=0x1d54) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 80 95 1 2 t ∧ t.pc=0x1e4c ∧
      ∀ a, Retained a → t.getMem a=s.getMem a := by
  obtain ⟨copied,copyTrace,copyInv,_,frame⟩ := copy_all SphincsMaskedImages.sign 0x1d8c leafCopy_code
    0x20 0x40028 4 (leafSetup s) (leafSetup_copyInvariant s pc)
    (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
  have copyPc : copied.pc=0x1da4 := by simpa [CopyInvariant] using copyInv.2.2.1
  refine ⟨leafAnswer hash copied,(leafSetup_block s pc).trace.trans
    (copyTrace.trace.trans (leafHash_trace hash copied copyPc)),leafAnswer_pc hash copied copyPc,?_⟩
  intro a ha
  rw [leafAnswer_frame hash copied a ha,frame]
  · exact leafSetup_frame s a ha
  · intro i hi eq
    have val := congrArg BitVec.toNat eq
    simp only [wordAddress,BitVec.toNat_ofNat] at val
    rw [Nat.mod_eq_of_lt (by omega)] at val
    rcases ha with low|high <;> omega



abbrev CoreAddress (a : Word) : Prop := a=0x43040#64 ∨ a=0x430a0#64 ∨
  a=0x430a8#64 ∨ a=0x43078#64 ∨ (0x44800≤a.toNat ∧ a.toNat<0x44818)

theorem core_values (a : Word) (ha : CoreAddress a) :
    a.toNat=0x43040 ∨ a.toNat=0x430a0 ∨ a.toNat=0x430a8 ∨ a.toNat=0x43078 ∨
      (0x44800≤a.toNat ∧ a.toNat<0x44818) := by
  rcases ha with h|h|h|h|h
  · rw [h];exact Or.inl rfl
  · rw [h];exact Or.inr (Or.inl rfl)
  · rw [h];exact Or.inr (Or.inr (Or.inl rfl))
  · rw [h];exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem core_retained (a : Word) (ha : CoreAddress a) : Retained a := by
  have values := core_values a ha
  exact Or.inr (by omega)

theorem core_suffix (a : Word) (ha : CoreAddress a) :
    a.toNat<0x40000 ∨ (0x43000≤a.toNat ∧ a.toNat<0x44b00 ∧ a≠0x43020#64) := by
  have values := core_values a ha
  refine Or.inr ⟨by omega,by omega,?_⟩
  intro eq
  have val := congrArg BitVec.toNat eq
  norm_num at val
  omega

/-- One leaf iteration with all enclosing forest controls retained. -/
theorem leaf_execution (hash : Hash) (s : MachineState) (leaf : Fin 256)
    (pc : s.pc=0x1d54) (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 183 205 2 3 t ∧
      t.pc=(if leaf.val+1=256 then 0x1fe8 else 0x1d54) ∧
      t.getMem 0x43020=BitVec.ofNat 64 (leaf.val+1) ∧
      ∀ a, CoreAddress a → t.getMem a=s.getMem a := by
  obtain ⟨mid,first,midPc,frame⟩ := leaf_prefix hash s pc
  have midCount := (frame 0x43020 (by decide)).trans counter
  obtain ⟨last,count,loc⟩ := SphincsMaskedSignForestLoop.leaf_suffix hash mid leaf midPc midCount
  refine ⟨SphincsMaskedSignForestLoop.nextLeaf (SphincsMaskedSignForestLoop.answer hash mid),
    first.trans last,loc,count,?_⟩
  intro a ha
  rw [SphincsMaskedSignForestLoop.leaf_suffix_frame hash mid leaf midCount a (core_suffix a ha),
    frame a (core_retained a ha)]

/-- The finite leaf loop, without any semantic oracle assumptions. -/
theorem leaves_execution (hash : Hash) (s : MachineState) (pc : s.pc=0x1d54)
    (counter : s.getMem 0x43020=0) (n : Nat) (bound : n≤256) :
    ∃ t, Trace hash SphincsMaskedImages.sign s (183*n) (205*n) (2*n) (3*n) t ∧
      t.pc=(if n=256 then 0x1fe8 else 0x1d54) ∧
      t.getMem 0x43020=BitVec.ofNat 64 n ∧
      ∀ a, CoreAddress a → t.getMem a=s.getMem a := by
  induction n with
  | zero => exact ⟨s,Trace.refl _,pc,counter,by intro _ _;rfl⟩
  | succ n ih =>
    obtain ⟨mid,first,midPc,midCount,frame⟩ := ih (by omega)
    have here : mid.pc=0x1d54 := by simpa only [if_neg (show n≠256 by omega)] using midPc
    obtain ⟨t,last,loc,count,kept⟩ := leaf_execution hash mid ⟨n,by omega⟩ here midCount
    refine ⟨t,?_,loc,count,?_⟩
    · simpa only [Nat.mul_add,Nat.mul_one] using first.trans last
    · intro a ha;rw [kept a ha,frame a ha]


open SphincsMaskedSignForestParents

theorem core_node_safe (a : Word) (ha : CoreAddress a) :
    a.toNat<0x50000 ∧ a ∉ preWrites ∧ a≠0x43088#64 := by
  have values := core_values a ha
  refine ⟨by omega,?_,?_⟩
  · intro mem
    have small : ∀ b ∈ preWrites, b.toNat<0x43020 := by
      simp [preWrites,payloadWrites,headerWrites,answerWrites]
    have bad := small a mem
    omega
  · intro eq
    have val := congrArg BitVec.toNat eq
    norm_num at val
    omega

theorem core_loop_safe (a : Word) (ha : CoreAddress a) : a ∉ loopWrites := by
  have values := core_values a ha
  simp only [loopWrites,List.mem_cons,List.not_mem_nil,or_false]
  intro h
  rcases h with h|h|h|h|h <;>
    have val := congrArg BitVec.toNat h <;> norm_num at val <;> omega

/-- Lift the concrete parent-node execution to its retained memory frame. -/
theorem parent_nodes_frame (hash : Hash) (s : MachineState) (k : Fin 8)
    (pc : s.pc=0x2040) (ctrl : Controls s k.val 0)
    (n : Nat) (bound : n≤width (k.val+1)) (a : Word) (ha : CoreAddress a) :
    (nodes hash s n).getMem a=s.getMem a := by
  induction n with
  | zero => rw [nodes]
  | succ n ih =>
    obtain ⟨_,current,_⟩ := nodes_execution hash s k pc ctrl n (by omega)
    obtain ⟨sourceEnd,targetEnd,targetBound,baseAlign,targetAlign,baseAbove,targetAbove,positive,small,twice,half,total⟩ := layout k
    obtain ⟨low,outside,notNode⟩ := core_node_safe a ha
    rw [nodes,next_control hash (nodes hash s n) (cacheBase (k.val+1)) n
      current.target current.node targetAbove (by omega) a low outside notNode]
    exact ih (by omega)

/-- Parent-level execution, retaining all forest control words and selectors. -/
theorem parent_level_execution (hash : Hash) (s : MachineState) (k : Fin 8)
    (pc : s.pc=0x2030) (ctrl : LevelControls s k.val) :
    ∃ t, Trace hash SphincsMaskedImages.sign s (39+125*width (k.val+1))
      (39+140*width (k.val+1)) (width (k.val+1)) (2*width (k.val+1)) t ∧
      LevelControls t (k.val+1) ∧ t.pc=(if k.val+1=8 then 0x22c0 else 0x2030) ∧
      ∀ a, CoreAddress a → t.getMem a=s.getMem a := by
  have entryCtrl := levelEntry_controls s k.val ctrl
  have entryPc := levelEntry_pc s pc
  obtain ⟨run,done,loc⟩ := nodes_execution hash (levelEntry s) k entryPc entryCtrl
    (width (k.val+1)) (by omega)
  let mid := nodes hash (levelEntry s) (width (k.val+1))
  have here : mid.pc=0x2234 := by simpa using loc
  refine ⟨levelFinish mid,?_,levelFinish_controls mid k done,levelFinish_pc mid k here done.level,?_⟩
  · have trace := (levelEntry_block s pc).trace.trans (run.trans (levelFinish_block mid here).trace)
    convert trace using 1 <;> omega
  · intro a ha
    rw [levelFinish_frame mid a (core_loop_safe a ha)]
    change (nodes hash (levelEntry s) (width (k.val+1))).getMem a=s.getMem a
    rw [parent_nodes_frame hash (levelEntry s) k entryPc entryCtrl _ (by omega) a ha]
    exact levelEntry_frame s a (core_node_safe a ha).2.2

theorem parent_levels_execution (hash : Hash) (s : MachineState)
    (pc : s.pc=0x2030) (ctrl : LevelControls s 0) (n : Nat) (bound : n≤8) :
    ∃ t, Trace hash SphincsMaskedImages.sign s (39*n+125*totalNodes n)
      (39*n+140*totalNodes n) (totalNodes n) (2*totalNodes n) t ∧
      LevelControls t n ∧ t.pc=(if n=8 then 0x22c0 else 0x2030) ∧
      ∀ a, CoreAddress a → t.getMem a=s.getMem a := by
  induction n with
  | zero => exact ⟨s,Trace.refl _,ctrl,pc,by intro _ _;rfl⟩
  | succ n ih =>
    obtain ⟨mid,first,midCtrl,midPc,frame⟩ := ih (by omega)
    have here : mid.pc=0x2030 := by simpa only [if_neg (show n≠8 by omega)] using midPc
    let k : Fin 8 := ⟨n,by omega⟩
    obtain ⟨t,last,done,loc,kept⟩ := parent_level_execution hash mid k here midCtrl
    refine ⟨t,?_,done,loc,?_⟩
    · have total : totalNodes (n+1)=totalNodes n+width (n+1) := (layout k).2.2.2.2.2.2.2.2.2.2.2
      have trace := first.trans last
      dsimp [k] at trace
      rw [total]
      convert trace using 1 <;> omega
    · intro a ha;rw [kept a ha,frame a ha]

/-- Unconditional parent block with the frame needed by the forest tail. -/
theorem parents_execution_framed (hash : Hash) (s : MachineState) (pc : s.pc=0x1fe8) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 32205 36030 255 510 t ∧
      t.pc=0x22c0 ∧ t.getMem 0x43068=0x527d8 ∧
      ∀ a, CoreAddress a → t.getMem a=s.getMem a := by
  obtain ⟨t,run,ctrl,loc,frame⟩ := parent_levels_execution hash (init s)
    (init_pc s pc) (init_controls s) 8 (by decide)
  refine ⟨t,(init_block s pc).trace.trans run,by simpa using loc,ctrl.base,?_⟩
  intro a ha
  rw [frame a ha,init_frame s a (core_loop_safe a ha)]

/-- The body contract is discharged for arbitrary oracle/memory contents. -/
theorem body_execution (hash : Hash) : SphincsMaskedSignForestTail.BodyExecution hash := by
  intro tree selected s pc leaf counter pointer selector
  obtain ⟨mid,leaves,midPc,_,leafFrame⟩ := leaves_execution hash s pc leaf 256 (by decide)
  have here : mid.pc=0x1fe8 := by simpa using midPc
  obtain ⟨t,parents,done,root,parentFrame⟩ := parents_execution_framed hash mid here
  have frame (a : Word) (ha : CoreAddress a) : t.getMem a=s.getMem a :=
    (parentFrame a ha).trans (leafFrame a ha)
  refine ⟨t,leaves.trans parents,done,root,
    (frame _ (by decide)).trans counter,(frame _ (by decide)).trans pointer,
    (frame _ (by decide)).trans selector,?_⟩
  intro a ha
  apply frame
  rcases ha with h|h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- Exact whole-forest execution for every oracle and every incoming state.
    The only premise is the successful-grinding exit PC; no query identity,
    signing-secret assumption, or semantic body contract is required. -/
theorem forest_execution (hash : Hash) (s : MachineState) (pc : s.pc=0x1cc8) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 1915509 2142908 18433 30729 t ∧ t.pc=0x2764 :=
  SphincsMaskedSignForestTail.forest_execution hash (body_execution hash) s pc

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestExecution.leaf_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_prefix

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestExecution.leaf_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestExecution.leaves_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaves_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestExecution.parent_nodes_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parent_nodes_frame

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestExecution.parent_level_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parent_level_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestExecution.parent_levels_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parent_levels_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestExecution.parents_execution_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parents_execution_framed

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestExecution.body_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms body_execution

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestExecution.forest_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forest_execution

end SigGolfCandidate.SphincsMaskedSignForestExecution
