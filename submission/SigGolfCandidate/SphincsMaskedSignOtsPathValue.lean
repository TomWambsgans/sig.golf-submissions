import SigGolfCandidate.SphincsMaskedSignOtsPathFinish
import RiscvZkvm.Rv64.Logic.ByteOps
import SigGolfCandidate.SphincsVerifierWotsDecodeData

namespace SigGolfCandidate.SphincsMaskedSignOtsPathValue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedSignOtsParents SphincsMaskedSignOtsTree SphincsMaskedSignOtsPath
open SphincsMaskedSignOtsPathSetup SphincsMaskedSignOtsPathSibling SphincsMaskedSignOtsPathFinish
open SphincsMaskedSignOtsShift SphincsMaskedKeygenPrefix
open SphincsSecurity SphincsBridge SphincsVerifierCopy SphincsVerifierFtsRootCopy SphincsMaskedChainDomain
open SphincsVerifierWotsDecode SphincsVerifierWotsDecodeData SphincsVerifierMessageCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- An emitted lower-layer sibling is the abstract seeded authentication node,
not merely a copy of an unspecified cache cell. -/
theorem copied_path_value (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (treeIdx : TreeIndex)
    (selected : LeafIndex) (level : Fin (Levels.height location)) (pointer : Nat)
    (pc : s.pc=0x1938+SphincsMaskedSignOtsParents.delta location)
    (ctrl : PathControls location s level.val (selected.val/2^level.val) pointer)
    (bitBound : selected.val/2^level.val < Levels.width location level.val)
    (pointerBound : pointer+20≤0x40000) (pointerAlign : pointer%4=0)
    (cache : ∀ l,l ≤ Levels.height location → ∀ node,node<Levels.width location l →
      Words20 s (Levels.cacheBase location l+20*node)
        (treeValue hash parameter seed (signerLayer location) treeIdx l node)) :
    let pathLevel : Fin (layerHeight (signerLayer location)) :=
      ⟨level.val,by rw [←signerLayer_height]; exact level.isLt⟩
    Words20 (copyRootState (setupState location s)) pointer
      (evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.treePath parameter (signerLayer location) treeIdx seed selected :
          OracleComp SphincsSecurity.HashSpec (Fin (layerHeight (signerLayer location)) → Digest)) pathLevel) := by
  let pathLevel : Fin (layerHeight (signerLayer location)) :=
    ⟨level.val,by rw [←signerLayer_height]; exact level.isLt⟩
  have sibling := sibling_in_width location level (selected.val/2^level.val) bitBound
  have abstract : treeValue hash parameter seed (signerLayer location) treeIdx level.val
      ((selected.val/2^level.val) ^^^ 1) =
      evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.treePath parameter (signerLayer location) treeIdx seed selected :
          OracleComp SphincsSecurity.HashSpec (Fin (layerHeight (signerLayer location)) → Digest)) pathLevel := by
    have ev := SphincsSecurity.Completeness.eval_treePath (adaptOracle hash)
      parameter (signerLayer location) treeIdx seed selected pathLevel
    simpa [treeValue,SphincsSecurity.Completeness.node,pathLevel] using ev.symm
  dsimp only
  intro i
  have emitted := (copy_sibling location s level (selected.val/2^level.val) pointer
    pc ctrl bitBound pointerBound pointerAlign).2 i
  have stored := cache level.val (by omega) ((selected.val/2^level.val) ^^^ 1) sibling i
  exact emitted.trans (by simpa only [abstract] using stored)

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.copied_path_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copied_path_value

theorem byteOffset_mod (a : Word) : byteOffset a = a.toNat % 8 := by
  simp only [byteOffset, BitVec.toNat_and, BitVec.toNat_ofNat]
  simpa using (Nat.and_two_pow_sub_one_eq_mod a.toNat 3)

theorem word_before_distinct (read write : Nat)
    (before : read+4≤write) (within : write<0x40000)
    (readAlign : read%4=0) (writeAlign : write%4=0) :
    alignToDword (BitVec.ofNat 64 write) ≠ alignToDword (BitVec.ofNat 64 read) ∨
    byteOffset (BitVec.ofNat 64 write)/4 ≠ byteOffset (BitVec.ofNat 64 read)/4 := by
  by_contra h
  push Not at h
  obtain ⟨hcell,hpos⟩ := h
  have hread : read<2^64 := by omega
  have hwrite : write<2^64 := by omega
  norm_num at hread hwrite
  have rw := congrArg BitVec.toNat (RiscvZkvm.Rv64.alignToDword_add_byteOffset (BitVec.ofNat 64 read))
  have ww := congrArg BitVec.toNat (RiscvZkvm.Rv64.alignToDword_add_byteOffset (BitVec.ofNat 64 write))
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hread, Nat.mod_eq_of_lt hwrite] at rw ww
  have rbase : (alignToDword (BitVec.ofNat 64 read)).toNat ≤ read := by
    unfold alignToDword
    rw [BitVec.toNat_and]
    have := (Nat.and_le_left :
      (BitVec.ofNat 64 read).toNat &&& (~~~(7#64)).toNat ≤ (BitVec.ofNat 64 read).toNat)
    have hx : (BitVec.ofNat 64 read).toNat=read := by
      simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hread]
    omega
  have wbase : (alignToDword (BitVec.ofNat 64 write)).toNat ≤ write := by
    unfold alignToDword
    rw [BitVec.toNat_and]
    have := (Nat.and_le_left :
      (BitVec.ofNat 64 write).toNat &&& (~~~(7#64)).toNat ≤ (BitVec.ofNat 64 write).toNat)
    have hx : (BitVec.ofNat 64 write).toNat=write := by
      simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hwrite]
    omega
  have hrl := byteOffset_lt_8 (addr := BitVec.ofNat 64 read)
  have hwl := byteOffset_lt_8 (addr := BitVec.ofNat 64 write)
  have rsum : (alignToDword (BitVec.ofNat 64 read)).toNat + byteOffset (BitVec.ofNat 64 read) < 2^64 := by omega
  have wsum : (alignToDword (BitVec.ofNat 64 write)).toNat + byteOffset (BitVec.ofNat 64 write) < 2^64 := by omega
  have hrl64 : byteOffset (BitVec.ofNat 64 read) < 2^64 := by omega
  have hwl64 : byteOffset (BitVec.ofNat 64 write) < 2^64 := by omega
  simp only [Nat.mod_eq_of_lt hrl64] at rw
  simp only [Nat.mod_eq_of_lt hwl64] at ww
  simp only [Nat.mod_eq_of_lt rsum] at rw
  simp only [Nat.mod_eq_of_lt wsum] at ww
  have hr : byteOffset (BitVec.ofNat 64 read)%4=0 := by
    rw [byteOffset_mod]
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hread]
    omega
  have hw : byteOffset (BitVec.ofNat 64 write)%4=0 := by
    rw [byteOffset_mod]
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hwrite]
    omega
  have heq := congrArg BitVec.toNat hcell
  omega


theorem copied_before_word (location : Fin 5) (s : MachineState)
    (level bit pointer read : Nat)
    (ctrl : SphincsMaskedSignOtsPath.PathControls location s level bit pointer)
    (pointerBound : pointer+20≤0x40000)
    (readBefore : read+4≤pointer) (readAlign : read%4=0)
    (pointerAlign : pointer%4=0) :
    (SphincsVerifierCopy.copyRootState (SphincsMaskedSignOtsPathSetup.setupState location s)).getWord32
      (BitVec.ofNat 64 read) = s.getWord32 (BitVec.ofNat 64 read) := by
  have regs := SphincsMaskedSignOtsPathSetup.setup_regs location s level bit pointer ctrl
  rw [SphincsVerifierMessageFields.copyRoot_getWord32_frame]
  · simp only [MachineState.getWord32,SphincsMaskedSignOtsPathSetup.setup_frame]
  · intro offset
    rw [regs.2]
    have addr : BitVec.ofNat 64 pointer + signExtend12 (4#12 * BitVec.ofNat 12 offset.val) =
        BitVec.ofNat 64 (pointer+4*offset.val) := by
      fin_cases offset <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [addr]
    have before : read+4≤pointer+4*offset.val := by omega
    have within : pointer+4*offset.val<0x40000 := by have := offset.isLt;omega
    have align : (pointer+4*offset.val)%4=0 := by omega
    exact word_before_distinct read (pointer+4*offset.val) before within readAlign align



theorem finish_low_word (location : Fin 5) (s : MachineState)
    (read : Nat) (readBound : read<0x40000) :
    (SphincsMaskedSignOtsPathFinish.finished location s).getWord32 (BitVec.ofNat 64 read) =
      s.getWord32 (BitVec.ofNat 64 read) := by
  simp only [MachineState.getWord32]
  rw [SphincsMaskedSignOtsPathFinish.finish_frame]
  have bound := (SphincsMaskedSignForestTail.cell_bounds read 0 0x40000
    (by decide) (by omega) readBound (by decide)).2
  simp only [SphincsMaskedSignOtsPathFinish.controlWrites,List.mem_cons,List.not_mem_nil,
    not_or,not_false_eq_true,and_true]
  repeat' constructor
  all_goals
    intro h
    rw [h] at bound
    norm_num at bound

theorem pathNext_before_word (location : Fin 5) (s : MachineState)
    (level bit pointer read : Nat)
    (ctrl : SphincsMaskedSignOtsPath.PathControls location s level bit pointer)
    (pointerBound : pointer+20≤0x40000)
    (readBefore : read+4≤pointer) (readAlign : read%4=0)
    (pointerAlign : pointer%4=0) :
    (SphincsMaskedSignOtsPathFinish.pathNext location s).getWord32 (BitVec.ofNat 64 read) =
      s.getWord32 (BitVec.ofNat 64 read) := by
  rw [SphincsMaskedSignOtsPathFinish.pathNext,
    finish_low_word location _ read (by omega),
    copied_before_word location s level bit pointer read ctrl pointerBound
      readBefore readAlign pointerAlign]



theorem path_step_word (location : Fin 5) (s : MachineState)
    (level : Fin (SphincsMaskedSignOtsParents.Levels.height location))
    (bit pointer : Nat) (i : Fin 5)
    (pc : s.pc=0x1938+SphincsMaskedSignOtsParents.delta location)
    (ctrl : SphincsMaskedSignOtsPath.PathControls location s level.val bit pointer)
    (bitBound : bit<SphincsMaskedSignOtsParents.Levels.width location level.val)
    (pointerBound : pointer+20≤0x40000) (pointerAlign : pointer%4=0) :
    (SphincsMaskedSignOtsPathFinish.pathNext location s).getWord32
      (BitVec.ofNat 64 (pointer+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64
        (SphincsMaskedSignOtsParents.Levels.cacheBase location level.val+
          20*(bit ^^^ 1)+4*i.val)) := by
  rw [SphincsMaskedSignOtsPathFinish.pathNext,
    finish_low_word location _ (pointer+4*i.val) (by omega)]
  exact (SphincsMaskedSignOtsPathSibling.copy_sibling location s level bit pointer
    pc ctrl bitBound pointerBound pointerAlign).2 i


/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.path_step_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms path_step_word

theorem cache_word_frame (location : Fin 5) (level : Fin (Levels.height location))
    (bit : Nat) (bitBound : bit<Levels.width location level.val)
    (s mid : MachineState)
    (frame : ∀ a, OtsPathRetained a → mid.getMem a=s.getMem a)
    (i : Fin 5) :
    mid.getWord32 (BitVec.ofNat 64
      (Levels.cacheBase location level.val+20*(bit ^^^ 1)+4*i.val)) =
    s.getWord32 (BitVec.ofNat 64
      (Levels.cacheBase location level.val+20*(bit ^^^ 1)+4*i.val)) := by
  obtain ⟨_,sourceAbove,sourceBound⟩ := sibling_source location level bit bitBound
  let source := Levels.cacheBase location level.val+20*(bit ^^^ 1)
  have inBounds := SphincsMaskedSignForestTail.cell_bounds (source+4*i.val)
    0x50000 0x53000 (by decide) (by omega) (by have := i.isLt;omega) (by decide)
  have retained : OtsPathRetained (alignToDword (BitVec.ofNat 64 (source+4*i.val))) := by
    constructor
    · omega
    · simp only [controlWrites,List.mem_cons,List.not_mem_nil,
        not_or,not_false_eq_true,and_true]
      repeat' constructor
      all_goals
        intro h
        rw [h] at inBounds
        norm_num at inBounds
  simp only [MachineState.getWord32]
  exact congrArg (fun w => extractWord32 w
    (byteOffset (BitVec.ofNat 64 (source+4*i.val))/4)) (frame _ retained)

/-- All sibling lanes in a completed prefix equal the original cached nodes. -/
theorem paths_execution_data (location : Fin 5) (s : MachineState)
    (selected pointer : Nat)
    (pc : s.pc=0x1938+delta location)
    (ctrl : PathControls location s 0 selected pointer)
    (selectedBound : selected<Levels.width location 0)
    (pointerBound : pointer+20*Levels.height location≤0x40000)
    (aligned : pointer%4=0)
    (n : Nat) (bound : n≤Levels.height location) :
    ∃ t, OrdinarySteps SphincsMaskedImages.sign s (70*n) t ∧
      PathControls location t n (selected/2^n) (pointer+20*n) ∧
      t.pc=(if n=Levels.height location then 0x1a50+delta location
        else 0x1938+delta location) ∧
      (∀ a, OtsPathRetained a → t.getMem a=s.getMem a) ∧
      (∀ j : Fin n, ∀ i : Fin 5,
        t.getWord32 (BitVec.ofNat 64 (pointer+20*j.val+4*i.val)) =
        s.getWord32 (BitVec.ofNat 64
          (Levels.cacheBase location j.val+20*((selected/2^j.val) ^^^ 1)+4*i.val))) := by
  induction n with
  | zero =>
      have positive : 0<Levels.height location := by fin_cases location <;> decide
      refine ⟨s,OrdinarySteps.refl _,?_,?_,?_,?_⟩
      · simpa using ctrl
      · simpa only [if_neg (show 0≠Levels.height location by omega)] using pc
      · intro _ _;rfl
      · intro j; exact Fin.elim0 j
  | succ n ih =>
      obtain ⟨mid,first,midCtrl,midPc,frame,values⟩ := ih (by omega)
      have here : mid.pc=0x1938+delta location := by
        simpa only [if_neg (show n≠Levels.height location by omega)] using midPc
      let level : Fin (Levels.height location) := ⟨n,by omega⟩
      have bitBound := divided_selector_bound location selected selectedBound level
      have currentBound : pointer+20*n+20≤0x40000 := by omega
      have currentAlign : (pointer+20*n)%4=0 := by omega
      obtain ⟨step,done,loc⟩ := path_step location mid level (selected/2^n)
        (pointer+20*n) here midCtrl bitBound currentBound currentAlign
      refine ⟨pathNext location mid,?_,?_,loc,?_,?_⟩
      · simpa only [Nat.mul_add,Nat.mul_one,Nat.add_comm] using first.append step
      · convert done using 1
        · simp [Nat.pow_succ,Nat.div_div_eq_div_mul]
        · omega
      · intro a ha
        rw [pathNext_frame location mid n (selected/2^n) (pointer+20*n)
          midCtrl currentBound a ha,frame a ha]
      · intro j i
        by_cases hj : j.val<n
        · let old : Fin n := ⟨j.val,hj⟩
          have priorBound : pointer+20*j.val+4*i.val+4≤pointer+20*n := by
            have := i.isLt
            omega
          rw [pathNext_before_word location mid n (selected/2^n) (pointer+20*n)
            (pointer+20*j.val+4*i.val) midCtrl currentBound priorBound
            (by omega) currentAlign]
          exact values old i
        · have eq : j.val=n := by have := j.isLt;omega
          rw [eq]
          rw [show pointer+20*n+4*i.val=(pointer+20*n)+4*i.val by omega,
            path_step_word location mid level (selected/2^n) (pointer+20*n) i
              here midCtrl bitBound currentBound currentAlign]
          exact cache_word_frame location level (selected/2^n) bitBound s mid frame i
/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.paths_execution_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paths_execution_data

/-- Every emitted path digest refines the seeded Merkle authentication path. -/
theorem paths_abstract (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (treeIdx : TreeIndex)
    (selected : LeafIndex) (pointer : Nat)
    (pc : s.pc=0x1938+delta location)
    (ctrl : PathControls location s 0 selected.val pointer)
    (selectedBound : selected.val<Levels.width location 0)
    (pointerBound : pointer+20*Levels.height location≤0x40000)
    (aligned : pointer%4=0)
    (cache : ∀ l,l ≤ Levels.height location → ∀ node,node<Levels.width location l →
      Words20 s (Levels.cacheBase location l+20*node)
        (treeValue hash parameter seed (signerLayer location) treeIdx l node))
    (n : Nat) (bound : n≤Levels.height location) :
    ∃ t, OrdinarySteps SphincsMaskedImages.sign s (70*n) t ∧
      PathControls location t n (selected.val/2^n) (pointer+20*n) ∧
      t.pc=(if n=Levels.height location then 0x1a50+delta location
        else 0x1938+delta location) ∧
      ∀ j : Fin n,
        let pathLevel : Fin (layerHeight (signerLayer location)) :=
          ⟨j.val,by rw [←signerLayer_height]; exact lt_of_lt_of_le j.isLt bound⟩
        Words20 t (pointer+20*j.val)
          (evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
            (Seeded.treePath parameter (signerLayer location) treeIdx seed selected :
              OracleComp SphincsSecurity.HashSpec
                (Fin (layerHeight (signerLayer location)) → Digest)) pathLevel) := by
  obtain ⟨t,trace,controls,endPc,_,data⟩ := paths_execution_data location s selected.val pointer
    pc ctrl selectedBound pointerBound aligned n bound
  refine ⟨t,trace,controls,endPc,?_⟩
  intro j
  dsimp only
  let level : Fin (Levels.height location) := ⟨j.val,by omega⟩
  let pathLevel : Fin (layerHeight (signerLayer location)) :=
    ⟨j.val,by rw [←signerLayer_height]; omega⟩
  have bitBound := divided_selector_bound location selected.val selectedBound level
  have sibling := sibling_in_width location level (selected.val/2^level.val) bitBound
  have abstract : treeValue hash parameter seed (signerLayer location) treeIdx level.val
      ((selected.val/2^level.val) ^^^ 1) =
      evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.treePath parameter (signerLayer location) treeIdx seed selected :
          OracleComp SphincsSecurity.HashSpec (Fin (layerHeight (signerLayer location)) → Digest)) pathLevel := by
    have ev := SphincsSecurity.Completeness.eval_treePath (adaptOracle hash)
      parameter (signerLayer location) treeIdx seed selected pathLevel
    simpa [treeValue,SphincsSecurity.Completeness.node,pathLevel,level] using ev.symm
  intro i
  have emitted := data j i
  have stored := cache level.val (by omega) ((selected.val/2^level.val) ^^^ 1) sibling i
  exact emitted.trans (by simpa only [abstract,level,pathLevel] using stored)
/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.paths_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paths_abstract

theorem initialized_frame (location : Fin 5) (s : MachineState) (a : Word)
    (outside : a∉controlWrites) :
    (initialized location s).getMem a=s.getMem a := by
  simp only [controlWrites,List.mem_cons,List.not_mem_nil,not_or,
    not_false_eq_true,and_true] at outside
  obtain ⟨h0,h1,h2,h3,h4⟩:=outside
  simp [initialized,initCode,runSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    h0,h1,h2,h3,h4]



theorem cache_node_bounds (location : Fin 5) (level node : Nat)
    (levelBound : level≤Levels.height location)
    (nodeBound : node<Levels.width location level) :
    0x50000≤Levels.cacheBase location level+20*node ∧
      Levels.cacheBase location level+20*node+20≤0x53000 := by
  fin_cases location <;>
    simp [Levels.height] at levelBound <;>
    interval_cases level <;>
    simp [Levels.height,Levels.width,Levels.cacheBase] at * <;> omega



def entryState (location : Fin 5) (s : MachineState) : MachineState :=
  shift (delta location) (initialized location (s.setPC 0x18d8))

theorem entry_mem_frame (location : Fin 5) (s : MachineState) (a : Word)
    (high : 0x50000≤a.toNat) :
    (entryState location s).getMem a=s.getMem a := by
  simp only [entryState,shift_mem]
  rw [initialized_frame]
  · rfl
  · simp only [controlWrites,List.mem_cons,List.not_mem_nil,
      not_or,not_false_eq_true,and_true]
    refine ⟨?_,?_,?_,?_,?_⟩
    all_goals
      intro h
      rw [h] at high
      norm_num at high

theorem entry_cache (location : Fin 5) (s : MachineState)
    (hash : Hash) (parameter : PublicParameter) (seed : MasterSeed) (treeIdx : TreeIndex)
    (cache : ∀ l,l ≤ Levels.height location → ∀ node,node<Levels.width location l →
      Words20 s (Levels.cacheBase location l+20*node)
        (treeValue hash parameter seed (signerLayer location) treeIdx l node)) :
    ∀ l,l ≤ Levels.height location → ∀ node,node<Levels.width location l →
      Words20 (entryState location s) (Levels.cacheBase location l+20*node)
        (treeValue hash parameter seed (signerLayer location) treeIdx l node) := by
  intro l lb node nb i
  have bounds := cache_node_bounds location l node lb nb
  let source := Levels.cacheBase location l+20*node
  have cell := SphincsMaskedSignForestTail.cell_bounds (source+4*i.val)
    0x50000 0x53000 (by decide) (by omega) (by have := i.isLt;omega) (by decide)
  have saved := cache l lb node nb i
  simp only [MachineState.getWord32] at saved ⊢
  rw [entry_mem_frame location s _ cell.1]
  exact saved



theorem entry_pc (location : Fin 5) (s : MachineState) :
    (entryState location s).pc=0x1938+delta location := by
  rw [entryState,shift_pc,initialized_pc location (s.setPC 0x18d8) rfl]

theorem entry_controls (location : Fin 5) (s : MachineState) (selected : Nat)
    (hs : s.getMem 0x430a8=BitVec.ofNat 64 selected) :
    PathControls location (entryState location s) 0 selected (pathPointer location) := by
  have controls := initialized_controls location (s.setPC 0x18d8) selected (by simpa using hs)
  constructor
  · simpa only [entryState,shift_mem] using controls.base
  · simpa only [entryState,shift_mem] using controls.count
  · simpa only [entryState,shift_mem] using controls.level
  · simpa only [entryState,shift_mem] using controls.bit
  · simpa only [entryState,shift_mem] using controls.pointer

theorem pointer_height_bound (location : Fin 5) :
    pathPointer location+20*Levels.height location≤0x40000 := by
  fin_cases location <;> decide

/-- The real path initializer followed by all sibling copies. -/
theorem path_complete (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (treeIdx : TreeIndex)
    (selected : LeafIndex)
    (pc : s.pc=0x18d8+delta location)
    (selectedMem : s.getMem 0x430a8=BitVec.ofNat 64 selected.val)
    (selectedBound : selected.val<Levels.width location 0)
    (cache : ∀ l,l ≤ Levels.height location → ∀ node,node<Levels.width location l →
      Words20 s (Levels.cacheBase location l+20*node)
        (treeValue hash parameter seed (signerLayer location) treeIdx l node)) :
    ∃ t, OrdinarySteps SphincsMaskedImages.sign s (24+70*Levels.height location) t ∧
      t.pc=0x1a50+delta location ∧
      ∀ j : Fin (Levels.height location),
        let pathLevel : Fin (layerHeight (signerLayer location)) :=
          ⟨j.val,by rw [←signerLayer_height]; exact j.isLt⟩
        Words20 t (pathPointer location+20*j.val)
          (evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
            (Seeded.treePath parameter (signerLayer location) treeIdx seed selected :
              OracleComp SphincsSecurity.HashSpec
                (Fin (layerHeight (signerLayer location)) → Digest)) pathLevel) := by
  have first := init_block location s pc
  have controls := entry_controls location s selected.val selectedMem
  have cached := entry_cache location s hash parameter seed treeIdx cache
  obtain ⟨t,second,_,endPc,values⟩ := paths_abstract location hash (entryState location s)
    parameter seed treeIdx selected (pathPointer location)
    (entry_pc location s) controls selectedBound (pointer_height_bound location)
    (pointer_bound location).1 cached (Levels.height location) (le_refl _)
  refine ⟨t,?_,?_,?_⟩
  · exact first.append second
  · simpa using endPc
  · intro j
    simpa only using values j

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.path_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms path_complete

/-- A completed lower-layer subtree feeds its exact certified authentication path. -/
theorem subtree_root_path (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (treeIdx : TreeIndex)
    (selected : LeafIndex)
    (pc : s.pc=0x111c+chainDelta location)
    (counter : s.getMem 0x43020=0)
    (ctx : SphincsMaskedSignOtsParents.KeyContext s parameter seed (signerLayer location) treeIdx)
    (selectedMem : s.getMem 0x430a8=BitVec.ofNat 64 selected.val)
    (selectedBound : selected.val<Levels.width location 0) :
    ∃ t, Trace hash SphincsMaskedImages.sign s
      (41220*SphincsMaskedSignOtsTree.Finish.width location+33+39*Levels.height location+
        124*Levels.totalNodes location (Levels.height location)+
        (24+70*Levels.height location))
      (44683*SphincsMaskedSignOtsTree.Finish.width location+33+39*Levels.height location+
        139*Levels.totalNodes location (Levels.height location)+
        (24+70*Levels.height location))
      (417*SphincsMaskedSignOtsTree.Finish.width location+
        Levels.totalNodes location (Levels.height location))
      (485*SphincsMaskedSignOtsTree.Finish.width location+
        2*Levels.totalNodes location (Levels.height location)) t ∧
      t.pc=0x1a50+delta location ∧
      ∀ j : Fin (Levels.height location),
        let pathLevel : Fin (layerHeight (signerLayer location)) :=
          ⟨j.val,by rw [←signerLayer_height]; exact j.isLt⟩
        Words20 t (pathPointer location+20*j.val)
          (evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
            (Seeded.treePath parameter (signerLayer location) treeIdx seed selected :
              OracleComp SphincsSecurity.HashSpec
                (Fin (layerHeight (signerLayer location)) → Digest)) pathLevel) := by
  obtain ⟨mid,rootTrace,midPc,_,_,cache,retained⟩ :=
    subtree_root location hash s parameter seed treeIdx pc counter ctx
  have midSelected : mid.getMem 0x430a8=BitVec.ofNat 64 selected.val := by
    rw [retained 0x430a8 (by simp [SphincsMaskedSignOtsTree.Frame.Retained,
      SphincsMaskedSignOtsTree.Frame.controls]) (by decide) (by decide) (by decide)]
    exact selectedMem
  obtain ⟨t,pathTrace,endPc,values⟩ := path_complete location hash mid parameter seed treeIdx
    selected midPc midSelected selectedBound cache
  refine ⟨t,?_,endPc,values⟩
  exact rootTrace.trans pathTrace.trace
/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.subtree_root_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms subtree_root_path

/-- The twenty instructions after the path transfer the selected leaf into
WOTS signing controls, reset the retry counter and position, and set INDEX. -/
def otsPreludeCode : List (Word × Instr) := [
  (0x1a50,.LUI .x28 67),
  (0x1a54,.ADDI .x28 .x28 168),
  (0x1a58,.LD .x6 .x28 0),
  (0x1a5c,.LUI .x28 67),
  (0x1a60,.ADDI .x28 .x28 32),
  (0x1a64,.SD .x28 .x6 0),
  (0x1a68,.ADDI .x6 .x0 0),
  (0x1a6c,.LUI .x28 67),
  (0x1a70,.ADDI .x28 .x28 184),
  (0x1a74,.SD .x28 .x6 0),
  (0x1a78,.ADDI .x6 .x0 0),
  (0x1a7c,.LUI .x28 67),
  (0x1a80,.ADDI .x28 .x28 16),
  (0x1a84,.SD .x28 .x6 0),
  (0x1a88,.LUI .x28 67),
  (0x1a8c,.ADDI .x28 .x28 32),
  (0x1a90,.LD .x6 .x28 0),
  (0x1a94,.LUI .x28 67),
  (0x1a98,.ADDI .x28 .x28 24),
  (0x1a9c,.SD .x28 .x6 0)]

def otsPreludeState (s : MachineState) : MachineState := runSchedule otsPreludeCode s

def otsPrelude (location : Fin 5) (s : MachineState) : MachineState :=
  shift (delta location) (otsPreludeState (s.setPC 0x1a50))

theorem otsPrelude_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (660+offset location) otsPreludeCode := by
  fin_cases location <;> rfl

theorem otsPrelude_encoded (location : Fin 5) : ∀ e∈otsPreludeCode,
    instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  apply encoded_of_block _ (660+offset location) _ _ (otsPrelude_image location)
  · have h := SphincsMaskedSignOtsParents.offset_bound location
    change 660+offset location+20≤11000
    omega
  · intro i
    have h : ∀ i : Fin otsPreludeCode.length,
        otsPreludeCode[i.val].1=BitVec.ofNat 64 (0x1a50+4*i.val) := by
      intro j
      fin_cases j <;> rfl
    rw [h i,delta,←BitVec.ofNat_add]
    congr 1
    omega

theorem otsPrelude_supported : ∀ e∈otsPreludeCode,Supported e.2 := by decide

theorem otsPrelude_checked (s : MachineState) (pc : s.pc=0x1a50) :
    Checked otsPreludeCode s := by
  simp [otsPreludeCode,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem otsPrelude_block (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x1a50+delta location) :
    OrdinarySteps SphincsMaskedImages.sign s 20 (otsPrelude location s) := by
  have trace := block_shift SphincsMaskedImages.sign (delta location) otsPreludeCode
    otsPrelude_supported (otsPrelude_encoded location) (s.setPC 0x1a50)
    (otsPrelude_checked (s.setPC 0x1a50) rfl)
  rw [SphincsMaskedSignOtsDomain.rebase_eq _ _ s pc] at trace
  have len : otsPreludeCode.length=20 := rfl
  simpa only [otsPrelude,otsPreludeState,len] using trace

theorem otsPrelude_pc (location : Fin 5) (s : MachineState) :
    (otsPrelude location s).pc=0x1aa0+delta location := by
  simp [otsPrelude,otsPreludeState,otsPreludeCode,runSchedule,execInstrBr,
    signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem otsPrelude_controls (location : Fin 5) (s : MachineState) (selected : Nat)
    (hs : s.getMem 0x430a8=BitVec.ofNat 64 selected) :
    (otsPrelude location s).getMem 0x43020=BitVec.ofNat 64 selected ∧
    (otsPrelude location s).getMem 0x430b8=0 ∧
    (otsPrelude location s).getMem 0x43010=0 ∧
    (otsPrelude location s).getMem 0x43018=BitVec.ofNat 64 selected := by
  change s.getMem 0x430a8#64 = _ at hs
  simp [otsPrelude,otsPreludeState,otsPreludeCode,runSchedule,execInstrBr,
    signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,hs]


def otsPreludeWrites : List Word :=
  [0x43020#64,0x430b8#64,0x43010#64,0x43018#64]

theorem otsPrelude_frame (location : Fin 5) (s : MachineState) (a : Word)
    (outside : a∉otsPreludeWrites) :
    (otsPrelude location s).getMem a=s.getMem a := by
  simp only [otsPrelude,shift_mem]
  simp only [otsPreludeWrites,List.mem_cons,List.not_mem_nil,
    not_or,not_false_eq_true,and_true] at outside
  obtain ⟨h0,h1,h2,h3⟩:=outside
  simp [otsPreludeState,otsPreludeCode,runSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3]

theorem otsPrelude_low_word (location : Fin 5) (s : MachineState)
    (read : Nat) (readBound : read<0x40000) :
    (otsPrelude location s).getWord32 (BitVec.ofNat 64 read) =
      s.getWord32 (BitVec.ofNat 64 read) := by
  have cell := (SphincsMaskedSignForestTail.cell_bounds read 0 0x40000
    (by decide) (by omega) readBound (by decide)).2
  simp only [MachineState.getWord32]
  rw [otsPrelude_frame]
  simp only [otsPreludeWrites,List.mem_cons,List.not_mem_nil,
    not_or,not_false_eq_true,and_true]
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    intro h
    rw [h] at cell
    norm_num at cell

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.otsPrelude_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms otsPrelude_block

def otsHashPrepCode : List (Word × Instr) := [
  (0x1aa0, .LUI .x6 0x00045#20),
  (0x1aa4, .ADDI .x6 .x6 0xa00#12),
  (0x1aa8, .LUI .x7 0x00040#20),
  (0x1aac, .ADDI .x7 .x7 0x028#12),
  (0x1ab0, .LWU .x13 .x6 0x000#12),
  (0x1ab4, .SW .x7 .x13 0x000#12),
  (0x1ab8, .LWU .x13 .x6 0x004#12),
  (0x1abc, .SW .x7 .x13 0x004#12),
  (0x1ac0, .LWU .x13 .x6 0x008#12),
  (0x1ac4, .SW .x7 .x13 0x008#12),
  (0x1ac8, .LWU .x13 .x6 0x00c#12),
  (0x1acc, .SW .x7 .x13 0x00c#12),
  (0x1ad0, .LWU .x13 .x6 0x010#12),
  (0x1ad4, .SW .x7 .x13 0x010#12),
  (0x1ad8, .LUI .x6 0x00043#20),
  (0x1adc, .ADDI .x6 .x6 0x0b8#12),
  (0x1ae0, .LWU .x10 .x6 0x000#12),
  (0x1ae4, .LUI .x7 0x00040#20),
  (0x1ae8, .ADDI .x7 .x7 0x000#12),
  (0x1aec, .SW .x7 .x10 0x03c#12),
  (0x1af0, .ADDI .x6 .x0 0x401#12),
  (0x1af4, .LUI .x28 0x00043#20),
  (0x1af8, .ADDI .x28 .x28 0x000#12),
  (0x1afc, .LD .x7 .x28 0x000#12),
  (0x1b00, .SLLI .x7 .x7 0x10#6),
  (0x1b04, .ADD .x6 .x6 .x7),
  (0x1b08, .LUI .x7 0x00040#20),
  (0x1b0c, .ADDI .x7 .x7 0x000#12),
  (0x1b10, .SW .x7 .x6 0x000#12),
  (0x1b14, .LUI .x28 0x00043#20),
  (0x1b18, .ADDI .x28 .x28 0x010#12),
  (0x1b1c, .LD .x6 .x28 0x000#12),
  (0x1b20, .SW .x7 .x6 0x004#12),
  (0x1b24, .LUI .x28 0x00043#20),
  (0x1b28, .ADDI .x28 .x28 0x008#12),
  (0x1b2c, .LD .x6 .x28 0x000#12),
  (0x1b30, .SD .x7 .x6 0x008#12),
  (0x1b34, .LUI .x28 0x00043#20),
  (0x1b38, .ADDI .x28 .x28 0x018#12),
  (0x1b3c, .LD .x6 .x28 0x000#12),
  (0x1b40, .SW .x7 .x6 0x010#12),
  (0x1b44, .ADDI .x6 .x0 0x074#12),
  (0x1b48, .LUI .x7 0x00040#20),
  (0x1b4c, .ADDI .x7 .x7 0x014#12),
  (0x1b50, .LWU .x13 .x6 0x000#12),
  (0x1b54, .SW .x7 .x13 0x000#12),
  (0x1b58, .LWU .x13 .x6 0x004#12),
  (0x1b5c, .SW .x7 .x13 0x004#12),
  (0x1b60, .LWU .x13 .x6 0x008#12),
  (0x1b64, .SW .x7 .x13 0x008#12),
  (0x1b68, .LWU .x13 .x6 0x00c#12),
  (0x1b6c, .SW .x7 .x13 0x00c#12),
  (0x1b70, .LWU .x13 .x6 0x010#12),
  (0x1b74, .SW .x7 .x13 0x010#12),
  (0x1b78, .LUI .x10 0x00040#20),
  (0x1b7c, .ADDI .x10 .x10 0x000#12),
  (0x1b80, .ADDI .x11 .x0 0x200#12),
  (0x1b84, .LUI .x12 0x00042#20),
  (0x1b88, .ADDI .x12 .x12 0x000#12),
  (0x1b8c, .ADDI .x5 .x0 0x001#12)]

def otsHashPrepState (s : MachineState) : MachineState := runSchedule otsHashPrepCode s

def otsHashPrep (location : Fin 5) (s : MachineState) : MachineState :=
  shift (delta location) (otsHashPrepState (s.setPC 0x1aa0))

theorem otsHashPrep_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (680+offset location) otsHashPrepCode := by
  fin_cases location <;> rfl


theorem otsHashPrep_encoded (location : Fin 5) : ∀ e∈otsHashPrepCode,
    instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  apply encoded_of_block _ (680+offset location) _ _ (otsHashPrep_image location)
  · have h := SphincsMaskedSignOtsParents.offset_bound location
    change 680+offset location+60≤11000
    omega
  · intro i
    have h : ∀ i : Fin otsHashPrepCode.length,
        otsHashPrepCode[i.val].1=BitVec.ofNat 64 (0x1aa0+4*i.val) := by
      intro j
      fin_cases j <;> rfl
    rw [h i,delta,←BitVec.ofNat_add]
    congr 1
    omega

theorem otsHashPrep_supported : ∀ e∈otsHashPrepCode,Supported e.2 := by decide

theorem otsHashPrep_checked (s : MachineState) (pc : s.pc=0x1aa0) :
    Checked otsHashPrepCode s := by
  simp [otsHashPrepCode,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem otsHashPrep_block (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x1aa0+delta location) :
    OrdinarySteps SphincsMaskedImages.sign s 60 (otsHashPrep location s) := by
  have trace := block_shift SphincsMaskedImages.sign (delta location) otsHashPrepCode
    otsHashPrep_supported (otsHashPrep_encoded location) (s.setPC 0x1aa0)
    (otsHashPrep_checked (s.setPC 0x1aa0) rfl)
  rw [SphincsMaskedSignOtsDomain.rebase_eq _ _ s pc] at trace
  have len : otsHashPrepCode.length=60 := rfl
  simpa only [otsHashPrep,otsHashPrepState,len] using trace

theorem otsHashPrep_pc (location : Fin 5) (s : MachineState) :
    (otsHashPrep location s).pc=0x1b90+delta location := by
  simp [otsHashPrep,otsHashPrepState,otsHashPrepCode,runSchedule,execInstrBr,
    signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.otsHashPrep_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms otsHashPrep_block


theorem otsHashPrep_registers (location : Fin 5) (s : MachineState) :
    (otsHashPrep location s).getReg .x10 = 0x40000 ∧
    (otsHashPrep location s).getReg .x11 = 512 ∧
    (otsHashPrep location s).getReg .x12 = 0x42000 ∧
    (otsHashPrep location s).getReg .x5 = 1 := by
  simp [otsHashPrep,otsHashPrepState,otsHashPrepCode,runSchedule,execInstrBr,
    signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem otsHashPrep_hash_valid (location : Fin 5) (s : MachineState) :
    hashArgumentsValid (otsHashPrep location s)=true := by
  obtain ⟨src,bits,dst,_⟩:=otsHashPrep_registers location s
  simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]

theorem otsHashPrep_fetch (location : Fin 5) (s : MachineState) :
    fetch SphincsMaskedImages.sign (otsHashPrep location s)=some (.base .ECALL) := by
  rw [fetch_at,otsHashPrep_pc]
  fin_cases location <;> decide

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.otsHashPrep_hash_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms otsHashPrep_hash_valid


theorem otsHashPrep_hash_step (location : Fin 5) (hash : Hash) (s : MachineState) :
    Trace hash SphincsMaskedImages.sign (otsHashPrep location s) 1 8 1 1
      (writeHash (otsHashPrep location s) (hash (hashInput (otsHashPrep location s)))) := by
  have fetch := otsHashPrep_fetch location s
  have service := (otsHashPrep_registers location s).2.2.2
  have valid := otsHashPrep_hash_valid location s
  have len : (hashInput (otsHashPrep location s)).1=512 := by
    simp [hashInput,(otsHashPrep_registers location s).2.1]
  have step := Trace.hash (hash:=hash) (image:=SphincsMaskedImages.sign)
    (otsHashPrep location s) _ 0 0 0 0 fetch service valid (Trace.refl _)
  simpa only [len,show compressions 512=1 from by decide,Nat.zero_add] using step

/-- One WOTS encoding attempt reaches and executes its tag-4 HASH call. The trace is
valid for any cache contents and any oracle; encoding success is a separate question. -/
theorem ots_encoding_hash (location : Fin 5) (hash : Hash) (s : MachineState)
    (pc : s.pc=0x1a50+delta location) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 81 88 1 1 t ∧
      t.pc=0x1b94+delta location := by
  let mid := otsPrelude location s
  let prep := otsHashPrep location mid
  let t := writeHash prep (hash (hashInput prep))
  refine ⟨t,?_,?_⟩
  · have prelude := (otsPrelude_block location s pc).trace (hash:=hash)
    have setup := (otsHashPrep_block location mid (otsPrelude_pc location s)).trace (hash:=hash)
    have hashed := otsHashPrep_hash_step location hash mid
    have combined := prelude.trans (setup.trans hashed)
    simpa only [mid,prep,t,Nat.reduceAdd] using combined
  · simp [t,prep,writeHash,otsHashPrep_pc]
    bv_omega

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.ots_encoding_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ots_encoding_hash

def otsHashPrepWrites : List Word :=
  [0x40000#64,0x40008#64,0x40010#64,0x40018#64,
   0x40020#64,0x40028#64,0x40030#64,0x40038#64]

theorem otsHashPrep_frame (location : Fin 5) (s : MachineState) (a : Word)
    (outside : a∉otsHashPrepWrites) :
    (otsHashPrep location s).getMem a=s.getMem a := by
  simp only [otsHashPrep,shift_mem]
  simp only [otsHashPrepWrites,List.mem_cons,List.not_mem_nil,
    not_or,not_false_eq_true,and_true] at outside
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩:=outside
  simp [otsHashPrepState,otsHashPrepCode,runSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    setWord32_eq,MachineState.getMem_setMem_ne,alignToDword,byteOffset,
    h0,h1,h2,h3,h4,h5,h6,h7]


theorem otsHashPrep_low_word (location : Fin 5) (s : MachineState)
    (read : Nat) (readBound : read<0x40000) :
    (otsHashPrep location s).getWord32 (BitVec.ofNat 64 read) =
      s.getWord32 (BitVec.ofNat 64 read) := by
  have cell := (SphincsMaskedSignForestTail.cell_bounds read 0 0x40000
    (by decide) (by omega) readBound (by decide)).2
  simp only [MachineState.getWord32]
  rw [otsHashPrep_frame]
  simp only [otsHashPrepWrites,List.mem_cons,List.not_mem_nil,
    not_or,not_false_eq_true,and_true]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    intro h
    rw [h] at cell
    norm_num at cell


theorem ots_encoding_hash_low_word (location : Fin 5) (s : MachineState)
    (answer : BitVec 256) (read : Nat) (readBound : read<0x40000) :
    (writeHash (otsHashPrep location (otsPrelude location s)) answer).getWord32
      (BitVec.ofNat 64 read) = s.getWord32 (BitVec.ofNat 64 read) := by
  let prep := otsHashPrep location (otsPrelude location s)
  have cell := (SphincsMaskedSignForestTail.cell_bounds read 0 0x40000
    (by decide) (by omega) readBound (by decide)).2
  have dest : prep.getReg .x12 = 0x42000 := (otsHashPrep_registers location _).2.2.1
  have frame : (writeHash prep answer).getMem (alignToDword (BitVec.ofNat 64 read)) =
      prep.getMem (alignToDword (BitVec.ofNat 64 read)) := by
    apply SphincsVerifierFtsLevelInit.writeHash_mem_frame prep answer dest
    all_goals
      intro h
      have impossible : ¬ (alignToDword (BitVec.ofNat 64 read)).toNat < 0x40000 := by
        rw [h]
        decide
      exact impossible cell
  simp only [MachineState.getWord32]
  rw [frame]
  have h1 := otsHashPrep_low_word location (otsPrelude location s) read readBound
  have h2 := otsPrelude_low_word location s read readBound
  simp only [MachineState.getWord32] at h1 h2
  exact h1.trans h2


def otsPaddingFirstCode : List (Word × Instr) := [
 (0x1b94,.LUI .x6 0x42),
 (0x1b98,.ADDI .x6 .x6 0),
 (0x1b9c,.LBU .x10 .x6 9),
 (0x1ba0,.ANDI .x10 .x10 0xc0),
 (0x1ba4,.BEQ .x10 .x0 8)]

def otsPaddingFirstState (s : MachineState) : MachineState :=
  runSchedule otsPaddingFirstCode s

def otsPaddingFirst (location : Fin 5) (s : MachineState) : MachineState :=
  shift (delta location) (otsPaddingFirstState (s.setPC 0x1b94))

theorem otsPaddingFirst_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (741+offset location) otsPaddingFirstCode := by
  fin_cases location <;> rfl

theorem otsPaddingFirst_encoded (location : Fin 5) : ∀ e∈otsPaddingFirstCode,
    instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  apply encoded_of_block _ (741+offset location) _ _ (otsPaddingFirst_image location)
  · have h := SphincsMaskedSignOtsParents.offset_bound location
    change 741+offset location+5≤11000
    omega
  · intro i
    have h : ∀ i : Fin otsPaddingFirstCode.length,
        otsPaddingFirstCode[i.val].1=BitVec.ofNat 64 (0x1b94+4*i.val) := by
      intro j
      fin_cases j <;> rfl
    rw [h i,delta,←BitVec.ofNat_add]
    congr 1
    omega

theorem otsPaddingFirst_supported : ∀ e∈otsPaddingFirstCode,Supported e.2 := by decide

theorem otsPaddingFirst_checked (s : MachineState) (pc : s.pc=0x1b94) :
    Checked otsPaddingFirstCode s := by
  simp [otsPaddingFirstCode,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem otsPaddingFirst_block (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x1b94+delta location) :
    OrdinarySteps SphincsMaskedImages.sign s 5 (otsPaddingFirst location s) := by
  have trace := block_shift SphincsMaskedImages.sign (delta location) otsPaddingFirstCode
    otsPaddingFirst_supported (otsPaddingFirst_encoded location) (s.setPC 0x1b94)
    (otsPaddingFirst_checked (s.setPC 0x1b94) rfl)
  rw [SphincsMaskedSignOtsDomain.rebase_eq _ _ s pc] at trace
  have len : otsPaddingFirstCode.length=5 := rfl
  simpa only [otsPaddingFirst,otsPaddingFirstState,len] using trace

theorem otsPaddingFirst_register (location : Fin 5) (s : MachineState) :
    (otsPaddingFirst location s).getReg .x10 =
      (((s.getByte 0x42009).setWidth 64) &&& 0xc0) := by
  simp [otsPaddingFirst,otsPaddingFirstState,otsPaddingFirstCode,runSchedule,execInstrBr,
    signExtend12,MachineState.getByte,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem otsPaddingFirst_good_pc (location : Fin 5) (s : MachineState)
    (good : (otsPaddingFirst location s).getReg .x10 = 0) :
    (otsPaddingFirst location s).pc=0x1bac+delta location := by
  simp [otsPaddingFirst,otsPaddingFirstState,otsPaddingFirstCode,runSchedule,execInstrBr,
    signExtend12,signExtend13,MachineState.getByte,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] at good ⊢
  exact good

theorem otsPaddingFirst_bad_pc (location : Fin 5) (s : MachineState)
    (bad : (otsPaddingFirst location s).getReg .x10 ≠ 0) :
    (otsPaddingFirst location s).pc=0x1ba8+delta location := by
  simp [otsPaddingFirst,otsPaddingFirstState,otsPaddingFirstCode,runSchedule,execInstrBr,
    signExtend12,signExtend13,MachineState.getByte,MachineState.getReg_setReg_eq] at bad ⊢
  exact bad

def otsPaddingSecondCode : List (Word × Instr) := [
 (0x1bac,.LUI .x6 0x42),
 (0x1bb0,.ADDI .x6 .x6 0),
 (0x1bb4,.LBU .x10 .x6 19),
 (0x1bb8,.ANDI .x10 .x10 0xc0),
 (0x1bbc,.BEQ .x10 .x0 8)]

def otsPaddingSecondState (s : MachineState) : MachineState :=
  runSchedule otsPaddingSecondCode s

def otsPaddingSecond (location : Fin 5) (s : MachineState) : MachineState :=
  shift (delta location) (otsPaddingSecondState (s.setPC 0x1bac))

theorem otsPaddingSecond_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (747+offset location) otsPaddingSecondCode := by
  fin_cases location <;> rfl

theorem otsPaddingSecond_encoded (location : Fin 5) : ∀ e∈otsPaddingSecondCode,
    instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  apply encoded_of_block _ (747+offset location) _ _ (otsPaddingSecond_image location)
  · have h := SphincsMaskedSignOtsParents.offset_bound location
    change 747+offset location+5≤11000
    omega
  · intro i
    have h : ∀ i : Fin otsPaddingSecondCode.length,
        otsPaddingSecondCode[i.val].1=BitVec.ofNat 64 (0x1bac+4*i.val) := by
      intro j
      fin_cases j <;> rfl
    rw [h i,delta,←BitVec.ofNat_add]
    congr 1
    omega

theorem otsPaddingSecond_supported : ∀ e∈otsPaddingSecondCode,Supported e.2 := by decide

theorem otsPaddingSecond_checked (s : MachineState) (pc : s.pc=0x1bac) :
    Checked otsPaddingSecondCode s := by
  simp [otsPaddingSecondCode,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem otsPaddingSecond_block (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x1bac+delta location) :
    OrdinarySteps SphincsMaskedImages.sign s 5 (otsPaddingSecond location s) := by
  have trace := block_shift SphincsMaskedImages.sign (delta location) otsPaddingSecondCode
    otsPaddingSecond_supported (otsPaddingSecond_encoded location) (s.setPC 0x1bac)
    (otsPaddingSecond_checked (s.setPC 0x1bac) rfl)
  rw [SphincsMaskedSignOtsDomain.rebase_eq _ _ s pc] at trace
  have len : otsPaddingSecondCode.length=5 := rfl
  simpa only [otsPaddingSecond,otsPaddingSecondState,len] using trace

theorem otsPaddingSecond_register (location : Fin 5) (s : MachineState) :
    (otsPaddingSecond location s).getReg .x10 =
      (((s.getByte 0x42013).setWidth 64) &&& 0xc0) := by
  simp [otsPaddingSecond,otsPaddingSecondState,otsPaddingSecondCode,runSchedule,execInstrBr,
    signExtend12,MachineState.getByte,MachineState.getReg_setReg_eq]

theorem otsPaddingSecond_good_pc (location : Fin 5) (s : MachineState)
    (good : (otsPaddingSecond location s).getReg .x10 = 0) :
    (otsPaddingSecond location s).pc=0x1bc4+delta location := by
  simp [otsPaddingSecond,otsPaddingSecondState,otsPaddingSecondCode,runSchedule,execInstrBr,
    signExtend12,signExtend13,MachineState.getByte,MachineState.getReg_setReg_eq] at good ⊢
  exact good

theorem otsPaddingSecond_bad_pc (location : Fin 5) (s : MachineState)
    (bad : (otsPaddingSecond location s).getReg .x10 ≠ 0) :
    (otsPaddingSecond location s).pc=0x1bc0+delta location := by
  simp [otsPaddingSecond,otsPaddingSecondState,otsPaddingSecondCode,runSchedule,execInstrBr,
    signExtend12,signExtend13,MachineState.getByte,MachineState.getReg_setReg_eq] at bad ⊢
  exact bad


def otsPaddingRetryFirstCode : List (Word × Instr) :=
  [(0x1ba8,.JAL .x0 0x7ec)]

def otsPaddingRetrySecondCode : List (Word × Instr) :=
  [(0x1bc0,.JAL .x0 0x7d4)]

theorem otsPaddingRetryFirst_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (746+offset location) otsPaddingRetryFirstCode := by
  fin_cases location <;> rfl

theorem otsPaddingRetrySecond_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (752+offset location) otsPaddingRetrySecondCode := by
  fin_cases location <;> rfl

theorem otsPaddingRetryFirst_block (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x1ba8+delta location) :
    OrdinarySteps SphincsMaskedImages.sign s 1 (execInstrBr s (.JAL .x0 0x7ec)) := by
  have fetched : fetch SphincsMaskedImages.sign s = some (.base (.JAL .x0 0x7ec)) := by
    rw [fetch_at,pc]
    fin_cases location <;> decide
  have stepped : ordinaryStep s (.base (.JAL .x0 0x7ec)) =
      some (execInstrBr s (.JAL .x0 0x7ec)) := by simp [ordinaryStep,memoryArgumentsValid]
  exact OrdinarySteps.step s _ _ _ 0 fetched stepped (OrdinarySteps.refl _)

theorem otsPaddingRetrySecond_block (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x1bc0+delta location) :
    OrdinarySteps SphincsMaskedImages.sign s 1 (execInstrBr s (.JAL .x0 0x7d4)) := by
  have fetched : fetch SphincsMaskedImages.sign s = some (.base (.JAL .x0 0x7d4)) := by
    rw [fetch_at,pc]
    fin_cases location <;> decide
  have stepped : ordinaryStep s (.base (.JAL .x0 0x7d4)) =
      some (execInstrBr s (.JAL .x0 0x7d4)) := by simp [ordinaryStep,memoryArgumentsValid]
  exact OrdinarySteps.step s _ _ _ 0 fetched stepped (OrdinarySteps.refl _)

theorem otsPaddingRetryFirst_pc (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x1ba8+delta location) :
    (execInstrBr s (.JAL .x0 0x7ec)).pc=0x2394+delta location := by
  simp [execInstrBr,signExtend21,pc]
  calc
    _ = (7080#64+2028#64)+delta location := by ac_rfl
    _ = 9108#64+delta location := by congr 1

theorem otsPaddingRetrySecond_pc (location : Fin 5) (s : MachineState)
    (pc : s.pc=0x1bc0+delta location) :
    (execInstrBr s (.JAL .x0 0x7d4)).pc=0x2394+delta location := by
  simp [execInstrBr,signExtend21,pc]
  calc
    _ = (7104#64+2004#64)+delta location := by ac_rfl
    _ = 9108#64+delta location := by congr 1

def signerDecoderMiddleState (i : Fin 52) (state : MachineState) : MachineState :=
  let shift := digitBit i.val % 8
  if shift = 0 then state
  else
    let first := execInstrBr state (.SRLI .x10 .x10 (BitVec.ofNat 6 shift))
    if shift ≤ 5 then first
    else
      let second := execInstrBr first
        (.LBU .x12 .x6 (BitVec.ofNat 12 (digitBit i.val / 8 + 1)))
      let third := execInstrBr second
        (.SLLI .x12 .x12 (BitVec.ofNat 6 (8 - shift)))
      execInstrBr third (.ADD .x10 .x10 .x12)

def signerDecoderState (i : Fin 52) (state : MachineState) : MachineState :=
  decoderSuffixState i (signerDecoderMiddleState i (decoderPrefixState i state))

theorem signerDecoderMiddle_value (i : Fin 52) (state : MachineState)
    (source : state.getReg .x6 = 0x42000) :
    (signerDecoderMiddleState i state).getReg .x10 = middleValue i state := by
  fin_cases i <;>
    simp [signerDecoderMiddleState,middleValue,digitBit,execInstrBr,signExtend12,
      source,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getByte]

theorem signerDecoderMiddle_memory (i : Fin 52) (state : MachineState)
    (address : Word) :
    (signerDecoderMiddleState i state).getByte address = state.getByte address := by
  fin_cases i <;>
    simp [signerDecoderMiddleState,execInstrBr,MachineState.getByte]

theorem signerDecoderMiddle_checksum (i : Fin 52) (state : MachineState) :
    (signerDecoderMiddleState i state).getReg .x15 = state.getReg .x15 := by
  fin_cases i <;>
    simp [signerDecoderMiddleState,execInstrBr,MachineState.getReg_setReg_ne]

theorem signerDecoder_word (i : Fin 52) (state : MachineState) :
    (signerDecoderMiddleState i (decoderPrefixState i state)).getReg .x10 =
      answerWord i state := by
  rw [signerDecoderMiddle_value i (decoderPrefixState i state)
    (decoder_prefix_source i state)]
  simp [middleValue,answerWord,decoder_prefix_value,decoder_prefix_memory]

theorem signerDecoder_digit (i : Fin 52) (state : MachineState) :
    (signerDecoderState i state).getByte (BitVec.ofNat 64 (0x44000+i.val)) =
      answerDigit i state := by
  change (decoderSuffixState i
    (signerDecoderMiddleState i (decoderPrefixState i state))).getByte _ = _
  rw [decoder_suffix_byte,signerDecoder_word]
  rfl

theorem signerDecoder_checksum (i : Fin 52) (state : MachineState) :
    (signerDecoderState i state).getReg .x15 =
      state.getReg .x15 + (answerWord i state &&& 7#64) := by
  change (decoderSuffixState i
    (signerDecoderMiddleState i (decoderPrefixState i state))).getReg .x15 = _
  rw [decoder_suffix_sum,signerDecoder_word,signerDecoderMiddle_checksum,
    decoder_prefix_checksum]

theorem signerDecoder_memory (i : Fin 52) (state : MachineState)
    (address : Word) :
    (signerDecoderState i state).getByte address =
      if address = BitVec.ofNat 64 (0x44000+i.val) then answerDigit i state
      else state.getByte address := by
  change (decoderSuffixState i
    (signerDecoderMiddleState i (decoderPrefixState i state))).getByte address = _
  rw [decoder_suffix_memory]
  by_cases same : address = BitVec.ofNat 64 (0x44000+i.val)
  · simp [same,answerDigit,signerDecoder_word]
  · simp [same,signerDecoderMiddle_memory,decoder_prefix_memory]

def signerDecoderRun : Nat → MachineState → MachineState
  | 0, state => state
  | count + 1, state =>
      signerDecoderState ⟨count % 52, Nat.mod_lt _ (by decide)⟩
        (signerDecoderRun count state)

theorem signer_run_answer_byte (count : Nat) (state : MachineState)
    (within : count ≤ 52) (index : Fin 32) :
    (signerDecoderRun count state).getByte
      (BitVec.ofNat 64 (0x42000 + index.val)) =
      state.getByte (BitVec.ofNat 64 (0x42000 + index.val)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have small : count < 52 := by omega
      let i : Fin 52 := ⟨count, small⟩
      have different :
          BitVec.ofNat 64 (0x42000 + index.val) ≠
            BitVec.ofNat 64 (0x44000 + i.val) := by
        intro eq
        have h := congrArg BitVec.toNat eq
        have leftSmall : 0x42000 + index.val < 2^64 := by omega
        have rightSmall : 0x44000 + i.val < 2^64 := by
          have := i.isLt
          omega
        simp only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt leftSmall, Nat.mod_eq_of_lt rightSmall] at h
        have := index.isLt
        have := i.isLt
        omega
      have stepEq : signerDecoderRun (count + 1) state =
          signerDecoderState i (signerDecoderRun count state) := by
        simp [signerDecoderRun, i, Nat.mod_eq_of_lt small]
      rw [stepEq]
      rw [signerDecoder_memory]
      simp only [if_neg different]
      exact ih (by omega)

theorem signer_answerWord_run (count : Nat) (state : MachineState)
    (within : count ≤ 52) (i : Fin 52) :
    answerWord i (signerDecoderRun count state) = answerWord i state := by
  let lowIndex : Fin 32 := ⟨digitBit i.val / 8, by fin_cases i <;> decide⟩
  let highIndex : Fin 32 := ⟨digitBit i.val / 8 + 1, by fin_cases i <;> decide⟩
  have low := signer_run_answer_byte count state within lowIndex
  have high := signer_run_answer_byte count state within highIndex
  have high' : (signerDecoderRun count state).getByte
      (BitVec.ofNat 64 (0x42000 + digitBit i.val / 8 + 1)) =
      state.getByte (BitVec.ofNat 64 (0x42000 + digitBit i.val / 8 + 1)) := by
    simpa [highIndex, Nat.add_assoc] using high
  simp [answerWord, lowIndex, low, high']

theorem signer_answerDigit_run (count : Nat) (state : MachineState)
    (within : count ≤ 52) (i : Fin 52) :
    answerDigit i (signerDecoderRun count state) = answerDigit i state := by
  simp [answerDigit, signer_answerWord_run count state within i]

theorem signer_run_digit (count : Nat) (state : MachineState)
    (within : count ≤ 52) (i : Fin 52) (inside : i.val < count) :
    (signerDecoderRun count state).getByte
      (BitVec.ofNat 64 (0x44000 + i.val)) = answerDigit i state := by
  induction count with
  | zero => omega
  | succ count ih =>
      have small : count < 52 := by omega
      let last : Fin 52 := ⟨count, small⟩
      have stepEq : signerDecoderRun (count + 1) state =
          signerDecoderState last (signerDecoderRun count state) := by
        simp [signerDecoderRun, last, Nat.mod_eq_of_lt small]
      rw [stepEq]
      by_cases same : i.val = count
      · have equality : i = last := Fin.ext (by simpa [last] using same)
        subst i
        rw [signerDecoder_digit]
        exact signer_answerDigit_run count state (by omega) last
      · have different :
            BitVec.ofNat 64 (0x44000 + i.val) ≠
              BitVec.ofNat 64 (0x44000 + last.val) := by
          intro eq
          have h := congrArg BitVec.toNat eq
          have ismall : 0x44000 + i.val < 2^64 := by
            have := i.isLt
            omega
          have lsmall : 0x44000 + last.val < 2^64 := by
            have := last.isLt
            omega
          simp only [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt ismall, Nat.mod_eq_of_lt lsmall] at h
          have : last.val = count := rfl
          omega
        rw [signerDecoder_memory]
        simp only [if_neg different]
        exact ih (by omega) (by omega)

def answerSum : Nat → MachineState → Word
  | 0, _ => 0
  | count + 1, state =>
      answerSum count state +
        (answerWord ⟨count % 52, Nat.mod_lt _ (by decide)⟩ state &&& 7#64)

theorem signer_run_checksum (count : Nat) (state : MachineState)
    (within : count ≤ 52) :
    (signerDecoderRun count state).getReg .x15 =
      state.getReg .x15 + answerSum count state := by
  induction count with
  | zero => simp [signerDecoderRun, answerSum]
  | succ count ih =>
      have small : count < 52 := by omega
      let last : Fin 52 := ⟨count, small⟩
      have stepEq : signerDecoderRun (count + 1) state =
          signerDecoderState last (signerDecoderRun count state) := by
        simp [signerDecoderRun, last, Nat.mod_eq_of_lt small]
      rw [stepEq, signerDecoder_checksum, ih (by omega),
        signer_answerWord_run count state (by omega) last]
      simp [answerSum, last, Nat.mod_eq_of_lt small, BitVec.add_assoc]

def signerDigitIndex (location : Fin 5) (i : Nat) : Nat :=
  754+offset location+digitCost i

theorem signerDigit_slice (location : Fin 5) :
    (SphincsMaskedImages.sign.code.drop (754+offset location)).take 496 =
    (SphincsMaskedImages.sign.code.drop 2210).take 496 := by
  fin_cases location <;> rfl

theorem signerDigit_word (location : Fin 5) (n : Nat) (hn : n<496) :
    SphincsMaskedImages.sign.code[754+offset location+n]? =
      SphincsMaskedImages.sign.code[2210+n]? := by
  have eq:=congrArg (fun words : List (BitVec 32) => words[n]?) (signerDigit_slice location)
  simpa only [List.getElem?_take_of_lt hn,List.getElem?_drop] using eq

theorem signerDigit_code (location : Fin 5) (n : Nat) (hn : n<496) :
    (SphincsMaskedImages.sign.code[754+offset location+n]?).bind decodeInstruction =
      (SphincsMaskedImages.sign.code[2210+n]?).bind decodeInstruction := by
  rw [signerDigit_word location n hn]

theorem signerDigit_prefix_code (location : Fin 5) (i : Fin 52) :
    (SphincsMaskedImages.sign.code[signerDigitIndex location i.val]?).bind decodeInstruction =
      some (.base (.LUI .x6 0x42)) ∧
    (SphincsMaskedImages.sign.code[signerDigitIndex location i.val+1]?).bind decodeInstruction =
      some (.base (.ADDI .x6 .x6 0)) ∧
    (SphincsMaskedImages.sign.code[signerDigitIndex location i.val+2]?).bind decodeInstruction =
      some (.base (.LBU .x10 .x6 (BitVec.ofNat 12 (digitBit i.val/8)))) := by
  have b0 : digitCost i.val<496 := by fin_cases i <;> decide
  have b1 : digitCost i.val+1<496 := by fin_cases i <;> decide
  have b2 : digitCost i.val+2<496 := by fin_cases i <;> decide
  simp only [signerDigitIndex]
  rw [signerDigit_code location _ b0]
  rw [show 754+offset location+digitCost i.val+1 = 754+offset location+(digitCost i.val+1) by omega]
  rw [signerDigit_code location _ b1]
  rw [show 754+offset location+digitCost i.val+2 = 754+offset location+(digitCost i.val+2) by omega]
  rw [signerDigit_code location _ b2]
  fin_cases i <;> decide


def signerDigitSuffixIndex (location : Fin 5) (i : Nat) : Nat :=
  signerDigitIndex location i + digitWords i - 5

theorem signerDigit_suffix_at (location : Fin 5) (i : Fin 52) (j : Fin 5) :
    (SphincsMaskedImages.sign.code[signerDigitSuffixIndex location i.val+j.val]?).bind decodeInstruction =
      (SphincsMaskedImages.sign.code[2210+(digitCost i.val+digitWords i.val-5+j.val)]?).bind decodeInstruction := by
  have bound : digitCost i.val+digitWords i.val-5+j.val<496 := by
    fin_cases i <;> fin_cases j <;> decide
  have width : 5≤digitWords i.val := by fin_cases i <;> decide
  rw [show signerDigitSuffixIndex location i.val+j.val =
      754+offset location+(digitCost i.val+digitWords i.val-5+j.val) by
      simp only [signerDigitSuffixIndex,signerDigitIndex]
      omega]
  exact signerDigit_code location _ bound

theorem signerDigit_suffix_code (location : Fin 5) (i : Fin 52) :
    (SphincsMaskedImages.sign.code[signerDigitSuffixIndex location i.val]?).bind decodeInstruction =
      some (.base (.ANDI .x10 .x10 7)) ∧
    (SphincsMaskedImages.sign.code[signerDigitSuffixIndex location i.val+1]?).bind decodeInstruction =
      some (.base (.ADD .x15 .x15 .x10)) ∧
    (SphincsMaskedImages.sign.code[signerDigitSuffixIndex location i.val+2]?).bind decodeInstruction =
      some (.base (.LUI .x6 0x44)) ∧
    (SphincsMaskedImages.sign.code[signerDigitSuffixIndex location i.val+3]?).bind decodeInstruction =
      some (.base (.ADDI .x6 .x6 i.val)) ∧
    (SphincsMaskedImages.sign.code[signerDigitSuffixIndex location i.val+4]?).bind decodeInstruction =
      some (.base (.SB .x6 .x10 0)) := by
  have e0 : (SphincsMaskedImages.sign.code[signerDigitSuffixIndex location i.val]?).bind decodeInstruction =
      (SphincsMaskedImages.sign.code[2210+(digitCost i.val+digitWords i.val-5)]?).bind decodeInstruction := by
    simpa only [Nat.add_zero] using signerDigit_suffix_at location i ⟨0,by decide⟩
  rw [e0]
  rw [signerDigit_suffix_at location i ⟨1,by decide⟩]
  rw [signerDigit_suffix_at location i ⟨2,by decide⟩]
  rw [signerDigit_suffix_at location i ⟨3,by decide⟩]
  rw [signerDigit_suffix_at location i ⟨4,by decide⟩]
  fin_cases i <;> decide

theorem signerDigit_middle_at (location : Fin 5) (i : Fin 52) (j : Fin 7)
    (bound : digitCost i.val+j.val<496) :
    (SphincsMaskedImages.sign.code[signerDigitIndex location i.val+j.val]?).bind decodeInstruction =
      (SphincsMaskedImages.sign.code[2210+digitCost i.val+j.val]?).bind decodeInstruction := by
  rw [show signerDigitIndex location i.val+j.val =
      754+offset location+(digitCost i.val+j.val) by
      simp [signerDigitIndex]; omega]
  simpa only [Nat.add_assoc] using signerDigit_code location _ bound

theorem signerDigit_shift_code (location : Fin 5) (i : Fin 52) :
    (digitBit i.val % 8 ≠ 0 →
      (SphincsMaskedImages.sign.code[signerDigitIndex location i.val+3]?).bind decodeInstruction =
        some (.base (.SRLI .x10 .x10 (BitVec.ofNat 6 (digitBit i.val % 8))))) ∧
    (digitBit i.val % 8 > 5 →
      (SphincsMaskedImages.sign.code[signerDigitIndex location i.val+4]?).bind decodeInstruction =
        some (.base (.LBU .x12 .x6 (BitVec.ofNat 12 (digitBit i.val/8+1)))) ∧
      (SphincsMaskedImages.sign.code[signerDigitIndex location i.val+5]?).bind decodeInstruction =
        some (.base (.SLLI .x12 .x12 (BitVec.ofNat 6 (8-digitBit i.val%8)))) ∧
      (SphincsMaskedImages.sign.code[signerDigitIndex location i.val+6]?).bind decodeInstruction =
        some (.base (.ADD .x10 .x10 .x12))) := by
  have b3 : digitCost i.val+3<496 := by fin_cases i <;> decide
  have b4 : digitCost i.val+4<496 := by fin_cases i <;> decide
  have b5 : digitCost i.val+5<496 := by fin_cases i <;> decide
  have b6 : digitCost i.val+6<496 := by fin_cases i <;> decide
  rw [signerDigit_middle_at location i ⟨3,by decide⟩ b3]
  rw [signerDigit_middle_at location i ⟨4,by decide⟩ b4]
  rw [signerDigit_middle_at location i ⟨5,by decide⟩ b5]
  rw [signerDigit_middle_at location i ⟨6,by decide⟩ b6]
  fin_cases i <;> decide

theorem signerDigitPC_small (location : Fin 5) (i : Fin 52) (j : Nat)
    (hj : j≤12) :
    0x1000+4*(signerDigitIndex location i.val+j)<2^64 := by
  have cost : digitCost i.val≤496 := by fin_cases i <;> decide
  have off := SphincsMaskedSignOtsParents.offset_bound location
  simp only [signerDigitIndex]
  omega

theorem signerDigit_prefix_block (location : Fin 5) (i : Fin 52) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * signerDigitIndex location i.val)) :
    OrdinarySteps SphincsMaskedImages.sign state 3
      (decoderPrefixState i state) ∧
    (decoderPrefixState i state).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (signerDigitIndex location i.val + 3)) ∧
    (decoderPrefixState i state).getReg .x6 = 0x42000 := by
  let s1 := execInstrBr state (.LUI .x6 0x42)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LBU .x10 .x6 (BitVec.ofNat 12 (digitBit i.val / 8)))
  have hcode := signerDigit_prefix_code location i
  have p1 : s1.pc = BitVec.ofNat 64
      (0x1000 + 4 * (signerDigitIndex location i.val + 1)) := by
    simp [s1, execInstrBr, pc, ← BitVec.ofNat_add]
    congr 1
  have p2 : s2.pc = BitVec.ofNat 64
      (0x1000 + 4 * (signerDigitIndex location i.val + 2)) := by
    simp [s2, execInstrBr, p1, ← BitVec.ofNat_add]
    congr 1
  have source : s2.getReg .x6 = 0x42000 := by
    simp [s2, s1, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have valid : memoryArgumentsValid s2
      (.LBU .x10 .x6 (BitVec.ofNat 12 (digitBit i.val / 8))) = true := by
    simp only [memoryArgumentsValid, source]
    fin_cases i <;> decide
  have trace : OrdinarySteps SphincsMaskedImages.sign state 3 s3 := by
    apply OrdinarySteps.step state s1 _ (.base (.LUI .x6 0x42)) 2
    · rw [fetch_index SphincsMaskedImages.sign state (signerDigitIndex location i.val)
        (signerDigitPC_small location i 0 (by decide)) pc]
      exact hcode.1
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 1
    · rw [fetch_index SphincsMaskedImages.sign s1 (signerDigitIndex location i.val + 1)
        (signerDigitPC_small location i 1 (by decide)) p1]
      exact hcode.2.1
    · rfl
    apply OrdinarySteps.step s2 s3 _
      (.base (.LBU .x10 .x6 (BitVec.ofNat 12 (digitBit i.val / 8)))) 0
    · rw [fetch_index SphincsMaskedImages.sign s2 (signerDigitIndex location i.val + 2)
        (signerDigitPC_small location i 2 (by decide)) p2]
      exact hcode.2.2
    · simp [s3, ordinaryStep, valid]
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [decoderPrefixState] using trace, ?_, ?_⟩
  · change s3.pc = _
    simp [s3, execInstrBr, p2, ← BitVec.ofNat_add]
    congr 1
  · change s3.getReg .x6 = _
    simpa [s3, execInstrBr, MachineState.getReg_setReg_ne] using source


theorem signerDigitSuffixPC_small (location : Fin 5) (i : Fin 52) (j : Nat)
    (hj : j≤5) :
    0x1000+4*(signerDigitSuffixIndex location i.val+j)<2^64 := by
  have cost : digitCost i.val≤496 := by fin_cases i <;> decide
  have width : 5≤digitWords i.val := by fin_cases i <;> decide
  have words : digitWords i.val≤12 := by fin_cases i <;> decide
  have off := SphincsMaskedSignOtsParents.offset_bound location
  simp only [signerDigitSuffixIndex,signerDigitIndex]
  omega

theorem signerDigit_suffix_block (location : Fin 5) (i : Fin 52) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * signerDigitSuffixIndex location i.val)) :
    OrdinarySteps SphincsMaskedImages.sign state 5
      (decoderSuffixState i state) ∧
    (decoderSuffixState i state).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (signerDigitSuffixIndex location i.val + 5)) := by
  let s1 := execInstrBr state (.ANDI .x10 .x10 7)
  let s2 := execInstrBr s1 (.ADD .x15 .x15 .x10)
  let s3 := execInstrBr s2 (.LUI .x6 0x44)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 i.val)
  let s5 := execInstrBr s4 (.SB .x6 .x10 0)
  have hcode := signerDigit_suffix_code location i
  have p1 : s1.pc = BitVec.ofNat 64
      (0x1000 + 4 * (signerDigitSuffixIndex location i.val + 1)) := by
    simp [s1, execInstrBr, pc, ← BitVec.ofNat_add]
    congr 1
  have p2 : s2.pc = BitVec.ofNat 64
      (0x1000 + 4 * (signerDigitSuffixIndex location i.val + 2)) := by
    simp [s2, execInstrBr, p1, ← BitVec.ofNat_add]
    congr 1
  have p3 : s3.pc = BitVec.ofNat 64
      (0x1000 + 4 * (signerDigitSuffixIndex location i.val + 3)) := by
    simp [s3, execInstrBr, p2, ← BitVec.ofNat_add]
    congr 1
  have p4 : s4.pc = BitVec.ofNat 64
      (0x1000 + 4 * (signerDigitSuffixIndex location i.val + 4)) := by
    simp [s4, execInstrBr, p3, ← BitVec.ofNat_add]
    congr 1
  have destination : s4.getReg .x6 = BitVec.ofNat 64 (0x44000 + i.val) := by
    fin_cases i <;> simp [s4, s3, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have valid : memoryArgumentsValid s4 (.SB .x6 .x10 0) = true := by
    simp only [memoryArgumentsValid, destination]
    fin_cases i <;> decide
  have trace : OrdinarySteps SphincsMaskedImages.sign state 5 s5 := by
    apply OrdinarySteps.step state s1 _ (.base (.ANDI .x10 .x10 7)) 4
    · rw [fetch_index SphincsMaskedImages.sign state (signerDigitSuffixIndex location i.val)
        (signerDigitSuffixPC_small location i 0 (by decide)) pc]
      exact hcode.1
    · rfl
    apply OrdinarySteps.step s1 s2 _ (.base (.ADD .x15 .x15 .x10)) 3
    · rw [fetch_index SphincsMaskedImages.sign s1 (signerDigitSuffixIndex location i.val + 1)
        (signerDigitSuffixPC_small location i 1 (by decide)) p1]
      exact hcode.2.1
    · rfl
    apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x6 0x44)) 2
    · rw [fetch_index SphincsMaskedImages.sign s2 (signerDigitSuffixIndex location i.val + 2)
        (signerDigitSuffixPC_small location i 2 (by decide)) p2]
      exact hcode.2.2.1
    · rfl
    apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 i.val)) 1
    · rw [fetch_index SphincsMaskedImages.sign s3 (signerDigitSuffixIndex location i.val + 3)
        (signerDigitSuffixPC_small location i 3 (by decide)) p3]
      exact hcode.2.2.2.1
    · rfl
    apply OrdinarySteps.step s4 s5 _ (.base (.SB .x6 .x10 0)) 0
    · rw [fetch_index SphincsMaskedImages.sign s4 (signerDigitSuffixIndex location i.val + 4)
        (signerDigitSuffixPC_small location i 4 (by decide)) p4]
      exact hcode.2.2.2.2
    · simp [s5, ordinaryStep, memoryArgumentsValid, destination,
        signExtend12, accessValid, rangeValid, MEMORY_BYTES]
      fin_cases i <;> decide
    exact OrdinarySteps.refl _
  refine ⟨by simpa only [decoderSuffixState] using trace, ?_⟩
  change s5.pc = _
  simp [s5, execInstrBr, p4, ← BitVec.ofNat_add]
  congr 1


theorem signerDigit_middle_block (location : Fin 5) (i : Fin 52) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (signerDigitIndex location i.val + 3)))
    (source : state.getReg .x6 = 0x42000) :
    OrdinarySteps SphincsMaskedImages.sign state (digitWords i.val - 8)
      (signerDecoderMiddleState i state) ∧
    (signerDecoderMiddleState i state).pc =
      BitVec.ofNat 64 (0x1000 + 4 * signerDigitSuffixIndex location i.val) ∧
    (signerDecoderMiddleState i state).getReg .x6 = 0x42000 := by
  let shift := digitBit i.val % 8
  by_cases hz : shift = 0
  · have words : digitWords i.val = 8 := by simp [digitWords, shift, hz]
    have start : signerDigitSuffixIndex location i.val = signerDigitIndex location i.val + 3 := by
      simp [signerDigitSuffixIndex, words] <;> omega
    simp [signerDecoderMiddleState, shift, hz, words, start, pc, source,
      OrdinarySteps.refl]
  · let s1 := execInstrBr state (.SRLI .x10 .x10 (BitVec.ofNat 6 shift))
    have code1 := (signerDigit_shift_code location i).1 hz
    have p1 : s1.pc = BitVec.ofNat 64
        (0x1000 + 4 * (signerDigitIndex location i.val + 4)) := by
      simp [s1, execInstrBr, pc, ← BitVec.ofNat_add]
      congr 1
    have source1 : s1.getReg .x6 = 0x42000 := by
      simpa [s1, execInstrBr, MachineState.getReg_setReg_ne] using source
    have first : OrdinarySteps SphincsMaskedImages.sign state 1 s1 := by
      apply OrdinarySteps.step state s1 _
        (.base (.SRLI .x10 .x10 (BitVec.ofNat 6 shift))) 0
      · rw [fetch_index SphincsMaskedImages.sign state (signerDigitIndex location i.val + 3)
          (signerDigitPC_small location i 3 (by decide)) pc]
        exact code1
      · rfl
      exact OrdinarySteps.refl _
    by_cases hsmall : shift ≤ 5
    · have words : digitWords i.val = 9 := by
        simp [digitWords, shift, hz]
        omega
      have start : signerDigitSuffixIndex location i.val = signerDigitIndex location i.val + 4 := by
        simp [signerDigitSuffixIndex, words] <;> omega
      refine ⟨?_, ?_, ?_⟩
      · simpa [signerDecoderMiddleState, shift, hz, hsmall, words] using first
      · simpa [signerDecoderMiddleState, shift, hz, hsmall, start] using p1
      · simpa [signerDecoderMiddleState, shift, hz, hsmall] using source1
    · have hlarge : shift > 5 := by omega
      have words : digitWords i.val = 12 := by
        simp [digitWords, shift, hz]
        omega
      have start : signerDigitSuffixIndex location i.val = signerDigitIndex location i.val + 7 := by
        simp [signerDigitSuffixIndex, words] <;> omega
      let s2 := execInstrBr s1
        (.LBU .x12 .x6 (BitVec.ofNat 12 (digitBit i.val / 8 + 1)))
      let s3 := execInstrBr s2 (.SLLI .x12 .x12 (BitVec.ofNat 6 (8 - shift)))
      let s4 := execInstrBr s3 (.ADD .x10 .x10 .x12)
      have code := (signerDigit_shift_code location i).2 hlarge
      have p2 : s2.pc = BitVec.ofNat 64
          (0x1000 + 4 * (signerDigitIndex location i.val + 5)) := by
        simp [s2, execInstrBr, p1, ← BitVec.ofNat_add]
        congr 1
      have p3 : s3.pc = BitVec.ofNat 64
          (0x1000 + 4 * (signerDigitIndex location i.val + 6)) := by
        simp [s3, execInstrBr, p2, ← BitVec.ofNat_add]
        congr 1
      have p4 : s4.pc = BitVec.ofNat 64
          (0x1000 + 4 * (signerDigitIndex location i.val + 7)) := by
        simp [s4, execInstrBr, p3, ← BitVec.ofNat_add]
        congr 1
      have valid : memoryArgumentsValid s1
          (.LBU .x12 .x6 (BitVec.ofNat 12 (digitBit i.val / 8 + 1))) = true := by
        simp only [memoryArgumentsValid, source1]
        fin_cases i <;> decide
      have rest : OrdinarySteps SphincsMaskedImages.sign s1 3 s4 := by
        apply OrdinarySteps.step s1 s2 _
          (.base (.LBU .x12 .x6 (BitVec.ofNat 12 (digitBit i.val / 8 + 1)))) 2
        · rw [fetch_index SphincsMaskedImages.sign s1 (signerDigitIndex location i.val + 4)
            (signerDigitPC_small location i 4 (by decide)) p1]
          exact code.1
        · simp [s2, ordinaryStep, valid]
        apply OrdinarySteps.step s2 s3 _
          (.base (.SLLI .x12 .x12 (BitVec.ofNat 6 (8 - shift)))) 1
        · rw [fetch_index SphincsMaskedImages.sign s2 (signerDigitIndex location i.val + 5)
            (signerDigitPC_small location i 5 (by decide)) p2]
          exact code.2.1
        · rfl
        apply OrdinarySteps.step s3 s4 _
          (.base (.ADD .x10 .x10 .x12)) 0
        · rw [fetch_index SphincsMaskedImages.sign s3 (signerDigitIndex location i.val + 6)
            (signerDigitPC_small location i 6 (by decide)) p3]
          exact code.2.2
        · rfl
        exact OrdinarySteps.refl _
      refine ⟨?_, ?_, ?_⟩
      · simpa [signerDecoderMiddleState, shift, hz, hsmall, words] using first.append rest
      · simpa [signerDecoderMiddleState, shift, hz, hsmall, start] using p4
      · have source4 : s4.getReg .x6 = 0x42000 := by
          simpa [s4, s3, s2, execInstrBr,
            MachineState.getReg_setReg_ne] using source1
        simpa [signerDecoderMiddleState, shift, hz, hsmall] using source4


theorem signerDigit_block (location : Fin 5) (i : Fin 52) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * signerDigitIndex location i.val)) :
    OrdinarySteps SphincsMaskedImages.sign state (digitWords i.val)
      (signerDecoderState i state) ∧
    (signerDecoderState i state).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (signerDigitIndex location i.val + digitWords i.val)) := by
  have first := signerDigit_prefix_block location i state pc
  have middle := signerDigit_middle_block location i (decoderPrefixState i state)
    first.2.1 first.2.2
  have suffix := signerDigit_suffix_block location i
    (signerDecoderMiddleState i (decoderPrefixState i state)) middle.2.1
  have width : 8 ≤ digitWords i.val := by fin_cases i <;> decide
  have count : 3 + (digitWords i.val - 8) + 5 = digitWords i.val := by
    omega
  have finish : signerDigitSuffixIndex location i.val + 5 =
      signerDigitIndex location i.val + digitWords i.val := by
    simp [signerDigitSuffixIndex]
    omega
  refine ⟨?_, ?_⟩
  · simpa only [signerDecoderState, count] using
      (first.1.append middle.1).append suffix.1
  · simpa only [signerDecoderState, finish] using suffix.2



theorem signerDigitIndex_succ (location : Fin 5) (count : Nat) :
    signerDigitIndex location (count+1) =
      signerDigitIndex location count+digitWords count := by
  simp [signerDigitIndex,digitCost_succ,Nat.add_assoc]

theorem signerDigit_run_block (location : Fin 5) (count : Nat) (state : MachineState)
    (within : count≤52)
    (pc : state.pc=BitVec.ofNat 64 (0x1000+4*signerDigitIndex location 0)) :
    OrdinarySteps SphincsMaskedImages.sign state (digitCost count)
      (signerDecoderRun count state) ∧
    (signerDecoderRun count state).pc =
      BitVec.ofNat 64 (0x1000+4*signerDigitIndex location count) := by
  induction count with
  | zero =>
      constructor
      · simpa [digitCost,signerDecoderRun] using
          OrdinarySteps.refl (image:=SphincsMaskedImages.sign) state
      · simpa [signerDecoderRun] using pc
  | succ count ih =>
      have small : count<52 := by omega
      obtain ⟨pre,prePc⟩ := ih (by omega)
      let i : Fin 52 := ⟨count,small⟩
      have step := signerDigit_block location i (signerDecoderRun count state)
        (by simpa [i] using prePc)
      have result : signerDecoderRun (count+1) state =
          signerDecoderState i (signerDecoderRun count state) := by
        simp [signerDecoderRun,i,Nat.mod_eq_of_lt small]
      refine ⟨?_,?_⟩
      · simpa [result,digitCost_succ,i] using pre.append step.1
      · simpa [result,signerDigitIndex_succ,i] using step.2

theorem signerDigit_run_all (location : Fin 5) (state : MachineState)
    (pc : state.pc=0x1bc8+delta location) :
    OrdinarySteps SphincsMaskedImages.sign state 496
      (signerDecoderRun 52 state) ∧
    (signerDecoderRun 52 state).pc=0x2388+delta location := by
  have start : state.pc = BitVec.ofNat 64 (0x1000+4*signerDigitIndex location 0) := by
    rw [pc]
    fin_cases location <;> decide
  have all := signerDigit_run_block location 52 state (by decide) start
  have cost : digitCost 52=496 := by decide
  have finish : BitVec.ofNat 64 (0x1000+4*signerDigitIndex location 52) =
      0x2388+delta location := by
    fin_cases location <;> decide
  simpa [cost,finish] using all

end SigGolfCandidate.SphincsMaskedSignOtsPathValue
