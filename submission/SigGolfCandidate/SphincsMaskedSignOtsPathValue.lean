import SigGolfCandidate.SphincsMaskedSignOtsPathFinish
import RiscvZkvm.Rv64.Logic.ByteOps

namespace SigGolfCandidate.SphincsMaskedSignOtsPathValue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedSignOtsParents SphincsMaskedSignOtsTree SphincsMaskedSignOtsPath
open SphincsMaskedSignOtsPathSetup SphincsMaskedSignOtsPathSibling SphincsMaskedSignOtsPathFinish
open SphincsSecurity SphincsBridge SphincsVerifierCopy SphincsMaskedChainDomain
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

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

end SigGolfCandidate.SphincsMaskedSignOtsPathValue
