import SigGolfCandidate.SphincsMaskedLeafLoop

namespace SigGolfCandidate.SphincsMaskedLeafCache
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedLeafLoop SphincsMaskedChainEndpoints
open SphincsVerifierCopy SphincsVerifierCopyMemory SphincsVerifierCopy20DataGeneral
open SphincsVerifierFtsPriorRoots SphincsVerifierFtsRootCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private def CopyInvariant (original : MachineState) (c : Fin 2048) (count : Nat)
    (s : MachineState) : Prop :=
  s.getReg .x6 = 0x42000 ∧ s.getReg .x7 = BitVec.ofNat 64 (0x88 + 20 * c.val) ∧
  (∀ i : Fin 5, s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
    original.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val))) ∧
  (∀ i : Fin 5, i.val < count → s.getWord32 (BitVec.ofNat 64 (0x88 + 20 * c.val + 4 * i.val)) =
    original.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)))

private theorem copyStep (original s : MachineState) (c : Fin 2048) (slot : Fin 5)
    (inv : CopyInvariant original c slot.val s) :
    CopyInvariant original c (slot.val + 1) (copyWordState slot s) := by
  obtain ⟨src, dst, source, copied⟩ := inv
  obtain ⟨srcAfter, dstAfter⟩ := copyWord_pointers slot s
  refine ⟨srcAfter.trans src, dstAfter.trans dst, ?_, ?_⟩
  · intro i
    rw [copyWord_lane_frame s (0x88 + 20 * c.val) (0x42000 + 4 * i.val) slot dst
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact source i
  · intro i hi
    by_cases same : slot = i
    · subst i
      rw [copyWord_data_general slot s 0x42000 (0x88 + 20 * c.val) src dst]
      exact source slot
    · have ne : slot.val ≠ i.val := fun h => same (Fin.ext h)
      rw [copyWord_lane_frame s (0x88 + 20 * c.val) (0x88 + 20 * c.val + 4 * i.val) slot dst
        (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact copied i (by omega)

theorem copy_data (s : MachineState) (c : Fin 2048)
    (src : s.getReg .x6 = 0x42000)
    (dst : s.getReg .x7 = BitVec.ofNat 64 (0x88 + 20 * c.val)) (i : Fin 5) :
    (copyRootState s).getWord32 (BitVec.ofNat 64 (0x88 + 20 * c.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) := by
  have initial : CopyInvariant s c 0 s := ⟨src, dst, fun _ => rfl, by intro _ h; omega⟩
  have s0 := copyStep s s c 0 initial
  have s1 := copyStep s (copyWordState 0 s) c 1 s0
  have s2 := copyStep s (copyWordState 1 (copyWordState 0 s)) c 2 s1
  have s3 := copyStep s (copyWordState 2 (copyWordState 1 (copyWordState 0 s))) c 3 s2
  have s4 := copyStep s (copyWordState 3 (copyWordState 2 (copyWordState 1 (copyWordState 0 s)))) c 4 s3
  exact s4.2.2.2 i (by omega)


theorem storeSetup_frame (s : MachineState) (a : Word) : (storeSetup s).getMem a = s.getMem a := by
  simp [storeSetup,runSchedule,storeSetupSchedule,execInstrBr]

theorem stored_data (s : MachineState) (leaf : Fin 2048)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) (i : Fin 5) :
    (stored s).getWord32 (BitVec.ofNat 64 (0x88 + 20 * leaf.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) := by
  have regs := storeSetup_registers s leaf.val counter
  rw [stored,copy_data _ leaf regs.1 regs.2 i]
  simp only [MachineState.getWord32,storeSetup_frame]

theorem finish_frame (s : MachineState) (a : Word) (outside : a ≠ 0x43020#64) :
    (finish s).getMem a = s.getMem a := by
  simp [finish,runSchedule,finishSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,outside]

theorem cache_word_bounded (leaf : Fin 2048) (i : Fin 5) :
    (alignToDword (BitVec.ofNat 64 (0x88 + 20 * leaf.val + 4 * i.val))).toNat < 0x40000 := by
  unfold alignToDword
  rw [BitVec.toNat_and]
  apply lt_of_le_of_lt Nat.and_le_left
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem finish_cache_word (s : MachineState) (leaf : Fin 2048) (i : Fin 5) :
    (finish s).getWord32 (BitVec.ofNat 64 (0x88 + 20 * leaf.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x88 + 20 * leaf.val + 4 * i.val)) := by
  simp only [MachineState.getWord32]
  rw [finish_frame]
  intro eq
  have bound := cache_word_bounded leaf i
  rw [eq] at bound
  contradiction

theorem nextLeaf_data (s : MachineState) (leaf : Fin 2048)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) (i : Fin 5) :
    (nextLeaf s).getWord32 (BitVec.ofNat 64 (0x88 + 20 * leaf.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) := by
  rw [nextLeaf,finish_cache_word,stored_data s leaf counter i]

theorem nextLeaf_other (s : MachineState) (leaf other : Fin 2048) (ne : leaf ≠ other)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) (i : Fin 5) :
    (nextLeaf s).getWord32 (BitVec.ofNat 64 (0x88 + 20 * other.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x88 + 20 * other.val + 4 * i.val)) := by
  rw [nextLeaf,finish_cache_word]
  change (copyRootState (storeSetup s)).getWord32 _ = _
  rw [copyRoot_word_frame]
  · simp only [MachineState.getWord32,storeSetup_frame]
  · intro j
    have address : (storeSetup s).getReg .x7 + signExtend12 (4#12 * BitVec.ofNat 12 j.val) =
        BitVec.ofNat 64 (0x88 + 20 * leaf.val + 4 * j.val) := by
      rw [(storeSetup_registers s leaf.val counter).2]
      fin_cases j <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [address]
    have hn : leaf.val ≠ other.val := fun h => ne (Fin.ext h)
    exact wordLaneDistinct _ _ (by omega) (by omega) (by omega) (by omega) (by omega)

theorem nextLeaf_bytes (s : MachineState) (leaf : Fin 2048)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) (j : Fin 20) :
    (nextLeaf s).getByte (BitVec.ofNat 64 (0x88 + 20 * leaf.val + j.val)) =
      s.getByte (BitVec.ofNat 64 (0x42000 + j.val)) :=
  bytes_of_lanes _ _ 0x42000 (0x88 + 20 * leaf.val) (by decide) (by omega)
    (by decide) (by omega) (nextLeaf_data s leaf counter) j

theorem nextLeaf_other_bytes (s : MachineState) (leaf other : Fin 2048) (ne : leaf ≠ other)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val) (j : Fin 20) :
    (nextLeaf s).getByte (BitVec.ofNat 64 (0x88 + 20 * other.val + j.val)) =
      s.getByte (BitVec.ofNat 64 (0x88 + 20 * other.val + j.val)) :=
  bytes_of_lanes _ _ (0x88 + 20 * other.val) (0x88 + 20 * other.val) (by omega) (by omega)
    (by omega) (by omega) (nextLeaf_other s leaf other ne counter) j

/-- info: 'SigGolfCandidate.SphincsMaskedLeafCache.nextLeaf_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nextLeaf_data

/-- info: 'SigGolfCandidate.SphincsMaskedLeafCache.nextLeaf_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nextLeaf_other

/-- info: 'SigGolfCandidate.SphincsMaskedLeafCache.nextLeaf_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nextLeaf_bytes

/-- info: 'SigGolfCandidate.SphincsMaskedLeafCache.nextLeaf_other_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nextLeaf_other_bytes

end SigGolfCandidate.SphincsMaskedLeafCache
