import SigGolfCandidate.SphincsMaskedMaskNode

namespace SigGolfCandidate.SphincsMaskedMaskXor
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedMaskCode SphincsMaskedMaskNode
open SphincsVerifierCopyMemory SphincsVerifierFtsPriorRoots
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def xorWord (i : Fin 5) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr s
    (.LWU .x13 .x6 (4*i.val))) (.LWU .x14 .x12 (4*i.val)))
      (.XOR .x15 .x13 .x14)) (.SW .x6 .x15 (4*i.val))

theorem applyXor_eq (s : MachineState) : applyXor s =
    xorWord 4 (xorWord 3 (xorWord 2 (xorWord 1 (xorWord 0 s)))) := rfl

theorem xorWord_registers (i : Fin 5) (s : MachineState) :
    (xorWord i s).getReg .x6 = s.getReg .x6 ∧ (xorWord i s).getReg .x12 = s.getReg .x12 := by
  simp [xorWord,execInstrBr,MachineState.getReg_setReg_ne,MachineState.setWord32]

theorem xorWord_data (i : Fin 5) (s : MachineState) (base : Nat)
    (ptr : s.getReg .x6 = BitVec.ofNat 64 base) (pad : s.getReg .x12 = 0x42000) :
    (xorWord i s).getWord32 (BitVec.ofNat 64 (base+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (base+4*i.val)) ^^^
        s.getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) := by
  fin_cases i <;>
    simp [xorWord,execInstrBr,getWord32_setWord32_same,ptr,pad,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.ofNat_add]

theorem xorWord_word_frame (i : Fin 5) (s : MachineState) (a : Word)
    (outside : alignToDword (s.getReg .x6 + signExtend12 (4#12 * BitVec.ofNat 12 i.val)) ≠ alignToDword a ∨
      byteOffset (s.getReg .x6 + signExtend12 (4#12 * BitVec.ofNat 12 i.val)) / 4 ≠ byteOffset a / 4) :
    (xorWord i s).getWord32 a = s.getWord32 a := by
  simp only [xorWord,execInstrBr,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact getWord32_setWord32_other _ _ _ _ outside

theorem xorWord_lane_frame (i : Fin 5) (s : MachineState) (base read : Nat)
    (ptr : s.getReg .x6 = BitVec.ofNat 64 base) (small : base+20 < 2^64)
    (readSmall : read < 2^64) (aligned : base%4 = 0) (readAligned : read%4 = 0)
    (different : base+4*i.val ≠ read) :
    (xorWord i s).getWord32 (BitVec.ofNat 64 read) = s.getWord32 (BitVec.ofNat 64 read) := by
  apply xorWord_word_frame
  have address : s.getReg .x6 + signExtend12 (4#12 * BitVec.ofNat 12 i.val) = BitVec.ofNat 64 (base+4*i.val) := by
    rw [ptr];fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
  rw [address]
  exact wordLaneDistinct _ _ (by omega) readSmall (by omega) readAligned different

private def Invariant (original : MachineState) (base count : Nat) (s : MachineState) : Prop :=
  s.getReg .x6 = BitVec.ofNat 64 base ∧ s.getReg .x12 = 0x42000 ∧
    (∀ i : Fin 5, s.getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) = original.getWord32 (BitVec.ofNat 64 (0x42000+4*i.val))) ∧
    (∀ i : Fin 5, s.getWord32 (BitVec.ofNat 64 (base+4*i.val)) =
      if i.val < count then original.getWord32 (BitVec.ofNat 64 (base+4*i.val)) ^^^ original.getWord32 (BitVec.ofNat 64 (0x42000+4*i.val))
      else original.getWord32 (BitVec.ofNat 64 (base+4*i.val)))

private theorem xor_step (original s : MachineState) (base : Nat) (slot : Fin 5)
    (aligned : base%4 = 0) (bounded : base+20 ≤ 0x40000)
    (inv : Invariant original base slot.val s) : Invariant original base (slot.val+1) (xorWord slot s) := by
  obtain ⟨ptr,pad,source,values⟩ := inv
  obtain ⟨ptrAfter,padAfter⟩ := xorWord_registers slot s
  refine ⟨ptrAfter.trans ptr,padAfter.trans pad,?_,?_⟩
  · intro i
    rw [xorWord_lane_frame slot s base (0x42000+4*i.val) ptr (by omega) (by omega) aligned (by omega) (by omega)]
    exact source i
  · intro i
    by_cases same : slot = i
    · subst i
      rw [xorWord_data slot s base ptr pad,source,values]
      simp
    · have ne : slot.val ≠ i.val := fun h => same (Fin.ext h)
      rw [xorWord_lane_frame slot s base (base+4*i.val) ptr (by omega) (by omega) aligned (by omega) (by omega),values]
      by_cases before : i.val < slot.val
      · simp [before,show i.val < slot.val+1 by omega]
      · simp [before,show ¬ i.val < slot.val+1 by omega]

theorem applyXor_data (s : MachineState) (base : Nat)
    (ptr : s.getReg .x6 = BitVec.ofNat 64 base) (pad : s.getReg .x12 = 0x42000)
    (aligned : base%4 = 0) (bounded : base+20 ≤ 0x40000) (i : Fin 5) :
    (applyXor s).getWord32 (BitVec.ofNat 64 (base+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (base+4*i.val)) ^^^ s.getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) := by
  have inv : Invariant s base 0 s := ⟨ptr,pad,fun _ => rfl,by intro i;simp⟩
  have h0 := xor_step s s base 0 aligned bounded inv
  have h1 := xor_step s (xorWord 0 s) base 1 aligned bounded h0
  have h2 := xor_step s (xorWord 1 (xorWord 0 s)) base 2 aligned bounded h1
  have h3 := xor_step s (xorWord 2 (xorWord 1 (xorWord 0 s))) base 3 aligned bounded h2
  have h4 := xor_step s (xorWord 3 (xorWord 2 (xorWord 1 (xorWord 0 s)))) base 4 aligned bounded h3
  rw [applyXor_eq]
  simpa using h4.2.2.2 i

theorem xorWord_mem_frame (i : Fin 5) (s : MachineState) (a : Word)
    (outside : a ≠ alignToDword (s.getReg .x6 + signExtend12 (4#12 * BitVec.ofNat 12 i.val))) :
    (xorWord i s).getMem a = s.getMem a := by
  simp [xorWord,execInstrBr,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,outside]

theorem applyXor_mem_frame (s : MachineState) (a : Word)
    (outside : ∀ i : Fin 5, a ≠ alignToDword (s.getReg .x6 + signExtend12 (4#12 * BitVec.ofNat 12 i.val))) :
    (applyXor s).getMem a = s.getMem a := by
  have h0 := outside 0
  have h1 := outside 1
  have h2 := outside 2
  have h3 := outside 3
  have h4 := outside 4
  change a ≠ alignToDword (s.getReg .x6 + 0#64) at h0
  change a ≠ alignToDword (s.getReg .x6 + 4#64) at h1
  change a ≠ alignToDword (s.getReg .x6 + 8#64) at h2
  change a ≠ alignToDword (s.getReg .x6 + 12#64) at h3
  change a ≠ alignToDword (s.getReg .x6 + 16#64) at h4
  simp only [BitVec.add_zero] at h0
  simp [applyXor,runSchedule,xorSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,h0,h1,h2,h3,h4]

theorem applyXor_high_frame (s : MachineState) (base : Nat) (ptr : s.getReg .x6 = BitVec.ofNat 64 base)
    (bounded : base+20 ≤ 0x40000) (a : Word) (high : 0x40000 ≤ a.toNat) :
    (applyXor s).getMem a = s.getMem a := by
  apply applyXor_mem_frame
  intro i equal
  have address : s.getReg .x6 + signExtend12 (4#12 * BitVec.ofNat 12 i.val) = BitVec.ofNat 64 (base+4*i.val) := by
    rw [ptr];fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
  rw [address] at equal
  have small : (alignToDword (BitVec.ofNat 64 (base+4*i.val))).toNat < 0x40000 := by
    unfold alignToDword
    rw [BitVec.toNat_and]
    apply lt_of_le_of_lt Nat.and_le_left
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [← equal] at small
  omega

/-- info: 'SigGolfCandidate.SphincsMaskedMaskXor.applyXor_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyXor_data

end SigGolfCandidate.SphincsMaskedMaskXor
