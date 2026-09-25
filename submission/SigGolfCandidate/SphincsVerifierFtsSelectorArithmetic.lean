import SigGolfCandidate.SphincsVerifierFtsResultControls

/-! Relate the machine's shifted FORS selector to the abstract leaf index. -/

namespace SigGolfCandidate.SphincsVerifierFtsSelectorArithmetic
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsLevelBranch
open SigGolfCandidate.SphincsVerifierFtsLevelShift
set_option maxRecDepth 16384

theorem selector_shift_nat (leaf : FtsLeaf) (level : Nat) :
    ((BitVec.ofNat 64 leaf.val) >>> level).toNat =
      leaf.val / 2 ^ level := by
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt]
  have bound := leaf.isLt
  norm_num [ftsTreeHeight] at bound ⊢
  omega

theorem selector_parent_index (leaf : FtsLeaf) (level : Nat) :
    ((BitVec.ofNat 64 leaf.val >>> level) >>> 1) =
      BitVec.ofNat 64 (leaf.val / 2 ^ (level + 1)) := by
  have small : leaf.val < 2 ^ 64 := by
    have bound := leaf.isLt
    norm_num [ftsTreeHeight] at bound ⊢
    omega
  have quotientSmall : leaf.val / 2 ^ (level + 1) < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) small
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt small, Nat.div_div_eq_div_mul,
    Nat.mod_eq_of_lt quotientSmall]
  simp [pow_succ]

theorem selector_next (leaf : FtsLeaf) (level : Nat) :
    ((BitVec.ofNat 64 leaf.val >>> level) >>> 1) =
      BitVec.ofNat 64 leaf.val >>> (level + 1) := by
  rw [selector_parent_index]
  apply BitVec.eq_of_toNat_eq
  rw [selector_shift_nat, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have bound := leaf.isLt
  have small : leaf.val < 2 ^ 64 := by
    norm_num [ftsTreeHeight] at bound ⊢
    omega
  exact lt_of_le_of_lt (Nat.div_le_self _ _) small

theorem selector_parity_nat (leaf : FtsLeaf) (level : Nat) :
    (((BitVec.ofNat 64 leaf.val) >>> level) &&& 1).toNat =
      (leaf.val / 2 ^ level) % 2 := by
  rw [BitVec.toNat_and, selector_shift_nat]
  simp

theorem selector_parity_zero (leaf : FtsLeaf) (level : Nat) :
    (((BitVec.ofNat 64 leaf.val) >>> level) &&& 1 = 0) ↔
      (leaf.val / 2 ^ level) % 2 = 0 := by
  constructor
  · intro h
    have hNat := congrArg BitVec.toNat h
    rw [selector_parity_nat] at hNat
    exact hNat
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [selector_parity_nat, h]
    rfl

theorem selector_parity_testBit (leaf : FtsLeaf) (level : Nat) :
    (((BitVec.ofNat 64 leaf.val) >>> level) &&& 1 = 0) ↔
      leaf.val.testBit level = false := by
  rw [selector_parity_zero]
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem machine_parity_testBit (state : MachineState)
    (leaf : FtsLeaf) (level : Nat)
    (selector : state.getMem 0x43070 =
      BitVec.ofNat 64 leaf.val >>> level) :
    (parityState state).getReg .x6 = 0 ↔
      leaf.val.testBit level = false := by
  rw [parity_reg, selector]
  exact selector_parity_testBit leaf level

theorem machine_parent_index (state : MachineState)
    (leaf : FtsLeaf) (level : Nat)
    (selector : state.getMem 0x43070 =
      BitVec.ofNat 64 leaf.val >>> level) :
    (shiftIndexState state).getMem 0x43018 =
      BitVec.ofNat 64 (leaf.val / 2 ^ (level + 1)) := by
  rw [(shiftIndex_cells state).2, selector]
  exact selector_parent_index leaf level

/-- info: 'SigGolfCandidate.SphincsVerifierFtsSelectorArithmetic.machine_parity_testBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms machine_parity_testBit

/-- info: 'SigGolfCandidate.SphincsVerifierFtsSelectorArithmetic.machine_parent_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms machine_parent_index

end SigGolfCandidate.SphincsVerifierFtsSelectorArithmetic
