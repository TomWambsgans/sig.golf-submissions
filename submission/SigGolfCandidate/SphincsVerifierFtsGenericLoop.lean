import SigGolfCandidate.SphincsVerifierFtsGenericHashStep

/-! Loop back after any nonfinal FORS authentication level. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsParentLevel
open SigGolfCandidate.SphincsVerifierFtsParentLoop
set_option maxRecDepth 16384

theorem parent_loopBack_generic (state : MachineState) (level : Nat)
    (pc : state.pc = 0x1b54)
    (levelValue : state.getMem 0x43048 = BitVec.ofNat 64 level)
    (notFinal : level < 8) :
    let advanced := advanceLevelState state
    let checked := levelCheckState advanced
    let branched := levelBranchState checked
    OrdinarySteps SphincsImages.verify state 12 branched ∧
      branched.pc = 0x1914 ∧
      branched.getMem 0x43048 = BitVec.ofNat 64 (level + 1) := by
  let advanced := advanceLevelState state
  let checked := levelCheckState advanced
  let branched := levelBranchState checked
  have first := advanceLevel_block state pc
  have nextPc := advanceLevel_pc state pc
  have second := levelCheck_block advanced nextPc
  have checkedPc := levelCheck_pc advanced nextPc
  have values := levelCheck_values advanced
  have advancedLevel : advanced.getMem 0x43048 =
      BitVec.ofNat 64 (level + 1) := by
    rw [advanceLevel_cell, levelValue, BitVec.ofNat_add]
    rfl
  have unequal : checked.getReg .x6 ≠ checked.getReg .x7 := by
    rw [values.1, values.2, advancedLevel]
    interval_cases level <;> decide
  have third := levelBranch_block checked checkedPc
  exact ⟨(first.append second).append third,
    levelBranch_pc_repeat checked checkedPc unequal,
    by rw [levelBranch_mem, levelCheck_mem]; exact advancedLevel⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericLoop.parent_loopBack_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parent_loopBack_generic

end SigGolfCandidate.SphincsVerifierFtsGenericLoop
