import SigGolfCandidate.SphincsVerifierXmssPathComplete

namespace SigGolfCandidate.SphincsVerifierXmssTransition
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssNext
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsVerifierXmssNodeSite
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def targetLayer (target : Fin 5) : Layer := ⟨target.val, by
  exact lt_trans target.isLt (by decide)⟩

def previousLayer (target : Fin 5) : Layer := ⟨target.val + 1, by
  have := target.isLt
  simp only [numLayers]
  omega⟩

def transitionPc (target : Fin 5) : Word :=
  branchPc (previousLayer target) + 4

def transitionSchedule (target : Fin 5) : List (Word × Instr) :=
  let p := transitionPc target
  let lay := targetLayer target
  [
  (p, .ADDI .x6 .x0 (BitVec.ofNat 12 lay.val)),
  (p + 4, .LUI .x28 0x43),
  (p + 8, .ADDI .x28 .x28 0),
  (p + 12, .SD .x28 .x6 0),
  (p + 16, .LUI .x28 0x43),
  (p + 20, .ADDI .x28 .x28 120),
  (p + 24, .LD .x6 .x28 0),
  (p + 28, .SRLI .x6 .x6
    (BitVec.ofNat 6 (heightBelow lay + layerHeight lay))),
  (p + 32, .LUI .x28 0x43),
  (p + 36, .ADDI .x28 .x28 8),
  (p + 40, .SD .x28 .x6 0),
  (p + 44, .LUI .x28 0x43),
  (p + 48, .ADDI .x28 .x28 120),
  (p + 52, .LD .x6 .x28 0),
  (p + 56, .SRLI .x6 .x6 (BitVec.ofNat 6 (heightBelow lay))),
  (p + 60, .ANDI .x6 .x6 (BitVec.ofNat 12 (2 ^ layerHeight lay - 1))),
  (p + 64, .LUI .x28 0x43),
  (p + 68, .ADDI .x28 .x28 32),
  (p + 72, .SD .x28 .x6 0),
  (p + 76, .ADDI .x6 .x0 0),
  (p + 80, .LUI .x28 0x43),
  (p + 84, .ADDI .x28 .x28 16),
  (p + 88, .SD .x28 .x6 0),
  (p + 92, .LUI .x28 0x43),
  (p + 96, .ADDI .x28 .x28 32),
  (p + 100, .LD .x6 .x28 0),
  (p + 104, .LUI .x28 0x43),
  (p + 108, .ADDI .x28 .x28 24),
  (p + 112, .SD .x28 .x6 0)]

theorem transition_code (target : Fin 5) :
    ∀ entry ∈ transitionSchedule target,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by
  fin_cases target <;>
    decide

def transitionState (target : Fin 5) (s : MachineState) : MachineState :=
  runSchedule (transitionSchedule target) s

theorem transition_checked (target : Fin 5) (s : MachineState)
    (pc : s.pc = transitionPc target) :
    Checked (transitionSchedule target) s := by
  fin_cases target <;>
    simp [Checked, transitionSchedule, transitionPc, targetLayer,
      previousLayer, branchPc, checkPc, advancePc, nodeHashPc, nodePc,
      heightBelow, layerHeight, maxLayerHeight, execInstrBr,
      ordinaryStep, memoryArgumentsValid, accessValid, rangeValid,
      MEMORY_BYTES, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, pc] <;> bv_decide

theorem transition_block (target : Fin 5) (s : MachineState)
    (pc : s.pc = transitionPc target) :
    OrdinarySteps SphincsImages.verify s 29 (transitionState target s) := by
  simpa only [transitionState,
      show (transitionSchedule target).length = 29 by
        simp [transitionSchedule]] using
    checked_sound _ (transitionSchedule target) (transition_code target)
      s (transition_checked target s pc)

theorem transition_pc (target : Fin 5) (s : MachineState)
    (pc : s.pc = transitionPc target) :
    (transitionState target s).pc = transitionPc target + 116 := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, transitionPc, previousLayer, branchPc,
      checkPc, advancePc, nodeHashPc, pc] <;>
    bv_decide

theorem transition_layer (target : Fin 5) (s : MachineState) :
    (transitionState target s).getMem 0x43000 =
      BitVec.ofNat 64 target.val := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] <;>
    decide

theorem transition_tree (target : Fin 5) (s : MachineState) :
    (transitionState target s).getMem 0x43008 =
      s.getMem 0x43078 >>>
        (heightBelow (targetLayer target) + layerHeight (targetLayer target)) := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      targetLayer, heightBelow, layerHeight, maxLayerHeight] <;>
    congr 1 <;> decide

theorem transition_leaf (target : Fin 5) (s : MachineState) :
    (transitionState target s).getMem 0x43020 =
      (s.getMem 0x43078 >>> heightBelow (targetLayer target)) &&&
        BitVec.ofNat 64 (2 ^ layerHeight (targetLayer target) - 1) := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      targetLayer, heightBelow, layerHeight, maxLayerHeight] <;>
    congr 1 <;> decide

theorem transition_level (target : Fin 5) (s : MachineState) :
    (transitionState target s).getMem 0x43010 = 0 := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem transition_index (target : Fin 5) (s : MachineState) :
    (transitionState target s).getMem 0x43018 =
      (transitionState target s).getMem 0x43020 := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem transition_global_index (target : Fin 5) (s : MachineState) :
    (transitionState target s).getMem 0x43078 = s.getMem 0x43078 := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem transition_current_mem (target : Fin 5) (s : MachineState)
    (read : Word) (inside : 0x44a00 ≤ read.toNat ∧ read.toNat < 0x44a18) :
    (transitionState target s).getMem read = s.getMem read := by
  have ne (address : Word) (small : address.toNat < 0x44a00) :
      read ≠ address := by
    intro h
    have eqNat := congrArg BitVec.toNat h
    omega
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] <;>
    split_ifs <;> bv_omega

theorem transition_current_byte (target : Fin 5) (s : MachineState)
    (i : Nat) (hi : i < 20) :
    (transitionState target s).getByte
        (BitVec.ofNat 64 (0x44a00 + i)) =
      s.getByte (BitVec.ofNat 64 (0x44a00 + i)) := by
  simp only [MachineState.getByte]
  rw [transition_current_mem target s _ (by interval_cases i <;> decide)]

/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransition.transition_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transition_block
/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransition.transition_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transition_tree
/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransition.transition_current_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transition_current_byte

end SigGolfCandidate.SphincsVerifierXmssTransition


namespace SigGolfCandidate.SphincsVerifierXmssTransitionIndex
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SphincsSecurity.Concrete
open SigGolfCandidate.SphincsVerifierXmssTransition
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem index_small (index : Index) : index.val < 2 ^ 64 := by
  exact lt_trans index.isLt (by decide)

theorem target_tree_exponent (target : Fin 5) :
    heightBelow (targetLayer target) + layerHeight (targetLayer target) =
      totalHeight - heightAbove (targetLayer target) := by
  fin_cases target <;> decide

theorem target_height_small (target : Fin 5) :
    2 ^ layerHeight (targetLayer target) - 1 < 2 ^ 64 := by
  fin_cases target <;> decide

theorem transition_tree_index (target : Fin 5) (s : MachineState)
    (index : Index)
    (global : s.getMem 0x43078 = BitVec.ofNat 64 index.val) :
    (transitionState target s).getMem 0x43008 =
      BitVec.ofNat 64 (treeIndexAt index (targetLayer target)).val := by
  rw [transition_tree, global]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (index_small index)]
  rw [target_tree_exponent]
  have small : (treeIndexAt index (targetLayer target)).val < 2 ^ 64 :=
    lt_trans (treeIndexAt index (targetLayer target)).isLt (by decide)
  rw [Nat.mod_eq_of_lt small]
  rfl

theorem transition_leaf_index (target : Fin 5) (s : MachineState)
    (index : Index)
    (global : s.getMem 0x43078 = BitVec.ofNat 64 index.val) :
    (transitionState target s).getMem 0x43020 =
      BitVec.ofNat 64 (leafIndexAt index (targetLayer target)).val := by
  rw [transition_leaf, global]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (index_small index),
    Nat.mod_eq_of_lt (target_height_small target)]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have small : (leafIndexAt index (targetLayer target)).val < 2 ^ 64 :=
    lt_trans (leafIndexAt index (targetLayer target)).isLt (by decide)
  rw [Nat.mod_eq_of_lt small]
  rfl

theorem transition_index_leaf (target : Fin 5) (s : MachineState)
    (index : Index)
    (global : s.getMem 0x43078 = BitVec.ofNat 64 index.val) :
    (transitionState target s).getMem 0x43018 =
      BitVec.ofNat 64 (leafIndexAt index (targetLayer target)).val := by
  rw [transition_index]
  exact transition_leaf_index target s index global

/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransitionIndex.transition_tree_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transition_tree_index
/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransitionIndex.transition_leaf_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transition_leaf_index

end SigGolfCandidate.SphincsVerifierXmssTransitionIndex
