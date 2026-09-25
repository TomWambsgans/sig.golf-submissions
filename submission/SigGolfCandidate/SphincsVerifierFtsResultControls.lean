import SigGolfCandidate.SphincsVerifierFtsResultPointer

/-! Parent HASH and loopback preserve the FORS tree and selector control cells. -/

namespace SigGolfCandidate.SphincsVerifierFtsResultControls
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsParentResult
open SigGolfCandidate.SphincsVerifierFtsParentLevel
open SigGolfCandidate.SphincsVerifierFtsParentLoop
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierFtsResultWitness
set_option maxRecDepth 16384

theorem hashedResult_mem_frame (state : MachineState)
    (answer : BitVec 256) (read : Word)
    (destination : state.getReg .x12 = 0x42000)
    (not0 : read ≠ 0x42000) (not8 : read ≠ 0x42008)
    (not16 : read ≠ 0x42010) (not24 : read ≠ 0x42018)
    (notCopy : ∀ offset : Fin 5,
      read ≠ alignToDword
        (0x44a00 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val))) :
    (resultState (writeHash state answer)).getMem read =
      state.getMem read := by
  change (SphincsVerifierCopy.copyRootState
    (resultPointers (writeHash state answer))).getMem read = _
  rw [SphincsVerifierCopyMemory.copyRoot_mem_frame _ read (by
    intro offset
    rw [(resultPointers_regs _).2]
    exact notCopy offset)]
  rw [resultPointers_mem]
  exact writeHash_mem_frame state answer destination read
    not0 not8 not16 not24

theorem fullParent_mem_frame (state : MachineState)
    (answer : BitVec 256) (read : Word)
    (destination : state.getReg .x12 = 0x42000)
    (notLevel : read ≠ 0x43048)
    (not0 : read ≠ 0x42000) (not8 : read ≠ 0x42008)
    (not16 : read ≠ 0x42010) (not24 : read ≠ 0x42018)
    (notCopy : ∀ offset : Fin 5,
      read ≠ alignToDword
        (0x44a00 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val))) :
    (levelBranchState (levelCheckState
      (advanceLevelState (resultState (writeHash state answer))))).getMem
      read = state.getMem read := by
  rw [levelBranch_mem, levelCheck_mem,
    advanceLevel_mem_frame _ read notLevel]
  exact hashedResult_mem_frame state answer read destination
    not0 not8 not16 not24 notCopy

theorem fullParent_tree (state : MachineState)
    (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (levelBranchState (levelCheckState
      (advanceLevelState (resultState (writeHash state answer))))).getMem
      0x43000 = state.getMem 0x43000 := by
  apply fullParent_mem_frame state answer 0x43000 destination
  all_goals try { intro offset; fin_cases offset <;> decide }
  all_goals decide

theorem fullParent_selector (state : MachineState)
    (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (levelBranchState (levelCheckState
      (advanceLevelState (resultState (writeHash state answer))))).getMem
      0x43070 = state.getMem 0x43070 := by
  apply fullParent_mem_frame state answer 0x43070 destination
  all_goals try { intro offset; fin_cases offset <;> decide }
  all_goals decide

theorem fullParent_index (state : MachineState)
    (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (levelBranchState (levelCheckState
      (advanceLevelState (resultState (writeHash state answer))))).getMem
      0x43008 = state.getMem 0x43008 := by
  apply fullParent_mem_frame state answer 0x43008 destination
  all_goals try { intro offset; fin_cases offset <;> decide }
  all_goals decide

theorem fullParent_level (state : MachineState)
    (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (levelBranchState (levelCheckState
      (advanceLevelState (resultState (writeHash state answer))))).getMem
      0x43048 = state.getMem 0x43048 + 1 := by
  rw [levelBranch_mem, levelCheck_mem, advanceLevel_cell]
  exact congrArg (· + 1) (hashedResult_mem_frame state answer 0x43048
    destination (by decide) (by decide) (by decide) (by decide)
    (by intro offset; fin_cases offset <;> decide))

/-- info: 'SigGolfCandidate.SphincsVerifierFtsResultControls.fullParent_mem_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullParent_mem_frame

end SigGolfCandidate.SphincsVerifierFtsResultControls
