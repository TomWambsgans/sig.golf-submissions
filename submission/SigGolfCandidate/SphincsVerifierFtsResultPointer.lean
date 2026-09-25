import SigGolfCandidate.SphincsVerifierFtsResultWitness

/-! The FORS path pointer survives the parent HASH and level loopback. -/

namespace SigGolfCandidate.SphincsVerifierFtsResultPointer
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsParentResult
open SigGolfCandidate.SphincsVerifierFtsParentLevel
open SigGolfCandidate.SphincsVerifierFtsParentLoop
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierFtsResultWitness
set_option maxRecDepth 16384

theorem hashedResult_pointer (state : MachineState)
    (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (resultState (writeHash state answer)).getMem 0x43028 =
      state.getMem 0x43028 := by
  change (SphincsVerifierCopy.copyRootState
    (resultPointers (writeHash state answer))).getMem 0x43028 = _
  rw [SphincsVerifierCopyMemory.copyRoot_mem_frame _ 0x43028 (by
    intro offset
    rw [(resultPointers_regs _).2]
    fin_cases offset <;> decide)]
  rw [resultPointers_mem]
  exact writeHash_mem_frame state answer destination 0x43028
    (by decide) (by decide) (by decide) (by decide)

theorem parentLoop_pointer (state : MachineState) :
    (levelBranchState (levelCheckState (advanceLevelState state))).getMem
      0x43028 = state.getMem 0x43028 := by
  rw [levelBranch_mem, levelCheck_mem,
    advanceLevel_mem_frame state 0x43028 (by decide)]

theorem fullParent_pointer (state : MachineState)
    (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (levelBranchState (levelCheckState
      (advanceLevelState (resultState (writeHash state answer))))).getMem
      0x43028 = state.getMem 0x43028 := by
  rw [parentLoop_pointer]
  exact hashedResult_pointer state answer destination

/-- info: 'SigGolfCandidate.SphincsVerifierFtsResultPointer.fullParent_pointer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fullParent_pointer

end SigGolfCandidate.SphincsVerifierFtsResultPointer
