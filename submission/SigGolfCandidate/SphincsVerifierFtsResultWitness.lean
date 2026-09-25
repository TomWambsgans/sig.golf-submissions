import SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame

/-! Parent HASH answers and the result copy preserve the entire signature witness. -/

namespace SigGolfCandidate.SphincsVerifierFtsResultWitness
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierFtsParentResult
open SigGolfCandidate.SphincsVerifierFtsWitnessFrame
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierFtsParentLevel
open SigGolfCandidate.SphincsVerifierFtsParentLoop
set_option maxRecDepth 16384

theorem resultPointers_mem (state : MachineState) (address : Word) :
    (resultPointers state).getMem address = state.getMem address := by
  simp [resultPointers, execInstrBr]

theorem resultState_lowByte_frame (state : MachineState) (address : Word)
    (low : (alignToDword address).toNat < 0x40000) :
    (resultState state).getByte address = state.getByte address := by
  simp only [MachineState.getByte, resultState]
  rw [copyRoot_mem_frame (resultPointers state) (alignToDword address)
    (by
      intro offset
      rw [(resultPointers_regs state).2]
      intro equal
      have same := congrArg BitVec.toNat equal
      have high : 0x40000 ≤
          (alignToDword (0x44a00 + signExtend12
            (4#12 * BitVec.ofNat 12 offset.val))).toNat := by
        fin_cases offset <;> decide
      omega)]
  rw [resultPointers_mem]

theorem resultState_FtsWitness (state : MachineState)
    (signature : SphincsSecurity.Signature)
    (witness : FtsWitness state signature) :
    FtsWitness (resultState state) signature := by
  apply FtsWitness.transport state _ signature witness
  intro i hi
  exact resultState_lowByte_frame state _ (witnessByte_aligned_low i hi)

theorem hashedResult_FtsWitness (state : MachineState)
    (answer : BitVec 256)
    (signature : SphincsSecurity.Signature)
    (destination : state.getReg .x12 = 0x42000)
    (witness : FtsWitness state signature) :
    FtsWitness (resultState (writeHash state answer)) signature := by
  have written : FtsWitness (writeHash state answer) signature := by
    apply FtsWitness.transport state _ signature witness
    intro i hi
    exact writeHash_allWitness_frame state answer i hi destination
  exact resultState_FtsWitness _ signature written

theorem parentLoop_FtsWitness (state : MachineState)
    (signature : SphincsSecurity.Signature)
    (witness : FtsWitness state signature) :
    FtsWitness
      (levelBranchState (levelCheckState (advanceLevelState state)))
      signature := by
  apply FtsWitness.transport state _ signature witness
  intro i hi
  simp only [MachineState.getByte]
  rw [levelBranch_mem, levelCheck_mem]
  have low := witnessByte_aligned_low i hi
  have other : alignToDword (BitVec.ofNat 64 (0x22ca0 + i)) ≠
      0x43048 := by
    intro equal
    have same := congrArg BitVec.toNat equal
    have high : (0x43048 : Word).toNat ≥ 0x40000 := by decide
    omega
  rw [advanceLevel_mem_frame state _ other]

theorem fullParent_FtsWitness (state : MachineState)
    (answer : BitVec 256)
    (signature : SphincsSecurity.Signature)
    (destination : state.getReg .x12 = 0x42000)
    (witness : FtsWitness state signature) :
    FtsWitness
      (levelBranchState (levelCheckState
        (advanceLevelState (resultState (writeHash state answer)))))
      signature :=
  parentLoop_FtsWitness _ signature
    (hashedResult_FtsWitness state answer signature destination witness)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsResultWitness.hashedResult_FtsWitness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms hashedResult_FtsWitness

/-- info: 'SigGolfCandidate.SphincsVerifierFtsResultWitness.fullParent_FtsWitness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fullParent_FtsWitness

end SigGolfCandidate.SphincsVerifierFtsResultWitness
