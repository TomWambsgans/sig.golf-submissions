import SigGolfCandidate.SphincsVerifierFtsParentLoop

/-! The FORS parent-pair instructions preserve the submitted public-key bytes. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentWitness
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierHashBytes
set_option maxRecDepth 16384

theorem positioned_witness_byte (start : MachineState) (base : Nat)
    (supported : base = 0x22ca0 ∨ base = 0x22cb4)
    (i : Fin 20) :
    (firstPositionedState start).getByte
      (BitVec.ofNat 64 (base + i.val)) =
        start.getByte (BitVec.ofNat 64 (base + i.val)) := by
  let address := alignToDword (BitVec.ofNat 64 (base + i.val))
  let pair := pairState start
  let advanced := advancePointerState pair
  let shifted := shiftIndexState advanced
  have pairFrame : pair.getMem address = start.getMem address := by
    apply pair_scratch_frame
    · intro offset
      rcases supported with h | h <;> subst base <;>
        fin_cases i <;> fin_cases offset <;> decide
    · intro offset
      rcases supported with h | h <;> subst base <;>
        fin_cases i <;> fin_cases offset <;> decide
  have addressFrame :
      address ≠ 0x43028 ∧ address ≠ 0x43070 ∧
      address ≠ 0x43018 ∧ address ≠ 0x43010 := by
    rcases supported with h | h <;> subst base <;>
      fin_cases i <;> decide
  simp only [MachineState.getByte, firstPositionedState]
  change extractByte ((levelPositionState shifted).getMem address) _ = _
  rw [levelPosition_mem_frame shifted address addressFrame.2.2.2,
    shiftIndex_mem_frame advanced address addressFrame.2.1
      addressFrame.2.2.1,
    advancePointer_mem_frame pair address addressFrame.1,
    pairFrame]

theorem positioned_WitnessPrefix (start : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (witnessPrefix : WitnessPrefix start pk) :
    WitnessPrefix (firstPositionedState start) pk := by
  constructor
  · intro i hi
    let offset : Fin 20 := ⟨i, hi⟩
    rw [show i = offset.val by rfl,
      positioned_witness_byte start 0x22ca0 (Or.inl rfl) offset]
    exact witnessPrefix.root i hi
  · intro i hi
    let offset : Fin 20 := ⟨i, hi⟩
    rw [show i = offset.val by rfl,
      positioned_witness_byte start 0x22cb4 (Or.inr rfl) offset]
    exact witnessPrefix.parameter i hi

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentWitness.positioned_WitnessPrefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms positioned_WitnessPrefix

end SigGolfCandidate.SphincsVerifierFtsParentWitness
