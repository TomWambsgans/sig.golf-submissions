import SigGolfCandidate.SphincsVerifierFtsRoundTrace

/-! A FORS parent round keeps the witness public-key prefix available. -/

namespace SigGolfCandidate.SphincsVerifierFtsRoundPrefix
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierFtsResultControls
open SigGolfCandidate.SphincsVerifierFtsRoundInvariant
open SigGolfCandidate.SphincsVerifierHashBytes
set_option maxRecDepth 16384

private theorem low_ne (read written : Word)
    (low : read.toNat < 0x40000)
    (high : 0x40000 ≤ written.toNat) : read ≠ written := by
  intro equal
  have same := congrArg BitVec.toNat equal
  omega

theorem parentRound_low_mem_frame (start : MachineState)
    (answer : BitVec 256) (read : Word)
    (low : read.toNat < 0x40000) :
    (parentRoundState start answer).getMem read = start.getMem read := by
  let positioned := firstPositionedState start
  let ready := firstParentReadyState start
  have notCopy : ∀ offset : Fin 5,
      read ≠ alignToDword
        (0x44a00 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    apply low_ne read _ low
    fin_cases offset <;> decide
  have resultFrame : (parentRoundState start answer).getMem read =
      ready.getMem read := by
    apply fullParent_mem_frame ready answer read (ready_destination start)
    · exact low_ne read 0x43048 low (by decide)
    · exact low_ne read 0x42000 low (by decide)
    · exact low_ne read 0x42008 low (by decide)
    · exact low_ne read 0x42010 low (by decide)
    · exact low_ne read 0x42018 low (by decide)
    · exact notCopy
  calc
    (parentRoundState start answer).getMem read = ready.getMem read := resultFrame
    _ = positioned.getMem read := parentHashReady_mem_frame positioned read (Or.inl low)
    _ = start.getMem read := positioned_low_mem_frame start read low

theorem parentRound_WitnessPrefix (start : MachineState)
    (answer : BitVec 256) (pk : SphincsSecurity.PublicKey)
    (hprefix : WitnessPrefix start pk) :
    WitnessPrefix (parentRoundState start answer) pk := by
  constructor
  · intro i hi
    have low : (alignToDword (BitVec.ofNat 64 (0x22ca0 + i))).toNat <
        0x40000 := by
      apply witnessByte_aligned_low i
      have size := SphincsWire.signatureBytes_eq
      omega
    change (parentRoundState start answer).getByte
      (BitVec.ofNat 64 (0x22ca0 + i)) = _
    simp only [MachineState.getByte]
    rw [parentRound_low_mem_frame start answer _ low]
    exact hprefix.root i hi
  · intro i hi
    have low : (alignToDword (BitVec.ofNat 64 (0x22cb4 + i))).toNat <
        0x40000 := by
      have same : (0x22cb4 + i : Nat) = 0x22ca0 + (20 + i) := by omega
      rw [same]
      apply witnessByte_aligned_low (20 + i)
      have size := SphincsWire.signatureBytes_eq
      omega
    simp only [MachineState.getByte]
    rw [parentRound_low_mem_frame start answer _ low]
    exact hprefix.parameter i hi

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRoundPrefix.parentRound_WitnessPrefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentRound_WitnessPrefix

end SigGolfCandidate.SphincsVerifierFtsRoundPrefix
