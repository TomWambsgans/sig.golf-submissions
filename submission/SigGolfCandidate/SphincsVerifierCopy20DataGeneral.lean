import SigGolfCandidate.SphincsVerifierFtsLeafCopy

/-! Data transfer facts for the verifier's five 32-bit load/store pairs. -/

namespace SigGolfCandidate.SphincsVerifierCopy20DataGeneral
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
set_option maxRecDepth 16384

theorem copyWord_data_general (offset : Fin 5) (state : MachineState)
    (sourceBase destinationBase : Nat)
    (source : state.getReg .x6 = BitVec.ofNat 64 sourceBase)
    (destination : state.getReg .x7 = BitVec.ofNat 64 destinationBase) :
    (copyWordState offset state).getWord32
      (BitVec.ofNat 64 (destinationBase + 4 * offset.val)) =
      state.getWord32 (BitVec.ofNat 64 (sourceBase + 4 * offset.val)) := by
  fin_cases offset <;>
    simp [copyWordState, execInstrBr, getWord32_setWord32_same,
      source, destination, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      BitVec.ofNat_add]

end SigGolfCandidate.SphincsVerifierCopy20DataGeneral
