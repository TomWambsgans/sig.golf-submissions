import SigGolfCandidate.SphincsVerifierWotsSemanticFrame
import SigGolfCandidate.SphincsVerifierFtsPostForestCopy

namespace SigGolfCandidate.SphincsVerifierWotsSemanticLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsSemanticFrame
open SigGolfCandidate.SphincsVerifierWotsStepIteration
open SigGolfCandidate.SphincsVerifierFtsPostForestCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- One exact WOTS hash step preserves the public-key prefix inside the witness. -/
theorem stepNext_witnessPrefix (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk) :
    SphincsVerifierHashBytes.WitnessPrefix (stepNext hash state) pk := by
  apply witnessPrefix_of_low_mem_frame state (stepNext hash state) pk hprefix
  intro address low
  exact stepNext_safeFrame hash state address (Or.inl low)

/-- The exact WOTS hash step cannot alter its layer, tree, leaf, or chain controls. -/
theorem stepNext_controlCells (hash : Hash) (state : MachineState) :
    (stepNext hash state).getMem 0x43000 = state.getMem 0x43000 ∧
    (stepNext hash state).getMem 0x43008 = state.getMem 0x43008 ∧
    (stepNext hash state).getMem 0x43018 = state.getMem 0x43018 ∧
    (stepNext hash state).getMem 0x43050 = state.getMem 0x43050 := by
  constructor
  · exact stepNext_safeFrame hash state _ (Or.inr ⟨by decide, by decide, by decide, by decide⟩)
  constructor
  · exact stepNext_safeFrame hash state _ (Or.inr ⟨by decide, by decide, by decide, by decide⟩)
  constructor
  · exact stepNext_safeFrame hash state _ (Or.inr ⟨by decide, by decide, by decide, by decide⟩)
  · exact stepNext_safeFrame hash state _ (Or.inr ⟨by decide, by decide, by decide, by decide⟩)

#print axioms stepNext_witnessPrefix
#print axioms stepNext_controlCells

end SigGolfCandidate.SphincsVerifierWotsSemanticLoop
