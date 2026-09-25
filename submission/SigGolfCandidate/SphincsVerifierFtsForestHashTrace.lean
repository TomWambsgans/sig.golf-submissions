import SigGolfCandidate.SphincsVerifierFtsForestHash

namespace SigGolfCandidate.SphincsVerifierFtsForestHashTrace
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsPostForestCopy
open SigGolfCandidate.SphincsVerifierFtsForestHashReady
open SigGolfCandidate.SphincsVerifierFtsForestHash
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- The exact post-FORS path reaches the 520-byte HASH service after 430
    ordinary instructions. The call costs nine compressions and 72 cycles. -/
theorem forest_hash_trace (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x1c08) (steps : Nat) (result : Execution)
    (tail : ∀ copied,
      OrdinarySteps SphincsImages.verify state 387 copied →
      copied.pc = 0x1c8c →
      Executes hash SphincsImages.verify
        (writeHash (forestHashReadyState copied)
          (hash (hashInput (forestHashReadyState copied)))) steps result) :
    Executes hash SphincsImages.verify state (steps + 431)
      (result.charge 502 1 9) := by
  obtain ⟨copied, copiedTrace, copiedPc, _⟩ :=
    forestRootBytes_copied state pc
  have header := forestHashReady_block copied copiedPc
  have final := hash_step hash (forestHashReadyState copied)
    header.2.1 header.2.2.1 header.2.2.2.1
    header.2.2.2.2.1 header.2.2.2.2.2
    steps result (tail copied copiedTrace copiedPc)
  have ordinary := copiedTrace.append header.1
  have combined := ordinary.then_executes final
  simpa [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using combined

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestHashTrace.forest_hash_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forest_hash_trace

end SigGolfCandidate.SphincsVerifierFtsForestHashTrace
