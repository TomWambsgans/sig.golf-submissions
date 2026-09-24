import SigGolfCandidate.SphincsVerifierSecondHashSetup

/-!
# Verifier trace to the message-index HASH call

After an accepting public-key commitment answer, 65 instructions copy the
message and witness fields. The next 42 instructions construct the second HASH
header, copy its public parameter, and select the 896-bit HASH service.
-/

namespace SigGolfCandidate.SphincsVerifierSecondHashTrace
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsSubmission
open SigGolfCandidate.SphincsVerifierSecondHashSetup
open SigGolfCandidate.SphincsVerifierWitnessAtHash

theorem loaded_secondHashReady (publicKey : SigGolf.PublicKey)
    (message : Message) (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState submission .verify (message, publicKey, witness) =
      some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64) :
    ∃ ready,
      OrdinarySteps SphincsImages.verify
        (writeHash (SphincsVerifierHashSetup.firstHashState state) answer)
        107 ready ∧
      ready.pc = 0x12a0 ∧
      ready.getReg .x10 = 0x40000 ∧
      ready.getReg .x11 = 896 ∧
      ready.getReg .x12 = 0x42000 ∧
      ready.getReg .x5 = 1 := by
  obtain ⟨copied, trace, inv, _, _⟩ :=
    loaded_message_payload_exact publicKey message witness state answer
      loaded answerMatches
  have copiedPc : copied.pc = 0x11f8 := by
    simpa [SphincsVerifierMessage32.LoopInvariant] using inv.2.1
  let ready := secondHashReadyState copied
  have next := secondHashReady_block copied copiedPc
  refine ⟨ready, ?_, secondHashReady_pc copied copiedPc, ?_⟩
  · simpa [ready] using trace.append next
  · exact secondHashReady_regs copied

/-- info: 'SigGolfCandidate.SphincsVerifierSecondHashTrace.loaded_secondHashReady' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_secondHashReady

end SigGolfCandidate.SphincsVerifierSecondHashTrace
