import SigGolfCandidate.SphincsVerifierMessageHash
import SigGolfCandidate.SphincsVerifierParameterAtHash

/-!
# Submitted payload at the second verifier HASH call

The verifier's 107 ordinary instructions after the commitment answer place
the submitted message and witness fields into the second HASH input. This
includes the public parameter, which remains in its original witness cells
until the final five-word copy.
-/

namespace SigGolfCandidate.SphincsVerifierSecondHashPayload
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierWitnessFrame
open SigGolfCandidate.SphincsVerifierParameterSourceFrame
open SigGolfCandidate.SphincsVerifierParameterAtHash
open SigGolfCandidate.SphincsVerifierSecondHashSetup
open SigGolfCandidate.SphincsVerifierSecondHashFrame
open SigGolfCandidate.SphincsSubmission

theorem parameter_word_of_cells (original final : MachineState)
    (cells : ∀ slot : Fin 3,
      final.getMem (parameterCell slot) =
        original.getMem (parameterCell slot))
    (index : Fin 5) :
    final.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  have address : ∃ slot : Fin 3,
      alignToDword (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
        parameterCell slot := by
    fin_cases index <;>
      first
      | exact ⟨0, by decide⟩
      | exact ⟨1, by decide⟩
      | exact ⟨1, by decide⟩
      | exact ⟨2, by decide⟩
      | exact ⟨2, by decide⟩
  obtain ⟨slot, eqCell⟩ := address
  simp only [MachineState.getWord32]
  rw [eqCell, cells slot]

theorem loaded_secondHash_payload (publicKey : SigGolf.PublicKey)
    (message : Message) (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState submission .verify (message, publicKey, witness) =
      some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64) :
    ∃ ready, OrdinarySteps SphincsImages.verify
      (writeHash (SphincsVerifierHashSetup.firstHashState state) answer)
      107 ready ∧
      ready.pc = 0x12a0 ∧
      ready.getReg .x10 = 0x40000 ∧ ready.getReg .x11 = 896 ∧
      ready.getReg .x12 = 0x42000 ∧ ready.getReg .x5 = 1 ∧
      (∀ index : Fin 4,
        ready.getMem (BitVec.ofNat 64 (0x40050 + 8 * index.val)) =
          message.extractLsb' (64 * index.val) 64) ∧
      (∀ pair : CopyPair, ∀ index : Fin 5,
        ready.getWord32 (destinationWord pair index) =
          witness.extractLsb'
            (8 * (witnessOffset pair + 4 * index.val)) 32) ∧
      (∀ index : Fin 5,
        ready.getWord32 (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
          state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val))) := by
  obtain ⟨copied, trace, inv, messageWords, fieldWords, parameterCells⟩ :=
    loaded_message_payload_parameter_exact publicKey message witness state
      answer loaded answerMatches
  have copiedPc : copied.pc = 0x11f8 := by
    simpa [SphincsVerifierMessage32.LoopInvariant] using inv.2.1
  let ready := secondHashReadyState copied
  have next := secondHashReady_block copied copiedPc
  have regs := secondHashReady_regs copied
  refine ⟨ready, ?_, secondHashReady_pc copied copiedPc,
    regs.1, regs.2.1, regs.2.2.1, regs.2.2.2,
    ?_, ?_, ?_⟩
  · simpa [ready] using trace.append next
  · intro index
    exact (secondHashReady_message_frame copied index).trans
      (messageWords index)
  · intro pair index
    exact (secondHashReady_field_frame copied pair index).trans
      (fieldWords pair index)
  · intro index
    exact (secondHashReady_data copied index).trans
      (parameter_word_of_cells state copied parameterCells index)

/-- info: 'SigGolfCandidate.SphincsVerifierSecondHashPayload.loaded_secondHash_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_secondHash_payload

end SigGolfCandidate.SphincsVerifierSecondHashPayload
