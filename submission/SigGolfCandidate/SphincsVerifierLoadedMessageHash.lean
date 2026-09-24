import SigGolfCandidate.SphincsVerifierMessageReady

/-!
# The loaded verifier's exact message-digest HASH query

The native verifier executes 107 instructions after the first HASH answer,
then calls HASH on the scheme's 112-byte message-digest input.
-/

namespace SigGolfCandidate.SphincsVerifierLoadedMessageHash
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierMessageHash
open SigGolfCandidate.SphincsVerifierMessageReady
open SigGolfCandidate.SphincsVerifierSecondHashPayload
open SigGolfCandidate.SphincsVerifierSecondHashBytes
open SigGolfCandidate.SphincsVerifierLoader
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierWitnessFrame
open SigGolfCandidate.SphincsSubmission

theorem loaded_message_ready (publicKey : SigGolf.PublicKey)
    (message : SigGolf.Message)
    (witness : Bytes SphincsWire.signatureBytes)
    (inner : SphincsSecurity.PublicKey)
    (randomness : Randomness)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState submission .verify (message, publicKey, witness) =
      some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64)
    (encoded : EncodedWitness witness inner)
    (encodedRandomness : ∀ i, (hi : i < 20) →
      witness.extractLsb' (8 * (40 + i)) 8 =
        randomness.extractLsb' (8 * i) 8) :
    ∃ ready, OrdinarySteps SphincsImages.verify
      (writeHash (SphincsVerifierHashSetup.firstHashState state) answer)
      107 ready ∧ ready.pc = 0x12a0 ∧
      MessageReady ready inner message randomness := by
  obtain ⟨ready, trace, pc, source, bits, destination, service,
    messageWords, fieldWords, parameterWords, header⟩ :=
    loaded_secondHash_payload publicKey message witness state answer
      loaded answerMatches
  have parameterBytes := parameter_bytes_of_words ready state inner
    parameterWords
    (loaded_prefix publicKey message witness inner state loaded encoded)
  have randomizerBytes := randomizer_bytes_of_words ready witness randomness
    (by
      intro index
      simpa [destinationWord, destinationBase, witnessOffset] using
        fieldWords .randomizer index)
    encodedRandomness
  have rootBytes := root_bytes_of_words ready witness inner
    (by
      intro index
      simpa [destinationWord, destinationBase, witnessOffset] using
        fieldWords .root index)
    encoded
  have messageBytes := message_bytes_of_words ready message messageWords
  exact ⟨ready, trace, pc,
    of_fields ready inner message randomness source bits destination service
      (by intro i hi; exact header ⟨i, hi⟩)
      parameterBytes randomizerBytes rootBytes messageBytes⟩

/-- info: 'SigGolfCandidate.SphincsVerifierLoadedMessageHash.loaded_message_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_message_ready

end SigGolfCandidate.SphincsVerifierLoadedMessageHash
