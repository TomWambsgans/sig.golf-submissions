import SigGolfCandidate.SphincsVerifierMessageInputBytes

/-!
# Byte-level invariant for the verifier's second HASH call

This packages the five serialized fields into the exact oracle input expected
by the abstract scheme.
-/

namespace SigGolfCandidate.SphincsVerifierMessageReady
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierMessageHash
open SigGolfCandidate.SphincsVerifierMessageInputBytes

theorem of_fields (state : MachineState) (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message) (randomness : Randomness)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 896)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1)
    (header : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x40000 + i)) =
        ((fieldBytes (tweakFields 12 0 0 0 0)).map UInt8.toBitVec)[i]'(by
          simpa [fieldBytes, bytesLE] using hi))
    (parameter : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x40014 + i)) =
        pk.parameter.extractLsb' (8 * i) 8)
    (randomizer : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        randomness.extractLsb' (8 * i) 8)
    (root : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x4003c + i)) =
        pk.root.extractLsb' (8 * i) 8)
    (messageBytes : ∀ i, (hi : i < 32) →
      state.getByte (BitVec.ofNat 64 (0x40050 + i)) =
        message.extractLsb' (8 * i) 8) :
    MessageReady state pk message randomness := by
  refine ⟨source, bits, destination, service, ?_⟩
  intro i hi
  have hi112 : i < 112 := by simpa [messageInput_length] using hi
  by_cases first : i < 20
  · exact (header i first).trans (input_header pk message randomness i first).symm
  by_cases second : i < 40
  · let j := i - 20
    have hj : j < 20 := by dsimp [j]; omega
    have e : i = 20 + j := by dsimp [j]; omega
    simpa [e, show 0x40000 + (20 + j) = 0x40014 + j by omega] using
      (parameter j hj).trans (input_parameter pk message randomness j hj).symm
  by_cases third : i < 60
  · let j := i - 40
    have hj : j < 20 := by dsimp [j]; omega
    have e : i = 40 + j := by dsimp [j]; omega
    simpa [e, show 0x40000 + (40 + j) = 0x40028 + j by omega] using
      (randomizer j hj).trans (input_randomizer pk message randomness j hj).symm
  by_cases fourth : i < 80
  · let j := i - 60
    have hj : j < 20 := by dsimp [j]; omega
    have e : i = 60 + j := by dsimp [j]; omega
    simpa [e, show 0x40000 + (60 + j) = 0x4003c + j by omega] using
      (root j hj).trans (input_root pk message randomness j hj).symm
  · let j := i - 80
    have hj : j < 32 := by dsimp [j]; omega
    have e : i = 80 + j := by dsimp [j]; omega
    simpa [e, show 0x40000 + (80 + j) = 0x40050 + j by omega] using
      (messageBytes j hj).trans (input_message pk message randomness j hj).symm

/-- info: 'SigGolfCandidate.SphincsVerifierMessageReady.of_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms of_fields

end SigGolfCandidate.SphincsVerifierMessageReady
