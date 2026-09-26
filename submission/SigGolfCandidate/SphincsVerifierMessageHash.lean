import SigGolfCandidate.SphincsVerifierSecondHashFrame
import SigGolfCandidate.SphincsVerifierSecondHashTrace

/-!
# The verifier's message-index HASH call

Given an exact 112-byte input-buffer invariant, the second ECALL issues the
scheme's message-digest query and charges two compressions and 16 cycles.
-/

namespace SigGolfCandidate.SphincsVerifierMessageHash
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierMessageCopy

def messageInput (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message) (randomness : Randomness) : List UInt8 :=
  tweakableHashInput pk.parameter .message
    (Concrete.messageDigestPayload pk.root message randomness)

theorem messageInput_length (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message) (randomness : Randomness) :
    (messageInput pk message randomness).length = 112 := by
  simp [messageInput, tweakableHashInput, tweakBytes, hashDomainFields,
    fieldBytes, Concrete.messageDigestPayload, bytesLE]

structure MessageReady (state : MachineState) (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message) (randomness : Randomness) : Prop where
  source : state.getReg .x10 = 0x40000
  bits : state.getReg .x11 = 896
  destination : state.getReg .x12 = 0x42000
  service : state.getReg .x5 = 1
  input : ∀ i, (hi : i < (messageInput pk message randomness).length) →
    state.getByte (BitVec.ofNat 64 (0x40000 + i)) =
      ((messageInput pk message randomness).map UInt8.toBitVec)[i]'(by simpa using hi)

theorem messageReady_hashInput (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (message : SphincsSecurity.Message)
    (randomness : Randomness)
    (ready : MessageReady state pk message randomness) :
    hashInput state = toQuery (messageInput pk message randomness) := by
  apply Serialization.hashInput_of_list state 0x40000
    ((messageInput pk message randomness).map UInt8.toBitVec)
  · exact ready.source
  · rw [ready.bits, List.length_map, messageInput_length]
    rfl
  · intro i hi
    exact ready.input i (by simpa using hi)

theorem messageReady_hashCost (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (message : SphincsSecurity.Message)
    (randomness : Randomness)
    (ready : MessageReady state pk message randomness) :
    hashArgumentsValid state = true ∧ compressions (hashInput state).1 = 2 := by
  constructor
  · simp [hashArgumentsValid, ready.source, ready.bits, ready.destination,
      accessValid, rangeValid, MEMORY_BYTES]
  · rw [messageReady_hashInput state pk message randomness ready]
    simp [toQuery, Serialization.legacyPacked,
      messageInput_length, compressions]

theorem hash_site (state : MachineState) (pc : state.pc = 0x12a0) :
    fetch SphincsImages.verify state = some (.base .ECALL) := by
  rw [fetch_index SphincsImages.verify state 168 (by decide)
    (by simpa using pc)]
  decide

theorem hash_step (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (message : SphincsSecurity.Message)
    (randomness : Randomness) (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash state (hash (toQuery (messageInput pk message randomness))))
      steps result) :
    Executes hash SphincsImages.verify state (steps + 1)
      (result.charge 16 1 2) := by
  have hquery := messageReady_hashInput state pk message randomness ready
  have hcost := (messageReady_hashCost state pk message randomness ready).2
  have htail : Executes hash SphincsImages.verify
      (writeHash state (hash (hashInput state))) steps result := by
    rw [hquery]
    exact tail
  have step := Executes.hash state steps result (hash_site state pc)
    ready.service (messageReady_hashCost state pk message randomness ready).1 htail
  simpa [hcost] using step

/-- info: 'SigGolfCandidate.SphincsVerifierMessageHash.hash_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hash_step

end SigGolfCandidate.SphincsVerifierMessageHash
