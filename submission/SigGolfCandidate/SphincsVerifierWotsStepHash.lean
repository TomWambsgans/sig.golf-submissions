import SigGolfCandidate.SphincsVerifierWotsStepHashReady

namespace SigGolfCandidate.SphincsVerifierWotsStepHash
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierWotsStepHashReady
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem step_hash_site (state : MachineState) (pc : state.pc = 0x2890) :
    fetch SphincsImages.verify state = some (.base .ECALL) := by
  rw [fetch_index SphincsImages.verify state 1572 (by decide)
    (by simpa using pc)]
  decide

theorem step_hash_arguments (state : MachineState)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000) :
    hashArgumentsValid state = true ∧
    compressions (hashInput state).1 = 1 := by
  constructor
  · simp [hashArgumentsValid, source, bits, destination,
      accessValid, rangeValid, MEMORY_BYTES]
  · simp [hashInput, source, bits, compressions]

theorem step_hash_call (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x2890)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash state (hash (hashInput state))) steps result) :
    Executes hash SphincsImages.verify state (steps + 1)
      (result.charge 8 1 1) := by
  have args := step_hash_arguments state source bits destination
  have step := Executes.hash state steps result (step_hash_site state pc)
    service args.1 tail
  simpa [args.2] using step

theorem step_hash_trace (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x27ec) (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash (stepHashReadyState state)
        (hash (hashInput (stepHashReadyState state)))) steps result) :
    Executes hash SphincsImages.verify state (steps + 42)
      (result.charge 49 1 1) := by
  obtain ⟨ordinary, hashPc, source, bits, destination, service⟩ :=
    stepHashReady_block state pc
  have hashStep := step_hash_call hash (stepHashReadyState state)
    hashPc source bits destination service steps result tail
  have combined := ordinary.then_executes hashStep
  simpa [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using combined

/-- info: 'SigGolfCandidate.SphincsVerifierWotsStepHash.step_hash_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_hash_trace

end SigGolfCandidate.SphincsVerifierWotsStepHash
