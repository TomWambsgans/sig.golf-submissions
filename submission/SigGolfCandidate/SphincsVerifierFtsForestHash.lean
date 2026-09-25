import SigGolfCandidate.SphincsVerifierFtsForestHashReady

/-! The 520-byte forest-root HASH call uses nine compressions and 72 cycles. -/

namespace SigGolfCandidate.SphincsVerifierFtsForestHash
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsForestHashReady
set_option maxRecDepth 16384

theorem hash_site (state : MachineState) (pc : state.pc = 0x1d38) :
    fetch SphincsImages.verify state = some (.base .ECALL) := by
  rw [fetch_index SphincsImages.verify state 846 (by decide)
    (by simpa using pc)]
  decide

theorem hash_arguments (state : MachineState)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 4160)
    (destination : state.getReg .x12 = 0x42000) :
    hashArgumentsValid state = true ∧ compressions (hashInput state).1 = 9 := by
  constructor
  · simp [hashArgumentsValid, source, bits, destination,
      accessValid, rangeValid, MEMORY_BYTES]
  · simp [hashInput, source, bits, compressions]

theorem hash_step (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x1d38)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 4160)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash state (hash (hashInput state))) steps result) :
    Executes hash SphincsImages.verify state (steps + 1)
      (result.charge 72 1 9) := by
  have args := hash_arguments state source bits destination
  have step := Executes.hash state steps result (hash_site state pc)
    service args.1 tail
  simpa [args.2] using step

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestHash.hash_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hash_step

end SigGolfCandidate.SphincsVerifierFtsForestHash
