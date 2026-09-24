import SigGolfCandidate.SphincsVerifierFtsParentSetup

/-! The first FORS parent HASH service call uses two compressions and 16 cycles. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentHash
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsParentSetup
set_option maxRecDepth 16384

theorem hash_site (state : MachineState) (pc : state.pc = 0x1b18) :
    fetch SphincsImages.verify state = some (.base .ECALL) := by
  rw [fetch_index SphincsImages.verify state 710 (by decide)
    (by simpa using pc)]
  decide

theorem hash_arguments (state : MachineState)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 640)
    (destination : state.getReg .x12 = 0x42000) :
    hashArgumentsValid state = true ∧ compressions (hashInput state).1 = 2 := by
  constructor
  · simp [hashArgumentsValid, source, bits, destination,
      accessValid, rangeValid, MEMORY_BYTES]
  · simp [hashInput, source, bits, compressions]

theorem hash_step (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x1b18)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 640)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash state (hash (hashInput state))) steps result) :
    Executes hash SphincsImages.verify state (steps + 1)
      (result.charge 16 1 2) := by
  have args := hash_arguments state source bits destination
  have step := Executes.hash state steps result (hash_site state pc)
    service args.1 tail
  simpa [args.2] using step

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentHash.hash_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hash_step

end SigGolfCandidate.SphincsVerifierFtsParentHash
