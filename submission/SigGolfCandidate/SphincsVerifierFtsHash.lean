import SigGolfCandidate.SphincsVerifierFtsSetup

/-! The first FORS leaf HASH service call uses one compression and eight cycles. -/

namespace SigGolfCandidate.SphincsVerifierFtsHash
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsSetup
set_option maxRecDepth 16384

theorem hash_site (state : MachineState) (pc : state.pc = 0x18c8) :
    fetch SphincsImages.verify state = some (.base .ECALL) := by
  rw [fetch_index SphincsImages.verify state 562 (by decide)
    (by simpa using pc)]
  decide

theorem hash_arguments (state : MachineState)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000) :
    hashArgumentsValid state = true ∧ compressions (hashInput state).1 = 1 := by
  constructor
  · simp [hashArgumentsValid, source, bits, destination,
      accessValid, rangeValid, MEMORY_BYTES]
  · simp [hashInput, source, bits, compressions]

theorem hash_step (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash state (hash (hashInput state))) steps result) :
    Executes hash SphincsImages.verify state (steps + 1)
      (result.charge 8 1 1) := by
  have args := hash_arguments state source bits destination
  have step := Executes.hash state steps result (hash_site state pc)
    service args.1 tail
  simpa [args.2] using step

/-- info: 'SigGolfCandidate.SphincsVerifierFtsHash.hash_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hash_step

end SigGolfCandidate.SphincsVerifierFtsHash
