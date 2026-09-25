import SigGolfCandidate.SphincsVerifierXmssInit

namespace SigGolfCandidate.SphincsVerifierXmssNodeSite
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierMessageCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def nodeHashPc (lay : Layer) : Word :=
  BitVec.ofNat 64 (0x2cd4 + 0xfcc * (5 - lay.val))

theorem nodeHash_site (lay : Layer) (state : MachineState)
    (pc : state.pc = nodeHashPc lay) :
    fetch SphincsImages.verify state = some (.base .ECALL) := by
  fin_cases lay
  · rw [fetch_index SphincsImages.verify state 6900 (by decide)
      (by simpa [nodeHashPc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify state 5889 (by decide)
      (by simpa [nodeHashPc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify state 4878 (by decide)
      (by simpa [nodeHashPc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify state 3867 (by decide)
      (by simpa [nodeHashPc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify state 2856 (by decide)
      (by simpa [nodeHashPc] using pc)]; decide
  · rw [fetch_index SphincsImages.verify state 1845 (by decide)
      (by simpa [nodeHashPc] using pc)]; decide

theorem nodeHash_arguments (state : MachineState)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 640)
    (destination : state.getReg .x12 = 0x42000) :
    hashArgumentsValid state = true ∧
      compressions (hashInput state).1 = 2 := by
  constructor
  · simp [hashArgumentsValid, source, bits, destination,
      accessValid, rangeValid, MEMORY_BYTES]
  · simp [hashInput, source, bits, compressions]

theorem nodeHash_step (hash : Hash) (lay : Layer) (state : MachineState)
    (pc : state.pc = nodeHashPc lay)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 640)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash state (hash (hashInput state))) steps result) :
    Executes hash SphincsImages.verify state (steps + 1)
      (result.charge 16 1 2) := by
  have args := nodeHash_arguments state source bits destination
  have step := Executes.hash state steps result (nodeHash_site lay state pc)
    service args.1 tail
  simpa [args.2] using step

#print axioms nodeHash_step

end SigGolfCandidate.SphincsVerifierXmssNodeSite
