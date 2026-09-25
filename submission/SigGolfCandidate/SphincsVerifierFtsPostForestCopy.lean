import SigGolfCandidate.SphincsVerifierFtsRootSetupFrame
import SigGolfCandidate.SphincsVerifierFtsRootCopyBytes

namespace SigGolfCandidate.SphincsVerifierFtsPostForestCopy
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsRootCopySetup
open SigGolfCandidate.SphincsVerifierFtsRootCopyBytes
open SigGolfCandidate.SphincsVerifierFtsRootSetupFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The exact verifier copies every forest-root byte into the next HASH
    input, in 387 ordinary instructions from the final FORS root store. -/
theorem forestRootBytes_copied (state : MachineState)
    (pc : state.pc = 0x1c08) :
    ∃ copied,
      OrdinarySteps SphincsImages.verify state 387 copied ∧
      copied.pc = 0x1c8c ∧
      (∀ tree : FtsTree, ∀ i, (hi : i < 20) →
        copied.getByte
          (BitVec.ofNat 64 (0x40028 + 20 * tree.val + i)) =
          state.getByte
            (BitVec.ofNat 64 (0x44100 + 20 * tree.val + i))) := by
  obtain ⟨entryTrace, entryPc, entrySource, entryDestination, entryCount⟩ :=
    rootCopyEntry state pc
  obtain ⟨copied, copyTrace, copiedPc, copiedBytes⟩ :=
    rootCopy_bytes (rootCopyEntryState state) entryPc
      entrySource entryDestination entryCount
  refine ⟨copied, by simpa only [show 27 + 360 = 387 by decide]
    using entryTrace.append copyTrace, copiedPc, ?_⟩
  intro tree i hi
  have indexBound : 20 * tree.val + i < 480 := by
    have ht := tree.isLt
    change tree.val < 24 at ht
    omega
  have copy := copiedBytes (20 * tree.val + i) indexBound
  have frame := rootCopyEntry_root_byte_frame state tree i hi
  simpa only [Nat.add_assoc] using copy.trans (by
    simpa only [Nat.add_assoc] using frame)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPostForestCopy.forestRootBytes_copied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestRootBytes_copied

end SigGolfCandidate.SphincsVerifierFtsPostForestCopy
