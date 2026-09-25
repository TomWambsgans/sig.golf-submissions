import SigGolfCandidate.SphincsVerifierFtsRootSetupFrame
import SigGolfCandidate.SphincsVerifierFtsRootCopyBytes

namespace SigGolfCandidate.SphincsVerifierFtsPostForestCopy
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsRootCopySetup
open SigGolfCandidate.SphincsVerifierFtsRootCopyBytes
open SigGolfCandidate.SphincsVerifierFtsRootCopy
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

/-- The copy phase carries its full memory frame, including public parameter
    and scratch cells needed by the next HASH. -/
theorem forestPostCopy_full (state : MachineState)
    (pc : state.pc = 0x1c08) :
    ∃ copied,
      OrdinarySteps SphincsImages.verify state 387 copied ∧
      copied.pc = 0x1c8c ∧
      (∀ i, (hi : i < 480) →
        copied.getByte (BitVec.ofNat 64 (0x40028 + i)) =
          state.getByte (BitVec.ofNat 64 (0x44100 + i))) ∧
      (∀ read, read.toNat < 0x40000 →
        copied.getMem read = state.getMem read) ∧
      (∀ read, 0x43000 ≤ read.toNat →
        copied.getMem read = (rootCopyEntryState state).getMem read) := by
  obtain ⟨entryTrace, entryPc, entrySource, entryDestination, entryCount⟩ :=
    rootCopyEntry state pc
  obtain ⟨copied, copyTrace, copiedPc, copiedWords, frame⟩ :=
    rootCopy_all (rootCopyEntryState state) entryPc entrySource
      entryDestination entryCount
  refine ⟨copied, by simpa only [show 27 + 360 = 387 by decide]
    using entryTrace.append copyTrace, copiedPc, ?_, ?_, ?_⟩
  · intro i hi
    have copiedByte := bytes_eq_of_words (rootCopyEntryState state)
      copied 0x44100 0x40028 480 (by decide) (by decide)
      (by decide) (by decide) (by
        intro j hj
        simpa only [wordAddress] using copiedWords j (by omega)) i hi
    let n := i / 20
    let j := i % 20
    have hn : n < 24 := by dsimp [n]; omega
    have hj : j < 20 := by dsimp [j]; omega
    have split : 20 * n + j = i := by dsimp [n, j]; omega
    have sourceFrame := rootCopyEntry_root_byte_frame state ⟨n, hn⟩ j hj
    have sourceFrame' : (rootCopyEntryState state).getByte
        (BitVec.ofNat 64 (0x44100 + i)) =
        state.getByte (BitVec.ofNat 64 (0x44100 + i)) := by
      simpa only [Nat.add_assoc, split] using sourceFrame
    exact copiedByte.trans sourceFrame'
  · intro read low
    have out : ∀ i, i < 60 →
        read ≠ BitVec.ofNat 64 (0x40028 + 8 * i) := by
      intro i hi equal
      have same := congrArg BitVec.toNat equal
      have upper : 0x40028 + 8 * i < 2 ^ 64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt upper] at same
      omega
    rw [frame read out]
    have low_ne (written : Word) (large : 0x40000 ≤ written.toNat) :
        read ≠ written := by
      intro equal
      have same := congrArg BitVec.toNat equal
      omega
    exact rootCopyEntry_mem_frame state read
      (low_ne 0x43000 (by decide))
      (low_ne 0x43008 (by decide))
      (low_ne 0x43010 (by decide))
      (low_ne 0x43018 (by decide))
  · intro read high
    apply frame
    intro i hi equal
    have same := congrArg BitVec.toNat equal
    have upper : 0x40028 + 8 * i < 2 ^ 64 := by omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt upper] at same
    omega

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPostForestCopy.forestPostCopy_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestPostCopy_full

end SigGolfCandidate.SphincsVerifierFtsPostForestCopy
