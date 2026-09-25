import SigGolfCandidate.SphincsVerifierFtsRootCopySetup

namespace SigGolfCandidate.SphincsVerifierFtsRootSetupFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsRootCopySetup
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- Preparing the forest-root hash only writes four scratch header cells and
    the tree-index cell. All root slots are preserved. -/
theorem rootCopyEntry_mem_frame (state : MachineState) (read : Word)
    (h0 : read ≠ 0x43000) (h1 : read ≠ 0x43008)
    (h2 : read ≠ 0x43010) (h3 : read ≠ 0x43018) :
    (rootCopyEntryState state).getMem read = state.getMem read := by
  change read ≠ (274432#64) at h0
  change read ≠ (274440#64) at h1
  change read ≠ (274448#64) at h2
  change read ≠ (274456#64) at h3
  simp [rootCopyEntryState, copySetupState, clearHeaderState, zeroLayer,
    zeroTree, zeroPosition, zeroIndex, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, h0, h1, h2, h3]

theorem rootCopyEntry_root_byte_frame (state : MachineState)
    (tree : FtsTree) (i : Nat) (hi : i < 20) :
    (rootCopyEntryState state).getByte
        (BitVec.ofNat 64 (0x44100 + 20 * tree.val + i)) =
      state.getByte (BitVec.ofNat 64 (0x44100 + 20 * tree.val + i)) := by
  let n := 20 * tree.val + i
  have hn : n < 480 := by
    have ht := tree.isLt
    change tree.val < 24 at ht
    omega
  have aligned : alignToDword (BitVec.ofNat 64 (0x44100 + n)) =
      BitVec.ofNat 64 (0x44100 + 8 * (n / 8)) := by
    have ha : ((BitVec.ofNat 64 0x44100).toNat % 8 = 0) := by decide
    have hover : (BitVec.ofNat 64 0x44100).toNat + n < 2 ^ 64 := by
      simpa using (show 0x44100 + n < 2 ^ 64 by omega)
    simpa only [BitVec.ofNat_add] using
      (alignToDword_add_ofNat_of_aligned ha hover)
  have outside (address : Word) (bound : address.toNat < 0x44100) :
      alignToDword (BitVec.ofNat 64 (0x44100 + n)) ≠ address := by
    rw [aligned]
    intro eq
    have values := congrArg BitVec.toNat eq
    have small : 0x44100 + 8 * (n / 8) < 2 ^ 64 := by omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at values
    omega
  simp only [MachineState.getByte]
  have h0 : alignToDword (BitVec.ofNat 64
      (0x44100 + 20 * tree.val + i)) ≠ 0x43000 := by
    simpa only [n, Nat.add_assoc] using outside 0x43000 (by decide)
  have h1 : alignToDword (BitVec.ofNat 64
      (0x44100 + 20 * tree.val + i)) ≠ 0x43008 := by
    simpa only [n, Nat.add_assoc] using outside 0x43008 (by decide)
  have h2 : alignToDword (BitVec.ofNat 64
      (0x44100 + 20 * tree.val + i)) ≠ 0x43010 := by
    simpa only [n, Nat.add_assoc] using outside 0x43010 (by decide)
  have h3 : alignToDword (BitVec.ofNat 64
      (0x44100 + 20 * tree.val + i)) ≠ 0x43018 := by
    simpa only [n, Nat.add_assoc] using outside 0x43018 (by decide)
  exact congrArg (fun word => extractByte word
    (byteOffset (BitVec.ofNat 64 (0x44100 + 20 * tree.val + i))))
      (rootCopyEntry_mem_frame state _ h0 h1 h2 h3)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootSetupFrame.rootCopyEntry_root_byte_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootCopyEntry_root_byte_frame

end SigGolfCandidate.SphincsVerifierFtsRootSetupFrame
