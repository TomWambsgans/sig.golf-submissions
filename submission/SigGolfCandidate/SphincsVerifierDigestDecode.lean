import SigGolfCandidate.SphincsVerifierMessageAnswer

/-!
# Message-digest bit extraction

The verifier reads overlapping bytes of the 256-bit HASH answer. The first
34 bits are a hypertree index; each following eight-bit group is a FORS leaf.
-/

namespace SigGolfCandidate.SphincsVerifierDigestDecode
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierMessageHash
open SigGolfCandidate.SphincsVerifierMessageAnswer

private theorem shifted_byte (value : Nat) :
    (((value % 256) / 4 + ((value / 256) % 256) * 64) % 256) =
      (value / 4) % 256 := by
  omega

theorem leaf_from_answer_bytes (answer : BitVec 256)
    (tree : SphincsSecurity.IndexGroup) :
    (((answer.extractLsb' (8 * (4 + tree.val)) 8).toNat / 4 +
      (answer.extractLsb' (8 * (5 + tree.val)) 8).toNat * 64) % 256) =
      (answer.extractLsb' (34 + 8 * tree.val) 8).toNat := by
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have start : 2 ^ (8 * (4 + tree.val)) =
      2 ^ (32 + 8 * tree.val) := by congr 1; omega
  have next : 2 ^ (8 * (5 + tree.val)) =
      2 ^ (32 + 8 * tree.val) * 256 := by
    rw [show 8 * (5 + tree.val) = (32 + 8 * tree.val) + 8 by omega,
      pow_add]
    norm_num
  have target : 2 ^ (34 + 8 * tree.val) =
      2 ^ (32 + 8 * tree.val) * 4 := by
    rw [show 34 + 8 * tree.val = (32 + 8 * tree.val) + 2 by omega,
      pow_add]
    norm_num
  rw [start, next, target, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul]
  exact shifted_byte (answer.toNat / 2 ^ (32 + 8 * tree.val))

theorem leaf_from_answer_bytes_eq_digestLeaves (answer : BitVec 256)
    (tree : SphincsSecurity.IndexGroup) :
    (((answer.extractLsb' (8 * (4 + tree.val)) 8).toNat / 4 +
      (answer.extractLsb' (8 * (5 + tree.val)) 8).toNat * 64) % 256) =
      (Concrete.digestLeaves (truncateMessageDigest answer) tree).val := by
  rw [leaf_from_answer_bytes]
  change (answer.extractLsb' (34 + 8 * tree.val) 8).toNat =
    ((answer.extractLsb' 0 messageDigestBits).extractLsb'
      (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight).toNat
  rw [BitVec.extractLsb'_extractLsb'_of_le (by
    simp [totalHeight, ftsTreeHeight, messageDigestBits, ftsTrees]
    have ht : tree.val < 25 := by simpa [ftsTrees] using tree.isLt
    omega)]
  rfl

theorem messageReady_leaf_decode (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (answer : BitVec 256) (tree : SphincsSecurity.IndexGroup) :
    ((((writeHash state answer).getByte
        (BitVec.ofNat 64 (0x42000 + 4 + tree.val))).toNat / 4 +
      ((writeHash state answer).getByte
        (BitVec.ofNat 64 (0x42000 + 5 + tree.val))).toNat * 64) % 256) =
      (Concrete.digestLeaves (truncateMessageDigest answer) tree).val := by
  have bound : tree.val < 25 := by simpa [ftsTrees] using tree.isLt
  have first := messageReady_answer_byte state pk message randomness ready
    answer (4 + tree.val) (by omega)
  have second := messageReady_answer_byte state pk message randomness ready
    answer (5 + tree.val) (by omega)
  simpa only [Nat.add_assoc] using
    (show ((((writeHash state answer).getByte
      (BitVec.ofNat 64 (0x42000 + (4 + tree.val)))).toNat / 4 +
      ((writeHash state answer).getByte
        (BitVec.ofNat 64 (0x42000 + (5 + tree.val)))).toNat * 64) % 256) =
      (Concrete.digestLeaves (truncateMessageDigest answer) tree).val from by
        rw [first, second]
        exact leaf_from_answer_bytes_eq_digestLeaves answer tree)

/-- info: 'SigGolfCandidate.SphincsVerifierDigestDecode.leaf_from_answer_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms leaf_from_answer_bytes

/-- info: 'SigGolfCandidate.SphincsVerifierDigestDecode.leaf_from_answer_bytes_eq_digestLeaves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms leaf_from_answer_bytes_eq_digestLeaves

/-- info: 'SigGolfCandidate.SphincsVerifierDigestDecode.messageReady_leaf_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_leaf_decode

end SigGolfCandidate.SphincsVerifierDigestDecode
