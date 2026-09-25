import SigGolfCandidate.SphincsVerifierFtsTreeHashStep
import SigGolfCandidate.SphincsVerifierFtsEarlyFrame

/-! Witness positions of the 24 FORS paths. -/

namespace SigGolfCandidate.SphincsVerifierFtsPathAddress
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolfCandidate.SphincsVerifierFtsGenericPairTrace
set_option maxRecDepth 16384

def pathAddress (tree : FtsTree) (level : Fin ftsTreeHeight) : Nat :=
  0x22ca0 + (60 + tree.val * SphincsWire.ftsOpeningBytes +
    (SphincsWire.digestBytes + level.val * SphincsWire.digestBytes))

theorem pathAddress_bound (tree : FtsTree)
    (level : Fin ftsTreeHeight) :
    pathAddress tree level + 20 ≤ 0x40000 := by
  have ht := tree.isLt
  have hl := level.isLt
  norm_num [pathAddress, ftsTrees, ftsTreeHeight,
    SphincsWire.ftsOpeningBytes, SphincsWire.digestBytes] at *
  omega

theorem pathAddress_aligned (tree : FtsTree)
    (level : Fin ftsTreeHeight) :
    pathAddress tree level % 4 = 0 := by
  norm_num [pathAddress, ftsTreeHeight,
    SphincsWire.ftsOpeningBytes, SphincsWire.digestBytes]
  omega

theorem pathPointer_toNat (tree : FtsTree)
    (level : Fin ftsTreeHeight) :
    (BitVec.ofNat 64 (pathAddress tree level)).toNat =
      pathAddress tree level := by
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by
    have bound := pathAddress_bound tree level
    omega)

theorem pathPointer_admissible (tree : FtsTree)
    (level : Fin ftsTreeHeight) :
    PathPointerAdmissible
      (BitVec.ofNat 64 (pathAddress tree level)) := by
  rw [PathPointerAdmissible, pathPointer_toNat]
  exact ⟨pathAddress_aligned tree level,
    by have bound := pathAddress_bound tree level
       unfold MEMORY_BYTES
       omega⟩

theorem pathPointer_small (tree : FtsTree)
    (level : Fin ftsTreeHeight) :
    (BitVec.ofNat 64 (pathAddress tree level)).toNat + 20 ≤
      0x40000 := by
  rw [pathPointer_toNat]
  exact pathAddress_bound tree level

theorem pathAddress_next (tree : FtsTree)
    (level : Fin ftsTreeHeight)
    (notLast : level.val + 1 < ftsTreeHeight) :
    pathAddress tree ⟨level.val + 1, notLast⟩ =
      pathAddress tree level + 20 := by
  simp [pathAddress, SphincsWire.digestBytes]
  omega

theorem witness_path_at_pointer (state : MachineState)
    (signature : SphincsSecurity.Signature)
    (witness : FtsWitness state signature)
    (tree : FtsTree) (level : Fin ftsTreeHeight)
    (i : Nat) (hi : i < 20) :
    state.getByte (BitVec.ofNat 64
      ((BitVec.ofNat 64 (pathAddress tree level)).toNat + i)) =
      (signature.ftsPath tree level).extractLsb' (8 * i) 8 := by
  rw [pathPointer_toNat]
  simpa only [pathAddress, SphincsWire.digestBytes, Nat.add_assoc] using
    witness.path tree level i (by simpa [SphincsWire.digestBytes] using hi)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPathAddress.witness_path_at_pointer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms witness_path_at_pointer

end SigGolfCandidate.SphincsVerifierFtsPathAddress
