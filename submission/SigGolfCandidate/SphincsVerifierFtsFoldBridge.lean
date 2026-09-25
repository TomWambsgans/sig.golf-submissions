import SigGolfCandidate.SphincsVerifierFtsInitialInvariant
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ExtractFts

/-! The machine's eight FORS parent answers equal the abstract `ftsFold` value. -/

namespace SigGolfCandidate.SphincsVerifierFtsFoldBridge
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsLoopTransition
open SigGolfCandidate.SphincsVerifierFtsLoopInvariant
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384

private theorem ordered_if (bit : Bool) (current sibling : Digest) :
    SphincsSecurity.Concrete.nodePayload
      (if bit then sibling else current)
      (if bit then current else sibling) =
      SphincsSecurity.Concrete.orderedPayload bit current sibling := by
  cases bit <;> rfl

theorem parentPathRun_value (hash : Hash)
    (pk : SphincsSecurity.PublicKey) (signature : Signature)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (start : MachineState) (initial : Digest)
    (n : Nat) (hn : n ≤ ftsTreeHeight) :
    (parentPathRun hash pk signature tree index leaf start initial n).2 =
      SphincsSecurity.Concrete.ftsFoldValue
        (adaptOracle hash) pk.parameter index tree leaf
        (signature.ftsPath tree) initial n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have before : n < ftsTreeHeight := by omega
      have prev := ih (by omega)
      rw [parentPathRun_succ]
      rw [SphincsSecurity.Concrete.ftsFoldValue_succ]
      rw [SphincsSecurity.Concrete.ftsFoldPayload]
      rw [← prev]
      have levelEq :
          (⟨n % ftsTreeHeight, Nat.mod_lt _ (by decide)⟩ :
            Fin ftsTreeHeight) = ⟨n, before⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt before
      rw [levelEq]
      simp only [SphincsSecurity.Concrete.ftsSibling, dif_pos before]
      change truncateHash
        (hash (toQuery (tweakableHashInput pk.parameter
          (.ftsNode index tree (n + 1) (leaf.val / 2 ^ (n + 1)))
          (SphincsSecurity.Concrete.nodePayload
            (if leaf.val.testBit n then signature.ftsPath tree ⟨n, before⟩
              else (parentPathRun hash pk signature tree index leaf start initial n).2)
            (if leaf.val.testBit n then
              (parentPathRun hash pk signature tree index leaf start initial n).2
              else signature.ftsPath tree ⟨n, before⟩))))) =
        truncateHash
          (hash (toQuery (tweakableHashInput pk.parameter
            (.ftsNode index tree (n + 1) (leaf.val / 2 ^ (n + 1)))
            (SphincsSecurity.Concrete.orderedPayload (leaf.val.testBit n)
              (parentPathRun hash pk signature tree index leaf start initial n).2
              (signature.ftsPath tree ⟨n, before⟩)))))
      rw [ordered_if]

theorem parentPathRun_abstract_root (hash : Hash)
    (pk : SphincsSecurity.PublicKey) (signature : Signature)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (start : MachineState) (initial : Digest)
    (initialInv : FtsLoopInv start signature pk tree index leaf
      ⟨0, by decide⟩ initial) :
    let final := parentPathRun hash pk signature tree index leaf start initial 8
    final.1.pc = 0x1b84 ∧
      ∀ i, (hi : i < 20) →
        final.1.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (SphincsSecurity.Concrete.ftsFoldValue
            (adaptOracle hash) pk.parameter index tree leaf
            (signature.ftsPath tree) initial 8).extractLsb' (8 * i) 8 := by
  have finished := parentPathRun_finish hash pk signature tree index leaf
    start initial initialInv
  have value := parentPathRun_value hash pk signature tree index leaf
    start initial 8 (by decide)
  refine ⟨finished.1, ?_⟩
  intro i hi
  rw [finished.2.1 i hi, value]

/-- info: 'SigGolfCandidate.SphincsVerifierFtsFoldBridge.parentPathRun_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parentPathRun_value

/-- info: 'SigGolfCandidate.SphincsVerifierFtsFoldBridge.parentPathRun_abstract_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentPathRun_abstract_root

end SigGolfCandidate.SphincsVerifierFtsFoldBridge
