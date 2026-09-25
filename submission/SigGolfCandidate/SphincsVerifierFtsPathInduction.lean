import SigGolfCandidate.SphincsVerifierFtsLoopTransition

/-! Iterate the certified FORS parent step over one eight-level path. -/

namespace SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsLoopInvariant
open SigGolfCandidate.SphincsVerifierFtsLoopTransition
open SigGolfCandidate.SphincsVerifierFtsRoundInvariant
set_option maxRecDepth 16384

def parentPathRun (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (tree : FtsTree) (index : Index)
    (leaf : FtsLeaf) (start : MachineState) (initial : Digest) :
    Nat → MachineState × Digest
  | 0 => (start, initial)
  | n + 1 =>
      let previous := parentPathRun hash pk signature tree index leaf start initial n
      let level : Fin ftsTreeHeight :=
        ⟨n % ftsTreeHeight, Nat.mod_lt _ (by decide)⟩
      let answer := hash (parentQuery pk signature tree index leaf level previous.2)
      (parentRoundState previous.1 answer, truncateHash answer)

theorem parentPathRun_succ (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (tree : FtsTree) (index : Index)
    (leaf : FtsLeaf) (start : MachineState) (initial : Digest)
    (n : Nat) :
    parentPathRun hash pk signature tree index leaf start initial (n + 1) =
      let previous := parentPathRun hash pk signature tree index leaf start initial n
      let level : Fin ftsTreeHeight :=
        ⟨n % ftsTreeHeight, Nat.mod_lt _ (by decide)⟩
      let answer := hash (parentQuery pk signature tree index leaf level previous.2)
      (parentRoundState previous.1 answer, truncateHash answer) := rfl

theorem parentPathRun_invariant (hash : Hash)
    (pk : SphincsSecurity.PublicKey) (signature : Signature)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (start : MachineState) (initial : Digest)
    (initialInv : FtsLoopInv start signature pk tree index leaf
      ⟨0, by decide⟩ initial)
    (n : Nat) (hn : n < ftsTreeHeight) :
    FtsLoopInv
      (parentPathRun hash pk signature tree index leaf start initial n).1
      signature pk tree index leaf ⟨n, hn⟩
      (parentPathRun hash pk signature tree index leaf start initial n).2 := by
  induction n with
  | zero =>
      simpa only [parentPathRun] using initialInv
  | succ n ih =>
      have before : n < ftsTreeHeight := by omega
      have prior := ih before
      have next := FtsLoopInv.advanceHash hash
        (parentPathRun hash pk signature tree index leaf start initial n).1
        signature pk tree index leaf ⟨n, before⟩
        (parentPathRun hash pk signature tree index leaf start initial n).2
        prior hn
      have levelEq :
          (⟨n % ftsTreeHeight, Nat.mod_lt _ (by decide)⟩ :
            Fin ftsTreeHeight) = ⟨n, before⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt before
      change FtsLoopInv
        (parentRoundState
          (parentPathRun hash pk signature tree index leaf start initial n).1
          (hash (parentQuery pk signature tree index leaf
            ⟨n % ftsTreeHeight, Nat.mod_lt _ (by decide)⟩
            (parentPathRun hash pk signature tree index leaf start initial n).2)))
        signature pk tree index leaf ⟨n + 1, hn⟩
        (truncateHash (hash (parentQuery pk signature tree index leaf
          ⟨n % ftsTreeHeight, Nat.mod_lt _ (by decide)⟩
          (parentPathRun hash pk signature tree index leaf start initial n).2)))
      rw [levelEq]
      exact next

theorem parentPathRun_finish (hash : Hash)
    (pk : SphincsSecurity.PublicKey) (signature : Signature)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (start : MachineState) (initial : Digest)
    (initialInv : FtsLoopInv start signature pk tree index leaf
      ⟨0, by decide⟩ initial) :
    let final := parentPathRun hash pk signature tree index leaf start initial 8
    final.1.pc = 0x1b84 ∧
      (∀ i, (hi : i < 20) →
        final.1.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          final.2.extractLsb' (8 * i) 8) ∧
      SphincsVerifierFtsEarlyFrame.FtsWitness final.1 signature ∧
      SphincsVerifierHashBytes.WitnessPrefix final.1 pk := by
  let before := parentPathRun hash pk signature tree index leaf start initial 7
  have inv := parentPathRun_invariant hash pk signature tree index leaf
    start initial initialInv 7 (by decide)
  have finished := FtsLoopInv.finish hash before.1 signature pk tree index
    leaf ⟨7, by decide⟩ before.2 inv rfl
  change
    (parentRoundState before.1
      (hash (parentQuery pk signature tree index leaf ⟨7, by decide⟩
        before.2))).pc = 0x1b84 ∧
    (∀ i, (hi : i < 20) →
      (parentRoundState before.1
        (hash (parentQuery pk signature tree index leaf ⟨7, by decide⟩
          before.2))).getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        (truncateHash (hash (parentQuery pk signature tree index leaf
          ⟨7, by decide⟩ before.2))).extractLsb' (8 * i) 8) ∧
    SphincsVerifierFtsEarlyFrame.FtsWitness
      (parentRoundState before.1
        (hash (parentQuery pk signature tree index leaf ⟨7, by decide⟩
          before.2))) signature ∧
    SphincsVerifierHashBytes.WitnessPrefix
      (parentRoundState before.1
        (hash (parentQuery pk signature tree index leaf ⟨7, by decide⟩
          before.2))) pk
  exact finished

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPathInduction.parentPathRun_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentPathRun_invariant

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPathInduction.parentPathRun_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentPathRun_finish

end SigGolfCandidate.SphincsVerifierFtsPathInduction
