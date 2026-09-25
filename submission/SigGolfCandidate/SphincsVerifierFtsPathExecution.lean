import SigGolfCandidate.SphincsVerifierFtsFoldBridge

/-! Compose the certified machine executions of all FORS path levels. -/

namespace SigGolfCandidate.SphincsVerifierFtsPathExecution
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsLoopInvariant
open SigGolfCandidate.SphincsVerifierFtsLoopTransition
open SigGolfCandidate.SphincsVerifierFtsRoundInvariant
set_option maxRecDepth 16384

theorem parentPathRun_executes (hash : Hash)
    (pk : SphincsSecurity.PublicKey) (signature : Signature)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (start : MachineState) (initial : Digest)
    (initialInv : FtsLoopInv start signature pk tree index leaf
      ⟨0, by decide⟩ initial)
    (n : Nat) (hn : n ≤ ftsTreeHeight)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (parentPathRun hash pk signature tree index leaf start initial n).1
      steps result) :
    ∃ totalSteps totalResult,
      Executes hash SphincsImages.verify start totalSteps totalResult := by
  induction n generalizing steps result with
  | zero =>
      exact ⟨steps, result, by simpa only [parentPathRun] using tail⟩
  | succ n ih =>
      have before : n < ftsTreeHeight := by omega
      have invariant := parentPathRun_invariant hash pk signature tree index
        leaf start initial initialInv n before
      have levelEq :
          (⟨n % ftsTreeHeight, Nat.mod_lt _ (by decide)⟩ :
            Fin ftsTreeHeight) = ⟨n, before⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt before
      have roundTail : Executes hash SphincsImages.verify
          (parentRoundState
            (parentPathRun hash pk signature tree index leaf start initial n).1
            (hash (parentQuery pk signature tree index leaf ⟨n, before⟩
              (parentPathRun hash pk signature tree index leaf start initial n).2)))
          steps result := by
        change Executes hash SphincsImages.verify
          (parentRoundState
            (parentPathRun hash pk signature tree index leaf start initial n).1
            (hash (parentQuery pk signature tree index leaf
              ⟨n % ftsTreeHeight, Nat.mod_lt _ (by decide)⟩
              (parentPathRun hash pk signature tree index leaf start initial n).2)))
          steps result at tail
        rw [levelEq] at tail
        exact tail
      have roundExec := FtsLoopInv.executesRound hash
        (parentPathRun hash pk signature tree index leaf start initial n).1
        signature pk tree index leaf ⟨n, before⟩
        (parentPathRun hash pk signature tree index leaf start initial n).2
        invariant steps result roundTail
      exact ih (by omega) _ _ roundExec

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPathExecution.parentPathRun_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentPathRun_executes

end SigGolfCandidate.SphincsVerifierFtsPathExecution
