import SigGolfCandidate.SphincsVerifierFtsPathExecution

/-! Exact instruction and cycle accounting for repeated FORS parent rounds. -/

namespace SigGolfCandidate.SphincsVerifierFtsPathCost
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsLoopInvariant
open SigGolfCandidate.SphincsVerifierFtsLoopTransition
open SigGolfCandidate.SphincsVerifierFtsRoundInvariant
set_option maxRecDepth 16384

def parentBranchCount (state : MachineState) : Nat :=
  if (SigGolfCandidate.SphincsVerifierFtsLevelBranch.parityState state).getReg .x6 = 0
    then 34 else 35

def parentInstructions (state : MachineState) : Nat :=
  parentBranchCount state + 65 + 27

def parentCycles (state : MachineState) : Nat :=
  parentBranchCount state + 65 + 42

theorem parentCycles_le (state : MachineState) : parentCycles state ≤ 142 := by
  unfold parentCycles parentBranchCount
  split_ifs <;> omega

theorem parentInstructions_le (state : MachineState) :
    parentInstructions state ≤ 127 := by
  unfold parentInstructions parentBranchCount
  split_ifs <;> omega

theorem FtsLoopInv.executesRound_flat (hash : Hash) (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (level : Fin ftsTreeHeight) (current : Digest)
    (inv : FtsLoopInv state signature pk tree index leaf level current)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (parentRoundState state
        (hash (parentQuery pk signature tree index leaf level current)))
      steps result) :
    Executes hash SphincsImages.verify state
      (steps + parentInstructions state)
      (result.charge (parentCycles state) 1 2) := by
  have step := FtsLoopInv.executesRound hash state signature pk tree index
    leaf level current inv steps result tail
  simpa [parentInstructions, parentCycles, parentBranchCount,
    Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using step

def pathInstructions (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (tree : FtsTree) (index : Index)
    (leaf : FtsLeaf) (start : MachineState) (initial : Digest) : Nat → Nat
  | 0 => 0
  | n + 1 => pathInstructions hash pk signature tree index leaf start initial n +
      parentInstructions
        (parentPathRun hash pk signature tree index leaf start initial n).1

def pathCycles (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (tree : FtsTree) (index : Index)
    (leaf : FtsLeaf) (start : MachineState) (initial : Digest) : Nat → Nat
  | 0 => 0
  | n + 1 => pathCycles hash pk signature tree index leaf start initial n +
      parentCycles
        (parentPathRun hash pk signature tree index leaf start initial n).1

theorem pathCycles_le (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (tree : FtsTree) (index : Index)
    (leaf : FtsLeaf) (start : MachineState) (initial : Digest)
    (n : Nat) :
    pathCycles hash pk signature tree index leaf start initial n ≤ 142 * n := by
  induction n with
  | zero => simp [pathCycles]
  | succ n ih =>
      rw [pathCycles]
      have step := parentCycles_le
        (parentPathRun hash pk signature tree index leaf start initial n).1
      omega

theorem pathInstructions_le (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (tree : FtsTree) (index : Index)
    (leaf : FtsLeaf) (start : MachineState) (initial : Digest)
    (n : Nat) :
    pathInstructions hash pk signature tree index leaf start initial n ≤
      127 * n := by
  induction n with
  | zero => simp [pathInstructions]
  | succ n ih =>
      rw [pathInstructions]
      have step := parentInstructions_le
        (parentPathRun hash pk signature tree index leaf start initial n).1
      omega

theorem fullPath_cost_le (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (signature : Signature) (tree : FtsTree) (index : Index)
    (leaf : FtsLeaf) (start : MachineState) (initial : Digest) :
    pathCycles hash pk signature tree index leaf start initial 8 ≤ 1136 ∧
    pathInstructions hash pk signature tree index leaf start initial 8 ≤
      1016 := by
  constructor
  · simpa using (pathCycles_le hash pk signature tree index leaf
      start initial 8)
  · simpa using (pathInstructions_le hash pk signature tree index leaf
      start initial 8)

private theorem charge_charge (result : Execution)
    (c1 h1 b1 c2 h2 b2 : Nat) :
    (result.charge c1 h1 b1).charge c2 h2 b2 =
      result.charge (c1 + c2) (h1 + h2) (b1 + b2) := by
  cases result
  simp [Execution.charge, Nat.add_comm, Nat.add_left_comm]

theorem parentPathRun_executes_exact (hash : Hash)
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
    Executes hash SphincsImages.verify start
      (steps + pathInstructions hash pk signature tree index leaf start initial n)
      (result.charge
        (pathCycles hash pk signature tree index leaf start initial n)
        n (2 * n)) := by
  induction n generalizing steps result with
  | zero =>
      simpa [pathInstructions, pathCycles, Execution.charge, parentPathRun]
        using tail
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
      have roundExec := FtsLoopInv.executesRound_flat hash
        (parentPathRun hash pk signature tree index leaf start initial n).1
        signature pk tree index leaf ⟨n, before⟩
        (parentPathRun hash pk signature tree index leaf start initial n).2
        invariant steps result roundTail
      have prior := ih (by omega) _ _ roundExec
      change Executes hash SphincsImages.verify start
        (steps + (pathInstructions hash pk signature tree index leaf start initial n +
          parentInstructions
            (parentPathRun hash pk signature tree index leaf start initial n).1))
        (result.charge
          (pathCycles hash pk signature tree index leaf start initial n +
            parentCycles
              (parentPathRun hash pk signature tree index leaf start initial n).1)
          (n + 1) (2 * (n + 1)))
      simpa [charge_charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_add] using prior

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPathCost.parentPathRun_executes_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentPathRun_executes_exact

/-- info: 'SigGolfCandidate.SphincsVerifierFtsPathCost.fullPath_cost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullPath_cost_le

end SigGolfCandidate.SphincsVerifierFtsPathCost
