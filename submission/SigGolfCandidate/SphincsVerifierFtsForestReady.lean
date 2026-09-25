import SigGolfCandidate.SphincsVerifierFtsTreeWitnessStep

namespace SigGolfCandidate.SphincsVerifierFtsForestReady
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsTreeControlStep
open SigGolfCandidate.SphincsVerifierFtsTreeWitnessStep
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsLevelInit
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- The concrete machine state on entry to the nth FORS tree. Only n < 24 is used. -/
def forestReady (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf) : Nat → MachineState
  | 0 => initial
  | n + 1 =>
      let tree : FtsTree := ⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩
      nextReadyState hash
        (forestReady hash initial signature pk index leaves n)
        signature pk tree index (leaves tree)

theorem forestReady_inv (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩)
    (n : Nat) (hn : n < ftsTrees - 1) :
    ReadyInv (forestReady hash initial signature pk index leaves n)
      signature pk index leaves ⟨n, hn⟩ := by
  induction n with
  | zero =>
      simpa only [forestReady] using initialInv
  | succ n ih =>
      have before : n < ftsTrees - 1 := by omega
      have inv := ih before
      have next := ReadyInv.next hash
        (forestReady hash initial signature pk index leaves n)
        signature pk index leaves ⟨n, before⟩ inv hn
      have treeEq :
          (⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩ : FtsTree) =
            ⟨n, before⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt before
      change ReadyInv
        (nextReadyState hash
          (forestReady hash initial signature pk index leaves n)
          signature pk
          ⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩ index
          (leaves ⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩))
        signature pk index leaves ⟨n + 1, hn⟩
      rw [treeEq]
      exact next

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestReady.forestReady_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestReady_inv

/-- The 24th FORS tree stores its root and leaves the forest loop. -/
theorem forest_final_exit (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩) :
    let last : FtsTree := ⟨23, by decide⟩
    let state := forestReady hash initial signature pk index leaves 23
    let answer := hash (hashInput state)
    let start := firstLeafStartState state answer
    let path := (parentPathRun hash pk signature last index (leaves last)
      start (truncateHash answer) 8).1
    OrdinarySteps SphincsImages.verify path 33 (treeFinishState path) ∧
      (treeFinishState path).pc = 0x1c08 ∧
      (treeFinishState path).getMem 0x43040 = 24 := by
  let last : FtsTree := ⟨23, by decide⟩
  let state := forestReady hash initial signature pk index leaves 23
  let answer := hash (hashInput state)
  let start := firstLeafStartState state answer
  let path := (parentPathRun hash pk signature last index (leaves last)
    start (truncateHash answer) 8).1
  have inv := forestReady_inv hash initial signature pk index leaves
    initialInv 23 (by decide)
  have pathPc : path.pc = 0x1b84 :=
    (tree_abstract_root hash state answer signature pk last index
      (leaves last) inv.controls.pc inv.controls.source inv.controls.bits
      inv.controls.destination inv.controls.pointer inv.controls.selector
      inv.controls.treeCell inv.controls.indexCell inv.publicKey inv.witness).1
  have pathCounter : path.getMem 0x43040 = 23 := by
    calc
      _ = start.getMem 0x43040 :=
        parentPathRun_counter_frame hash pk signature last index
          (leaves last) start (truncateHash answer) 8
      _ = state.getMem 0x43040 :=
        levelStart_counter_frame state answer inv.controls.destination
      _ = 23 := inv.controls.counter
  exact ⟨treeFinish_block path last pathPc pathCounter,
    treeFinish_pc_done path pathPc pathCounter,
    by simpa [last] using treeFinish_counter path last pathCounter⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestReady.forest_final_exit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forest_final_exit

end SigGolfCandidate.SphincsVerifierFtsForestReady
