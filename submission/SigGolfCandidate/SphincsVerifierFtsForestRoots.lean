import SigGolfCandidate.SphincsVerifierFtsForestExecution

namespace SigGolfCandidate.SphincsVerifierFtsForestRoots
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsForestReady
open SigGolfCandidate.SphincsVerifierFtsTreeControlStep
open SigGolfCandidate.SphincsVerifierFtsTreeWitnessStep
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsRootFrame
open SigGolfCandidate.SphincsVerifierFtsRootBytes
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsNextTreeSetup
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def treeValue (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf) (tree : FtsTree) : Digest :=
  let state := forestReady hash initial signature pk index leaves tree.val
  SphincsSecurity.Concrete.ftsFoldValue (adaptOracle hash) pk.parameter
    index tree (leaves tree) (signature.ftsPath tree)
    (truncateHash (hash (hashInput state))) 8

def forestEndState (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf) : MachineState :=
  let last : FtsTree := ⟨23, by decide⟩
  let state := forestReady hash initial signature pk index leaves 23
  let answer := hash (hashInput state)
  let start := firstLeafStartState state answer
  let path := (parentPathRun hash pk signature last index (leaves last)
    start (truncateHash answer) 8).1
  treeFinishState path

/-- At tree n's entry, all earlier root slots contain their certified folds. -/
theorem forestReady_prior_roots (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩)
    (n : Nat) (hn : n < ftsTrees - 1)
    (prior : FtsTree) (older : prior.val < n)
    (i : Nat) (hi : i < 20) :
    (forestReady hash initial signature pk index leaves n).getByte
        (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) =
      (treeValue hash initial signature pk index leaves prior).extractLsb'
        (8 * i) 8 := by
  induction n with
  | zero => omega
  | succ n ih =>
      have before : n < ftsTrees - 1 := by omega
      let tree : FtsTree := ⟨n, before⟩
      let state := forestReady hash initial signature pk index leaves n
      let answer := hash (hashInput state)
      let start := firstLeafStartState state answer
      let path := (parentPathRun hash pk signature tree index (leaves tree)
        start (truncateHash answer) 8).1
      have inv := forestReady_inv hash initial signature pk index leaves
        initialInv n before
      have treeEq :
          (⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩ : FtsTree) =
            tree := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt before
      change (nextTreeHashState (treeFinishState
          (parentPathRun hash pk signature
            ⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩ index
            (leaves ⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩)
            (firstLeafStartState state answer) (truncateHash answer) 8).1)).getByte
        (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) = _
      rw [treeEq]
      rw [nextTreeSetup_root_byte_frame (treeFinishState path) prior i hi]
      by_cases h : prior.val < n
      · rw [treeProcess_prior_root_byte hash state signature pk tree prior
          index (leaves tree) inv.controls.counter
          inv.controls.destination h i hi]
        exact ih before h
      · have equal : prior = tree := by
          apply Fin.ext
          change prior.val = n
          omega
        subst prior
        rw [treeFinish_abstract_root_bytes hash state signature pk tree index
          (leaves tree) inv.controls.pc inv.controls.source
          inv.controls.bits inv.controls.destination inv.controls.pointer
          inv.controls.selector inv.controls.treeCell inv.controls.indexCell
          inv.controls.counter inv.publicKey inv.witness i hi]
        rfl

/-- All 24 root slots are correct after the final tree's root store. -/
theorem forestEnd_all_roots (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩)
    (tree : FtsTree) (i : Nat) (hi : i < 20) :
    (forestEndState hash initial signature pk index leaves).getByte
        (BitVec.ofNat 64 (0x44100 + 20 * tree.val + i)) =
      (treeValue hash initial signature pk index leaves tree).extractLsb'
        (8 * i) 8 := by
  let last : FtsTree := ⟨23, by decide⟩
  let state := forestReady hash initial signature pk index leaves 23
  have inv := forestReady_inv hash initial signature pk index leaves
    initialInv 23 (by decide)
  by_cases h : tree.val < 23
  · exact (treeProcess_prior_root_byte hash state signature pk last tree
      index (leaves last) inv.controls.counter inv.controls.destination h i hi).trans
      (forestReady_prior_roots hash initial signature pk index leaves
        initialInv 23 (by decide) tree h i hi)
  · have equal : tree = last := by
      apply Fin.ext
      have upper := tree.isLt
      change tree.val < 24 at upper
      change tree.val = 23
      omega
    subst tree
    exact treeFinish_abstract_root_bytes hash state signature pk last index
      (leaves last) inv.controls.pc inv.controls.source inv.controls.bits
      inv.controls.destination inv.controls.pointer inv.controls.selector
      inv.controls.treeCell inv.controls.indexCell inv.controls.counter
      inv.publicKey inv.witness i hi

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestRoots.forestEnd_all_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestEnd_all_roots

end SigGolfCandidate.SphincsVerifierFtsForestRoots
