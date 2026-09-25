import SigGolfCandidate.SphincsVerifierFtsForestReady

namespace SigGolfCandidate.SphincsVerifierFtsForestExecution
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsForestReady
open SigGolfCandidate.SphincsVerifierFtsTreeControlStep
open SigGolfCandidate.SphincsVerifierFtsTreeWitnessStep
open SigGolfCandidate.SphincsVerifierFtsFinishNextSetup
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsInitialInvariant
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- Compose the first n nonfinal FORS trees, each including successor setup. -/
theorem forest_prefix_executes (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩)
    (n : Nat) (hn : n < ftsTrees - 1)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (forestReady hash initial signature pk index leaves n) steps result) :
    ∃ totalSteps totalResult,
      Executes hash SphincsImages.verify initial totalSteps totalResult ∧
      totalSteps ≤ steps + 1167 * n ∧
      totalResult.cycles ≤ result.cycles + 1294 * n ∧
      totalResult.hashCalls = result.hashCalls + 9 * n ∧
      totalResult.hashCompressions = result.hashCompressions + 17 * n := by
  induction n generalizing steps result with
  | zero =>
      exact ⟨steps, result, by simpa only [forestReady] using tail,
        by simp, by simp, by simp, by simp⟩
  | succ n ih =>
      have priorBound : n < ftsTrees - 1 := by omega
      let state := forestReady hash initial signature pk index leaves n
      let tree : FtsTree := ⟨n, priorBound⟩
      let leaf := leaves tree
      have inv := forestReady_inv hash initial signature pk index leaves
        initialInv n priorBound
      have next : tree.val + 1 < ftsTrees - 1 := hn
      have treeEq :
          (⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩ : FtsTree) =
            tree := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt priorBound
      have tail' : Executes hash SphincsImages.verify
          (nextReadyState hash state signature pk tree index leaf)
          steps result := by
        change Executes hash SphincsImages.verify
          (nextReadyState hash state signature pk
            ⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩ index
            (leaves ⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩))
          steps result at tail
        rw [treeEq] at tail
        exact tail
      obtain ⟨firstSteps, firstResult, firstExec, firstStepBound,
          firstCycleBound, firstHashCount, firstCompressionCount⟩ :=
        tree_through_next_ready_executes hash state signature pk tree
          index leaf inv.controls.pc inv.controls.source inv.controls.bits
          inv.controls.destination inv.controls.service inv.controls.pointer
          inv.controls.selector inv.controls.treeCell inv.controls.indexCell
          inv.publicKey inv.witness inv.controls.counter next steps result tail'
      obtain ⟨totalSteps, totalResult, totalExec, totalStepBound,
          totalCycleBound, totalHashCount, totalCompressionCount⟩ :=
        ih priorBound firstSteps firstResult firstExec
      refine ⟨totalSteps, totalResult, totalExec, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · omega

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestExecution.forest_prefix_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forest_prefix_executes

/-- All 24 FORS trees, with exact hash-call counts and uniform instruction/cycle bounds. -/
theorem forest_all_executes (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩)
    (steps : Nat) (result : Execution)
    (tail :
      let last : FtsTree := ⟨23, by decide⟩
      let state := forestReady hash initial signature pk index leaves 23
      let answer := hash (hashInput state)
      let start := firstLeafStartState state answer
      let path := (parentPathRun hash pk signature last index (leaves last)
        start (truncateHash answer) 8).1
      Executes hash SphincsImages.verify (treeFinishState path)
        steps result) :
    ∃ totalSteps totalResult,
      Executes hash SphincsImages.verify initial totalSteps totalResult ∧
      totalSteps ≤ steps + 27909 ∧
      totalResult.cycles ≤ result.cycles + 30957 ∧
      totalResult.hashCalls = result.hashCalls + 216 ∧
      totalResult.hashCompressions = result.hashCompressions + 408 := by
  let last : FtsTree := ⟨23, by decide⟩
  let state := forestReady hash initial signature pk index leaves 23
  have inv := forestReady_inv hash initial signature pk index leaves
    initialInv 23 (by decide)
  obtain ⟨lastSteps, lastResult, lastExec, lastStepBound, lastCycleBound,
      lastHashCount, lastCompressionCount⟩ :=
    treeThroughFinish_executes hash state signature pk last index (leaves last)
      inv.controls.pc inv.controls.source inv.controls.bits
      inv.controls.destination inv.controls.service inv.controls.pointer
      inv.controls.selector inv.controls.treeCell inv.controls.indexCell
      inv.publicKey inv.witness inv.controls.counter steps result tail
  obtain ⟨totalSteps, totalResult, allExec, allStepBound, allCycleBound,
      allHashCount, allCompressionCount⟩ :=
    forest_prefix_executes hash initial signature pk index leaves initialInv
      23 (by decide) lastSteps lastResult lastExec
  refine ⟨totalSteps, totalResult, allExec, ?_, ?_, ?_, ?_⟩
  · norm_num at allStepBound ⊢
    omega
  · norm_num at allCycleBound ⊢
    omega
  · norm_num at allHashCount ⊢
    omega
  · norm_num at allCompressionCount ⊢
    omega

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestExecution.forest_all_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forest_all_executes

end SigGolfCandidate.SphincsVerifierFtsForestExecution
