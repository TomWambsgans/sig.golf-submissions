import SigGolfCandidate.SphincsMaskedSignOtsPathSibling

namespace SigGolfCandidate.SphincsMaskedSignOtsPathValue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedSignOtsParents SphincsMaskedSignOtsTree SphincsMaskedSignOtsPath
open SphincsMaskedSignOtsPathSetup SphincsMaskedSignOtsPathSibling
open SphincsSecurity SphincsBridge SphincsVerifierCopy SphincsMaskedChainDomain
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- An emitted lower-layer sibling is the abstract seeded authentication node,
not merely a copy of an unspecified cache cell. -/
theorem copied_path_value (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (treeIdx : TreeIndex)
    (selected : LeafIndex) (level : Fin (Levels.height location)) (pointer : Nat)
    (pc : s.pc=0x1938+SphincsMaskedSignOtsParents.delta location)
    (ctrl : PathControls location s level.val (selected.val/2^level.val) pointer)
    (bitBound : selected.val/2^level.val < Levels.width location level.val)
    (pointerBound : pointer+20≤0x40000) (pointerAlign : pointer%4=0)
    (cache : ∀ l,l ≤ Levels.height location → ∀ node,node<Levels.width location l →
      Words20 s (Levels.cacheBase location l+20*node)
        (treeValue hash parameter seed (signerLayer location) treeIdx l node)) :
    let pathLevel : Fin (layerHeight (signerLayer location)) :=
      ⟨level.val,by rw [←signerLayer_height]; exact level.isLt⟩
    Words20 (copyRootState (setupState location s)) pointer
      (evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.treePath parameter (signerLayer location) treeIdx seed selected :
          OracleComp SphincsSecurity.HashSpec (Fin (layerHeight (signerLayer location)) → Digest)) pathLevel) := by
  let pathLevel : Fin (layerHeight (signerLayer location)) :=
    ⟨level.val,by rw [←signerLayer_height]; exact level.isLt⟩
  have sibling := sibling_in_width location level (selected.val/2^level.val) bitBound
  have abstract : treeValue hash parameter seed (signerLayer location) treeIdx level.val
      ((selected.val/2^level.val) ^^^ 1) =
      evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.treePath parameter (signerLayer location) treeIdx seed selected :
          OracleComp SphincsSecurity.HashSpec (Fin (layerHeight (signerLayer location)) → Digest)) pathLevel := by
    have ev := SphincsSecurity.Completeness.eval_treePath (adaptOracle hash)
      parameter (signerLayer location) treeIdx seed selected pathLevel
    simpa [treeValue,SphincsSecurity.Completeness.node,pathLevel] using ev.symm
  dsimp only
  intro i
  have emitted := (copy_sibling location s level (selected.val/2^level.val) pointer
    pc ctrl bitBound pointerBound pointerAlign).2 i
  have stored := cache level.val (by omega) ((selected.val/2^level.val) ^^^ 1) sibling i
  exact emitted.trans (by simpa only [abstract] using stored)

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsPathValue.copied_path_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copied_path_value

end SigGolfCandidate.SphincsMaskedSignOtsPathValue
