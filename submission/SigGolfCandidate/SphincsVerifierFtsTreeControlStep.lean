import SigGolfCandidate.SphincsVerifierFtsSelectorFrame

namespace SigGolfCandidate.SphincsVerifierFtsTreeControlStep
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsNextTreeSetup
open SigGolfCandidate.SphincsVerifierFtsNextPointer
open SigGolfCandidate.SphincsVerifierFtsNextReadyControls
open SigGolfCandidate.SphincsVerifierFtsPersistentIndex
open SigGolfCandidate.SphincsVerifierFtsSelectorFrame
open SigGolfCandidate.SphincsVerifierFtsPathAddress
open SigGolfCandidate.SphincsVerifierFtsInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- Persistent machine controls at the entry HASH of any FORS tree. -/
structure ReadyControls (state : MachineState) (index : Index)
    (leaves : FtsTree → FtsLeaf) (tree : FtsTree) : Prop where
  pc : state.pc = 0x18c8
  source : state.getReg .x10 = 0x40000
  bits : state.getReg .x11 = 480
  destination : state.getReg .x12 = 0x42000
  service : state.getReg .x5 = 1
  pointer : state.getMem 0x43028 =
    BitVec.ofNat 64 (pathAddress tree ⟨0, by decide⟩)
  selector : state.getMem 0x43070 = BitVec.ofNat 64 (leaves tree).val
  treeCell : state.getMem 0x43000 = BitVec.ofNat 64 tree.val
  indexCell : state.getMem 0x43008 = BitVec.ofNat 64 index.val
  counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val
  savedIndex : state.getMem 0x43078 = BitVec.ofNat 64 index.val
  selectorTable : ∀ slot : FtsTree,
    state.getByte (BitVec.ofNat 64 (0x44800 + slot.val)) =
      BitVec.ofNat 8 (leaves slot).val

def nextReadyState (hash : Hash) (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf) : MachineState :=
  let answer := hash (hashInput state)
  let start := firstLeafStartState state answer
  let path := (parentPathRun hash pk signature tree index leaf start
    (truncateHash answer) 8).1
  nextTreeHashState (treeFinishState path)

theorem ReadyControls.next (hash : Hash) (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf) (tree : FtsTree)
    (inv : ReadyControls state index leaves tree)
    (hprefix : WitnessPrefix state pk)
    (witness : FtsWitness state signature)
    (next : tree.val + 1 < ftsTrees - 1) :
    ReadyControls
      (nextReadyState hash state signature pk tree index (leaves tree))
      index leaves ⟨tree.val + 1, next⟩ := by
  let leaf := leaves tree
  let answer := hash (hashInput state)
  let start := firstLeafStartState state answer
  let path := (parentPathRun hash pk signature tree index leaf start
    (truncateHash answer) 8).1
  let finished := treeFinishState path
  let nextTree : FtsTree := ⟨tree.val + 1, next⟩
  have pathPc : path.pc = 0x1b84 :=
    (tree_abstract_root hash state answer signature pk tree index leaf
      inv.pc inv.source inv.bits inv.destination inv.pointer inv.selector
      inv.treeCell inv.indexCell hprefix witness).1
  have pathCounter : path.getMem 0x43040 =
      BitVec.ofNat 64 tree.val := by
    calc
      _ = start.getMem 0x43040 :=
        parentPathRun_counter_frame hash pk signature tree index leaf start
          (truncateHash answer) 8
      _ = state.getMem 0x43040 :=
        levelStart_counter_frame state answer inv.destination
      _ = BitVec.ofNat 64 tree.val := inv.counter
  have finishPc : finished.pc = 0x173c :=
    treeFinish_pc_next path tree pathPc pathCounter next
  have finishCounter : finished.getMem 0x43040 =
      BitVec.ofNat 64 nextTree.val := by
    exact treeFinish_counter path tree pathCounter
  have finishSource : finished.getMem 0x43028 =
      BitVec.ofNat 64 (0x22cdc + 180 * nextTree.val) := by
    exact treeFinish_next_source hash state signature pk tree index leaf
      inv.counter inv.destination inv.pointer
  have finishIndex : finished.getMem 0x43078 =
      BitVec.ofNat 64 index.val := by
    exact (treeProcess_savedIndex_frame hash state signature pk tree
      index leaf inv.counter inv.destination).trans inv.savedIndex
  have finishSelector : finished.getByte
      (BitVec.ofNat 64 (0x44800 + nextTree.val)) =
      BitVec.ofNat 8 (leaves nextTree).val := by
    exact (treeProcess_selector_byte_frame hash state signature pk tree
      index leaf inv.counter inv.destination nextTree).trans
        (inv.selectorTable nextTree)
  have controls := nextTreeHashState_controls finished nextTree index
    (leaves nextTree) finishPc finishCounter finishSource finishIndex
    finishSelector
  have table : ∀ slot : FtsTree,
      (nextReadyState hash state signature pk tree index leaf).getByte
        (BitVec.ofNat 64 (0x44800 + slot.val)) =
      BitVec.ofNat 8 (leaves slot).val := by
    intro slot
    exact (nextTreeSetup_selector_byte_frame finished slot).trans
      ((treeProcess_selector_byte_frame hash state signature pk tree
        index leaf inv.counter inv.destination slot).trans
        (inv.selectorTable slot))
  have savedIndex :
      (nextReadyState hash state signature pk tree index leaf).getMem
        0x43078 = BitVec.ofNat 64 index.val := by
    exact (nextTreeSetup_savedIndex_frame finished).trans finishIndex
  rcases controls with
    ⟨cpc, csource, cbits, cdestination, cservice, ccounter,
      ctree, cindex, cselector, cpointer⟩
  exact {
    pc := cpc
    source := csource
    bits := cbits
    destination := cdestination
    service := cservice
    pointer := cpointer
    selector := cselector
    treeCell := ctree
    indexCell := cindex
    counter := ccounter
    savedIndex := savedIndex
    selectorTable := table }

/-- info: 'SigGolfCandidate.SphincsVerifierFtsTreeControlStep.ReadyControls.next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ReadyControls.next

end SigGolfCandidate.SphincsVerifierFtsTreeControlStep
