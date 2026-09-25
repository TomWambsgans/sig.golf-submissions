import SigGolfCandidate.SphincsVerifierFtsTreeControlStep

namespace SigGolfCandidate.SphincsVerifierFtsTreeWitnessStep
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsTreeAdvance
open SigGolfCandidate.SphincsVerifierFtsRootStore
open SigGolfCandidate.SphincsVerifierFtsNextTreeSetup
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolfCandidate.SphincsVerifierFtsAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierFtsTreeControlStep
open SigGolfCandidate.SphincsVerifierFtsGenericInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsPathInduction
set_option maxRecDepth 16384
set_option maxHeartbeats 0

private theorem low_ne (read written : Word)
    (low : read.toNat < 0x40000)
    (high : 0x40000 ≤ written.toNat) : read ≠ written := by
  intro equal
  have same := congrArg BitVec.toNat equal
  omega

theorem treeFinish_low_mem_frame (state : MachineState)
    (tree : FtsTree)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (read : Word) (low : read.toNat < 0x40000) :
    (treeFinishState state).getMem read = state.getMem read := by
  have destination := rootStoreSetup_destination state tree counter
  have outside : ∀ offset : Fin 5,
      read ≠ alignToDword
        ((rootStoreSetupState state).getReg .x7 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [destination]
    apply low_ne read _ low
    fin_cases tree <;> fin_cases offset <;> decide
  change (treeAdvanceState (SphincsVerifierCopy.copyRootState
    (rootStoreSetupState state))).getMem read = _
  rw [treeAdvance_mem_frame _ read
    (low_ne read 0x43040 low (by decide)),
    SphincsVerifierCopyMemory.copyRoot_mem_frame _ read outside,
    rootStoreSetup_mem]

theorem nextTreeSetup_low_mem_frame (state : MachineState)
    (read : Word) (low : read.toNat < 0x40000) :
    (nextTreeHashState state).getMem read = state.getMem read := by
  let header := ftsTreeHeaderState state
  let selected := ftsSelectState header
  let pointers := ftsCopyPointers selected
  let copied := SphincsVerifierCopy.copyRootState pointers
  let advanced := ftsAdvanceState copied
  have readyFrame : (SphincsVerifierFtsSetup.ftsHashReadyState advanced).getMem
      read = advanced.getMem read := by
    apply hashReady_mem_frame
    · exact low_ne read 0x40000 low (by decide)
    · exact low_ne read 0x40000 low (by decide)
    · exact low_ne read 0x40008 low (by decide)
    · exact low_ne read 0x40010 low (by decide)
    · intro offset
      apply low_ne read _ low
      fin_cases offset <;> decide
  have advanceFrame : advanced.getMem read = copied.getMem read := by
    apply ftsAdvance_mem_frame
    · exact low_ne read 0x43028 low (by decide)
    · exact low_ne read 0x43018 low (by decide)
  have copyFrame : copied.getMem read = pointers.getMem read := by
    apply SphincsVerifierCopyMemory.copyRoot_mem_frame
    intro offset
    rw [(ftsCopyPointers_regs selected).2]
    apply low_ne read _ low
    fin_cases offset <;> decide
  have pointerFrame : pointers.getMem read = selected.getMem read :=
    ftsCopyPointers_mem selected read
  have selectFrame : selected.getMem read = header.getMem read := by
    apply ftsSelect_mem_frame
    · exact low_ne read 0x43010 low (by decide)
    · exact low_ne read 0x43020 low (by decide)
    · exact low_ne read 0x43070 low (by decide)
  have headerFrame : header.getMem read = state.getMem read := by
    apply ftsTreeHeader_mem_frame
    · exact low_ne read 0x43000 low (by decide)
    · exact low_ne read 0x43008 low (by decide)
  exact readyFrame.trans (advanceFrame.trans (copyFrame.trans
    (pointerFrame.trans (selectFrame.trans headerFrame))))

theorem treeFinish_low_byte_frame (state : MachineState)
    (tree : FtsTree)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (i : Nat) (hi : i < SphincsWire.signatureBytes) :
    (treeFinishState state).getByte (BitVec.ofNat 64 (0x22ca0 + i)) =
      state.getByte (BitVec.ofNat 64 (0x22ca0 + i)) := by
  simp only [MachineState.getByte]
  rw [treeFinish_low_mem_frame state tree counter _
    (witnessByte_aligned_low i hi)]

theorem nextTreeSetup_low_byte_frame (state : MachineState)
    (i : Nat) (hi : i < SphincsWire.signatureBytes) :
    (nextTreeHashState state).getByte (BitVec.ofNat 64 (0x22ca0 + i)) =
      state.getByte (BitVec.ofNat 64 (0x22ca0 + i)) := by
  simp only [MachineState.getByte]
  rw [nextTreeSetup_low_mem_frame state _
    (witnessByte_aligned_low i hi)]

theorem nextTreeSetup_witness (state : MachineState)
    (signature : Signature) (witness : FtsWitness state signature) :
    FtsWitness (nextTreeHashState state) signature := by
  exact FtsWitness.transport state _ signature witness
    (nextTreeSetup_low_byte_frame state)

theorem nextTreeSetup_prefix (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (hprefix : WitnessPrefix state pk) :
    WitnessPrefix (nextTreeHashState state) pk := by
  constructor
  · intro i hi
    exact (nextTreeSetup_low_byte_frame state i (by
      rw [SphincsWire.signatureBytes_eq]; omega)).trans (hprefix.root i hi)
  · intro i hi
    have frame := nextTreeSetup_low_byte_frame state (20 + i) (by
      rw [SphincsWire.signatureBytes_eq]; omega)
    have address : 0x22ca0 + (20 + i) = 0x22cb4 + i := by omega
    rw [address] at frame
    exact frame.trans (hprefix.parameter i hi)

theorem treeFinish_witness (state : MachineState)
    (signature : Signature) (tree : FtsTree)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (witness : FtsWitness state signature) :
    FtsWitness (treeFinishState state) signature := by
  exact FtsWitness.transport state _ signature witness
    (treeFinish_low_byte_frame state tree counter)

theorem treeFinish_prefix (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (hprefix : WitnessPrefix state pk) :
    WitnessPrefix (treeFinishState state) pk := by
  constructor
  · intro i hi
    exact (treeFinish_low_byte_frame state tree counter i (by
      rw [SphincsWire.signatureBytes_eq]; omega)).trans (hprefix.root i hi)
  · intro i hi
    have frame := treeFinish_low_byte_frame state tree counter (20 + i) (by
      rw [SphincsWire.signatureBytes_eq]; omega)
    have address : 0x22ca0 + (20 + i) = 0x22cb4 + i := by omega
    rw [address] at frame
    exact frame.trans (hprefix.parameter i hi)

structure ReadyInv (state : MachineState) (signature : Signature)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (leaves : FtsTree → FtsLeaf) (tree : FtsTree) : Prop where
  controls : ReadyControls state index leaves tree
  witness : FtsWitness state signature
  publicKey : WitnessPrefix state pk

theorem ReadyInv.next (hash : Hash) (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf) (tree : FtsTree)
    (inv : ReadyInv state signature pk index leaves tree)
    (next : tree.val + 1 < ftsTrees - 1) :
    ReadyInv
      (nextReadyState hash state signature pk tree index (leaves tree))
      signature pk index leaves ⟨tree.val + 1, next⟩ := by
  let leaf := leaves tree
  let answer := hash (hashInput state)
  let start := SphincsVerifierFtsInitialInvariant.firstLeafStartState
    state answer
  let path := (parentPathRun hash pk signature tree index leaf start
    (truncateHash answer) 8).1
  let finished := treeFinishState path
  have initial := leafInitialInv state answer signature pk tree index leaf
    inv.controls.pc inv.controls.source inv.controls.bits
    inv.controls.destination inv.controls.pointer inv.controls.selector
    inv.controls.treeCell inv.controls.indexCell inv.publicKey inv.witness
  have pathProof := parentPathRun_finish hash pk signature tree index leaf
    start (truncateHash answer) initial
  have pathCounter : path.getMem 0x43040 =
      BitVec.ofNat 64 tree.val := by
    calc
      _ = start.getMem 0x43040 :=
        parentPathRun_counter_frame hash pk signature tree index leaf start
          (truncateHash answer) 8
      _ = state.getMem 0x43040 :=
        SphincsVerifierFtsLevelInit.levelStart_counter_frame state answer
          inv.controls.destination
      _ = BitVec.ofNat 64 tree.val := inv.controls.counter
  have finishedWitness : FtsWitness finished signature :=
    treeFinish_witness path signature tree pathCounter pathProof.2.2.1
  have finishedPrefix : WitnessPrefix finished pk :=
    treeFinish_prefix path pk tree pathCounter pathProof.2.2.2
  exact {
    controls := inv.controls.next hash state signature pk index leaves tree
      inv.publicKey inv.witness next
    witness := nextTreeSetup_witness finished signature finishedWitness
    publicKey := nextTreeSetup_prefix finished pk finishedPrefix }

/-- info: 'SigGolfCandidate.SphincsVerifierFtsTreeWitnessStep.ReadyInv.next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ReadyInv.next

end SigGolfCandidate.SphincsVerifierFtsTreeWitnessStep
