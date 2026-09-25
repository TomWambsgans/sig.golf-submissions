import SigGolfCandidate.SphincsVerifierFtsPathAddress

/-! Parent HASH setup leaves witness bytes and verifier control cells untouched. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierFtsParentTag
open SigGolfCandidate.SphincsVerifierFtsParentHeader
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsParentExecution
set_option maxRecDepth 16384

def OutsideHashBuffer (address : Word) : Prop :=
  address.toNat < 0x40000 ∨ 0x40100 ≤ address.toNat

private theorem outside_hash_address (read written : Word)
    (outside : OutsideHashBuffer read)
    (lower : 0x40000 ≤ written.toNat)
    (upper : written.toNat < 0x40100) : read ≠ written := by
  intro equal
  have same := congrArg BitVec.toNat equal
  rcases outside with low | high <;> omega

private theorem low_ne (read written : Word)
    (low : read.toNat < 0x40000)
    (high : 0x40000 ≤ written.toNat) : read ≠ written := by
  intro equal
  have same := congrArg BitVec.toNat equal
  omega

theorem witnessByte_aligned_low (i : Nat)
    (hi : i < SphincsWire.signatureBytes) :
    (alignToDword (BitVec.ofNat 64 (0x22ca0 + i))).toNat <
      0x40000 := by
  have bound : 0x22ca0 + i < 0x40000 := by
    have length := SphincsWire.signatureBytes_eq
    omega
  have small : 0x22ca0 + i < 2 ^ 64 := by omega
  have aligned : (alignToDword
      (BitVec.ofNat 64 (0x22ca0 + i))).toNat ≤
      (BitVec.ofNat 64 (0x22ca0 + i)).toNat := by
    unfold alignToDword
    rw [BitVec.toNat_and]
    exact Nat.and_le_left
  simp only [BitVec.toNat_ofNat] at aligned
  rw [Nat.mod_eq_of_lt small] at aligned
  omega

theorem pair_low_mem_frame (state : MachineState) (read : Word)
    (low : read.toNat < 0x40000) :
    (pairState state).getMem read = state.getMem read := by
  apply pair_scratch_frame
  · intro offset
    apply low_ne read _ low
    fin_cases offset <;> decide
  · intro offset
    apply low_ne read _ low
    fin_cases offset <;> decide

theorem positioned_low_mem_frame (state : MachineState) (read : Word)
    (low : read.toNat < 0x40000) :
    (firstPositionedState state).getMem read =
      state.getMem read := by
  let pair := pairState state
  let advanced := advancePointerState pair
  let shifted := shiftIndexState advanced
  change (levelPositionState shifted).getMem read = _
  rw [levelPosition_mem_frame shifted read
      (low_ne read 0x43010 low (by decide)),
    shiftIndex_mem_frame advanced read
      (low_ne read 0x43070 low (by decide))
      (low_ne read 0x43018 low (by decide)),
    advancePointer_mem_frame pair read
      (low_ne read 0x43028 low (by decide)),
    pair_low_mem_frame state read low]

theorem positioned_FtsWitness (state : MachineState)
    (signature : SphincsSecurity.Signature)
    (witness : FtsWitness state signature) :
    FtsWitness (firstPositionedState state) signature := by
  apply FtsWitness.transport state _ signature witness
  intro i hi
  simp only [MachineState.getByte]
  rw [positioned_low_mem_frame state _ (witnessByte_aligned_low i hi)]

theorem parentTree_mem_frame (state : MachineState) (read : Word)
    (outside : OutsideHashBuffer read)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.treeState state).getMem read =
      state.getMem read := by
  simp only [SphincsVerifierHeader.treeState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.treeBeforeStore_pointer, destination]
  change ((SphincsVerifierHeader.treeBeforeStore state).setMem 0x40008
    ((SphincsVerifierHeader.treeBeforeStore state).getReg .x6)).getMem read = _
  rw [MachineState.getMem_setMem_ne (outside_hash_address read 0x40008
    outside (by decide) (by decide))]
  exact SphincsVerifierHeader.treeBeforeStore_memory state read

theorem parentIndex_mem_frame (state : MachineState) (read : Word)
    (outside : OutsideHashBuffer read)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.indexState state).getMem read =
      state.getMem read := by
  simp only [SphincsVerifierHeader.indexState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.indexBeforeStore_pointer, destination]
  simp only [setWord32_eq]
  change ((SphincsVerifierHeader.indexBeforeStore state).setMem 0x40010
    _).getMem read = _
  rw [MachineState.getMem_setMem_ne (outside_hash_address read 0x40010
    outside (by decide) (by decide))]
  exact SphincsVerifierHeader.indexBeforeStore_memory state read

theorem parentHeader_mem_frame (state : MachineState) (read : Word)
    (outside : OutsideHashBuffer read) :
    (parentHeaderState state).getMem read = state.getMem read := by
  let tagged := parentTagState state
  let prefixed := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState prefixed
  have tagDestination := parentTag_hash_pointer state
  have prefixDestination : prefixed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagDestination
  have treeDestination : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer prefixed).trans prefixDestination
  change (SphincsVerifierHeader.indexState treed).getMem read = _
  rw [parentIndex_mem_frame treed read outside treeDestination,
    parentTree_mem_frame prefixed read outside prefixDestination,
    parentPosition_mem_frame tagged tagDestination read
      (outside_hash_address read 0x40000 outside (by decide) (by decide)),
    parentTag_mem_frame state read
      (outside_hash_address read 0x40000 outside (by decide) (by decide))]

theorem parentHashReady_mem_frame (state : MachineState) (read : Word)
    (outside : OutsideHashBuffer read) :
    (parentHashReadyState state).getMem read = state.getMem read := by
  let headed := parentHeaderState state
  let pointers := parameterPointers headed
  change (hashRegistersState (copyRootState pointers)).getMem read = _
  have registers (s : MachineState) (address : Word) :
      (hashRegistersState s).getMem address = s.getMem address := by
    simp [hashRegistersState, execInstrBr]
  rw [registers]
  have destination := (parameterPointers_regs headed).2
  rw [copyRoot_mem_frame pointers read (by
    intro offset
    rw [destination]
    apply outside_hash_address read _ outside
    · fin_cases offset <;> decide
    · fin_cases offset <;> decide)]
  have unchanged : pointers.getMem read = headed.getMem read := by
    simp [pointers, parameterPointers, execInstrBr]
  rw [unchanged]
  exact parentHeader_mem_frame state read outside

theorem parentHashReady_witness_byte (state : MachineState)
    (address : Word)
    (low : (alignToDword address).toNat < 0x40000) :
    (parentHashReadyState state).getByte address =
      state.getByte address := by
  simp only [MachineState.getByte]
  rw [parentHashReady_mem_frame state (alignToDword address)
    (Or.inl low)]

theorem parentHashReady_FtsWitness (state : MachineState)
    (signature : SphincsSecurity.Signature)
    (witness : FtsWitness state signature) :
    FtsWitness (parentHashReadyState state) signature := by
  apply FtsWitness.transport state _ signature witness
  intro i hi
  exact parentHashReady_witness_byte state _ (witnessByte_aligned_low i hi)

theorem firstParentReady_FtsWitness (state : MachineState)
    (signature : SphincsSecurity.Signature)
    (witness : FtsWitness state signature) :
    FtsWitness (firstParentReadyState state) signature :=
  parentHashReady_FtsWitness _ signature
    (positioned_FtsWitness state signature witness)

theorem parentHashReady_pointer (state : MachineState) :
    (parentHashReadyState state).getMem 0x43028 =
      state.getMem 0x43028 := by
  apply parentHashReady_mem_frame
  exact Or.inr (by decide)

theorem firstParentReady_pointer (state : MachineState) :
    (firstParentReadyState state).getMem 0x43028 =
      state.getMem 0x43028 + 20 := by
  let pair := pairState state
  let advanced := advancePointerState pair
  let shifted := shiftIndexState advanced
  change (parentHashReadyState
    (levelPositionState shifted)).getMem 0x43028 = _
  rw [parentHashReady_pointer,
    levelPosition_mem_frame shifted 0x43028 (by decide),
    shiftIndex_mem_frame advanced 0x43028 (by decide) (by decide),
    advancePointer_cell, pair_pointer_frame]

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame.parentHashReady_mem_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentHashReady_mem_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame.parentHashReady_FtsWitness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parentHashReady_FtsWitness

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame.firstParentReady_FtsWitness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstParentReady_FtsWitness

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame.firstParentReady_pointer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstParentReady_pointer

end SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
