import SigGolfCandidate.SphincsVerifierFtsForestHashReady
import SigGolfCandidate.SphincsVerifierCopyMemory

namespace SigGolfCandidate.SphincsVerifierFtsForestPayloadFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsForestHeader
open SigGolfCandidate.SphincsVerifierFtsForestHashReady
open SigGolfCandidate.SphincsVerifierFtsParentTag
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierFtsPostForestCopy
open SigGolfCandidate.SphincsVerifierCopy20DataGeneral
open SigGolfCandidate.SphincsVerifierSecondHashParameterData
open SigGolfCandidate.SphincsVerifierSecondHashBytes
open SigGolfCandidate.SphincsVerifierHashBytes
set_option maxRecDepth 16384
set_option maxHeartbeats 0

private theorem forestTree_mem_frame (state : MachineState) (read : Word)
    (outside : read ≠ 0x40008)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.treeState state).getMem read = state.getMem read := by
  simp only [SphincsVerifierHeader.treeState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.treeBeforeStore_pointer, destination]
  change ((SphincsVerifierHeader.treeBeforeStore state).setMem 0x40008
    ((SphincsVerifierHeader.treeBeforeStore state).getReg .x6)).getMem read = _
  rw [MachineState.getMem_setMem_ne outside]
  exact SphincsVerifierHeader.treeBeforeStore_memory state read

private theorem forestIndex_mem_frame (state : MachineState) (read : Word)
    (outside : read ≠ 0x40010)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.indexState state).getMem read = state.getMem read := by
  simp only [SphincsVerifierHeader.indexState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.indexBeforeStore_pointer, destination]
  simp only [setWord32_eq]
  change ((SphincsVerifierHeader.indexBeforeStore state).setMem 0x40010
    _).getMem read = _
  rw [MachineState.getMem_setMem_ne outside]
  exact SphincsVerifierHeader.indexBeforeStore_memory state read

private theorem forestHeader_mem_frame (state : MachineState) (read : Word)
    (outside : read.toNat < 0x40000 ∨ 0x40028 ≤ read.toNat) :
    (forestHeaderState state).getMem read = state.getMem read := by
  let tagged := forestTagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have hneq (written : Word) (lower : 0x40000 ≤ written.toNat)
      (upper : written.toNat < 0x40028) :
      read ≠ written := by
    intro equal
    have same := congrArg BitVec.toNat equal
    rcases outside with low | high <;> omega
  have tagDestination := forestTag_hash_pointer state
  have positionDestination : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagDestination
  have treeDestination : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionDestination
  change (SphincsVerifierHeader.indexState treed).getMem read = _
  rw [forestIndex_mem_frame treed read (hneq 0x40010 (by decide)
      (by decide)) treeDestination,
    forestTree_mem_frame positioned read (hneq 0x40008 (by decide)
      (by decide))
      positionDestination,
    parentPosition_mem_frame tagged tagDestination read
      (hneq 0x40000 (by decide) (by decide)),
    forestTag_mem_frame state read (hneq 0x40000 (by decide) (by decide))]

theorem forestHashReady_payload_mem_frame (state : MachineState)
    (read : Word) (outside : 0x40028 ≤ read.toNat) :
    (forestHashReadyState state).getMem read = state.getMem read := by
  let headed := forestHeaderState state
  let pointers := forestParameterPointers headed
  change (forestHashRegistersState (copyRootState pointers)).getMem read = _
  have registers (s : MachineState) (address : Word) :
      (forestHashRegistersState s).getMem address = s.getMem address := by
    simp [forestHashRegistersState, execInstrBr]
  rw [registers]
  have destination := (forestParameterPointers_regs headed).2
  rw [copyRoot_mem_frame pointers read (by
    intro offset
    rw [destination]
    intro equal
    have same := congrArg BitVec.toNat equal
    have bound : (alignToDword
      (0x40014 + signExtend12 (4#12 * BitVec.ofNat 12 offset.val))).toNat <
        0x40028 := by
      fin_cases offset <;> decide
    omega)]
  have unchanged : pointers.getMem read = headed.getMem read := by
    simp [pointers, forestParameterPointers, execInstrBr]
  rw [unchanged]
  exact forestHeader_mem_frame state read (Or.inr outside)

theorem forestHashReady_payload_byte_frame (state : MachineState)
    (i : Nat) (hi : i < 480) :
    (forestHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40028 + i)) =
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) := by
  have aligned : alignToDword (BitVec.ofNat 64 (0x40028 + i)) =
      BitVec.ofNat 64 (0x40028 + 8 * (i / 8)) := by
    have ha : ((BitVec.ofNat 64 0x40028).toNat % 8 = 0) := by decide
    have hover : (BitVec.ofNat 64 0x40028).toNat + i < 2 ^ 64 := by
      simpa using (show 0x40028 + i < 2 ^ 64 by omega)
    simpa only [BitVec.ofNat_add] using
      (alignToDword_add_ofNat_of_aligned ha hover)
  have outside : 0x40028 ≤
      (alignToDword (BitVec.ofNat 64 (0x40028 + i))).toNat := by
    rw [aligned]
    have small : 0x40028 + 8 * (i / 8) < 2 ^ 64 := by omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    omega
  simp only [MachineState.getByte]
  rw [forestHashReady_payload_mem_frame state _ outside]

/-- Each public-parameter word is copied from the witness's public parameter. -/
theorem forestHashReady_parameter_word (state : MachineState)
    (index : Fin 5) :
    (forestHashReadyState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  let headed := forestHeaderState state
  let pointers := forestParameterPointers headed
  change (forestHashRegistersState (copyRootState pointers)).getWord32 _ = _
  have registers (s : MachineState) (address : Word) :
      (forestHashRegistersState s).getWord32 address = s.getWord32 address := by
    simp [MachineState.getWord32, forestHashRegistersState, execInstrBr]
  rw [registers]
  have copied := copySecondParameter_data pointers
    (forestParameterPointers_regs headed).1
    (forestParameterPointers_regs headed).2 index
  rw [copied]
  have pointersFrame : pointers.getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
      headed.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
    simp [pointers, forestParameterPointers, execInstrBr,
      MachineState.getWord32]
  rw [pointersFrame]
  simp only [MachineState.getWord32]
  rw [forestHeader_mem_frame state _ (Or.inl (by
    fin_cases index <;> decide))]

theorem forestHashReady_parameter_byte (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (encoded : WitnessPrefix state pk)
    (i : Nat) (hi : i < 20) :
    (forestHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40014 + i)) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  exact parameter_bytes_of_words (forestHashReadyState state) state pk
    (forestHashReady_parameter_word state) encoded i hi

/-- The 480 copied FORS-root bytes survive all 43 HASH setup instructions. -/
theorem forest_roots_hash_ready (state : MachineState)
    (pc : state.pc = 0x1c08) :
    ∃ copied,
      OrdinarySteps SphincsImages.verify state 387 copied ∧
      copied.pc = 0x1c8c ∧
      (∀ tree : FtsTree, ∀ i, (hi : i < 20) →
        (forestHashReadyState copied).getByte
          (BitVec.ofNat 64 (0x40028 + 20 * tree.val + i)) =
        state.getByte
          (BitVec.ofNat 64 (0x44100 + 20 * tree.val + i))) := by
  obtain ⟨copied, trace, copiedPc, bytes⟩ :=
    forestRootBytes_copied state pc
  refine ⟨copied, trace, copiedPc, ?_⟩
  intro tree i hi
  have bound : 20 * tree.val + i < 480 := by
    have ht := tree.isLt
    change tree.val < 24 at ht
    omega
  simpa only [Nat.add_assoc] using
    (forestHashReady_payload_byte_frame copied _ bound).trans
      (by simpa only [Nat.add_assoc] using bytes tree i hi)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestPayloadFrame.forestHashReady_payload_mem_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestHashReady_payload_mem_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestPayloadFrame.forestHashReady_payload_byte_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestHashReady_payload_byte_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestPayloadFrame.forestHashReady_parameter_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestHashReady_parameter_word

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestPayloadFrame.forestHashReady_parameter_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestHashReady_parameter_byte

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestPayloadFrame.forest_roots_hash_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forest_roots_hash_ready

end SigGolfCandidate.SphincsVerifierFtsForestPayloadFrame
