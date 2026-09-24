import SigGolfCandidate.SphincsVerifierFtsParentHash
import SigGolfCandidate.SphincsVerifierFtsPayload

/-! The first FORS parent HASH setup preserves both assembled child digests. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentPayload
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierSecondHashBytes
open SigGolfCandidate.SphincsVerifierFtsParentTag
open SigGolfCandidate.SphincsVerifierFtsParentHeader
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierFtsParentSetup
set_option maxRecDepth 16384

theorem header_pair_data (state : MachineState) (index : Fin 5) :
    (parentHeaderState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x40028 + 4 * index.val)) ∧
    (parentHeaderState state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x4003c + 4 * index.val)) := by
  let prefixed := parentPrefixState state
  let treed := SphincsVerifierHeader.treeState prefixed
  have prefixPointer : prefixed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer (parentTagState state)).trans
      (parentTag_hash_pointer state)
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer prefixed).trans prefixPointer
  have pair := parentPrefix_pair_data state index
  constructor
  · change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
    rw [index_word_frame treed _ treePointer (by fin_cases index <;> decide),
      tree_word_frame prefixed _ prefixPointer (by fin_cases index <;> decide)]
    exact pair.1
  · change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
    rw [index_word_frame treed _ treePointer (by fin_cases index <;> decide),
      tree_word_frame prefixed _ prefixPointer (by fin_cases index <;> decide)]
    exact pair.2

theorem ready_pair_data (state : MachineState) (index : Fin 5) :
    (parentHashReadyState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x40028 + 4 * index.val)) ∧
    (parentHashReadyState state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x4003c + 4 * index.val)) := by
  let headed := parentHeaderState state
  let pointers := parameterPointers headed
  have destination := (parameterPointers_regs headed).2
  have pair := header_pair_data state index
  constructor
  · change (hashRegistersState (copyRootState pointers)).getWord32 _ = _
    simp only [MachineState.getWord32]
    have registers (s : MachineState) (address : Word) :
        (hashRegistersState s).getMem (alignToDword address) =
          s.getMem (alignToDword address) := by
      simp [hashRegistersState, execInstrBr]
    rw [registers]
    change (copyRootState pointers).getWord32 _ = _
    rw [copyRoot_getWord32_frame pointers _ (by
      intro offset
      rw [destination]
      fin_cases offset <;> fin_cases index <;> decide)]
    simp [pointers, parameterPointers, execInstrBr, MachineState.getWord32]
    exact pair.1
  · change (hashRegistersState (copyRootState pointers)).getWord32 _ = _
    simp only [MachineState.getWord32]
    have registers (s : MachineState) (address : Word) :
        (hashRegistersState s).getMem (alignToDword address) =
          s.getMem (alignToDword address) := by
      simp [hashRegistersState, execInstrBr]
    rw [registers]
    change (copyRootState pointers).getWord32 _ = _
    rw [copyRoot_getWord32_frame pointers _ (by
      intro offset
      rw [destination]
      fin_cases offset <;> fin_cases index <;> decide)]
    simp [pointers, parameterPointers, execInstrBr, MachineState.getWord32]
    exact pair.2

theorem header_parameter_source (state : MachineState) (index : Fin 5) :
    (parentHeaderState state).getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  let read := BitVec.ofNat 64 (0x22cb4 + 4 * index.val)
  let tagged := parentTagState state
  let prefixed := parentPrefixState state
  let treed := SphincsVerifierHeader.treeState prefixed
  have tagPointer := parentTag_hash_pointer state
  have prefixPointer : prefixed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer prefixed).trans prefixPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 read =
    state.getWord32 read
  rw [index_word_frame treed read treePointer
      (by fin_cases index <;> decide),
    tree_word_frame prefixed read prefixPointer
      (by fin_cases index <;> decide)]
  change (SphincsVerifierHeader.positionState tagged).getWord32 read = _
  rw [position_word_frame tagged read tagPointer
      (by fin_cases index <;> decide)]
  exact parentTag_word_frame state read (by fin_cases index <;> decide)

theorem ready_parameter_data (state : MachineState) (index : Fin 5) :
    (parentHashReadyState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  let headed := parentHeaderState state
  change (hashRegistersState (parameterState headed)).getWord32 _ = _
  have registers (s : MachineState) (address : Word) :
      (hashRegistersState s).getWord32 address = s.getWord32 address := by
    simp [MachineState.getWord32, hashRegistersState, execInstrBr]
  rw [registers]
  have copied := SphincsVerifierFtsPayload.parameterState_data headed index
  change (SphincsVerifierFtsParameter.parameterState headed).getWord32 _ = _
  rw [copied]
  exact header_parameter_source state index

theorem ready_pair_bytes (state : MachineState) (i : Nat) (hi : i < 20) :
    (parentHashReadyState state).getByte (BitVec.ofNat 64 (0x40028 + i)) =
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) ∧
    (parentHashReadyState state).getByte (BitVec.ofNat 64 (0x4003c + i)) =
      state.getByte (BitVec.ofNat 64 (0x4003c + i)) := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  have words := ready_pair_data state index
  constructor
  · have ready := word32_byte (parentHashReadyState state) 0x40028
      (Or.inr (Or.inl rfl)) index byte
    have original := word32_byte state 0x40028
      (Or.inr (Or.inl rfl)) index byte
    simpa only [Nat.add_assoc, split] using
      ready.trans ((congrArg (fun value : BitVec 32 =>
        value.extractLsb' (8 * byte.val) 8) words.1).trans original.symm)
  · have ready := word32_byte (parentHashReadyState state) 0x4003c
      (Or.inr (Or.inr (Or.inl rfl))) index byte
    have original := word32_byte state 0x4003c
      (Or.inr (Or.inr (Or.inl rfl))) index byte
    simpa only [Nat.add_assoc, split] using
      ready.trans ((congrArg (fun value : BitVec 32 =>
        value.extractLsb' (8 * byte.val) 8) words.2).trans original.symm)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentPayload.ready_pair_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ready_pair_data

end SigGolfCandidate.SphincsVerifierFtsParentPayload
