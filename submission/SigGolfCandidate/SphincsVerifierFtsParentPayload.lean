import SigGolfCandidate.SphincsVerifierFtsParentHash
import SigGolfCandidate.SphincsVerifierFtsPayload

/-! The first FORS parent HASH setup preserves both assembled child digests. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentPayload
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierMessageFields
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

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentPayload.ready_pair_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ready_pair_data

end SigGolfCandidate.SphincsVerifierFtsParentPayload
