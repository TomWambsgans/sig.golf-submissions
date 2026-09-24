import SigGolfCandidate.SphincsVerifierFtsCopyAccess
import SigGolfCandidate.SphincsVerifierCopyMemory

/-! Data transfer facts for the verifier's five 32-bit load/store pairs. -/

namespace SigGolfCandidate.SphincsVerifierCopy20DataGeneral
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
set_option maxRecDepth 16384

theorem copyWord_data_general (offset : Fin 5) (state : MachineState)
    (sourceBase destinationBase : Nat)
    (source : state.getReg .x6 = BitVec.ofNat 64 sourceBase)
    (destination : state.getReg .x7 = BitVec.ofNat 64 destinationBase) :
    (copyWordState offset state).getWord32
      (BitVec.ofNat 64 (destinationBase + 4 * offset.val)) =
      state.getWord32 (BitVec.ofNat 64 (sourceBase + 4 * offset.val)) := by
  fin_cases offset <;>
    simp [copyWordState, execInstrBr, getWord32_setWord32_same,
      source, destination, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      BitVec.ofNat_add]

theorem copyWord_other_fts (written read : Fin 5) (different : written ≠ read)
    (state : MachineState) (destination : state.getReg .x7 = 0x40028) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

theorem copyWord_source_fts (written read : Fin 5) (state : MachineState)
    (destination : state.getReg .x7 = 0x40028) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x22cdc + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cdc + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

private def FirstFtsCopyInvariant (original : MachineState) (count : Nat)
    (state : MachineState) : Prop :=
  state.getReg .x6 = 0x22cdc ∧
  state.getReg .x7 = 0x40028 ∧
  (∀ index : Fin 5,
    state.getWord32 (BitVec.ofNat 64 (0x22cdc + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22cdc + 4 * index.val))) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22cdc + 4 * index.val)))

private theorem firstFtsCopyStep (original state : MachineState) (slot : Fin 5)
    (invariant : FirstFtsCopyInvariant original slot.val state) :
    FirstFtsCopyInvariant original (slot.val + 1) (copyWordState slot state) := by
  rcases invariant with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ := copyWord_pointers slot state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination, ?_, ?_⟩
  · intro index
    rw [copyWord_source_fts slot index state destination]
    exact sourceWords index
  · intro index before
    by_cases same : slot = index
    · subst index
      rw [copyWord_data_general slot state 0x22cdc 0x40028 source destination]
      exact sourceWords slot
    · rw [copyWord_other_fts slot index same state destination]
      have smaller : index.val < slot.val := by
        have unequal : slot.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact copiedWords index smaller

theorem firstFtsCopy_data (original : MachineState)
    (source : original.getReg .x6 = 0x22cdc)
    (destination : original.getReg .x7 = 0x40028)
    (index : Fin 5) :
    (copyRootState original).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x22cdc + 4 * index.val)) := by
  have initial : FirstFtsCopyInvariant original 0 original := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro index impossible
    omega
  have after0 := firstFtsCopyStep original original 0 initial
  have after1 := firstFtsCopyStep original (copyWordState 0 original) 1 after0
  have after2 := firstFtsCopyStep original (copyWordState 1
    (copyWordState 0 original)) 2 after1
  have after3 := firstFtsCopyStep original (copyWordState 2
    (copyWordState 1 (copyWordState 0 original))) 3 after2
  have after4 := firstFtsCopyStep original (copyWordState 3
    (copyWordState 2 (copyWordState 1 (copyWordState 0 original)))) 4 after3
  exact (after4.2.2.2 index (by have := index.isLt; omega))

/-- info: 'SigGolfCandidate.SphincsVerifierCopy20DataGeneral.firstFtsCopy_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstFtsCopy_data

end SigGolfCandidate.SphincsVerifierCopy20DataGeneral
