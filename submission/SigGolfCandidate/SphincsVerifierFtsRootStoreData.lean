import SigGolfCandidate.SphincsVerifierFtsRootStore
import SigGolfCandidate.SphincsVerifierCopy20DataGeneral
import SigGolfCandidate.SphincsVerifierCopyMemory

/-! The root-copy block writes the current digest into the tree's root slot. -/

namespace SigGolfCandidate.SphincsVerifierFtsRootStoreData
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopy20DataGeneral
open SigGolfCandidate.SphincsVerifierFtsRootStore
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem rootStore_cells_disjoint (tree : FtsTree)
    (source destination : Fin 5) :
    alignToDword (BitVec.ofNat 64 (0x44a00 + 4 * source.val)) ≠
      alignToDword
        (BitVec.ofNat 64 (0x44100 + 20 * tree.val + 4 * destination.val)) := by
  fin_cases tree <;> fin_cases source <;> fin_cases destination <;> decide

theorem rootStore_source_frame (tree : FtsTree)
    (written read : Fin 5) (state : MachineState)
    (destination : state.getReg .x7 =
      BitVec.ofNat 64 (0x44100 + 20 * tree.val)) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x44a00 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * read.val)) := by
  have destinationCell : alignToDword
      (state.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 written.val)) =
      alignToDword (BitVec.ofNat 64
        (0x44100 + 20 * tree.val + 4 * written.val)) := by
    rw [destination]
    fin_cases tree <;> fin_cases written <;> decide
  have outside : alignToDword
      (BitVec.ofNat 64 (0x44a00 + 4 * read.val)) ≠
      alignToDword (state.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 written.val)) := by
    rw [destinationCell]
    exact rootStore_cells_disjoint tree read written
  simp only [MachineState.getWord32]
  rw [copyWord_mem_frame written state _ outside]

theorem rootStore_destination_other (tree : FtsTree)
    (written read : Fin 5) (different : written ≠ read)
    (state : MachineState)
    (destination : state.getReg .x7 =
      BitVec.ofNat 64 (0x44100 + 20 * tree.val)) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (0x44100 + 20 * tree.val + 4 * read.val)) =
      state.getWord32
        (BitVec.ofNat 64 (0x44100 + 20 * tree.val + 4 * read.val)) := by
  fin_cases tree <;> fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

private def RootCopyInvariant (original : MachineState)
    (tree : FtsTree) (count : Nat) (state : MachineState) : Prop :=
  state.getReg .x6 = 0x44a00 ∧
  state.getReg .x7 = BitVec.ofNat 64 (0x44100 + 20 * tree.val) ∧
  (∀ index : Fin 5,
    state.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val))) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32
      (BitVec.ofNat 64 (0x44100 + 20 * tree.val + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)))

private theorem rootCopyStep (original state : MachineState)
    (tree : FtsTree) (slot : Fin 5)
    (invariant : RootCopyInvariant original tree slot.val state) :
    RootCopyInvariant original tree (slot.val + 1)
      (copyWordState slot state) := by
  rcases invariant with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ := copyWord_pointers slot state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination,
    ?_, ?_⟩
  · intro index
    rw [rootStore_source_frame tree slot index state destination]
    exact sourceWords index
  · intro index before
    by_cases same : slot = index
    · subst index
      rw [copyWord_data_general slot state 0x44a00
        (0x44100 + 20 * tree.val) source destination]
      exact sourceWords slot
    · rw [rootStore_destination_other tree slot index same state destination]
      have smaller : index.val < slot.val := by
        have unequal : slot.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact copiedWords index smaller

theorem rootStore_copy_data (original : MachineState) (tree : FtsTree)
    (source : original.getReg .x6 = 0x44a00)
    (destination : original.getReg .x7 =
      BitVec.ofNat 64 (0x44100 + 20 * tree.val))
    (index : Fin 5) :
    (copyRootState original).getWord32
      (BitVec.ofNat 64 (0x44100 + 20 * tree.val + 4 * index.val)) =
      original.getWord32
        (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  have initial : RootCopyInvariant original tree 0 original := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro index impossible
    omega
  have after0 := rootCopyStep original original tree 0 initial
  have after1 := rootCopyStep original (copyWordState 0 original)
    tree 1 after0
  have after2 := rootCopyStep original
    (copyWordState 1 (copyWordState 0 original)) tree 2 after1
  have after3 := rootCopyStep original
    (copyWordState 2 (copyWordState 1 (copyWordState 0 original)))
    tree 3 after2
  have after4 := rootCopyStep original
    (copyWordState 3 (copyWordState 2 (copyWordState 1
      (copyWordState 0 original)))) tree 4 after3
  exact after4.2.2.2 index (by have := index.isLt; omega)

theorem rootStore_data (state : MachineState) (tree : FtsTree)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (index : Fin 5) :
    (copyRootState (rootStoreSetupState state)).getWord32
      (BitVec.ofNat 64 (0x44100 + 20 * tree.val + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  have copied := rootStore_copy_data (rootStoreSetupState state) tree
    (rootStoreSetup_source state)
    (rootStoreSetup_destination state tree counter) index
  rw [copied]
  simp only [MachineState.getWord32]
  rw [rootStoreSetup_mem]

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootStoreData.rootStore_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootStore_data

end SigGolfCandidate.SphincsVerifierFtsRootStoreData
