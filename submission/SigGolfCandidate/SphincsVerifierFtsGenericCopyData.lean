import SigGolfCandidate.SphincsVerifierFtsGenericPairTrace

/-! Data transfer for a FORS authentication sibling at any bounded path pointer. -/

namespace SigGolfCandidate.SphincsVerifierFtsGenericCopyData
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopy20DataGeneral
open SigGolfCandidate.SphincsVerifierFtsGenericPairTrace
open SigGolfCandidate.SphincsVerifierFtsRightPath
set_option maxRecDepth 16384

theorem source_dest_cells_disjoint (sourceBase destinationBase : Nat)
    (small : sourceBase + 20 ≤ 0x40000)
    (destination : destinationBase = 0x40028 ∨ destinationBase = 0x4003c)
    (written read : Fin 5) :
    alignToDword (BitVec.ofNat 64 (sourceBase + 4 * read.val)) ≠
      alignToDword (BitVec.ofNat 64 (destinationBase + 4 * written.val)) := by
  have sourceSmall : sourceBase + 4 * read.val < 0x40000 := by
    have := read.isLt
    omega
  have sourceNat :
      (BitVec.ofNat 64 (sourceBase + 4 * read.val)).toNat =
        sourceBase + 4 * read.val := by
    simp only [BitVec.toNat_ofNat]
    omega
  have sourceAligned :
      (alignToDword (BitVec.ofNat 64 (sourceBase + 4 * read.val))).toNat <
        0x40000 := by
    have bound : ∀ address : Word,
        (alignToDword address).toNat ≤ address.toNat := by
      intro address
      unfold alignToDword
      rw [BitVec.toNat_and]
      exact Nat.and_le_left
    have := bound (BitVec.ofNat 64 (sourceBase + 4 * read.val))
    omega
  have destinationAligned :
      0x40000 ≤ (alignToDword
        (BitVec.ofNat 64 (destinationBase + 4 * written.val))).toNat := by
    rcases destination with h | h <;> subst destinationBase <;>
      fin_cases written <;> decide
  intro equal
  have same := congrArg BitVec.toNat equal
  omega

theorem copyWord_source_frame (sourceBase destinationBase : Nat)
    (small : sourceBase + 20 ≤ 0x40000)
    (destinationSupported : destinationBase = 0x40028 ∨
      destinationBase = 0x4003c)
    (written read : Fin 5) (state : MachineState)
    (destination : state.getReg .x7 = BitVec.ofNat 64 destinationBase) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (sourceBase + 4 * read.val)) =
        state.getWord32
          (BitVec.ofNat 64 (sourceBase + 4 * read.val)) := by
  let address := alignToDword
    (BitVec.ofNat 64 (sourceBase + 4 * read.val))
  have destinationCell : alignToDword
      (state.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 written.val)) =
        alignToDword
          (BitVec.ofNat 64 (destinationBase + 4 * written.val)) := by
    rw [destination]
    rcases destinationSupported with h | h <;> subst destinationBase <;>
      fin_cases written <;> decide
  have outside : address ≠ alignToDword
      (state.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 written.val)) := by
    rw [destinationCell]
    exact source_dest_cells_disjoint sourceBase destinationBase small
      destinationSupported written read
  simp only [MachineState.getWord32]
  rw [copyWord_mem_frame written state address outside]

theorem copyWord_destination_other (destinationBase : Nat)
    (supported : destinationBase = 0x40028 ∨ destinationBase = 0x4003c)
    (written read : Fin 5) (different : written ≠ read)
    (state : MachineState)
    (destination : state.getReg .x7 = BitVec.ofNat 64 destinationBase) :
    (copyWordState written state).getWord32
      (BitVec.ofNat 64 (destinationBase + 4 * read.val)) =
        state.getWord32
          (BitVec.ofNat 64 (destinationBase + 4 * read.val)) := by
  rcases supported with h | h
  · subst destinationBase
    exact copyWord_other_fts written read different state destination
  · subst destinationBase
    exact rightCurrent_other written read different state destination

private def VariableCopyInvariant (original : MachineState)
    (sourceBase destinationBase count : Nat) (state : MachineState) : Prop :=
  state.getReg .x6 = BitVec.ofNat 64 sourceBase ∧
  state.getReg .x7 = BitVec.ofNat 64 destinationBase ∧
  (∀ index : Fin 5,
    state.getWord32 (BitVec.ofNat 64 (sourceBase + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (sourceBase + 4 * index.val))) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32 (BitVec.ofNat 64 (destinationBase + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (sourceBase + 4 * index.val)))

private theorem variableCopyStep (original state : MachineState)
    (sourceBase destinationBase : Nat)
    (small : sourceBase + 20 ≤ 0x40000)
    (supported : destinationBase = 0x40028 ∨ destinationBase = 0x4003c)
    (slot : Fin 5)
    (invariant : VariableCopyInvariant original sourceBase destinationBase
      slot.val state) :
    VariableCopyInvariant original sourceBase destinationBase
      (slot.val + 1) (copyWordState slot state) := by
  rcases invariant with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ := copyWord_pointers slot state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination, ?_, ?_⟩
  · intro index
    rw [copyWord_source_frame sourceBase destinationBase small supported
      slot index state destination]
    exact sourceWords index
  · intro index before
    by_cases same : slot = index
    · subst index
      rw [copyWord_data_general slot state sourceBase destinationBase
        source destination]
      exact sourceWords slot
    · rw [copyWord_destination_other destinationBase supported
        slot index same state destination]
      have smaller : index.val < slot.val := by
        have unequal : slot.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact copiedWords index smaller

theorem copyRoot_data_belowHash (original : MachineState)
    (sourceBase destinationBase : Nat)
    (small : sourceBase + 20 ≤ 0x40000)
    (supported : destinationBase = 0x40028 ∨ destinationBase = 0x4003c)
    (source : original.getReg .x6 = BitVec.ofNat 64 sourceBase)
    (destination : original.getReg .x7 = BitVec.ofNat 64 destinationBase)
    (index : Fin 5) :
    (copyRootState original).getWord32
      (BitVec.ofNat 64 (destinationBase + 4 * index.val)) =
        original.getWord32
          (BitVec.ofNat 64 (sourceBase + 4 * index.val)) := by
  have initial : VariableCopyInvariant original sourceBase destinationBase
      0 original := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro index impossible
    omega
  have after0 := variableCopyStep original original sourceBase destinationBase
    small supported 0 initial
  have after1 := variableCopyStep original (copyWordState 0 original)
    sourceBase destinationBase small supported 1 after0
  have after2 := variableCopyStep original
    (copyWordState 1 (copyWordState 0 original))
    sourceBase destinationBase small supported 2 after1
  have after3 := variableCopyStep original
    (copyWordState 2 (copyWordState 1 (copyWordState 0 original)))
    sourceBase destinationBase small supported 3 after2
  have after4 := variableCopyStep original
    (copyWordState 3 (copyWordState 2
      (copyWordState 1 (copyWordState 0 original))))
    sourceBase destinationBase small supported 4 after3
  exact after4.2.2.2 index (by have := index.isLt; omega)

theorem copyRoot_source_frame (state : MachineState)
    (sourceBase destinationBase : Nat)
    (small : sourceBase + 20 ≤ 0x40000)
    (supported : destinationBase = 0x40028 ∨ destinationBase = 0x4003c)
    (destination : state.getReg .x7 = BitVec.ofNat 64 destinationBase)
    (index : Fin 5) :
    (copyRootState state).getWord32
      (BitVec.ofNat 64 (sourceBase + 4 * index.val)) =
        state.getWord32
          (BitVec.ofNat 64 (sourceBase + 4 * index.val)) := by
  simp only [MachineState.getWord32]
  apply congrArg (fun value : Word =>
    extractWord32 value (byteOffset
      (BitVec.ofNat 64 (sourceBase + 4 * index.val)) / 4))
  apply copyRoot_mem_frame
  intro offset
  rw [destination]
  have cell : alignToDword
      (BitVec.ofNat 64 (sourceBase + 4 * index.val)) ≠
        alignToDword
          (BitVec.ofNat 64 (destinationBase + 4 * offset.val)) :=
    source_dest_cells_disjoint sourceBase destinationBase small supported
      offset index
  have equal : alignToDword
      (BitVec.ofNat 64 destinationBase + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) =
        alignToDword
          (BitVec.ofNat 64 (destinationBase + 4 * offset.val)) := by
    rcases supported with h | h <;> subst destinationBase <;>
      fin_cases offset <;> decide
  rw [equal]
  exact cell

/-- info: 'SigGolfCandidate.SphincsVerifierFtsGenericCopyData.copyRoot_data_belowHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms copyRoot_data_belowHash

end SigGolfCandidate.SphincsVerifierFtsGenericCopyData
