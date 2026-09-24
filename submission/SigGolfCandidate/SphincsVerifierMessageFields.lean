import SigGolfCandidate.SphincsVerifierMessageFrame

/-!
# Witness fields in the message-index hash input

The verifier copies the randomizer and internal root from the witness into
adjacent 20-byte fields before hashing the submitted message.
-/

namespace SigGolfCandidate.SphincsVerifierMessageFields
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierMessageCopy

inductive CopyPair where
  | randomizer
  | root
  deriving DecidableEq

def sourceBase : CopyPair → Nat
  | .randomizer => 0x22cc8
  | .root => 0x22ca0

def destinationBase : CopyPair → Nat
  | .randomizer => 0x40028
  | .root => 0x4003c

def sourceWord (pair : CopyPair) (index : Fin 5) : Word :=
  BitVec.ofNat 64 (sourceBase pair + 4 * index.val)

def destinationWord (pair : CopyPair) (index : Fin 5) : Word :=
  BitVec.ofNat 64 (destinationBase pair + 4 * index.val)

@[simp] private theorem getWord32_setPC (state : MachineState)
    (pc target : Word) :
    (state.setPC pc).getWord32 target = state.getWord32 target := rfl

@[simp] private theorem getWord32_setReg (state : MachineState)
    (register : Reg) (value target : Word) :
    (state.setReg register value).getWord32 target =
      state.getWord32 target := by
  simp [MachineState.getWord32]

theorem copyWord_data (pair : CopyPair) (index : Fin 5)
    (state : MachineState)
    (source : state.getReg .x6 = BitVec.ofNat 64 (sourceBase pair))
    (destination : state.getReg .x7 =
      BitVec.ofNat 64 (destinationBase pair)) :
    (copyWordState index state).getWord32 (destinationWord pair index) =
      state.getWord32 (sourceWord pair index) := by
  cases pair <;> fin_cases index <;>
    simp [copyWordState, execInstrBr, getWord32_setWord32_same,
      sourceWord, destinationWord, sourceBase, destinationBase,
      source, destination, signExtend12,
      MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

theorem copyWord_other (pair : CopyPair) (written read : Fin 5)
    (different : written ≠ read) (state : MachineState)
    (destination : state.getReg .x7 =
      BitVec.ofNat 64 (destinationBase pair)) :
    (copyWordState written state).getWord32 (destinationWord pair read) =
      state.getWord32 (destinationWord pair read) := by
  cases pair <;> fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr, destinationWord,
      destinationBase, signExtend12,
      MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

theorem copyWord_source (pair : CopyPair) (written read : Fin 5)
    (state : MachineState)
    (destination : state.getReg .x7 =
      BitVec.ofNat 64 (destinationBase pair)) :
    (copyWordState written state).getWord32 (sourceWord pair read) =
      state.getWord32 (sourceWord pair read) := by
  cases pair <;> fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr, sourceWord,
      destinationBase, sourceBase, signExtend12,
      MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

private def CopyInvariant (pair : CopyPair) (original : MachineState)
    (count : Nat) (state : MachineState) : Prop :=
  state.getReg .x6 = BitVec.ofNat 64 (sourceBase pair) ∧
  state.getReg .x7 = BitVec.ofNat 64 (destinationBase pair) ∧
  (∀ index : Fin 5,
    state.getWord32 (sourceWord pair index) =
      original.getWord32 (sourceWord pair index)) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32 (destinationWord pair index) =
      original.getWord32 (sourceWord pair index))

private theorem copyStep (pair : CopyPair) (original state : MachineState)
    (slot : Fin 5)
    (invariant : CopyInvariant pair original slot.val state) :
    CopyInvariant pair original (slot.val + 1) (copyWordState slot state) := by
  rcases invariant with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ := copyWord_pointers slot state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination, ?_, ?_⟩
  · intro index
    rw [copyWord_source pair slot index state destination]
    exact sourceWords index
  · intro index before
    by_cases same : slot = index
    · subst index
      rw [copyWord_data pair slot state source destination]
      exact sourceWords slot
    · rw [copyWord_other pair slot index same state destination]
      have smaller : index.val < slot.val := by
        have unequal : slot.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact copiedWords index smaller

theorem copyRoot_pair_data (pair : CopyPair) (original : MachineState)
    (source : original.getReg .x6 = BitVec.ofNat 64 (sourceBase pair))
    (destination : original.getReg .x7 =
      BitVec.ofNat 64 (destinationBase pair))
    (index : Fin 5) :
    (copyRootState original).getWord32 (destinationWord pair index) =
      original.getWord32 (sourceWord pair index) := by
  have initial : CopyInvariant pair original 0 original := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro index impossible
    omega
  have after0 := copyStep pair original original 0 initial
  have after1 := copyStep pair original (copyWordState 0 original) 1 after0
  have after2 := copyStep pair original
    (copyWordState 1 (copyWordState 0 original)) 2 after1
  have after3 := copyStep pair original
    (copyWordState 2 (copyWordState 1 (copyWordState 0 original))) 3 after2
  have after4 := copyStep pair original
    (copyWordState 3 (copyWordState 2
      (copyWordState 1 (copyWordState 0 original)))) 4 after3
  exact after4.2.2.2 index (by omega)

theorem copyWord_getWord32_frame (written : Fin 5) (state : MachineState)
    (target : Word)
    (other : alignToDword
        (state.getReg .x7 + signExtend12
          (4#12 * BitVec.ofNat 12 written.val)) ≠ alignToDword target ∨
      byteOffset (state.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 written.val)) / 4 ≠
        byteOffset target / 4) :
    (copyWordState written state).getWord32 target =
      state.getWord32 target := by
  simp_all [copyWordState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_ne]
  rw [getWord32_setWord32_other _ _ _ _ other]
  simp

theorem copyRoot_getWord32_frame (state : MachineState) (target : Word)
    (outside : ∀ offset : Fin 5,
      alignToDword (state.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) ≠ alignToDword target ∨
      byteOffset (state.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) / 4 ≠
        byteOffset target / 4) :
    (copyRootState state).getWord32 target = state.getWord32 target := by
  let s1 := copyWordState 0 state
  let s2 := copyWordState 1 s1
  let s3 := copyWordState 2 s2
  let s4 := copyWordState 3 s3
  have d1 : s1.getReg .x7 = state.getReg .x7 :=
    (copyWord_pointers 0 state).2
  have d2 : s2.getReg .x7 = state.getReg .x7 :=
    (copyWord_pointers 1 s1).2.trans d1
  have d3 : s3.getReg .x7 = state.getReg .x7 :=
    (copyWord_pointers 2 s2).2.trans d2
  have d4 : s4.getReg .x7 = state.getReg .x7 :=
    (copyWord_pointers 3 s3).2.trans d3
  change (copyWordState 4 s4).getWord32 target = state.getWord32 target
  rw [copyWord_getWord32_frame 4 s4 target (by rw [d4]; exact outside 4),
    copyWord_getWord32_frame 3 s3 target (by rw [d3]; exact outside 3),
    copyWord_getWord32_frame 2 s2 target (by rw [d2]; exact outside 2),
    copyWord_getWord32_frame 1 s1 target (by rw [d1]; exact outside 1),
    copyWord_getWord32_frame 0 state target (outside 0)]

theorem bothCopies_randomizer_word (state : MachineState) (index : Fin 5) :
    (bothCopiesState state).getWord32
      (destinationWord .randomizer index) =
      state.getWord32 (sourceWord .randomizer index) := by
  let first := firstPointers state
  let copied := firstCopyState state
  let second := secondPointers copied
  have firstRegs := firstPointers_regs state
  have secondDestination := (secondPointers_regs copied).2
  have outside : ∀ offset : Fin 5,
      alignToDword (second.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) ≠
          alignToDword (destinationWord .randomizer index) ∨
      byteOffset (second.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) / 4 ≠
          byteOffset (destinationWord .randomizer index) / 4 := by
    intro offset
    rw [secondDestination]
    fin_cases index <;> fin_cases offset <;>
      decide
  change (copyRootState second).getWord32
    (destinationWord .randomizer index) =
      state.getWord32 (sourceWord .randomizer index)
  rw [copyRoot_getWord32_frame second _ outside]
  have pointersFrame (address : Word) :
      second.getWord32 address = copied.getWord32 address := by
    simp [second, secondPointers, execInstrBr]
  rw [pointersFrame]
  change (copyRootState first).getWord32
    (destinationWord .randomizer index) =
      state.getWord32 (sourceWord .randomizer index)
  rw [copyRoot_pair_data .randomizer first firstRegs.1 firstRegs.2]
  simp [first, firstPointers, execInstrBr]

theorem firstCopy_root_source_frame (state : MachineState)
    (index : Fin 5) :
    (firstCopyState state).getWord32 (sourceWord .root index) =
      state.getWord32 (sourceWord .root index) := by
  let first := firstPointers state
  have destination := (firstPointers_regs state).2
  have outside : ∀ offset : Fin 5,
      alignToDword (first.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) ≠
          alignToDword (sourceWord .root index) ∨
      byteOffset (first.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) / 4 ≠
          byteOffset (sourceWord .root index) / 4 := by
    intro offset
    rw [destination]
    fin_cases index <;> fin_cases offset <;>
      decide
  change (copyRootState first).getWord32 (sourceWord .root index) =
    state.getWord32 (sourceWord .root index)
  rw [copyRoot_getWord32_frame first _ outside]
  simp [first, firstPointers, execInstrBr]

theorem bothCopies_root_word (state : MachineState) (index : Fin 5) :
    (bothCopiesState state).getWord32 (destinationWord .root index) =
      state.getWord32 (sourceWord .root index) := by
  let copied := firstCopyState state
  let second := secondPointers copied
  have secondRegs := secondPointers_regs copied
  change (copyRootState second).getWord32 (destinationWord .root index) =
    state.getWord32 (sourceWord .root index)
  rw [copyRoot_pair_data .root second secondRegs.1 secondRegs.2]
  have pointersFrame (address : Word) :
      second.getWord32 address = copied.getWord32 address := by
    simp [second, secondPointers, execInstrBr]
  rw [pointersFrame]
  exact firstCopy_root_source_frame state index

theorem bothCopies_pair_word (pair : CopyPair) (state : MachineState)
    (index : Fin 5) :
    (bothCopiesState state).getWord32 (destinationWord pair index) =
      state.getWord32 (sourceWord pair index) := by
  cases pair
  · exact bothCopies_randomizer_word state index
  · exact bothCopies_root_word state index

/-- info: 'SigGolfCandidate.SphincsVerifierMessageFields.copyRoot_pair_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms copyRoot_pair_data

/-- info: 'SigGolfCandidate.SphincsVerifierMessageFields.bothCopies_randomizer_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bothCopies_randomizer_word

/-- info: 'SigGolfCandidate.SphincsVerifierMessageFields.bothCopies_root_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bothCopies_root_word

end SigGolfCandidate.SphincsVerifierMessageFields
