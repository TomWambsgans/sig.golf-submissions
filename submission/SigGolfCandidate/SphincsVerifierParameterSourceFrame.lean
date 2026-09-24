import SigGolfCandidate.SphincsVerifierWitnessAtHash

/-!
# Public-parameter source through the first verifier HASH

The witness's 20-byte public parameter occupies three memory doublewords.
The commitment setup, HASH answer, comparison, and subsequent field copies
leave those doublewords unchanged.
-/

namespace SigGolfCandidate.SphincsVerifierParameterSourceFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopyParameter
open SigGolfCandidate.SphincsVerifierHashSetup
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierMessageFrame
open SigGolfCandidate.SphincsVerifierCommitmentCheck

def parameterCell (index : Fin 3) : Word :=
  BitVec.ofNat 64 (0x22cb0 + 8 * index.val)

def scratchCell (slot : Fin 4) : Word :=
  BitVec.ofNat 64 (0x43000 + 8 * slot.val)

theorem setupAndBoth_parameterCell_frame (state : MachineState)
    (index : Fin 3) :
    (setupAndBothState state).getMem (parameterCell index) =
      state.getMem (parameterCell index) := by
  let read := parameterCell index
  let jumped := execInstrBr state (.JAL .x0 16)
  let scratch := SphincsVerifierSlots.headerState jumped
  let firstPointers := addressSetupState scratch
  let firstCopy := copyRootState firstPointers
  let secondPointers := parameterPointers firstCopy
  have firstDestination := (addressSetup_regs scratch).2
  have secondDestination := (parameterPointers_regs firstCopy).2
  have firstOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (firstPointers.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [firstDestination]
    fin_cases index <;> fin_cases offset <;> decide
  have secondOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (secondPointers.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [secondDestination]
    fin_cases index <;> fin_cases offset <;> decide
  change (copyRootState secondPointers).getMem read = state.getMem read
  rw [copyRoot_mem_frame secondPointers read secondOutside,
    parameterPointers_memory,
    copyRoot_mem_frame firstPointers read firstOutside,
    addressSetup_memory]
  change (SphincsVerifierSlots.headerState jumped).getMem read =
    state.getMem read
  simp only [SphincsVerifierSlots.headerState]
  have slotOutside (slot : Fin 4) :
      read ≠ BitVec.ofNat 64 (0x43000 + 8 * slot.val) := by
    fin_cases index <;> fin_cases slot <;> decide
  rw [SphincsVerifierSlots.slot_memory 3,
    if_neg (slotOutside 3), SphincsVerifierSlots.slot_memory 2,
    if_neg (slotOutside 2), SphincsVerifierSlots.slot_memory 1,
    if_neg (slotOutside 1), SphincsVerifierSlots.slot_memory 0,
    if_neg (slotOutside 0)]
  simp [jumped, execInstrBr]

theorem firstHash_parameterCell_frame (state : MachineState)
    (index : Fin 3) :
    (firstHashState state).getMem (parameterCell index) =
      state.getMem (parameterCell index) := by
  let read := parameterCell index
  change (SphincsVerifierHashSetup.hashRegistersState
    (SphincsVerifierHeader.headerState (setupAndBothState state))).getMem
      read = state.getMem read
  rw [SphincsVerifierHashSetup.hashRegisters_memory]
  have outside0 : read ≠ 0x40000 := by fin_cases index <;> decide
  have outside8 : read ≠ 0x40008 := by fin_cases index <;> decide
  have outside16 : read ≠ 0x40010 := by fin_cases index <;> decide
  rw [SphincsVerifierHashMemory.header_mem_frame _ _
    outside0 outside8 outside16,
    setupAndBoth_parameterCell_frame]

theorem writeHash_parameterCell_frame (state : MachineState)
    (answer : BitVec 256) (index : Fin 3)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getMem (parameterCell index) =
      state.getMem (parameterCell index) := by
  fin_cases index <;>
    simp [parameterCell, writeHash, MachineState.writeWords_cons,
      destination, MachineState.getMem_setMem_ne]

theorem bothCopies_parameterCell_frame (state : MachineState)
    (index : Fin 3) :
    (bothCopiesState state).getMem (parameterCell index) =
      state.getMem (parameterCell index) := by
  let read := parameterCell index
  let first := firstPointers state
  let copied := firstCopyState state
  let second := secondPointers copied
  have firstDestination := (firstPointers_regs state).2
  have secondDestination := (secondPointers_regs copied).2
  have firstOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (first.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [firstDestination]
    fin_cases index <;> fin_cases offset <;> decide
  have secondOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (second.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [secondDestination]
    fin_cases index <;> fin_cases offset <;> decide
  change (copyRootState second).getMem read = state.getMem read
  rw [copyRoot_mem_frame second read secondOutside,
    secondPointers_memory]
  change (copyRootState first).getMem read = state.getMem read
  rw [copyRoot_mem_frame first read firstOutside,
    firstPointers_memory]

theorem afterMessageCopies_parameterCell_frame (state : MachineState)
    (answer : BitVec 256) (index : Fin 3) :
    (afterMessageCopiesState state answer).getMem (parameterCell index) =
      state.getMem (parameterCell index) := by
  have destination := (firstHash_registers state).2.2.1
  change (bothCopiesState
    (compareSuccessState (writeHash (firstHashState state) answer))).getMem
      (parameterCell index) = state.getMem (parameterCell index)
  rw [bothCopies_parameterCell_frame, compareSuccess_memory,
    writeHash_parameterCell_frame _ _ index destination,
    firstHash_parameterCell_frame]

theorem bothCopies_scratch_frame (state : MachineState) (slot : Fin 4) :
    (bothCopiesState state).getMem (scratchCell slot) =
      state.getMem (scratchCell slot) := by
  let read := scratchCell slot
  let first := firstPointers state
  let copied := firstCopyState state
  let second := secondPointers copied
  have firstDestination := (firstPointers_regs state).2
  have secondDestination := (secondPointers_regs copied).2
  have firstOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (first.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [firstDestination]
    fin_cases slot <;> fin_cases offset <;> decide
  have secondOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (second.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [secondDestination]
    fin_cases slot <;> fin_cases offset <;> decide
  change (copyRootState second).getMem read = state.getMem read
  rw [copyRoot_mem_frame second read secondOutside,
    secondPointers_memory]
  change (copyRootState first).getMem read = state.getMem read
  rw [copyRoot_mem_frame first read firstOutside,
    firstPointers_memory]

theorem writeHash_scratch_frame (state : MachineState)
    (answer : BitVec 256) (slot : Fin 4)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getMem (scratchCell slot) =
      state.getMem (scratchCell slot) := by
  fin_cases slot <;>
    simp [scratchCell, writeHash, MachineState.writeWords_cons,
      destination, MachineState.getMem_setMem_ne]

theorem afterMessageCopies_scratch_zero (state : MachineState)
    (answer : BitVec 256) (slot : Fin 4) :
    (afterMessageCopiesState state answer).getMem (scratchCell slot) = 0 := by
  have destination := (firstHash_registers state).2.2.1
  change (bothCopiesState
    (compareSuccessState (writeHash (firstHashState state) answer))).getMem
      (scratchCell slot) = 0
  rw [bothCopies_scratch_frame, compareSuccess_memory,
    writeHash_scratch_frame _ _ slot destination]
  simpa [scratchCell] using firstHash_scratch state slot

/-- info: 'SigGolfCandidate.SphincsVerifierParameterSourceFrame.afterMessageCopies_parameterCell_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms afterMessageCopies_parameterCell_frame

end SigGolfCandidate.SphincsVerifierParameterSourceFrame
