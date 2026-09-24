import SigGolfCandidate.SphincsVerifierMessage32Data
import SigGolfCandidate.SphincsVerifierHashMemory

/-!
# Message input frame through the commitment check

The verifier's early stores target scratch space, its commitment hash buffer,
and its HASH answer. None writes the four loaded message words at addresses
0, 8, 16, and 24.
-/

namespace SigGolfCandidate.SphincsVerifierMessageFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopyParameter
open SigGolfCandidate.SphincsVerifierHashSetup
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCommitmentCheck
open SigGolfCandidate.SphincsVerifierMessage32Data
open SigGolfCandidate.SphincsVerifierLoader
open SigGolfCandidate.SphincsSubmission

private def messageWord (index : Fin 4) : Word :=
  BitVec.ofNat 64 (8 * index.val)

theorem setupAndBoth_message_frame (state : MachineState) (index : Fin 4) :
    (setupAndBothState state).getMem (messageWord index) =
      state.getMem (messageWord index) := by
  let read := messageWord index
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
    fin_cases index <;> fin_cases offset <;>
      decide
  have secondOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (secondPointers.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [secondDestination]
    fin_cases index <;> fin_cases offset <;>
      decide
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
    fin_cases index <;> fin_cases slot <;>
      decide
  rw [SphincsVerifierSlots.slot_memory 3,
    if_neg (slotOutside 3), SphincsVerifierSlots.slot_memory 2,
    if_neg (slotOutside 2), SphincsVerifierSlots.slot_memory 1,
    if_neg (slotOutside 1), SphincsVerifierSlots.slot_memory 0,
    if_neg (slotOutside 0)]
  simp [jumped, execInstrBr]

theorem firstHash_message_frame (state : MachineState) (index : Fin 4) :
    (firstHashState state).getMem (messageWord index) =
      state.getMem (messageWord index) := by
  let read := messageWord index
  change (SphincsVerifierHashSetup.hashRegistersState
    (SphincsVerifierHeader.headerState (setupAndBothState state))).getMem
      read = state.getMem read
  rw [SphincsVerifierHashSetup.hashRegisters_memory]
  have outside0 : read ≠ 0x40000 := by fin_cases index <;> decide
  have outside8 : read ≠ 0x40008 := by fin_cases index <;> decide
  have outside16 : read ≠ 0x40010 := by fin_cases index <;> decide
  rw [header_mem_frame _ _ outside0 outside8 outside16,
    setupAndBoth_message_frame]

theorem writeHash_message_frame (state : MachineState)
    (answer : BitVec 256) (index : Fin 4)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getMem (messageWord index) =
      state.getMem (messageWord index) := by
  fin_cases index <;>
    simp [messageWord, writeHash, MachineState.writeWords_cons,
      destination,
      MachineState.getMem_setMem_ne]

theorem compareSuccess_memory (state : MachineState) (address : Word) :
    (compareSuccessState state).getMem address = state.getMem address := by
  simp [compareSuccessState, execInstrBr]

theorem firstPointers_memory (state : MachineState) (address : Word) :
    (firstPointers state).getMem address = state.getMem address := by
  simp [firstPointers, execInstrBr]

theorem secondPointers_memory (state : MachineState) (address : Word) :
    (secondPointers state).getMem address = state.getMem address := by
  simp [secondPointers, execInstrBr]

theorem bothCopies_message_frame (state : MachineState) (index : Fin 4) :
    (bothCopiesState state).getMem (messageWord index) =
      state.getMem (messageWord index) := by
  let read := messageWord index
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
    fin_cases index <;> fin_cases offset <;>
      decide
  have secondOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (second.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [secondDestination]
    fin_cases index <;> fin_cases offset <;>
      decide
  change (copyRootState second).getMem read = state.getMem read
  rw [copyRoot_mem_frame second read secondOutside,
    secondPointers_memory]
  change (copyRootState first).getMem read = state.getMem read
  rw [copyRoot_mem_frame first read firstOutside,
    firstPointers_memory]

theorem afterMessageCopies_message_frame (state : MachineState)
    (answer : BitVec 256) (index : Fin 4) :
    (afterMessageCopiesState state answer).getMem (messageWord index) =
      state.getMem (messageWord index) := by
  have destination := (firstHash_registers state).2.2.1
  change (bothCopiesState
    (compareSuccessState (writeHash (firstHashState state) answer))).getMem
      (messageWord index) = state.getMem (messageWord index)
  rw [bothCopies_message_frame, compareSuccess_memory,
    writeHash_message_frame _ _ index destination,
    firstHash_message_frame]

/-- The certified copy path places the organizer's submitted message into the
    second HASH input, word for word. -/
theorem loaded_message32_exact (publicKey : SigGolf.PublicKey)
    (message : Message) (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState submission .verify (message, publicKey, witness) =
      some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64) :
    ∃ final, OrdinarySteps SphincsImages.verify
      (writeHash (firstHashState state) answer) 65 final ∧
      SphincsVerifierMessage32.LoopInvariant 0 final ∧
      ∀ index : Fin 4,
        final.getMem (BitVec.ofNat 64 (0x40050 + 8 * index.val)) =
          message.extractLsb' (64 * index.val) 64 := by
  obtain ⟨final, steps, invariant, contents⟩ :=
    loaded_message32_block_with_data publicKey message witness state answer
      loaded answerMatches
  refine ⟨final, steps, invariant, ?_⟩
  intro index
  calc
    final.getMem (BitVec.ofNat 64 (0x40050 + 8 * index.val)) =
        (afterMessageCopiesState state answer).getMem
          (BitVec.ofNat 64 (8 * index.val)) :=
      copyData_final_word _ _ contents index
    _ = state.getMem (BitVec.ofNat 64 (8 * index.val)) := by
      simpa [messageWord] using
        afterMessageCopies_message_frame state answer index
    _ = message.extractLsb' (64 * index.val) 64 :=
      loaded_message_word publicKey message witness state loaded index

/-- info: 'SigGolfCandidate.SphincsVerifierMessageFrame.loaded_message32_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_message32_exact

end SigGolfCandidate.SphincsVerifierMessageFrame
