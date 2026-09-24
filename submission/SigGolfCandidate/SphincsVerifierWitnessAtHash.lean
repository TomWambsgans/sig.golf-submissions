import SigGolfCandidate.SphincsVerifierWitnessFrame

/-!
# Complete message-index payload before HASH

The four-iteration message copy leaves the two preceding 20-byte witness
fields intact. Its final state therefore contains the submitted witness
randomizer and root alongside the submitted message.
-/

namespace SigGolfCandidate.SphincsVerifierWitnessAtHash
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Sphincs.Expansion
open SigGolfCandidate.SphincsVerifierMessage32
open SigGolfCandidate.SphincsVerifierMessage32Data
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierWitnessFrame
open SigGolfCandidate.SphincsVerifierMessageFrame
open SigGolfCandidate.SphincsVerifierHashSetup
open SigGolfCandidate.SphincsSubmission

def FieldData (original state : MachineState) : Prop :=
  ∀ pair : CopyPair, ∀ index : Fin 5,
    state.getWord32 (destinationWord pair index) =
      original.getWord32 (destinationWord pair index)

theorem loopNext_field_cell_frame (pair : CopyPair) (index : Fin 5)
    (remaining : Nat) (state : MachineState)
    (inv : LoopInvariant (remaining + 1) state) :
    (loopNext state).getMem (alignToDword (destinationWord pair index)) =
      state.getMem (alignToDword (destinationWord pair index)) := by
  obtain ⟨bound, _, _, destination, _⟩ := inv
  rw [loop_next_mem, destination]
  have other : alignToDword (destinationWord pair index) ≠
      BitVec.ofNat 64 (0x40050 + 8 * (4 - (remaining + 1))) := by
    have small : remaining ≤ 3 := by omega
    interval_cases remaining <;> cases pair <;> fin_cases index <;>
      decide
  rw [if_neg other]

theorem loopNext_field_word_frame (pair : CopyPair) (index : Fin 5)
    (remaining : Nat) (state : MachineState)
    (inv : LoopInvariant (remaining + 1) state) :
    (loopNext state).getWord32 (destinationWord pair index) =
      state.getWord32 (destinationWord pair index) := by
  simp only [MachineState.getWord32]
  rw [loopNext_field_cell_frame pair index remaining state inv]

theorem fieldData_step (original state : MachineState)
    (remaining : Nat) (inv : LoopInvariant (remaining + 1) state)
    (fields : FieldData original state) :
    FieldData original (loopNext state) := by
  intro pair index
  rw [loopNext_field_word_frame pair index remaining state inv]
  exact fields pair index

theorem loop_run_with_full_data (remaining : Nat)
    (original state : MachineState)
    (inv : LoopInvariant remaining state)
    (data : CopyData original (4 - remaining) state)
    (fields : FieldData original state) :
    ∃ final, OrdinarySteps SphincsImages.verify state (6 * remaining) final ∧
      LoopInvariant 0 final ∧ CopyData original 4 final ∧
      FieldData original final := by
  induction remaining generalizing state with
  | zero =>
    exact ⟨state, by simpa using OrdinarySteps.refl state, inv,
      by simpa using data, fields⟩
  | succ remaining ih =>
    have pc : state.pc = 0x11e0 := by simpa [LoopInvariant] using inv.2.1
    have access := loop_accesses remaining state inv
    have first := loop_block state pc access.1 access.2
    have next := loop_invariant remaining state inv
    have nextData := copyData_step original state remaining inv data
    have nextFields := fieldData_step original state remaining inv fields
    obtain ⟨final, rest, finalInv, finalData, finalFields⟩ :=
      ih (loopNext state) next nextData nextFields
    refine ⟨final, ?_, finalInv, finalData, finalFields⟩
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using first.append rest

theorem message32_block_full_data (state : MachineState)
    (pc : state.pc = 0x11d0) :
    ∃ final, OrdinarySteps SphincsImages.verify state 28 final ∧
      LoopInvariant 0 final ∧ CopyData state 4 final ∧
      FieldData state final := by
  have prefixTrace := prefix_block state pc
  have prefixData : CopyData state 0
      (SphincsVerifierMessage32.prefixState state) := by
    constructor
    · intro index impossible
      omega
    · intro index
      exact prefix_memory state _
  have prefixFields : FieldData state
      (SphincsVerifierMessage32.prefixState state) := by
    intro pair index
    simp only [MachineState.getWord32, prefix_memory]
  obtain ⟨final, copied, invariant, contents, fields⟩ :=
    loop_run_with_full_data 4 state
      (SphincsVerifierMessage32.prefixState state)
      (prefix_invariant state pc) (by simpa using prefixData)
      prefixFields
  refine ⟨final, ?_, invariant, contents, fields⟩
  simpa using prefixTrace.append copied

/-- The exact verifier image reaches the next HASH setup with the submitted
    message and both 20-byte witness fields intact. -/
theorem loaded_message_payload_exact (publicKey : SigGolf.PublicKey)
    (message : Message) (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState submission .verify (message, publicKey, witness) =
      some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64) :
    ∃ final, OrdinarySteps SphincsImages.verify
      (writeHash (firstHashState state) answer) 65 final ∧
      LoopInvariant 0 final ∧
      (∀ index : Fin 4,
        final.getMem (BitVec.ofNat 64 (0x40050 + 8 * index.val)) =
          message.extractLsb' (64 * index.val) 64) ∧
      (∀ pair : CopyPair, ∀ index : Fin 5,
        final.getWord32 (destinationWord pair index) =
          witness.extractLsb'
            (8 * (witnessOffset pair + 4 * index.val)) 32) := by
  have copies := loaded_messageCopies_block publicKey message witness state
    answer loaded answerMatches
  have copiesPc := loaded_messageCopies_pc publicKey message witness state
    answer loaded answerMatches
  obtain ⟨final, messageCopy, invariant, contents, fields⟩ :=
    message32_block_full_data (afterMessageCopiesState state answer) copiesPc
  refine ⟨final, ?_, invariant, ?_, ?_⟩
  · simpa using copies.append messageCopy
  · intro index
    calc
      final.getMem (BitVec.ofNat 64 (0x40050 + 8 * index.val)) =
          (afterMessageCopiesState state answer).getMem
            (BitVec.ofNat 64 (8 * index.val)) :=
        copyData_final_word _ _ contents index
      _ = state.getMem (BitVec.ofNat 64 (8 * index.val)) := by
        exact afterMessageCopies_message_frame state answer index
      _ = message.extractLsb' (64 * index.val) 64 :=
        SphincsVerifierLoader.loaded_message_word publicKey message witness
          state loaded index
  · intro pair index
    calc
      final.getWord32 (destinationWord pair index) =
          (afterMessageCopiesState state answer).getWord32
            (destinationWord pair index) := fields pair index
      _ = witness.extractLsb'
            (8 * (witnessOffset pair + 4 * index.val)) 32 :=
        loaded_message_fields_exact publicKey message witness state answer
          loaded pair index

/-- info: 'SigGolfCandidate.SphincsVerifierWitnessAtHash.loaded_message_payload_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_message_payload_exact

end SigGolfCandidate.SphincsVerifierWitnessAtHash
