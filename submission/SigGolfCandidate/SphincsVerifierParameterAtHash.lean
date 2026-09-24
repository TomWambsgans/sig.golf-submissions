import SigGolfCandidate.SphincsVerifierParameterSourceFrame

/-!
# Witness parameter preserved through the message-copy loop

The verifier's four message-copy iterations write only the hash buffer. Their
final state retains all three memory doublewords containing the public
parameter supplied in the witness.
-/

namespace SigGolfCandidate.SphincsVerifierParameterAtHash
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Sphincs.Expansion
open SigGolfCandidate.SphincsSubmission
open SigGolfCandidate.SphincsVerifierMessage32
open SigGolfCandidate.SphincsVerifierMessage32Data
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierWitnessAtHash
open SigGolfCandidate.SphincsVerifierWitnessFrame
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierParameterSourceFrame

def ParameterCells (original state : MachineState) : Prop :=
  ∀ index : Fin 3,
    state.getMem (parameterCell index) =
      original.getMem (parameterCell index)

def ScratchCells (original state : MachineState) : Prop :=
  ∀ slot : Fin 4,
    state.getMem (scratchCell slot) =
      original.getMem (scratchCell slot)

theorem loopNext_parameterCell_frame (remaining : Nat)
    (state : MachineState) (inv : LoopInvariant (remaining + 1) state)
    (index : Fin 3) :
    (loopNext state).getMem (parameterCell index) =
      state.getMem (parameterCell index) := by
  obtain ⟨bound, _, _, destination, _⟩ := inv
  rw [loop_next_mem, destination]
  have other : parameterCell index ≠
      BitVec.ofNat 64 (0x40050 + 8 * (4 - (remaining + 1))) := by
    have small : remaining ≤ 3 := by omega
    interval_cases remaining <;> fin_cases index <;>
      decide
  rw [if_neg other]

theorem parameterCells_step (original state : MachineState)
    (remaining : Nat) (inv : LoopInvariant (remaining + 1) state)
    (cells : ParameterCells original state) :
    ParameterCells original (loopNext state) := by
  intro index
  rw [loopNext_parameterCell_frame remaining state inv index]
  exact cells index

theorem loopNext_scratchCell_frame (remaining : Nat)
    (state : MachineState) (inv : LoopInvariant (remaining + 1) state)
    (slot : Fin 4) :
    (loopNext state).getMem (scratchCell slot) =
      state.getMem (scratchCell slot) := by
  obtain ⟨bound, _, _, destination, _⟩ := inv
  rw [loop_next_mem, destination]
  have other : scratchCell slot ≠
      BitVec.ofNat 64 (0x40050 + 8 * (4 - (remaining + 1))) := by
    have small : remaining ≤ 3 := by omega
    interval_cases remaining <;> fin_cases slot <;>
      decide
  rw [if_neg other]

theorem scratchCells_step (original state : MachineState)
    (remaining : Nat) (inv : LoopInvariant (remaining + 1) state)
    (cells : ScratchCells original state) :
    ScratchCells original (loopNext state) := by
  intro slot
  rw [loopNext_scratchCell_frame remaining state inv slot]
  exact cells slot

theorem loop_run_full (remaining : Nat)
    (original state : MachineState)
    (inv : LoopInvariant remaining state)
    (data : CopyData original (4 - remaining) state)
    (fields : FieldData original state)
    (cells : ParameterCells original state)
    (scratch : ScratchCells original state) :
    ∃ final, OrdinarySteps SphincsImages.verify state (6 * remaining) final ∧
      LoopInvariant 0 final ∧ CopyData original 4 final ∧
      FieldData original final ∧ ParameterCells original final ∧
      ScratchCells original final := by
  induction remaining generalizing state with
  | zero =>
    exact ⟨state, by simpa using OrdinarySteps.refl state, inv,
      by simpa using data, fields, cells, scratch⟩
  | succ remaining ih =>
    have pc : state.pc = 0x11e0 := by simpa [LoopInvariant] using inv.2.1
    have access := loop_accesses remaining state inv
    have first := loop_block state pc access.1 access.2
    have next := loop_invariant remaining state inv
    have nextData := copyData_step original state remaining inv data
    have nextFields := fieldData_step original state remaining inv fields
    have nextCells := parameterCells_step original state remaining inv cells
    have nextScratch := scratchCells_step original state remaining inv scratch
    obtain ⟨final, rest, finalInv, finalData, finalFields, finalCells,
      finalScratch⟩ :=
      ih (loopNext state) next nextData nextFields nextCells nextScratch
    refine ⟨final, ?_, finalInv, finalData, finalFields, finalCells,
      finalScratch⟩
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using first.append rest

theorem message32_block_full (state : MachineState)
    (pc : state.pc = 0x11d0) :
    ∃ final, OrdinarySteps SphincsImages.verify state 28 final ∧
      LoopInvariant 0 final ∧ CopyData state 4 final ∧
      FieldData state final ∧ ParameterCells state final ∧
      ScratchCells state final := by
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
  have prefixCells : ParameterCells state
      (SphincsVerifierMessage32.prefixState state) := by
    intro index
    exact prefix_memory state _
  have prefixScratch : ScratchCells state
      (SphincsVerifierMessage32.prefixState state) := by
    intro slot
    exact prefix_memory state _
  obtain ⟨final, copied, invariant, contents, fields, cells, scratch⟩ :=
    loop_run_full 4 state
      (SphincsVerifierMessage32.prefixState state)
      (prefix_invariant state pc) (by simpa using prefixData)
      prefixFields prefixCells prefixScratch
  refine ⟨final, ?_, invariant, contents, fields, cells, scratch⟩
  simpa using prefixTrace.append copied

theorem loaded_message_payload_parameter_exact
    (publicKey : SigGolf.PublicKey) (message : Message)
    (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState submission .verify (message, publicKey, witness) =
      some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64) :
    ∃ final, OrdinarySteps SphincsImages.verify
      (writeHash (SphincsVerifierHashSetup.firstHashState state) answer)
      65 final ∧
      LoopInvariant 0 final ∧
      (∀ index : Fin 4,
        final.getMem (BitVec.ofNat 64 (0x40050 + 8 * index.val)) =
          message.extractLsb' (64 * index.val) 64) ∧
      (∀ pair : CopyPair, ∀ index : Fin 5,
        final.getWord32 (destinationWord pair index) =
          witness.extractLsb'
            (8 * (witnessOffset pair + 4 * index.val)) 32) ∧
      (∀ index : Fin 3,
        final.getMem (parameterCell index) =
          state.getMem (parameterCell index)) ∧
      (∀ slot : Fin 4, final.getMem (scratchCell slot) = 0) := by
  have copies := loaded_messageCopies_block publicKey message witness state
    answer loaded answerMatches
  have copiesPc := loaded_messageCopies_pc publicKey message witness state
    answer loaded answerMatches
  obtain ⟨final, messageCopy, invariant, contents, fields, cells, scratch⟩ :=
    message32_block_full (afterMessageCopiesState state answer) copiesPc
  refine ⟨final, ?_, invariant, ?_, ?_, ?_, ?_⟩
  · simpa using copies.append messageCopy
  · intro index
    calc
      final.getMem (BitVec.ofNat 64 (0x40050 + 8 * index.val)) =
          (afterMessageCopiesState state answer).getMem
            (BitVec.ofNat 64 (8 * index.val)) :=
        copyData_final_word _ _ contents index
      _ = state.getMem (BitVec.ofNat 64 (8 * index.val)) := by
        exact SphincsVerifierMessageFrame.afterMessageCopies_message_frame
          state answer index
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
        SphincsVerifierWitnessFrame.loaded_message_fields_exact
          publicKey message witness state answer loaded pair index
  · intro index
    calc
      final.getMem (parameterCell index) =
          (afterMessageCopiesState state answer).getMem
            (parameterCell index) := cells index
      _ = state.getMem (parameterCell index) :=
        afterMessageCopies_parameterCell_frame state answer index
  · intro slot
    calc
      final.getMem (scratchCell slot) =
          (afterMessageCopiesState state answer).getMem
            (scratchCell slot) := scratch slot
      _ = 0 := afterMessageCopies_scratch_zero state answer slot

/-- info: 'SigGolfCandidate.SphincsVerifierParameterAtHash.loaded_message_payload_parameter_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_message_payload_parameter_exact

end SigGolfCandidate.SphincsVerifierParameterAtHash
