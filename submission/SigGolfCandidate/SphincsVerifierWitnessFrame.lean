import SigGolfCandidate.SphincsVerifierMessageFields

/-!
# Loaded witness frame

The verifier's commitment setup, first HASH, comparison, and subsequent copy
blocks do not modify the witness words used by the message-index hash.
-/

namespace SigGolfCandidate.SphincsVerifierWitnessFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopyParameter
open SigGolfCandidate.SphincsVerifierHashSetup
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCommitmentCheck
open SigGolfCandidate.SphincsVerifierMessageFrame
open SigGolfCandidate.SphincsVerifierMessageFields

private theorem extractByte_of_extractWord32 (word : Word)
    (lane : Fin 2) (byte : Fin 4) :
    extractByte word (4 * lane.val + byte.val) =
      (extractWord32 word lane.val).extractLsb' (8 * byte.val) 8 := by
  ext i (hi : i < 8)
  simp [extractByte, extractWord32, BitVec.truncate_eq_setWidth]
  have within : 8 * byte.val + i < 32 := by
    have := byte.isLt
    omega
  simp only [within]
  simp only [decide_true, Bool.true_and]
  congr 1
  omega

private theorem extractByte_from_word32 (word : Word)
    (position : Fin 8) :
    extractByte word position.val =
      (extractWord32 word (position.val / 4)).extractLsb'
        (8 * (position.val % 4)) 8 := by
  fin_cases position <;>
    first
    | exact extractByte_of_extractWord32 word 0 0
    | exact extractByte_of_extractWord32 word 0 1
    | exact extractByte_of_extractWord32 word 0 2
    | exact extractByte_of_extractWord32 word 0 3
    | exact extractByte_of_extractWord32 word 1 0
    | exact extractByte_of_extractWord32 word 1 1
    | exact extractByte_of_extractWord32 word 1 2
    | exact extractByte_of_extractWord32 word 1 3

private theorem sourceByte (state : MachineState) (pair : CopyPair)
    (index : Fin 5) (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64
      (sourceBase pair + 4 * index.val + byte.val)) =
      (state.getWord32 (sourceWord pair index)).extractLsb'
        (8 * byte.val) 8 := by
  have split := extractByte_from_word32
    (state.getMem (alignToDword (BitVec.ofNat 64
      (sourceBase pair + 4 * index.val + byte.val))))
    ⟨(sourceBase pair + 4 * index.val + byte.val) % 8,
      Nat.mod_lt _ (by decide)⟩
  cases pair <;> fin_cases index <;> fin_cases byte <;>
    simpa [MachineState.getByte, MachineState.getWord32,
      sourceWord, sourceBase, alignToDword, byteOffset] using split

private theorem eq_of_four_bytes {left right : BitVec 32}
    (h : ∀ byte, byte < 4 →
      left.extractLsb' (8 * byte) 8 =
        right.extractLsb' (8 * byte) 8) : left = right := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bitBound
  have bitPart : bit % 8 < 8 := Nat.mod_lt _ (by decide)
  have split : bit / 8 * 8 + bit % 8 = bit := by omega
  have split' : 8 * (bit / 8) + bit % 8 = bit := by omega
  have byteEqual := congrArg (fun b => b.getLsbD (bit % 8))
    (h (bit / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', split', bitPart,
    decide_true, Bool.true_and] at byteEqual
  exact byteEqual

def witnessOffset : CopyPair → Nat
  | .randomizer => 40
  | .root => 0

private theorem sourceBase_eq (pair : CopyPair) :
    sourceBase pair = 0x22ca0 + witnessOffset pair := by
  cases pair <;> rfl

private theorem slice_byte {n : Nat} (value : BitVec n) (base byte : Nat)
    (small : byte < 4) :
    (value.extractLsb' (8 * base) 32).extractLsb' (8 * byte) 8 =
      value.extractLsb' (8 * (base + byte)) 8 := by
  ext bit bitBound
  simp [Nat.mul_add, Nat.add_assoc] <;> omega

theorem loaded_witness_field_word (publicKey : SigGolf.PublicKey)
    (message : Message) (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, witness) = some state)
    (pair : CopyPair) (index : Fin 5) :
    state.getWord32 (sourceWord pair index) =
      witness.extractLsb'
        (8 * (witnessOffset pair + 4 * index.val)) 32 := by
  apply eq_of_four_bytes
  intro byte byteBound
  let b : Fin 4 := ⟨byte, byteBound⟩
  have offsetBound : witnessOffset pair + 4 * index.val + byte <
      SphincsWire.signatureBytes := by
    rw [SphincsWire.signatureBytes_eq]
    cases pair <;> simp [witnessOffset] <;>
      have := index.isLt <;> omega
  have address : sourceBase pair + 4 * index.val + byte =
      0x22ca0 + (witnessOffset pair + 4 * index.val + byte) := by
    rw [sourceBase_eq]
    omega
  calc
    (state.getWord32 (sourceWord pair index)).extractLsb'
        (8 * byte) 8 =
        state.getByte (BitVec.ofNat 64
          (sourceBase pair + 4 * index.val + byte)) := by
      simpa [b] using (sourceByte state pair index b).symm
    _ = state.getByte (BitVec.ofNat 64
          (0x22ca0 + (witnessOffset pair + 4 * index.val + byte))) := by
      rw [address]
    _ = witness.extractLsb'
          (8 * (witnessOffset pair + 4 * index.val + byte)) 8 :=
      SphincsVerifierLoader.loaded_witness publicKey message witness state
        loaded _ offsetBound
    _ = (witness.extractLsb'
          (8 * (witnessOffset pair + 4 * index.val)) 32).extractLsb'
          (8 * byte) 8 := by
      simpa [Nat.add_assoc] using
        (slice_byte witness (witnessOffset pair + 4 * index.val)
          byte byteBound).symm

def sourceCell (pair : CopyPair) (index : Fin 5) : Word :=
  alignToDword (sourceWord pair index)

theorem setupAndBoth_sourceCell_frame (state : MachineState)
    (pair : CopyPair) (index : Fin 5) :
    (setupAndBothState state).getMem (sourceCell pair index) =
      state.getMem (sourceCell pair index) := by
  let read := sourceCell pair index
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
    cases pair <;> fin_cases index <;> fin_cases offset <;>
      decide
  have secondOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (secondPointers.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [secondDestination]
    cases pair <;> fin_cases index <;> fin_cases offset <;>
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
    cases pair <;> fin_cases index <;> fin_cases slot <;>
      decide
  rw [SphincsVerifierSlots.slot_memory 3,
    if_neg (slotOutside 3), SphincsVerifierSlots.slot_memory 2,
    if_neg (slotOutside 2), SphincsVerifierSlots.slot_memory 1,
    if_neg (slotOutside 1), SphincsVerifierSlots.slot_memory 0,
    if_neg (slotOutside 0)]
  simp [jumped, execInstrBr]

theorem firstHash_sourceCell_frame (state : MachineState)
    (pair : CopyPair) (index : Fin 5) :
    (firstHashState state).getMem (sourceCell pair index) =
      state.getMem (sourceCell pair index) := by
  let read := sourceCell pair index
  change (SphincsVerifierHashSetup.hashRegistersState
    (SphincsVerifierHeader.headerState (setupAndBothState state))).getMem
      read = state.getMem read
  rw [SphincsVerifierHashSetup.hashRegisters_memory]
  have outside0 : read ≠ 0x40000 := by
    cases pair <;> fin_cases index <;> decide
  have outside8 : read ≠ 0x40008 := by
    cases pair <;> fin_cases index <;> decide
  have outside16 : read ≠ 0x40010 := by
    cases pair <;> fin_cases index <;> decide
  rw [header_mem_frame _ _ outside0 outside8 outside16,
    setupAndBoth_sourceCell_frame]

theorem writeHash_sourceCell_frame (state : MachineState)
    (answer : BitVec 256) (pair : CopyPair) (index : Fin 5)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getMem (sourceCell pair index) =
      state.getMem (sourceCell pair index) := by
  cases pair <;> fin_cases index <;>
    simp [sourceCell, sourceWord, sourceBase, alignToDword, writeHash,
      MachineState.writeWords_cons, destination,
      MachineState.getMem_setMem_ne]

theorem bothCopies_sourceCell_frame (state : MachineState)
    (pair : CopyPair) (index : Fin 5) :
    (bothCopiesState state).getMem (sourceCell pair index) =
      state.getMem (sourceCell pair index) := by
  let read := sourceCell pair index
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
    cases pair <;> fin_cases index <;> fin_cases offset <;>
      decide
  have secondOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (second.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [secondDestination]
    cases pair <;> fin_cases index <;> fin_cases offset <;>
      decide
  change (copyRootState second).getMem read = state.getMem read
  rw [copyRoot_mem_frame second read secondOutside,
    secondPointers_memory]
  change (copyRootState first).getMem read = state.getMem read
  rw [copyRoot_mem_frame first read firstOutside,
    firstPointers_memory]

theorem afterMessageCopies_sourceCell_frame (state : MachineState)
    (answer : BitVec 256) (pair : CopyPair) (index : Fin 5) :
    (afterMessageCopiesState state answer).getMem
      (sourceCell pair index) =
      state.getMem (sourceCell pair index) := by
  have destination := (firstHash_registers state).2.2.1
  change (bothCopiesState
    (compareSuccessState (writeHash (firstHashState state) answer))).getMem
      (sourceCell pair index) = state.getMem (sourceCell pair index)
  rw [bothCopies_sourceCell_frame, compareSuccess_memory,
    writeHash_sourceCell_frame _ _ pair index destination,
    firstHash_sourceCell_frame]

theorem afterMessageCopies_sourceWord_frame (state : MachineState)
    (answer : BitVec 256) (pair : CopyPair) (index : Fin 5) :
    (afterMessageCopiesState state answer).getWord32
      (sourceWord pair index) =
      state.getWord32 (sourceWord pair index) := by
  simp only [MachineState.getWord32]
  exact congrArg
    (fun word : Word => extractWord32 word
      (byteOffset (sourceWord pair index) / 4))
    (afterMessageCopies_sourceCell_frame state answer pair index)

theorem beforeMessageCopies_sourceCell_frame (state : MachineState)
    (answer : BitVec 256) (pair : CopyPair) (index : Fin 5) :
    (compareSuccessState (writeHash (firstHashState state) answer)).getMem
      (sourceCell pair index) =
      state.getMem (sourceCell pair index) := by
  have destination := (firstHash_registers state).2.2.1
  rw [compareSuccess_memory,
    writeHash_sourceCell_frame _ _ pair index destination,
    firstHash_sourceCell_frame]

theorem beforeMessageCopies_sourceWord_frame (state : MachineState)
    (answer : BitVec 256) (pair : CopyPair) (index : Fin 5) :
    (compareSuccessState (writeHash (firstHashState state) answer)).getWord32
      (sourceWord pair index) =
      state.getWord32 (sourceWord pair index) := by
  simp only [MachineState.getWord32]
  exact congrArg
    (fun word : Word => extractWord32 word
      (byteOffset (sourceWord pair index) / 4))
    (beforeMessageCopies_sourceCell_frame state answer pair index)

theorem afterMessageCopies_field_word (state : MachineState)
    (answer : BitVec 256) (pair : CopyPair) (index : Fin 5) :
    (afterMessageCopiesState state answer).getWord32
      (destinationWord pair index) =
      state.getWord32 (sourceWord pair index) := by
  let before := compareSuccessState (writeHash (firstHashState state) answer)
  change (bothCopiesState before).getWord32
    (destinationWord pair index) =
      state.getWord32 (sourceWord pair index)
  rw [bothCopies_pair_word]
  exact beforeMessageCopies_sourceWord_frame state answer pair index

/-- The message-index buffer's two 20-byte witness fields match the submitted
    witness, word for word, after the verifier's copy blocks. -/
theorem loaded_message_fields_exact (publicKey : SigGolf.PublicKey)
    (message : Message) (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, witness) = some state)
    (pair : CopyPair) (index : Fin 5) :
    (afterMessageCopiesState state answer).getWord32
      (destinationWord pair index) =
      witness.extractLsb'
        (8 * (witnessOffset pair + 4 * index.val)) 32 := by
  rw [afterMessageCopies_field_word]
  exact loaded_witness_field_word publicKey message witness state loaded
    pair index

/-- info: 'SigGolfCandidate.SphincsVerifierWitnessFrame.loaded_message_fields_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_message_fields_exact

end SigGolfCandidate.SphincsVerifierWitnessFrame
