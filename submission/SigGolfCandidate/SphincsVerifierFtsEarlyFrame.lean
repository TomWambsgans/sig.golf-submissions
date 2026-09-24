import SigGolfCandidate.SphincsVerifierFtsWitnessFrame
import SigGolfCandidate.SphincsWireEncoding
import SigGolfCandidate.SphincsVerifierSecondHashPayload

/-! The first FORS opening remains in the loaded witness through the message HASH. -/

namespace SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopyParameter
open SigGolfCandidate.SphincsVerifierHashSetup
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierMessageFrame
open SigGolfCandidate.SphincsVerifierCommitmentCheck
open SigGolfCandidate.SphincsVerifierMessage32
open SigGolfCandidate.SphincsVerifierSecondHashFrame
open SigGolfCandidate.SphincsVerifierSecondHashSetup
open SigGolfCandidate.Sphincs.Expansion

def witnessPrefixCell (slot : Fin 10) : Word :=
  BitVec.ofNat 64 (0x22ca0 + 8 * slot.val)

theorem setupAndBoth_witnessPrefix_frame (state : MachineState)
    (slot : Fin 10) :
    (setupAndBothState state).getMem (witnessPrefixCell slot) =
      state.getMem (witnessPrefixCell slot) := by
  let read := witnessPrefixCell slot
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
    fin_cases slot <;> fin_cases offset <;> decide
  have secondOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (secondPointers.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    rw [secondDestination]
    fin_cases slot <;> fin_cases offset <;> decide
  change (copyRootState secondPointers).getMem read = state.getMem read
  rw [copyRoot_mem_frame secondPointers read secondOutside,
    SphincsVerifierCopyParameter.parameterPointers_memory,
    copyRoot_mem_frame firstPointers read firstOutside,
    addressSetup_memory]
  change (SphincsVerifierSlots.headerState jumped).getMem read =
    state.getMem read
  simp only [SphincsVerifierSlots.headerState]
  have slotOutside (other : Fin 4) :
      read ≠ BitVec.ofNat 64 (0x43000 + 8 * other.val) := by
    fin_cases slot <;> fin_cases other <;> decide
  rw [SphincsVerifierSlots.slot_memory 3,
    if_neg (slotOutside 3), SphincsVerifierSlots.slot_memory 2,
    if_neg (slotOutside 2), SphincsVerifierSlots.slot_memory 1,
    if_neg (slotOutside 1), SphincsVerifierSlots.slot_memory 0,
    if_neg (slotOutside 0)]
  simp [jumped, execInstrBr]

theorem firstHash_witnessPrefix_frame (state : MachineState)
    (slot : Fin 10) :
    (firstHashState state).getMem (witnessPrefixCell slot) =
      state.getMem (witnessPrefixCell slot) := by
  let read := witnessPrefixCell slot
  change (SphincsVerifierHashSetup.hashRegistersState
    (SphincsVerifierHeader.headerState (setupAndBothState state))).getMem
      read = state.getMem read
  rw [SphincsVerifierHashSetup.hashRegisters_memory]
  have outside0 : read ≠ 0x40000 := by fin_cases slot <;> decide
  have outside8 : read ≠ 0x40008 := by fin_cases slot <;> decide
  have outside16 : read ≠ 0x40010 := by fin_cases slot <;> decide
  rw [SphincsVerifierHashMemory.header_mem_frame _ _
    outside0 outside8 outside16, setupAndBoth_witnessPrefix_frame]

theorem writeHash_witnessPrefix_frame (state : MachineState)
    (answer : BitVec 256) (slot : Fin 10)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getMem (witnessPrefixCell slot) =
      state.getMem (witnessPrefixCell slot) := by
  fin_cases slot <;>
    simp [witnessPrefixCell, writeHash, MachineState.writeWords_cons,
      destination, MachineState.getMem_setMem_ne]

theorem bothCopies_witnessPrefix_frame (state : MachineState)
    (slot : Fin 10) :
    (bothCopiesState state).getMem (witnessPrefixCell slot) =
      state.getMem (witnessPrefixCell slot) := by
  let read := witnessPrefixCell slot
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

theorem afterMessageCopies_witnessPrefix_frame (state : MachineState)
    (answer : BitVec 256) (slot : Fin 10) :
    (afterMessageCopiesState state answer).getMem (witnessPrefixCell slot) =
      state.getMem (witnessPrefixCell slot) := by
  have destination := (firstHash_registers state).2.2.1
  change (bothCopiesState
    (compareSuccessState (writeHash (firstHashState state) answer))).getMem
      (witnessPrefixCell slot) = state.getMem (witnessPrefixCell slot)
  rw [bothCopies_witnessPrefix_frame, compareSuccess_memory,
    writeHash_witnessPrefix_frame _ _ slot destination,
    firstHash_witnessPrefix_frame]

theorem loopNext_witnessPrefix_frame (remaining : Nat) (state : MachineState)
    (slot : Fin 10) (inv : LoopInvariant (remaining + 1) state) :
    (loopNext state).getMem (witnessPrefixCell slot) =
      state.getMem (witnessPrefixCell slot) := by
  obtain ⟨bound, _, _, destination, _⟩ := inv
  rw [loop_next_mem, destination]
  have outside : witnessPrefixCell slot ≠
      BitVec.ofNat 64 (0x40050 + 8 * (4 - (remaining + 1))) := by
    have small : remaining ≤ 3 := by omega
    interval_cases remaining <;> fin_cases slot <;> decide
  rw [if_neg outside]

theorem loop_run_witnessPrefix_frame (remaining : Nat) (state : MachineState)
    (slot : Fin 10) (inv : LoopInvariant remaining state) :
    ∃ final, OrdinarySteps SphincsImages.verify state (6 * remaining) final ∧
      LoopInvariant 0 final ∧
      final.getMem (witnessPrefixCell slot) =
        state.getMem (witnessPrefixCell slot) := by
  induction remaining generalizing state with
  | zero =>
      exact ⟨state, by simpa using OrdinarySteps.refl state, inv, rfl⟩
  | succ remaining ih =>
      have pc : state.pc = 0x11e0 := by
        simpa [LoopInvariant] using inv.2.1
      have access := SphincsVerifierMessage32.loop_accesses remaining state inv
      have first := SphincsVerifierMessage32.loop_block state pc access.1 access.2
      have next := SphincsVerifierMessage32.loop_invariant remaining state inv
      obtain ⟨final, rest, finalInv, frame⟩ :=
        ih (loopNext state) next
      refine ⟨final, ?_, finalInv, ?_⟩
      · simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using first.append rest
      · exact frame.trans (loopNext_witnessPrefix_frame remaining state slot inv)

theorem message32_witnessPrefix_frame (state : MachineState)
    (slot : Fin 10) (pc : state.pc = 0x11d0) :
    ∃ final, OrdinarySteps SphincsImages.verify state 28 final ∧
      LoopInvariant 0 final ∧
      final.getMem (witnessPrefixCell slot) =
        state.getMem (witnessPrefixCell slot) := by
  have first := SphincsVerifierMessage32.prefix_block state pc
  obtain ⟨final, rest, inv, frame⟩ :=
    loop_run_witnessPrefix_frame 4
      (SphincsVerifierMessage32.prefixState state) slot
      (SphincsVerifierMessage32.prefix_invariant state pc)
  refine ⟨final, ?_, inv, ?_⟩
  · simpa using first.append rest
  · rw [frame]
    exact SphincsVerifierMessage32Data.prefix_memory state _

theorem secondHashReady_witnessPrefix_frame (state : MachineState)
    (slot : Fin 10) :
    (secondHashReadyState state).getMem (witnessPrefixCell slot) =
      state.getMem (witnessPrefixCell slot) := by
  apply secondHashReady_mem_frame
  · fin_cases slot <;> decide
  · fin_cases slot <;> decide
  · fin_cases slot <;> decide
  · intro offset
    fin_cases slot <;> fin_cases offset <;> decide

private theorem ordinary_deterministic {image : Image}
    {initial left right : MachineState} {n : Nat}
    (first : OrdinarySteps image initial n left)
    (second : OrdinarySteps image initial n right) : left = right := by
  induction first generalizing right with
  | refl state => cases second; rfl
  | step state next final instruction steps hf hs tail ih =>
      cases second with
      | step _ other _ otherInstruction _ hf' hs' tail' =>
          have instrEq := Option.some.inj (hf.symm.trans hf')
          subst otherInstruction
          have nextEq := Option.some.inj (hs.symm.trans hs')
          subst other
          exact ih tail'

theorem loaded_secondHash_witnessPrefix_frame
    (publicKey : SigGolf.PublicKey) (message : Message)
    (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, witness) = some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64)
    (ready : MachineState)
    (trace : OrdinarySteps SphincsImages.verify
      (writeHash (firstHashState state) answer) 107 ready)
    (slot : Fin 10) :
    ready.getMem (witnessPrefixCell slot) =
      state.getMem (witnessPrefixCell slot) := by
  have copies := loaded_messageCopies_block publicKey message witness state
    answer loaded answerMatches
  have copiesPc := loaded_messageCopies_pc publicKey message witness state
    answer loaded answerMatches
  obtain ⟨copied, messageTrace, invariant, frame⟩ :=
    message32_witnessPrefix_frame (afterMessageCopiesState state answer)
      slot copiesPc
  have copiedPc : copied.pc = 0x11f8 := by
    simpa [LoopInvariant] using invariant.2.1
  have next := secondHashReady_block copied copiedPc
  have alternate : OrdinarySteps SphincsImages.verify
      (writeHash (firstHashState state) answer) 107
      (secondHashReadyState copied) := by
    simpa using (copies.append messageTrace).append next
  have same := ordinary_deterministic trace alternate
  rw [same, secondHashReady_witnessPrefix_frame, frame,
    afterMessageCopies_witnessPrefix_frame]

theorem loaded_secondHash_witnessPrefix_byte_frame
    (publicKey : SigGolf.PublicKey) (message : Message)
    (witness : Bytes SphincsWire.signatureBytes)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, witness) = some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64)
    (ready : MachineState)
    (trace : OrdinarySteps SphincsImages.verify
      (writeHash (firstHashState state) answer) 107 ready)
    (i : Nat) (hi : i < 80) :
    ready.getByte (BitVec.ofNat 64 (0x22ca0 + i)) =
      state.getByte (BitVec.ofNat 64 (0x22ca0 + i)) := by
  let slot : Fin 10 := ⟨i / 8, by omega⟩
  have align : alignToDword (BitVec.ofNat 64 (0x22ca0 + i)) =
      witnessPrefixCell slot := by
    have bound : i ≤ 79 := by omega
    dsimp [slot, witnessPrefixCell]
    interval_cases i <;> decide
  simp only [MachineState.getByte, align]
  rw [loaded_secondHash_witnessPrefix_frame publicKey message witness state
    answer loaded answerMatches ready trace slot]

theorem loaded_honest_message_ready_with_witness
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (inner : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire inner signature) =
        some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64) :
    ∃ ready, OrdinarySteps SphincsImages.verify
      (writeHash (firstHashState state) answer) 107 ready ∧
      ready.pc = 0x12a0 ∧
      SphincsVerifierMessageHash.MessageReady ready inner message
        signature.randomness ∧
      SphincsVerifierHashBytes.WitnessPrefix ready inner ∧
      (∀ i, (hi : i < 20) →
        ready.getByte (BitVec.ofNat 64 (0x22cdc + i)) =
          (signature.ftsSecret ⟨0, by decide⟩).extractLsb' (8 * i) 8) := by
  obtain ⟨ready, trace, pc, messageReady⟩ :=
    SphincsWireEncoding.loaded_honest_message_ready publicKey message inner
      signature state answer loaded answerMatches
  have prefixState : SphincsVerifierHashBytes.WitnessPrefix state inner :=
    SphincsVerifierLoader.loaded_prefix publicKey message
      (SphincsWireEncoding.wire inner signature) inner state loaded
      (SphincsWireEncoding.wire_encodedWitness inner signature)
  have prefixReady : SphincsVerifierHashBytes.WitnessPrefix ready inner := by
    constructor
    · intro i hi
      exact (loaded_secondHash_witnessPrefix_byte_frame publicKey message
        (SphincsWireEncoding.wire inner signature) state answer loaded
        answerMatches ready trace i (by omega)).trans
        (prefixState.root i hi)
    · intro i hi
      have frame := loaded_secondHash_witnessPrefix_byte_frame publicKey
        message (SphincsWireEncoding.wire inner signature) state answer
        loaded answerMatches ready trace (20 + i) (by omega)
      have address : 0x22ca0 + (20 + i) = 0x22cb4 + i := by omega
      rw [address] at frame
      exact frame.trans (prefixState.parameter i hi)
  refine ⟨ready, trace, pc, messageReady, prefixReady, ?_⟩
  intro i hi
  have frame := loaded_secondHash_witnessPrefix_byte_frame publicKey
    message (SphincsWireEncoding.wire inner signature) state answer loaded
    answerMatches ready trace (60 + i) (by omega)
  have address : 0x22ca0 + (60 + i) = 0x22cdc + i := by omega
  rw [address] at frame
  have secret :=
    SphincsWireEncoding.loaded_honest_firstFtsSecret publicKey message
      inner signature state loaded i hi
  rw [address] at secret
  exact frame.trans secret

/-- The first FORS HASH query of an honest wire signature is the abstract query. -/
theorem loaded_honest_firstFts_query
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (inner : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (state : MachineState) (commitmentAnswer digestAnswer : BitVec 256)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire inner signature) =
        some state)
    (answerMatches : ∀ index : Fin 2,
      commitmentAnswer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest digestAnswer)) :
    ∃ ready final,
      OrdinarySteps SphincsImages.verify
        (writeHash (firstHashState state) commitmentAnswer) 107 ready ∧
      OrdinarySteps SphincsImages.verify
        (writeHash ready digestAnswer) 392 final ∧
      final.pc = 0x18c8 ∧
      hashInput final = SphincsBridge.toQuery
        (SphincsVerifierFtsQuery.firstFtsInput inner
          (SphincsSecurity.Concrete.digestIndex
            (SphincsSecurity.truncateMessageDigest digestAnswer))
          (SphincsSecurity.Concrete.digestLeaves
            (SphincsSecurity.truncateMessageDigest digestAnswer)
            ⟨0, by decide⟩)
          (signature.ftsSecret ⟨0, by decide⟩)) := by
  obtain ⟨ready, trace, pc, messageReady, prefixWitness, secret⟩ :=
    loaded_honest_message_ready_with_witness publicKey message inner
      signature state commitmentAnswer loaded answerMatches
  have query :=
    SphincsVerifierFtsWitnessFrame.messageReady_firstFts_query_from_state
      ready inner message signature.randomness messageReady pc digestAnswer
      admissible prefixWitness (signature.ftsSecret ⟨0, by decide⟩) secret
  let pointers := SphincsVerifierFtsQuery.firstFtsPointers ready digestAnswer
  let advanced := SphincsVerifierFtsAdvance.ftsAdvanceState
    (SphincsVerifierCopy.copyRootState pointers)
  let final := SphincsVerifierFtsSetup.ftsHashReadyState advanced
  exact ⟨ready, final, trace, query.1, query.2.1, query.2.2⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsEarlyFrame.loaded_secondHash_witnessPrefix_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_secondHash_witnessPrefix_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsEarlyFrame.loaded_honest_firstFts_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_firstFts_query

end SigGolfCandidate.SphincsVerifierFtsEarlyFrame
