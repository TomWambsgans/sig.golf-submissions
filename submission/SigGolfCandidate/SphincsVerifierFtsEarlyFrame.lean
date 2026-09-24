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

/-- The witness bytes encode every opened FORS secret and authentication path. -/
structure FtsWitness (state : MachineState)
    (signature : SphincsSecurity.Signature) : Prop where
  secret : ∀ tree : SphincsSecurity.FtsTree, ∀ i, (hi : i < 20) →
    state.getByte (BitVec.ofNat 64
      (0x22ca0 + (60 + tree.val * SphincsWire.ftsOpeningBytes + i))) =
      (signature.ftsSecret tree).extractLsb' (8 * i) 8
  path : ∀ tree : SphincsSecurity.FtsTree,
    ∀ level : Fin SphincsSecurity.ftsTreeHeight,
    ∀ i, (hi : i < SphincsWire.digestBytes) →
    state.getByte (BitVec.ofNat 64
      (0x22ca0 + (60 + tree.val * SphincsWire.ftsOpeningBytes +
        (SphincsWire.digestBytes + level.val * SphincsWire.digestBytes + i)))) =
      (signature.ftsPath tree level).extractLsb' (8 * i) 8

private theorem low_ne_high (read address : Word)
    (low : read.toNat < 0x40000)
    (high : 0x40000 ≤ address.toNat) : read ≠ address := by
  intro equal
  have values := congrArg BitVec.toNat equal
  omega

/-- Commitment setup only writes to HASH and scratch memory. -/
theorem setupAndBoth_low_frame (state : MachineState) (read : Word)
    (low : read.toNat < 0x40000) :
    (setupAndBothState state).getMem read = state.getMem read := by
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
    apply low_ne_high read _ low
    rw [firstDestination]
    fin_cases offset <;> decide
  have secondOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (secondPointers.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    apply low_ne_high read _ low
    rw [secondDestination]
    fin_cases offset <;> decide
  change (copyRootState secondPointers).getMem read = state.getMem read
  rw [copyRoot_mem_frame secondPointers read secondOutside,
    SphincsVerifierCopyParameter.parameterPointers_memory,
    copyRoot_mem_frame firstPointers read firstOutside,
    addressSetup_memory]
  change (SphincsVerifierSlots.headerState jumped).getMem read =
    state.getMem read
  simp only [SphincsVerifierSlots.headerState]
  have slotOutside (slot : Fin 4) :
      read ≠ BitVec.ofNat 64 (0x43000 + 8 * slot.val) := by
    apply low_ne_high read _ low
    fin_cases slot <;> decide
  rw [SphincsVerifierSlots.slot_memory 3,
    if_neg (slotOutside 3), SphincsVerifierSlots.slot_memory 2,
    if_neg (slotOutside 2), SphincsVerifierSlots.slot_memory 1,
    if_neg (slotOutside 1), SphincsVerifierSlots.slot_memory 0,
    if_neg (slotOutside 0)]
  simp [jumped, execInstrBr]

theorem firstHash_low_frame (state : MachineState) (read : Word)
    (low : read.toNat < 0x40000) :
    (firstHashState state).getMem read = state.getMem read := by
  change (SphincsVerifierHashSetup.hashRegistersState
    (SphincsVerifierHeader.headerState (setupAndBothState state))).getMem
      read = state.getMem read
  rw [SphincsVerifierHashSetup.hashRegisters_memory]
  have outside0 : read ≠ 0x40000 :=
    low_ne_high read 0x40000 low (by decide)
  have outside8 : read ≠ 0x40008 :=
    low_ne_high read 0x40008 low (by decide)
  have outside16 : read ≠ 0x40010 :=
    low_ne_high read 0x40010 low (by decide)
  rw [SphincsVerifierHashMemory.header_mem_frame _ _
    outside0 outside8 outside16, setupAndBoth_low_frame _ _ low]

theorem writeHash_low_frame (state : MachineState)
    (answer : BitVec 256) (read : Word)
    (low : read.toNat < 0x40000)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getMem read = state.getMem read := by
  have ne0 : read ≠ 0x42000 := low_ne_high read _ low (by decide)
  have ne8 : read ≠ 0x42008 := low_ne_high read _ low (by decide)
  have ne16 : read ≠ 0x42010 := low_ne_high read _ low (by decide)
  have ne24 : read ≠ 0x42018 := low_ne_high read _ low (by decide)
  change read ≠ (270336#64) at ne0
  change read ≠ (270344#64) at ne8
  change read ≠ (270352#64) at ne16
  change read ≠ (270360#64) at ne24
  simp [writeHash, MachineState.writeWords_cons, destination,
    ne0, ne8, ne16, ne24]

theorem bothCopies_low_frame (state : MachineState) (read : Word)
    (low : read.toNat < 0x40000) :
    (bothCopiesState state).getMem read = state.getMem read := by
  let first := firstPointers state
  let copied := firstCopyState state
  let second := secondPointers copied
  have firstDestination := (firstPointers_regs state).2
  have secondDestination := (secondPointers_regs copied).2
  have firstOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (first.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    apply low_ne_high read _ low
    rw [firstDestination]
    fin_cases offset <;> decide
  have secondOutside : ∀ offset : Fin 5, read ≠ alignToDword
      (second.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) := by
    intro offset
    apply low_ne_high read _ low
    rw [secondDestination]
    fin_cases offset <;> decide
  change (copyRootState second).getMem read = state.getMem read
  rw [copyRoot_mem_frame second read secondOutside,
    secondPointers_memory]
  change (copyRootState first).getMem read = state.getMem read
  rw [copyRoot_mem_frame first read firstOutside,
    firstPointers_memory]

theorem afterMessageCopies_low_frame (state : MachineState)
    (answer : BitVec 256) (read : Word)
    (low : read.toNat < 0x40000) :
    (afterMessageCopiesState state answer).getMem read =
      state.getMem read := by
  have destination := (firstHash_registers state).2.2.1
  change (bothCopiesState
    (compareSuccessState (writeHash (firstHashState state) answer))).getMem
      read = state.getMem read
  rw [bothCopies_low_frame _ _ low, compareSuccess_memory,
    writeHash_low_frame _ _ _ low destination,
    firstHash_low_frame _ _ low]

theorem loopNext_low_frame (remaining : Nat) (state : MachineState)
    (read : Word) (low : read.toNat < 0x40000)
    (inv : LoopInvariant (remaining + 1) state) :
    (loopNext state).getMem read = state.getMem read := by
  obtain ⟨bound, _, _, destination, _⟩ := inv
  rw [loop_next_mem, destination]
  have outside : read ≠
      BitVec.ofNat 64 (0x40050 + 8 * (4 - (remaining + 1))) := by
    apply low_ne_high read _ low
    have small : remaining ≤ 3 := by omega
    interval_cases remaining <;> decide
  rw [if_neg outside]

theorem loop_run_low_frame (remaining : Nat) (state : MachineState)
    (read : Word) (low : read.toNat < 0x40000)
    (inv : LoopInvariant remaining state) :
    ∃ final, OrdinarySteps SphincsImages.verify state (6 * remaining) final ∧
      LoopInvariant 0 final ∧ final.getMem read = state.getMem read := by
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
      · exact frame.trans (loopNext_low_frame remaining state read low inv)

theorem message32_low_frame (state : MachineState) (read : Word)
    (low : read.toNat < 0x40000) (pc : state.pc = 0x11d0) :
    ∃ final, OrdinarySteps SphincsImages.verify state 28 final ∧
      LoopInvariant 0 final ∧ final.getMem read = state.getMem read := by
  have first := SphincsVerifierMessage32.prefix_block state pc
  obtain ⟨final, rest, inv, frame⟩ :=
    loop_run_low_frame 4 (SphincsVerifierMessage32.prefixState state)
      read low (SphincsVerifierMessage32.prefix_invariant state pc)
  refine ⟨final, ?_, inv, ?_⟩
  · simpa using first.append rest
  · rw [frame]
    exact SphincsVerifierMessage32Data.prefix_memory state read

theorem secondHashReady_low_frame (state : MachineState) (read : Word)
    (low : read.toNat < 0x40000) :
    (secondHashReadyState state).getMem read = state.getMem read := by
  apply secondHashReady_mem_frame
  · exact low_ne_high read 0x40000 low (by decide)
  · exact low_ne_high read 0x40008 low (by decide)
  · exact low_ne_high read 0x40010 low (by decide)
  · intro offset
    apply low_ne_high read _ low
    fin_cases offset <;> decide

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

theorem loaded_secondHash_low_frame
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
    (read : Word) (low : read.toNat < 0x40000) :
    ready.getMem read = state.getMem read := by
  have copies := loaded_messageCopies_block publicKey message witness state
    answer loaded answerMatches
  have copiesPc := loaded_messageCopies_pc publicKey message witness state
    answer loaded answerMatches
  obtain ⟨copied, messageTrace, invariant, frame⟩ :=
    message32_low_frame (afterMessageCopiesState state answer)
      read low copiesPc
  have copiedPc : copied.pc = 0x11f8 := by
    simpa [LoopInvariant] using invariant.2.1
  have next := secondHashReady_block copied copiedPc
  have alternate : OrdinarySteps SphincsImages.verify
      (writeHash (firstHashState state) answer) 107
      (secondHashReadyState copied) := by
    simpa using (copies.append messageTrace).append next
  have same := ordinary_deterministic trace alternate
  rw [same, secondHashReady_low_frame _ _ low, frame,
    afterMessageCopies_low_frame _ _ _ low]

theorem loaded_secondHash_witnessByte_frame
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
    (i : Nat) (hi : i < SphincsWire.signatureBytes) :
    ready.getByte (BitVec.ofNat 64 (0x22ca0 + i)) =
      state.getByte (BitVec.ofNat 64 (0x22ca0 + i)) := by
  let address : Word := BitVec.ofNat 64 (0x22ca0 + i)
  have small : 0x22ca0 + i < 2 ^ 64 := by
    have length := SphincsWire.signatureBytes_eq
    omega
  have range : 0x22ca0 + i < 0x40000 := by
    have length := SphincsWire.signatureBytes_eq
    omega
  have alignedLow : (alignToDword address).toNat < 0x40000 := by
    have hle : (alignToDword address).toNat ≤ address.toNat := by
      unfold alignToDword
      rw [BitVec.toNat_and]
      exact Nat.and_le_left
    have haddr : address.toNat = 0x22ca0 + i := by
      simp only [address, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt small
    omega
  simp only [MachineState.getByte]
  rw [loaded_secondHash_low_frame publicKey message witness state answer
    loaded answerMatches ready trace (alignToDword address) alignedLow]

/-- Every honest FORS opening survives the verifier's message-hash prefix. -/
theorem loaded_honest_allFts_at_secondHash
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (inner : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (state : MachineState) (answer : BitVec 256)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire inner signature) =
        some state)
    (answerMatches : ∀ index : Fin 2,
      answer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64)
    (ready : MachineState)
    (trace : OrdinarySteps SphincsImages.verify
      (writeHash (firstHashState state) answer) 107 ready) :
    FtsWitness ready signature := by
  constructor
  · intro tree i hi
    have bound : 60 + tree.val * SphincsWire.ftsOpeningBytes + i <
        SphincsWire.signatureBytes := by
      have h := tree.isLt
      rw [SphincsWire.signatureBytes_eq]
      norm_num [SphincsSecurity.ftsTrees, SphincsWire.ftsOpeningBytes,
        SphincsSecurity.ftsTreeHeight, SphincsWire.digestBytes] at *
      omega
    exact (loaded_secondHash_witnessByte_frame publicKey message
      (SphincsWireEncoding.wire inner signature) state answer loaded
      answerMatches ready trace _ bound).trans
        (SphincsWireEncoding.loaded_honest_ftsSecret publicKey message
          inner signature state loaded tree i hi)
  · intro tree level i hi
    have bound : 60 + tree.val * SphincsWire.ftsOpeningBytes +
        (SphincsWire.digestBytes + level.val * SphincsWire.digestBytes + i) <
        SphincsWire.signatureBytes := by
      have htree := tree.isLt
      have hlevel := level.isLt
      rw [SphincsWire.signatureBytes_eq]
      norm_num [SphincsSecurity.ftsTrees, SphincsWire.ftsOpeningBytes,
        SphincsSecurity.ftsTreeHeight, SphincsWire.digestBytes] at *
      omega
    exact (loaded_secondHash_witnessByte_frame publicKey message
      (SphincsWireEncoding.wire inner signature) state answer loaded
      answerMatches ready trace _ bound).trans
        (SphincsWireEncoding.loaded_honest_ftsPath publicKey message
          inner signature state loaded tree level i hi)

theorem firstFtsPointers_preserve_FtsWitness (state : MachineState)
    (answer : BitVec 256) (signature : SphincsSecurity.Signature)
    (destination : state.getReg .x12 = 0x42000)
    (witness : FtsWitness state signature) :
    FtsWitness (SphincsVerifierFtsQuery.firstFtsPointers state answer)
      signature := by
  constructor
  · intro tree i hi
    have bound : 60 + tree.val * SphincsWire.ftsOpeningBytes + i <
        SphincsWire.signatureBytes := by
      have h := tree.isLt
      rw [SphincsWire.signatureBytes_eq]
      norm_num [SphincsSecurity.ftsTrees, SphincsWire.ftsOpeningBytes,
        SphincsSecurity.ftsTreeHeight, SphincsWire.digestBytes] at *
      omega
    exact (SphincsVerifierFtsWitnessFrame.firstFtsPointers_allWitness_frame
      state answer _ bound destination).trans (witness.secret tree i hi)
  · intro tree level i hi
    have bound : 60 + tree.val * SphincsWire.ftsOpeningBytes +
        (SphincsWire.digestBytes + level.val * SphincsWire.digestBytes + i) <
        SphincsWire.signatureBytes := by
      have htree := tree.isLt
      have hlevel := level.isLt
      rw [SphincsWire.signatureBytes_eq]
      norm_num [SphincsSecurity.ftsTrees, SphincsWire.ftsOpeningBytes,
        SphincsSecurity.ftsTreeHeight, SphincsWire.digestBytes] at *
      omega
    exact (SphincsVerifierFtsWitnessFrame.firstFtsPointers_allWitness_frame
      state answer _ bound destination).trans (witness.path tree level i hi)

theorem firstFtsHashReady_preserve_FtsWitness (state : MachineState)
    (answer : BitVec 256) (signature : SphincsSecurity.Signature)
    (destination : state.getReg .x12 = 0x42000)
    (witness : FtsWitness state signature) :
    FtsWitness (SphincsVerifierFtsSetup.ftsHashReadyState
      (SphincsVerifierFtsAdvance.ftsAdvanceState
        (SphincsVerifierCopy.copyRootState
          (SphincsVerifierFtsQuery.firstFtsPointers state answer))))
      signature := by
  constructor
  · intro tree i hi
    have bound : 60 + tree.val * SphincsWire.ftsOpeningBytes + i <
        SphincsWire.signatureBytes := by
      have h := tree.isLt
      rw [SphincsWire.signatureBytes_eq]
      norm_num [SphincsSecurity.ftsTrees, SphincsWire.ftsOpeningBytes,
        SphincsSecurity.ftsTreeHeight, SphincsWire.digestBytes] at *
      omega
    exact (SphincsVerifierFtsWitnessFrame.firstFtsHashReady_allWitness_frame
      state answer _ bound destination).trans (witness.secret tree i hi)
  · intro tree level i hi
    have bound : 60 + tree.val * SphincsWire.ftsOpeningBytes +
        (SphincsWire.digestBytes + level.val * SphincsWire.digestBytes + i) <
        SphincsWire.signatureBytes := by
      have htree := tree.isLt
      have hlevel := level.isLt
      rw [SphincsWire.signatureBytes_eq]
      norm_num [SphincsSecurity.ftsTrees, SphincsWire.ftsOpeningBytes,
        SphincsSecurity.ftsTreeHeight, SphincsWire.digestBytes] at *
      omega
    exact (SphincsVerifierFtsWitnessFrame.firstFtsHashReady_allWitness_frame
      state answer _ bound destination).trans (witness.path tree level i hi)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsEarlyFrame.firstFtsHashReady_preserve_FtsWitness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstFtsHashReady_preserve_FtsWitness

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
      exact (loaded_secondHash_witnessByte_frame publicKey message
        (SphincsWireEncoding.wire inner signature) state answer loaded
        answerMatches ready trace i (by
          rw [SphincsWire.signatureBytes_eq]
          omega)).trans
        (prefixState.root i hi)
    · intro i hi
      have frame := loaded_secondHash_witnessByte_frame publicKey
        message (SphincsWireEncoding.wire inner signature) state answer
        loaded answerMatches ready trace (20 + i) (by
          rw [SphincsWire.signatureBytes_eq]
          omega)
      have address : 0x22ca0 + (20 + i) = 0x22cb4 + i := by omega
      rw [address] at frame
      exact frame.trans (prefixState.parameter i hi)
  refine ⟨ready, trace, pc, messageReady, prefixReady, ?_⟩
  intro i hi
  have opening := (loaded_honest_allFts_at_secondHash publicKey message
    inner signature state answer loaded answerMatches ready trace).secret
      (⟨0, by decide⟩ : SphincsSecurity.FtsTree) i hi
  have address : 0x22ca0 + (60 + i) = 0x22cdc + i := by omega
  simp only [Nat.zero_mul] at opening
  rw [address] at opening
  exact opening

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
          (signature.ftsSecret ⟨0, by decide⟩)) ∧
      FtsWitness final signature := by
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
  have witnessReady := loaded_honest_allFts_at_secondHash publicKey
    message inner signature state commitmentAnswer loaded answerMatches
    ready trace
  have witnessFinal := firstFtsHashReady_preserve_FtsWitness ready
    digestAnswer signature messageReady.destination witnessReady
  exact ⟨ready, final, trace, query.1, query.2.1, query.2.2,
    by simpa only [final, advanced, pointers] using witnessFinal⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsEarlyFrame.loaded_honest_firstFts_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_firstFts_query

/-- info: 'SigGolfCandidate.SphincsVerifierFtsEarlyFrame.loaded_secondHash_witnessByte_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_secondHash_witnessByte_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsEarlyFrame.loaded_honest_allFts_at_secondHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_allFts_at_secondHash

end SigGolfCandidate.SphincsVerifierFtsEarlyFrame
