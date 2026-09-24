import SigGolfCandidate.SphincsVerifierMessage32

/-!
# Message copy contents

The four exact verifier loop iterations leave the four 64-bit input message
words in the next HASH buffer and preserve the original message.
-/

namespace SigGolfCandidate.SphincsVerifierMessage32Data
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessage32
open SigGolfCandidate.Sphincs.Expansion
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierHashSetup
open SigGolfCandidate.SphincsSubmission

private def sourceWord (index : Nat) : Word :=
  BitVec.ofNat 64 (8 * index)

private def destinationWord (index : Nat) : Word :=
  BitVec.ofNat 64 (0x40050 + 8 * index)

private theorem destination_injective (left right : Nat)
    (hl : left < 4) (hr : right < 4)
    (equal : destinationWord left = destinationWord right) : left = right := by
  have bits := congrArg BitVec.toNat equal
  simp only [destinationWord, BitVec.toNat_ofNat] at bits
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at bits
  omega

private theorem source_ne_destination (source destination : Nat)
    (hs : source < 4) (hd : destination < 4) :
    sourceWord source ≠ destinationWord destination := by
  intro equal
  have bits := congrArg BitVec.toNat equal
  simp only [sourceWord, destinationWord, BitVec.toNat_ofNat] at bits
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at bits
  omega

def CopyData (original : MachineState) (copied : Nat)
    (state : MachineState) : Prop :=
  (∀ index : Fin 4, index.val < copied →
    state.getMem (destinationWord index.val) =
      original.getMem (sourceWord index.val)) ∧
  (∀ index : Fin 4,
    state.getMem (sourceWord index.val) =
      original.getMem (sourceWord index.val))

theorem copyData_initial (state : MachineState) : CopyData state 0 state := by
  constructor
  · intro index impossible
    omega
  · intro index
    rfl

theorem copyData_step (original state : MachineState) (remaining : Nat)
    (inv : LoopInvariant (remaining + 1) state)
    (data : CopyData original (4 - (remaining + 1)) state) :
    CopyData original (4 - remaining) (loopNext state) := by
  obtain ⟨bound, _, source, destination, _⟩ := inv
  have doneBound : 4 - (remaining + 1) < 4 := by omega
  have nextDone : 4 - remaining = 4 - (remaining + 1) + 1 := by omega
  constructor
  · intro index copied
    rw [loop_next_mem]
    rw [destination]
    change (if destinationWord index.val =
        destinationWord (4 - (remaining + 1)) then
          state.getMem (state.getReg .x6)
        else state.getMem (destinationWord index.val)) =
      original.getMem (sourceWord index.val)
    by_cases same : index.val = 4 - (remaining + 1)
    · have address : destinationWord index.val =
          destinationWord (4 - (remaining + 1)) := by rw [same]
      rw [address, if_pos rfl, source]
      simpa [sourceWord, same] using data.2 index
    · have other : destinationWord index.val ≠
          destinationWord (4 - (remaining + 1)) := by
        intro equal
        exact same (destination_injective _ _ index.isLt doneBound equal)
      rw [if_neg other]
      exact data.1 index (by omega)
  · intro index
    rw [loop_next_mem]
    rw [destination]
    change (if sourceWord index.val =
        destinationWord (4 - (remaining + 1)) then
          state.getMem (state.getReg .x6)
        else state.getMem (sourceWord index.val)) =
      original.getMem (sourceWord index.val)
    have other := source_ne_destination index.val
      (4 - (remaining + 1)) index.isLt doneBound
    rw [if_neg other]
    exact data.2 index

theorem loop_run_with_data (remaining : Nat) (original state : MachineState)
    (inv : LoopInvariant remaining state)
    (data : CopyData original (4 - remaining) state) :
    ∃ final, OrdinarySteps SphincsImages.verify state (6 * remaining) final ∧
      LoopInvariant 0 final ∧ CopyData original 4 final := by
  induction remaining generalizing state with
  | zero =>
    exact ⟨state, by simpa using OrdinarySteps.refl state, inv,
      by simpa using data⟩
  | succ remaining ih =>
    have pc : state.pc = 0x11e0 := by simpa [LoopInvariant] using inv.2.1
    have access := loop_accesses remaining state inv
    have first := loop_block state pc access.1 access.2
    have next := loop_invariant remaining state inv
    have nextData := copyData_step original state remaining inv data
    obtain ⟨final, rest, finalInv, finalData⟩ :=
      ih (loopNext state) next nextData
    refine ⟨final, ?_, finalInv, finalData⟩
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using first.append rest

theorem prefix_memory (state : MachineState) (address : Word) :
    (SphincsVerifierMessage32.prefixState state).getMem address =
      state.getMem address := by
  simp [SphincsVerifierMessage32.prefixState, execInstrBr]

theorem message32_block_with_data (state : MachineState)
    (pc : state.pc = 0x11d0) :
    ∃ final, OrdinarySteps SphincsImages.verify state 28 final ∧
      LoopInvariant 0 final ∧ CopyData state 4 final := by
  have prefixTrace := prefix_block state pc
  have prefixData : CopyData state 0
      (SphincsVerifierMessage32.prefixState state) := by
    constructor
    · intro index impossible
      omega
    · intro index
      exact prefix_memory state _
  obtain ⟨final, copied, invariant, contents⟩ :=
    loop_run_with_data 4 state (SphincsVerifierMessage32.prefixState state)
      (prefix_invariant state pc) (by simpa using prefixData)
  refine ⟨final, ?_, invariant, contents⟩
  simpa using prefixTrace.append copied

theorem loaded_message32_block_with_data (publicKey : SigGolf.PublicKey)
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
      CopyData (afterMessageCopiesState state answer) 4 final := by
  have copies := loaded_messageCopies_block publicKey message witness state
    answer loaded answerMatches
  have copiesPc := loaded_messageCopies_pc publicKey message witness state
    answer loaded answerMatches
  obtain ⟨final, messageCopy, invariant, contents⟩ :=
    message32_block_with_data (afterMessageCopiesState state answer) copiesPc
  refine ⟨final, ?_, invariant, contents⟩
  simpa using copies.append messageCopy

theorem copyData_final_word (original final : MachineState)
    (data : CopyData original 4 final) (index : Fin 4) :
    final.getMem (BitVec.ofNat 64 (0x40050 + 8 * index.val)) =
      original.getMem (BitVec.ofNat 64 (8 * index.val)) := by
  simpa [destinationWord, sourceWord] using data.1 index (by omega)

/-- info: 'SigGolfCandidate.SphincsVerifierMessage32Data.copyData_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copyData_step

/-- info: 'SigGolfCandidate.SphincsVerifierMessage32Data.loop_run_with_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loop_run_with_data

/-- info: 'SigGolfCandidate.SphincsVerifierMessage32Data.loaded_message32_block_with_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_message32_block_with_data

end SigGolfCandidate.SphincsVerifierMessage32Data
