import SigGolfCandidate.SphincsVerifierFtsCopyAccess
import SigGolfCandidate.SphincsVerifierCopyMemory

/-! The first FORS leaf opening is copied from the witness into the HASH input. -/

namespace SigGolfCandidate.SphincsVerifierFtsLeafCopy
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsEntry
open SigGolfCandidate.SphincsVerifierLastLeaf
open SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierMessageHash
set_option maxRecDepth 16384

set_option maxHeartbeats 0 in
theorem ftsLeafCopy_code : Copy20Code SphincsImages.verify 497 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

theorem ftsLeafCopy_block (state : MachineState)
    (pc : state.pc = 0x17c4)
    (source : state.getReg .x6 = 0x22cdc)
    (destination : state.getReg .x7 = 0x40028) :
    OrdinarySteps SphincsImages.verify state 10 (copyRootState state) := by
  apply copy20_block_general SphincsImages.verify 497 ftsLeafCopy_code state
    0x22cdc 0x40028 (by simpa using pc) source destination
  all_goals decide

theorem ftsLeafCopy_pc (state : MachineState) (pc : state.pc = 0x17c4) :
    (copyRootState state).pc = 0x17ec := by
  simpa using copy20_final_pc state 497 (by simpa using pc)

theorem ftsLeafCopy_mem_frame (state : MachineState)
    (destination : state.getReg .x7 = 0x40028)
    (address : Word) (outside : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x40028 + signExtend12 (4#12 * BitVec.ofNat 12 offset.val))) :
    (copyRootState state).getMem address = state.getMem address := by
  apply copyRoot_mem_frame state address
  intro offset
  rw [destination]
  exact outside offset

theorem messageReady_admissible_ftsLeafCopy (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer)) :
    let initial := indexStoredState (indexValueState (writeHash state answer))
    let selected := leafStates initial 24 (by decide)
    let accepted := lastAcceptState selected
    let entered := ftsEntryState accepted
    let header := ftsTreeHeaderState entered
    let selection := ftsSelectState header
    let pointers := ftsCopyPointers selection
    let final := copyRootState pointers
    OrdinarySteps SphincsImages.verify (writeHash state answer) 337 final ∧
      final.pc = 0x17ec ∧
      final.getMem 0x43008 =
        BitVec.ofNat 64 (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest answer)).val ∧
      (final.getMem 0x43020).toNat = abstractLeaf answer (0 : Fin 24) ∧
      final.getMem 0x43028 = 0x22cdc := by
  obtain ⟨front, pointersPc, source, destination, treeIndex, leaf⟩ :=
    messageReady_admissible_ftsCopyPointers state pk message randomness
      ready pc answer admissible
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selected := leafStates initial 24 (by decide)
  let accepted := lastAcceptState selected
  let entered := ftsEntryState accepted
  let header := ftsTreeHeaderState entered
  let selection := ftsSelectState header
  let pointers := ftsCopyPointers selection
  have back := ftsLeafCopy_block pointers pointersPc source destination
  have finalPc := ftsLeafCopy_pc pointers pointersPc
  have pointer : pointers.getMem 0x43028 = 0x22cdc := by
    rw [ftsCopyPointers_mem]
    exact (messageReady_admissible_ftsSelect state pk message randomness
      ready pc answer admissible).2.2.2.2.1
  have frame (address : Word)
      (outside : ∀ offset : Fin 5,
        address ≠ alignToDword
          (0x40028 + signExtend12 (4#12 * BitVec.ofNat 12 offset.val))) :
      (copyRootState pointers).getMem address = pointers.getMem address :=
    ftsLeafCopy_mem_frame pointers destination address outside
  exact ⟨by simpa [initial, selected, accepted, entered, header, selection, pointers] using
      front.append back,
    finalPc,
    by rw [frame 0x43008 (by intro offset; fin_cases offset <;> decide)];
       exact treeIndex,
    by rw [frame 0x43020 (by intro offset; fin_cases offset <;> decide)];
       exact leaf,
    by rw [frame 0x43028 (by intro offset; fin_cases offset <;> decide)];
       exact pointer⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLeafCopy.messageReady_admissible_ftsLeafCopy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_admissible_ftsLeafCopy

end SigGolfCandidate.SphincsVerifierFtsLeafCopy
