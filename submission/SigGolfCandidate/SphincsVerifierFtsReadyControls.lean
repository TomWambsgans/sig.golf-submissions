import SigGolfCandidate.SphincsVerifierFtsFirstTreeExecution
import SigGolfCandidate.SphincsVerifierFtsHeaderFields

/-! The message-digest entry path establishes the first FORS tree controls. -/

namespace SigGolfCandidate.SphincsVerifierFtsReadyControls
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierMessageHash
open SigGolfCandidate.SphincsVerifierFtsQuery
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsAdvance
open SigGolfCandidate.SphincsVerifierFtsSetup
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierFtsHeaderFields
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolfCandidate.SphincsVerifierLastLeaf
open SigGolfCandidate.SphincsVerifierFtsEntry
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierFtsWitnessFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem messageReady_firstFts_controls (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (message : SphincsSecurity.Message)
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
    let advanced := ftsAdvanceState (SphincsVerifierCopy.copyRootState pointers)
    let final := ftsHashReadyState advanced
    final.getMem 0x43028 = 0x22cf0 ∧
      final.getMem 0x43070 = BitVec.ofNat 64
        (SphincsSecurity.Concrete.digestLeaves
          (SphincsSecurity.truncateMessageDigest answer)
          ⟨0, by decide⟩).val ∧
      final.getMem 0x43000 = 0 ∧
      final.getMem 0x43008 = BitVec.ofNat 64
        (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest answer)).val := by
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selected := leafStates initial 24 (by decide)
  let accepted := lastAcceptState selected
  let entered := ftsEntryState accepted
  let header := ftsTreeHeaderState entered
  let selection := ftsSelectState header
  let pointers := ftsCopyPointers selection
  let advanced := ftsAdvanceState (SphincsVerifierCopy.copyRootState pointers)
  let final := ftsHashReadyState advanced
  obtain ⟨_, _, pointer, _, index⟩ :=
    messageReady_admissible_ftsAdvance state pk message randomness
      ready pc answer admissible
  obtain ⟨_, _, _, _, _, leafCell, selectorCell, leafNat, _⟩ :=
    messageReady_admissible_ftsSelect state pk message randomness
      ready pc answer admissible
  have selectorAtSelection : selection.getMem 0x43070 = BitVec.ofNat 64
      (SphincsSecurity.Concrete.digestLeaves
        (SphincsSecurity.truncateMessageDigest answer)
        ⟨0, by decide⟩).val := by
    rw [selectorCell, ← leafCell]
    apply BitVec.eq_of_toNat_eq
    rw [leafNat]
    have leafValue : abstractLeaf answer (0 : Fin 24) =
        (SphincsSecurity.Concrete.digestLeaves
          (SphincsSecurity.truncateMessageDigest answer)
          ⟨0, by decide⟩).val := rfl
    rw [leafValue]
    have small : (SphincsSecurity.Concrete.digestLeaves
        (SphincsSecurity.truncateMessageDigest answer)
        ⟨0, by decide⟩).val < 2 ^ 64 := by
      have h := (SphincsSecurity.Concrete.digestLeaves
        (SphincsSecurity.truncateMessageDigest answer)
        ⟨0, by decide⟩).isLt
      simp only [SphincsSecurity.ftsTreeHeight] at h
      omega
    simp only [BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt small).symm
  have selectorAtAdvanced : advanced.getMem 0x43070 =
      selection.getMem 0x43070 := by
    exact advance_mem_frame selection 0x43070 (by decide) (by decide)
      (by intro offset; fin_cases offset <;> decide)
  have layer : advanced.getMem 0x43000 = 0 :=
    messageReady_firstFts_layerZero state pk message randomness
      ready pc answer admissible
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hashReady_pointer_frame advanced).trans pointer
  · exact (hashReady_selector_frame advanced).trans
      (selectorAtAdvanced.trans selectorAtSelection)
  · rw [hashReady_mem_frame advanced 0x43000 (by decide) (by decide)
      (by decide) (by decide)
      (by intro offset; fin_cases offset <;> decide)]
    exact layer
  · rw [hashReady_mem_frame advanced 0x43008 (by decide) (by decide)
      (by decide) (by decide)
      (by intro offset; fin_cases offset <;> decide)]
    exact index

theorem firstFtsHashReady_prefix (state : MachineState)
    (answer : BitVec 256) (pk : SphincsSecurity.PublicKey)
    (destination : state.getReg .x12 = 0x42000)
    (hprefix : WitnessPrefix state pk) :
    WitnessPrefix
      (ftsHashReadyState
        (ftsAdvanceState
          (SphincsVerifierCopy.copyRootState
            (firstFtsPointers state answer)))) pk := by
  constructor
  · intro i hi
    exact (firstFtsHashReady_allWitness_frame state answer i (by
      rw [SphincsWire.signatureBytes_eq]
      omega) destination).trans (hprefix.root i hi)
  · intro i hi
    have frame := firstFtsHashReady_allWitness_frame state answer
      (20 + i) (by rw [SphincsWire.signatureBytes_eq]; omega) destination
    have address : 0x22ca0 + (20 + i) = 0x22cb4 + i := by omega
    rw [address] at frame
    exact frame.trans (hprefix.parameter i hi)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsReadyControls.messageReady_firstFts_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_firstFts_controls

/-- info: 'SigGolfCandidate.SphincsVerifierFtsReadyControls.firstFtsHashReady_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstFtsHashReady_prefix

end SigGolfCandidate.SphincsVerifierFtsReadyControls
