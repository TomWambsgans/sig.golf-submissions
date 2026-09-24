import SigGolfCandidate.SphincsVerifierFtsQuery

/-! The verifier's first FORS prefix remains untouched while selectors are decoded. -/

namespace SigGolfCandidate.SphincsVerifierFtsWitnessFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierMessageHash
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierLeavesFrame
open SigGolfCandidate.SphincsVerifierLeafCode
open SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolfCandidate.SphincsVerifierLastLeaf
open SigGolfCandidate.SphincsVerifierFtsEntry
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolfCandidate.SphincsVerifierFtsQuery
open SigGolfCandidate.SphincsVerifierHashBytes

def witnessAddress (offset : Fin 80) : Word :=
  BitVec.ofNat 64 (0x22ca0 + offset.val)

def witnessCell (offset : Fin 80) : Word :=
  alignToDword (witnessAddress offset)

set_option maxHeartbeats 0 in
theorem witnessCell_outside : ∀ offset : Fin 80,
    witnessCell offset ≠ 0x43000 ∧
    witnessCell offset ≠ 0x43008 ∧
    witnessCell offset ≠ 0x43010 ∧
    witnessCell offset ≠ 0x43018 ∧
    witnessCell offset ≠ 0x43020 ∧
    witnessCell offset ≠ 0x43028 ∧
    witnessCell offset ≠ 0x43040 ∧
    witnessCell offset ≠ 0x43070 ∧
    witnessCell offset ≠ 0x43078 := by
  decide

set_option maxHeartbeats 0 in
theorem witnessCell_outsideHash : ∀ offset : Fin 80,
    witnessCell offset ≠ 0x42000 ∧
    witnessCell offset ≠ 0x42008 ∧
    witnessCell offset ≠ 0x42010 ∧
    witnessCell offset ≠ 0x42018 := by
  decide

theorem witnessAddress_ne_selector (offset : Fin 80) (tree : Fin 24) :
    witnessAddress offset ≠ BitVec.ofNat 64 (0x44800 + tree.val) := by
  intro equal
  have values := congrArg BitVec.toNat equal
  have offsetSmall : 0x22ca0 + offset.val < 2 ^ 64 := by
    have h := offset.isLt
    omega
  have treeSmall : 0x44800 + tree.val < 2 ^ 64 := by
    have h := tree.isLt
    omega
  simp only [witnessAddress, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt offsetSmall, Nat.mod_eq_of_lt treeSmall] at values
  have h := offset.isLt
  have h' := tree.isLt
  omega

theorem leafStates_witnessByte_frame (initial : MachineState)
    (offset : Fin 80) :
    ∀ n (bound : n ≤ 24),
      (leafStates initial n bound).getByte (witnessAddress offset) =
        initial.getByte (witnessAddress offset) := by
  intro n
  induction n with
  | zero =>
      intro bound
      rfl
  | succ n ih =>
      intro bound
      change (leafState ⟨n, by omega⟩
        (leafStates initial n (by omega))).getByte (witnessAddress offset) = _
      rw [leafState_frame _ _ _ (witnessAddress_ne_selector offset ⟨n, by omega⟩)]
      exact ih (by omega)

theorem ftsPrefix_witnessByte_frame (initial : MachineState)
    (offset : Fin 80) :
    (ftsCopyPointers
      (ftsSelectState
        (ftsTreeHeaderState (ftsEntryState (lastAcceptState initial))))).getByte
      (witnessAddress offset) = initial.getByte (witnessAddress offset) := by
  let read := witnessCell offset
  rcases witnessCell_outside offset with
    ⟨not0, not8, not10, _, not20, not28, not40, not70, _⟩
  simp only [MachineState.getByte]
  rw [show alignToDword (witnessAddress offset) = read by rfl]
  rw [ftsCopyPointers_mem,
    ftsSelect_mem_frame _ read not10 not20 not70,
    ftsTreeHeader_mem_frame _ read not0 not8,
    ftsEntry_mem_frame _ read not40 not28,
    lastAccept_mem]

theorem indexValue_witnessByte_frame (state : MachineState)
    (offset : Fin 80) :
    (indexValueState state).getByte (witnessAddress offset) =
      state.getByte (witnessAddress offset) := by
  simp [MachineState.getByte, indexValueState, execInstrBr]

theorem indexStored_witnessByte_frame (state : MachineState)
    (offset : Fin 80) :
    (indexStoredState state).getByte (witnessAddress offset) =
      state.getByte (witnessAddress offset) := by
  let read := witnessCell offset
  rcases witnessCell_outside offset with
    ⟨_, _, _, not18, _, _, _, _, not78⟩
  simp only [MachineState.getByte]
  rw [show alignToDword (witnessAddress offset) = read by rfl]
  dsimp only [read]
  change witnessCell offset ≠ (274456#64) at not18
  change witnessCell offset ≠ (274552#64) at not78
  simp [indexStoredState, execInstrBr, signExtend12,
    MachineState.getMem_setMem_ne, not18, not78,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem firstFtsPointers_witnessByte_frame (state : MachineState)
    (answer : BitVec 256) (offset : Fin 80) :
    (firstFtsPointers state answer).getByte (witnessAddress offset) =
      (writeHash state answer).getByte (witnessAddress offset) := by
  let hashed := writeHash state answer
  let indexed := indexStoredState (indexValueState hashed)
  change (ftsCopyPointers
    (ftsSelectState
      (ftsTreeHeaderState
        (ftsEntryState
          (lastAcceptState
            (leafStates indexed 24 (by decide))))))).getByte
      (witnessAddress offset) = hashed.getByte (witnessAddress offset)
  rw [ftsPrefix_witnessByte_frame,
    leafStates_witnessByte_frame,
    indexStored_witnessByte_frame,
    indexValue_witnessByte_frame]

theorem writeHash_witnessByte_frame (state : MachineState)
    (answer : BitVec 256) (offset : Fin 80)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getByte (witnessAddress offset) =
      state.getByte (witnessAddress offset) := by
  let read := witnessCell offset
  rcases witnessCell_outsideHash offset with ⟨not0, not8, not16, not24⟩
  simp only [MachineState.getByte]
  rw [show alignToDword (witnessAddress offset) = read by rfl]
  dsimp only [read]
  change witnessCell offset ≠ (270336#64) at not0
  change witnessCell offset ≠ (270344#64) at not8
  change witnessCell offset ≠ (270352#64) at not16
  change witnessCell offset ≠ (270360#64) at not24
  simp [writeHash, MachineState.writeWords_cons, destination,
    MachineState.getMem_setMem_ne, not0, not8, not16, not24]

theorem firstFtsPointers_messageByte_frame (state : MachineState)
    (answer : BitVec 256) (offset : Fin 80)
    (destination : state.getReg .x12 = 0x42000) :
    (firstFtsPointers state answer).getByte (witnessAddress offset) =
      state.getByte (witnessAddress offset) := by
  rw [firstFtsPointers_witnessByte_frame,
    writeHash_witnessByte_frame state answer offset destination]

theorem firstFtsPointers_prefix (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000)
    (prefixBytes : WitnessPrefix state pk) :
    WitnessPrefix (firstFtsPointers state answer) pk := by
  constructor
  · intro i hi
    let offset : Fin 80 := ⟨i, by omega⟩
    have frame := firstFtsPointers_messageByte_frame state answer offset destination
    simpa [witnessAddress, offset] using frame.trans (prefixBytes.root i hi)
  · intro i hi
    let offset : Fin 80 := ⟨20 + i, by omega⟩
    have frame := firstFtsPointers_messageByte_frame state answer offset destination
    have address : 0x22ca0 + (20 + i) = 0x22cb4 + i := by omega
    have frame' : (firstFtsPointers state answer).getByte
        (BitVec.ofNat 64 (0x22cb4 + i)) =
        state.getByte (BitVec.ofNat 64 (0x22cb4 + i)) := by
      simpa [witnessAddress, offset, address] using frame
    exact frame'.trans (prefixBytes.parameter i hi)

theorem firstFtsPointers_secret (state : MachineState)
    (answer : BitVec 256) (secret : SphincsSecurity.Digest)
    (destination : state.getReg .x12 = 0x42000)
    (secretBytes : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x22cdc + i)) =
        secret.extractLsb' (8 * i) 8) :
    ∀ i, (hi : i < 20) →
      (firstFtsPointers state answer).getByte
        (BitVec.ofNat 64 (0x22cdc + i)) =
        secret.extractLsb' (8 * i) 8 := by
  intro i hi
  let offset : Fin 80 := ⟨60 + i, by omega⟩
  have frame := firstFtsPointers_messageByte_frame state answer offset destination
  have address : 0x22ca0 + (60 + i) = 0x22cdc + i := by omega
  have frame' : (firstFtsPointers state answer).getByte
      (BitVec.ofNat 64 (0x22cdc + i)) =
      state.getByte (BitVec.ofNat 64 (0x22cdc + i)) := by
    simpa [witnessAddress, offset, address] using frame
  exact frame'.trans (secretBytes i hi)

theorem messageReady_firstFts_query_from_state (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer))
    (prefixBytes : WitnessPrefix state pk)
    (secret : SphincsSecurity.Digest)
    (secretBytes : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x22cdc + i)) =
        secret.extractLsb' (8 * i) 8) :
    let pointers := firstFtsPointers state answer
    let advanced := SphincsVerifierFtsAdvance.ftsAdvanceState
      (SphincsVerifierCopy.copyRootState pointers)
    let final := SphincsVerifierFtsSetup.ftsHashReadyState advanced
    OrdinarySteps SphincsImages.verify (writeHash state answer) 392 final ∧
      final.pc = 0x18c8 ∧
      hashInput final = SphincsBridge.toQuery (firstFtsInput pk
        (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest answer))
        (SphincsSecurity.Concrete.digestLeaves
          (SphincsSecurity.truncateMessageDigest answer) ⟨0, by decide⟩)
        secret) := by
  exact messageReady_firstFts_hashInput state pk message randomness ready pc
    answer admissible
    (firstFtsPointers_prefix state pk answer ready.destination prefixBytes)
    secret (firstFtsPointers_secret state answer secret ready.destination secretBytes)

theorem messageReady_firstFts_hashStep_from_state (hash : Hash)
    (state : MachineState) (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer))
    (prefixBytes : WitnessPrefix state pk)
    (secret : SphincsSecurity.Digest)
    (secretBytes : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x22cdc + i)) =
        secret.extractLsb' (8 * i) 8)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash
        (SphincsVerifierFtsSetup.ftsHashReadyState
          (SphincsVerifierFtsAdvance.ftsAdvanceState
            (SphincsVerifierCopy.copyRootState
              (firstFtsPointers state answer))))
        (hash (SphincsBridge.toQuery
          (firstFtsInput pk
            (SphincsSecurity.Concrete.digestIndex
              (SphincsSecurity.truncateMessageDigest answer))
            (SphincsSecurity.Concrete.digestLeaves
              (SphincsSecurity.truncateMessageDigest answer)
              ⟨0, by decide⟩) secret)))) steps result) :
    Executes hash SphincsImages.verify
      (SphincsVerifierFtsSetup.ftsHashReadyState
        (SphincsVerifierFtsAdvance.ftsAdvanceState
          (SphincsVerifierCopy.copyRootState
            (firstFtsPointers state answer))))
      (steps + 1) (result.charge 8 1 1) := by
  let pointers := firstFtsPointers state answer
  let advanced := SphincsVerifierFtsAdvance.ftsAdvanceState
    (SphincsVerifierCopy.copyRootState pointers)
  let final := SphincsVerifierFtsSetup.ftsHashReadyState advanced
  have facts := messageReady_firstFts_query_from_state state pk message
    randomness ready pc answer admissible prefixBytes secret secretBytes
  have regs := SphincsVerifierFtsSetup.ftsHashReady_regs advanced
  have tail' : Executes hash SphincsImages.verify
      (writeHash final (hash (hashInput final))) steps result := by
    rw [facts.2.2]
    exact tail
  exact SphincsVerifierFtsHash.hash_step hash final facts.2.1
    regs.1 regs.2.1 regs.2.2.1 regs.2.2.2 steps result tail'

/-- info: 'SigGolfCandidate.SphincsVerifierFtsWitnessFrame.messageReady_firstFts_query_from_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_firstFts_query_from_state

/-- info: 'SigGolfCandidate.SphincsVerifierFtsWitnessFrame.messageReady_firstFts_hashStep_from_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_firstFts_hashStep_from_state

/-- info: 'SigGolfCandidate.SphincsVerifierFtsWitnessFrame.leafStates_witnessByte_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms leafStates_witnessByte_frame

/-- info: 'SigGolfCandidate.SphincsVerifierFtsWitnessFrame.messageReady_firstFts_query_from_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_firstFts_query_from_state

end SigGolfCandidate.SphincsVerifierFtsWitnessFrame
