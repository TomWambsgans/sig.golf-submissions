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

private theorem low_ne_high (read address : Word)
    (low : read.toNat < 0x40000)
    (high : 0x40000 ≤ address.toNat) : read ≠ address := by
  intro equal
  have values := congrArg BitVec.toNat equal
  omega

theorem leafStates_lowByte_frame (initial : MachineState)
    (address : Word) (low : address.toNat < 0x40000) :
    ∀ n (bound : n ≤ 24),
      (leafStates initial n bound).getByte address =
        initial.getByte address := by
  intro n
  induction n with
  | zero =>
      intro bound
      rfl
  | succ n ih =>
      intro bound
      change (leafState ⟨n, by omega⟩
        (leafStates initial n (by omega))).getByte address = _
      rw [leafState_frame _ _ address (by
        apply low_ne_high address _ low
        have small : 0x44800 + n < 2 ^ 64 := by omega
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
        omega)]
      exact ih (by omega)

theorem ftsPrefix_lowByte_frame (initial : MachineState)
    (address : Word) (low : (alignToDword address).toNat < 0x40000) :
    (ftsCopyPointers
      (ftsSelectState
        (ftsTreeHeaderState (ftsEntryState (lastAcceptState initial))))).getByte
      address = initial.getByte address := by
  let read := alignToDword address
  have not0 : read ≠ 0x43000 := low_ne_high read _ low (by decide)
  have not8 : read ≠ 0x43008 := low_ne_high read _ low (by decide)
  have not10 : read ≠ 0x43010 := low_ne_high read _ low (by decide)
  have not20 : read ≠ 0x43020 := low_ne_high read _ low (by decide)
  have not28 : read ≠ 0x43028 := low_ne_high read _ low (by decide)
  have not40 : read ≠ 0x43040 := low_ne_high read _ low (by decide)
  have not70 : read ≠ 0x43070 := low_ne_high read _ low (by decide)
  simp only [MachineState.getByte]
  rw [ftsCopyPointers_mem,
    ftsSelect_mem_frame _ read not10 not20 not70,
    ftsTreeHeader_mem_frame _ read not0 not8,
    ftsEntry_mem_frame _ read not40 not28,
    lastAccept_mem]

theorem indexValue_lowByte_frame (state : MachineState)
    (address : Word) :
    (indexValueState state).getByte address = state.getByte address := by
  simp [MachineState.getByte, indexValueState, execInstrBr]

theorem indexStored_lowByte_frame (state : MachineState)
    (address : Word) (low : (alignToDword address).toNat < 0x40000) :
    (indexStoredState state).getByte address = state.getByte address := by
  let read := alignToDword address
  have not18 : read ≠ 0x43018 := low_ne_high read _ low (by decide)
  have not78 : read ≠ 0x43078 := low_ne_high read _ low (by decide)
  simp only [MachineState.getByte]
  change alignToDword address ≠ (274456#64) at not18
  change alignToDword address ≠ (274552#64) at not78
  simp [indexStoredState, execInstrBr, signExtend12,
    not18, not78,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem firstFtsPointers_lowByte_frame (state : MachineState)
    (answer : BitVec 256) (address : Word)
    (low : address.toNat < 0x40000)
    (alignedLow : (alignToDword address).toNat < 0x40000) :
    (firstFtsPointers state answer).getByte address =
      (writeHash state answer).getByte address := by
  let hashed := writeHash state answer
  let indexed := indexStoredState (indexValueState hashed)
  change (ftsCopyPointers
    (ftsSelectState
      (ftsTreeHeaderState
        (ftsEntryState
          (lastAcceptState
            (leafStates indexed 24 (by decide))))))).getByte
      address = hashed.getByte address
  rw [ftsPrefix_lowByte_frame _ address alignedLow,
    leafStates_lowByte_frame _ address low,
    indexStored_lowByte_frame _ address alignedLow,
    indexValue_lowByte_frame]

theorem writeHash_lowByte_frame (state : MachineState)
    (answer : BitVec 256) (address : Word)
    (alignedLow : (alignToDword address).toNat < 0x40000)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getByte address =
      state.getByte address := by
  have not0 : alignToDword address ≠ 0x42000 :=
    low_ne_high _ _ alignedLow (by decide)
  have not8 : alignToDword address ≠ 0x42008 :=
    low_ne_high _ _ alignedLow (by decide)
  have not16 : alignToDword address ≠ 0x42010 :=
    low_ne_high _ _ alignedLow (by decide)
  have not24 : alignToDword address ≠ 0x42018 :=
    low_ne_high _ _ alignedLow (by decide)
  change alignToDword address ≠ (270336#64) at not0
  change alignToDword address ≠ (270344#64) at not8
  change alignToDword address ≠ (270352#64) at not16
  change alignToDword address ≠ (270360#64) at not24
  simp [MachineState.getByte, writeHash, MachineState.writeWords_cons,
    destination, not0, not8, not16, not24]

theorem writeHash_allWitness_frame (state : MachineState)
    (answer : BitVec 256) (i : Nat)
    (hi : i < SphincsWire.signatureBytes)
    (destination : state.getReg .x12 = 0x42000) :
    (writeHash state answer).getByte (BitVec.ofNat 64 (0x22ca0 + i)) =
      state.getByte (BitVec.ofNat 64 (0x22ca0 + i)) := by
  let address : Word := BitVec.ofNat 64 (0x22ca0 + i)
  have low : (alignToDword address).toNat < 0x40000 := by
    have length := SphincsWire.signatureBytes_eq
    have small : 0x22ca0 + i < 2 ^ 64 := by omega
    have range : 0x22ca0 + i < 0x40000 := by omega
    have aligned : (alignToDword address).toNat ≤ address.toNat := by
      unfold alignToDword
      rw [BitVec.toNat_and]
      exact Nat.and_le_left
    have exactAddress : address.toNat = 0x22ca0 + i := by
      simp only [address, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt small
    omega
  exact writeHash_lowByte_frame state answer address low destination

theorem firstFtsPointers_lowMessageByte_frame (state : MachineState)
    (answer : BitVec 256) (address : Word)
    (low : address.toNat < 0x40000)
    (alignedLow : (alignToDword address).toNat < 0x40000)
    (destination : state.getReg .x12 = 0x42000) :
    (firstFtsPointers state answer).getByte address =
      state.getByte address := by
  rw [firstFtsPointers_lowByte_frame state answer address low alignedLow,
    writeHash_lowByte_frame state answer address alignedLow destination]

theorem firstFtsPointers_allWitness_frame (state : MachineState)
    (answer : BitVec 256) (i : Nat)
    (hi : i < SphincsWire.signatureBytes)
    (destination : state.getReg .x12 = 0x42000) :
    (firstFtsPointers state answer).getByte
      (BitVec.ofNat 64 (0x22ca0 + i)) =
      state.getByte (BitVec.ofNat 64 (0x22ca0 + i)) := by
  let address : Word := BitVec.ofNat 64 (0x22ca0 + i)
  have small : 0x22ca0 + i < 2 ^ 64 := by
    have length := SphincsWire.signatureBytes_eq
    omega
  have range : 0x22ca0 + i < 0x40000 := by
    have length := SphincsWire.signatureBytes_eq
    omega
  have low : address.toNat < 0x40000 := by
    simp only [address, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt small]
    exact range
  have alignedLow : (alignToDword address).toNat < 0x40000 := by
    have hle : (alignToDword address).toNat ≤ address.toNat := by
      unfold alignToDword
      rw [BitVec.toNat_and]
      exact Nat.and_le_left
    omega
  exact firstFtsPointers_lowMessageByte_frame state answer address
    low alignedLow destination

theorem firstFtsCopy_lowByte_frame (state : MachineState)
    (address : Word) (alignedLow : (alignToDword address).toNat < 0x40000)
    (destination : state.getReg .x7 = 0x40028) :
    (SphincsVerifierCopy.copyRootState state).getByte address =
      state.getByte address := by
  simp only [MachineState.getByte]
  rw [SphincsVerifierCopyMemory.copyRoot_mem_frame state
    (alignToDword address) (by
      intro offset
      have high : 0x40000 ≤
          (alignToDword
            (state.getReg .x7 + signExtend12
              (4#12 * BitVec.ofNat 12 offset.val))).toNat := by
        rw [destination]
        fin_cases offset <;> decide
      exact low_ne_high (alignToDword address) _ alignedLow high)]

theorem firstFtsAdvance_lowByte_frame (state : MachineState)
    (address : Word) (alignedLow : (alignToDword address).toNat < 0x40000) :
    (SphincsVerifierFtsAdvance.ftsAdvanceState state).getByte address =
      state.getByte address := by
  simp only [MachineState.getByte]
  rw [SphincsVerifierFtsAdvance.ftsAdvance_mem_frame state
    (alignToDword address)
    (low_ne_high (alignToDword address) _ alignedLow (by decide))
    (low_ne_high (alignToDword address) _ alignedLow (by decide))]

theorem firstFtsAdvanced_allWitness_frame (state : MachineState)
    (answer : BitVec 256) (i : Nat)
    (hi : i < SphincsWire.signatureBytes)
    (destination : state.getReg .x12 = 0x42000) :
    (SphincsVerifierFtsAdvance.ftsAdvanceState
      (SphincsVerifierCopy.copyRootState
        (firstFtsPointers state answer))).getByte
      (BitVec.ofNat 64 (0x22ca0 + i)) =
      state.getByte (BitVec.ofNat 64 (0x22ca0 + i)) := by
  let address : Word := BitVec.ofNat 64 (0x22ca0 + i)
  have low : (alignToDword address).toNat < 0x40000 := by
    have length := SphincsWire.signatureBytes_eq
    have small : 0x22ca0 + i < 2 ^ 64 := by omega
    have range : 0x22ca0 + i < 0x40000 := by omega
    have aligned : (alignToDword address).toNat ≤ address.toNat := by
      unfold alignToDword
      rw [BitVec.toNat_and]
      exact Nat.and_le_left
    have exactAddress : address.toNat = 0x22ca0 + i := by
      simp only [address, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt small
    omega
  have pointer : (firstFtsPointers state answer).getReg .x7 = 0x40028 := by
    unfold firstFtsPointers
    exact (SphincsVerifierFtsCopyPointers.ftsCopyPointers_regs _).2
  rw [firstFtsAdvance_lowByte_frame _ address low,
    firstFtsCopy_lowByte_frame _ address low pointer]
  exact firstFtsPointers_allWitness_frame state answer i hi destination

/-- info: 'SigGolfCandidate.SphincsVerifierFtsWitnessFrame.firstFtsAdvanced_allWitness_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstFtsAdvanced_allWitness_frame

theorem firstFtsTag_lowMem_frame (state : MachineState)
    (read : Word) (low : read.toNat < 0x40000) :
    (SphincsVerifierFtsHeader.tagState state).getMem read =
      state.getMem read := by
  have not0 : read ≠ 0x40000 :=
    low_ne_high read _ low (by decide)
  have notCell : read ≠ alignToDword (0x40000#64) := by
    have aligned : alignToDword (0x40000#64) = (0x40000 : Word) := by decide
    simpa only [aligned] using not0
  simp [SphincsVerifierFtsHeader.tagState,
    SphincsVerifierFtsHeader.tagBeforeStore,
    execInstrBr, signExtend12, setWord32_eq,
    MachineState.getMem_setMem_ne,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, notCell]

theorem firstFtsPosition_lowMem_frame (state : MachineState)
    (read : Word) (low : read.toNat < 0x40000)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.positionState state).getMem read =
      state.getMem read := by
  have not0 : read ≠ 0x40000 :=
    low_ne_high read _ low (by decide)
  have notCell : read ≠ alignToDword (0x40004#64) := by
    have aligned : alignToDword (0x40004#64) = (0x40000 : Word) := by decide
    simpa only [aligned] using not0
  simp [SphincsVerifierHeader.positionState,
    SphincsVerifierHeader.positionBeforeStore,
    execInstrBr, signExtend12, setWord32_eq, destination,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, notCell]

theorem firstFtsTree_lowMem_frame (state : MachineState)
    (read : Word) (low : read.toNat < 0x40000)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.treeState state).getMem read =
      state.getMem read := by
  have notCell : read ≠ 0x40008 :=
    low_ne_high read _ low (by decide)
  change read ≠ (262152#64) at notCell
  simp [SphincsVerifierHeader.treeState,
    SphincsVerifierHeader.treeBeforeStore,
    execInstrBr, signExtend12, destination,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, notCell]

theorem firstFtsIndex_lowMem_frame (state : MachineState)
    (read : Word) (low : read.toNat < 0x40000)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.indexState state).getMem read =
      state.getMem read := by
  have notCell : read ≠ alignToDword (0x40010#64) := by
    have not16 : read ≠ 0x40010 :=
      low_ne_high read _ low (by decide)
    have aligned : alignToDword (0x40010#64) = (0x40010 : Word) := by decide
    simpa only [aligned] using not16
  simp [SphincsVerifierHeader.indexState,
    SphincsVerifierHeader.indexBeforeStore,
    execInstrBr, signExtend12, setWord32_eq, destination,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, notCell]

theorem firstFtsHeader_lowMem_frame (state : MachineState)
    (read : Word) (low : read.toNat < 0x40000) :
    (SphincsVerifierFtsHeader.headerState state).getMem read =
      state.getMem read := by
  let tagged := SphincsVerifierFtsHeader.tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer : tagged.getReg .x7 = 0x40000 :=
    SphincsVerifierFtsHeader.tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getMem read = _
  rw [firstFtsIndex_lowMem_frame treed read low treePointer,
    firstFtsTree_lowMem_frame positioned read low positionPointer,
    firstFtsPosition_lowMem_frame tagged read low tagPointer,
    firstFtsTag_lowMem_frame state read low]

theorem firstFtsHeader_lowByte_frame (state : MachineState)
    (address : Word) (low : (alignToDword address).toNat < 0x40000) :
    (SphincsVerifierFtsHeader.headerState state).getByte address =
      state.getByte address := by
  simpa only [MachineState.getByte] using
    congrArg (fun value : Word => extractByte value (byteOffset address))
      (firstFtsHeader_lowMem_frame state (alignToDword address) low)

theorem firstFtsParameterPointers_mem_frame (state : MachineState)
    (read : Word) :
    (SphincsVerifierFtsParameter.parameterPointers state).getMem read =
      state.getMem read := by
  simp [SphincsVerifierFtsParameter.parameterPointers, execInstrBr]

theorem firstFtsParameterCopy_lowMem_frame (state : MachineState)
    (read : Word) (low : read.toNat < 0x40000)
    (destination : state.getReg .x7 = 0x40014) :
    (SphincsVerifierCopy.copyRootState state).getMem read =
      state.getMem read := by
  rw [SphincsVerifierCopyMemory.copyRoot_mem_frame state read (by
    intro offset
    have high : 0x40000 ≤
        (alignToDword
          (state.getReg .x7 + signExtend12
            (4#12 * BitVec.ofNat 12 offset.val))).toNat := by
      rw [destination]
      fin_cases offset <;> decide
    exact low_ne_high read _ low high)]

theorem firstFtsParameter_lowMem_frame (state : MachineState)
    (read : Word) (low : read.toNat < 0x40000) :
    (SphincsVerifierFtsParameter.parameterState state).getMem read =
      state.getMem read := by
  change (SphincsVerifierCopy.copyRootState
    (SphincsVerifierFtsParameter.parameterPointers state)).getMem read = _
  rw [firstFtsParameterCopy_lowMem_frame _ read low
      (SphincsVerifierFtsParameter.parameterPointers_regs state).2,
    firstFtsParameterPointers_mem_frame]

theorem firstFtsHashRegisters_mem_frame (state : MachineState)
    (read : Word) :
    (SphincsVerifierFtsSetup.hashRegistersState state).getMem read =
      state.getMem read := by
  simp [SphincsVerifierFtsSetup.hashRegistersState, execInstrBr]

theorem firstFtsHashReady_lowMem_frame (state : MachineState)
    (read : Word) (low : read.toNat < 0x40000) :
    (SphincsVerifierFtsSetup.ftsHashReadyState state).getMem read =
      state.getMem read := by
  change (SphincsVerifierFtsSetup.hashRegistersState
    (SphincsVerifierFtsParameter.parameterState
      (SphincsVerifierFtsHeader.headerState state))).getMem read = _
  rw [firstFtsHashRegisters_mem_frame,
    firstFtsParameter_lowMem_frame _ read low,
    firstFtsHeader_lowMem_frame _ read low]

theorem firstFtsHashReady_allWitness_frame (state : MachineState)
    (answer : BitVec 256) (i : Nat)
    (hi : i < SphincsWire.signatureBytes)
    (destination : state.getReg .x12 = 0x42000) :
    (SphincsVerifierFtsSetup.ftsHashReadyState
      (SphincsVerifierFtsAdvance.ftsAdvanceState
        (SphincsVerifierCopy.copyRootState
          (firstFtsPointers state answer)))).getByte
      (BitVec.ofNat 64 (0x22ca0 + i)) =
      state.getByte (BitVec.ofNat 64 (0x22ca0 + i)) := by
  let address : Word := BitVec.ofNat 64 (0x22ca0 + i)
  have low : (alignToDword address).toNat < 0x40000 := by
    have length := SphincsWire.signatureBytes_eq
    have small : 0x22ca0 + i < 2 ^ 64 := by omega
    have range : 0x22ca0 + i < 0x40000 := by omega
    have aligned : (alignToDword address).toNat ≤ address.toNat := by
      unfold alignToDword
      rw [BitVec.toNat_and]
      exact Nat.and_le_left
    have exactAddress : address.toNat = 0x22ca0 + i := by
      simp only [address, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt small
    omega
  simp only [MachineState.getByte]
  rw [firstFtsHashReady_lowMem_frame _ (alignToDword address) low]
  exact firstFtsAdvanced_allWitness_frame state answer i hi destination

/-- info: 'SigGolfCandidate.SphincsVerifierFtsWitnessFrame.firstFtsHashReady_allWitness_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstFtsHashReady_allWitness_frame


theorem firstFtsPointers_prefix (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000)
    (prefixBytes : WitnessPrefix state pk) :
    WitnessPrefix (firstFtsPointers state answer) pk := by
  constructor
  · intro i hi
    have frame := firstFtsPointers_allWitness_frame state answer i (by
      rw [SphincsWire.signatureBytes_eq]
      omega) destination
    exact frame.trans (prefixBytes.root i hi)
  · intro i hi
    have frame := firstFtsPointers_allWitness_frame state answer (20 + i) (by
      rw [SphincsWire.signatureBytes_eq]
      omega) destination
    have address : 0x22ca0 + (20 + i) = 0x22cb4 + i := by omega
    have frame' : (firstFtsPointers state answer).getByte
        (BitVec.ofNat 64 (0x22cb4 + i)) =
        state.getByte (BitVec.ofNat 64 (0x22cb4 + i)) := by
      simpa only [address] using frame
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
  have frame := firstFtsPointers_allWitness_frame state answer (60 + i) (by
    rw [SphincsWire.signatureBytes_eq]
    omega) destination
  have address : 0x22ca0 + (60 + i) = 0x22cdc + i := by omega
  have frame' : (firstFtsPointers state answer).getByte
      (BitVec.ofNat 64 (0x22cdc + i)) =
      state.getByte (BitVec.ofNat 64 (0x22cdc + i)) := by
    simpa only [address] using frame
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

/-- info: 'SigGolfCandidate.SphincsVerifierFtsWitnessFrame.firstFtsPointers_allWitness_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstFtsPointers_allWitness_frame

end SigGolfCandidate.SphincsVerifierFtsWitnessFrame
