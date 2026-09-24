import SigGolfCandidate.SphincsVerifierFtsPayload

/-! The exact byte query issued by the first FORS leaf HASH instruction. -/

namespace SigGolfCandidate.SphincsVerifierFtsQuery
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsSetup
open SigGolfCandidate.SphincsVerifierFtsAdvance
open SigGolfCandidate.SphincsVerifierFtsPayload
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierMessageHash
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolfCandidate.SphincsVerifierLastLeaf
open SigGolfCandidate.SphincsVerifierFtsEntry
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolfCandidate.SphincsVerifierFtsHeaderFields

def firstFtsInput (pk : SphincsSecurity.PublicKey) (index : Index)
    (leaf : FtsLeaf) (secret : Digest) : HashInput :=
  tweakableHashInput pk.parameter (.ftsLeaf index ⟨0, by decide⟩ leaf)
    (bytesLE 20 secret)

theorem firstFtsInput_eq (pk : SphincsSecurity.PublicKey) (index : Index)
    (leaf : FtsLeaf) (secret : Digest) :
    firstFtsInput pk index leaf secret =
      fieldBytes (tweakFields 9 0 index.val 0 leaf.val) ++
        bytesLE 20 pk.parameter ++ bytesLE 20 secret := by
  rfl

theorem firstFtsInput_length (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaf : FtsLeaf) (secret : Digest) :
    (firstFtsInput pk index leaf secret).length = 60 := by
  simp [firstFtsInput, tweakableHashInput, tweakBytes, hashDomainFields,
    fieldBytes, bytesLE]

theorem firstFtsInput_header (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaf : FtsLeaf) (secret : Digest)
    (i : Nat) (hi : i < 20) :
    ((firstFtsInput pk index leaf secret).map UInt8.toBitVec)[i]'(by
      rw [List.length_map, firstFtsInput_length]; omega) =
    ((fieldBytes (tweakFields 9 0 index.val 0 leaf.val)).map
      UInt8.toBitVec)[i]'(by simp [fieldBytes, bytesLE]; omega) := by
  simp only [firstFtsInput_eq, List.map_append]
  rw [
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega)]

theorem firstFtsInput_parameter (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaf : FtsLeaf) (secret : Digest)
    (i : Nat) (hi : i < 20) :
    ((firstFtsInput pk index leaf secret).map UInt8.toBitVec)[20 + i]'(by
      rw [List.length_map, firstFtsInput_length]; omega) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  simp only [firstFtsInput_eq, List.map_append]
  rw [
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [List.length_map, fieldBytes, bytesLE]
  rfl

theorem firstFtsInput_secret (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaf : FtsLeaf) (secret : Digest)
    (i : Nat) (hi : i < 20) :
    ((firstFtsInput pk index leaf secret).map UInt8.toBitVec)[40 + i]'(by
      rw [List.length_map, firstFtsInput_length]; omega) =
      secret.extractLsb' (8 * i) 8 := by
  simp only [firstFtsInput_eq, List.map_append]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [List.length_map, List.length_append, fieldBytes, bytesLE]
  rfl

theorem readyFirstFts_hashInput (pointers : MachineState)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (leaf : FtsLeaf) (secret : Digest)
    (source : pointers.getReg .x6 = 0x22cdc)
    (destination : pointers.getReg .x7 = 0x40028)
    (witnessPrefix : WitnessPrefix pointers pk)
    (secretEncoded : ∀ i, (hi : i < 20) →
      pointers.getByte (BitVec.ofNat 64 (0x22cdc + i)) =
        secret.extractLsb' (8 * i) 8)
    (layerZero : (ftsAdvanceState (copyRootState pointers)).getMem 0x43000 = 0)
    (positionZero : (ftsAdvanceState (copyRootState pointers)).getMem 0x43010 = 0)
    (treeIndex : (ftsAdvanceState (copyRootState pointers)).getMem 0x43008 =
      BitVec.ofNat 64 index.val)
    (leafIndex : (ftsAdvanceState (copyRootState pointers)).getMem 0x43018 =
      BitVec.ofNat 64 leaf.val) :
    hashInput (ftsHashReadyState (ftsAdvanceState (copyRootState pointers))) =
      toQuery (firstFtsInput pk index leaf secret) := by
  let advanced := ftsAdvanceState (copyRootState pointers)
  let ready := ftsHashReadyState advanced
  apply Serialization.hashInput_of_list ready 0x40000
    ((firstFtsInput pk index leaf secret).map UInt8.toBitVec)
  · exact (ftsHashReady_regs advanced).1
  · rw [(ftsHashReady_regs advanced).2.1,
      List.length_map, firstFtsInput_length]
    rfl
  · intro i hi
    have hi60 : i < 60 := by
      simpa [firstFtsInput_length] using hi
    by_cases header : i < 20
    · let byte : Fin 20 := ⟨i, header⟩
      have actual := readyHeader_bytes advanced index leaf
        layerZero positionZero treeIndex leafIndex byte
      have expected := firstFtsInput_header pk index leaf secret i header
      simpa [ready, advanced, byte] using actual.trans expected.symm
    · by_cases parameter : i < 40
      · have lower : 20 ≤ i := by omega
        have smaller : i - 20 < 20 := by omega
        have split : 20 + (i - 20) = i := by omega
        have actual := readyParameter_bytes pointers destination pk witnessPrefix
          (i - 20) smaller
        have expected := firstFtsInput_parameter pk index leaf secret
          (i - 20) smaller
        have joined := actual.trans expected.symm
        simp only [split] at joined
        have address : 0x40014 + (i - 20) = 0x40000 + i := by omega
        rw [address] at joined
        simpa only [ready, advanced] using joined
      · have lower : 40 ≤ i := by omega
        have smaller : i - 40 < 20 := by omega
        have split : 40 + (i - 40) = i := by omega
        have actual := readySecret_bytes pointers source destination secret
          secretEncoded (i - 40) smaller
        have expected := firstFtsInput_secret pk index leaf secret
          (i - 40) smaller
        have joined := actual.trans expected.symm
        simp only [split] at joined
        have address : 0x40028 + (i - 40) = 0x40000 + i := by omega
        rw [address] at joined
        simpa only [ready, advanced] using joined

theorem readyFirstFts_hashStep (hash : Hash) (pointers : MachineState)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (leaf : FtsLeaf) (secret : Digest)
    (pc : pointers.pc = 0x17c4)
    (source : pointers.getReg .x6 = 0x22cdc)
    (destination : pointers.getReg .x7 = 0x40028)
    (witnessPrefix : WitnessPrefix pointers pk)
    (secretEncoded : ∀ i, (hi : i < 20) →
      pointers.getByte (BitVec.ofNat 64 (0x22cdc + i)) =
        secret.extractLsb' (8 * i) 8)
    (layerZero : (ftsAdvanceState (copyRootState pointers)).getMem 0x43000 = 0)
    (positionZero : (ftsAdvanceState (copyRootState pointers)).getMem 0x43010 = 0)
    (treeIndex : (ftsAdvanceState (copyRootState pointers)).getMem 0x43008 =
      BitVec.ofNat 64 index.val)
    (leafIndex : (ftsAdvanceState (copyRootState pointers)).getMem 0x43018 =
      BitVec.ofNat 64 leaf.val)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash (ftsHashReadyState (ftsAdvanceState (copyRootState pointers)))
        (hash (toQuery (firstFtsInput pk index leaf secret)))) steps result) :
    Executes hash SphincsImages.verify
      (ftsHashReadyState (ftsAdvanceState (copyRootState pointers)))
      (steps + 1) (result.charge 8 1 1) := by
  let copied := copyRootState pointers
  let advanced := ftsAdvanceState copied
  let ready := ftsHashReadyState advanced
  have copiedPc := SphincsVerifierFtsLeafCopy.ftsLeafCopy_pc pointers pc
  have advancedPc := ftsAdvance_pc copied copiedPc
  have readyPc := ftsHashReady_pc advanced advancedPc
  have regs := ftsHashReady_regs advanced
  have query := readyFirstFts_hashInput pointers pk index leaf secret
    source destination witnessPrefix secretEncoded layerZero positionZero
    treeIndex leafIndex
  have tail' : Executes hash SphincsImages.verify
      (writeHash ready (hash (hashInput ready))) steps result := by
    rw [query]
    exact tail
  exact SphincsVerifierFtsHash.hash_step hash ready readyPc
    regs.1 regs.2.1 regs.2.2.1 regs.2.2.2 steps result tail'

def firstFtsPointers (state : MachineState) (answer : BitVec 256) : MachineState :=
  let initial := indexStoredState (indexValueState (writeHash state answer))
  let selected := leafStates initial 24 (by decide)
  let accepted := lastAcceptState selected
  let entered := ftsEntryState accepted
  let header := ftsTreeHeaderState entered
  ftsCopyPointers (ftsSelectState header)

theorem pointerWitnessPrefix (selection : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (witnessPrefix : WitnessPrefix selection pk) :
    WitnessPrefix (ftsCopyPointers selection) pk := by
  constructor
  · intro i hi
    simpa [MachineState.getByte, ftsCopyPointers_mem] using
      witnessPrefix.root i hi
  · intro i hi
    simpa [MachineState.getByte, ftsCopyPointers_mem] using
      witnessPrefix.parameter i hi

theorem pointerSecretBytes (selection : MachineState) (secret : Digest)
    (encoded : ∀ i, (hi : i < 20) →
      selection.getByte (BitVec.ofNat 64 (0x22cdc + i)) =
        secret.extractLsb' (8 * i) 8) :
    ∀ i, (hi : i < 20) →
      (ftsCopyPointers selection).getByte (BitVec.ofNat 64 (0x22cdc + i)) =
        secret.extractLsb' (8 * i) 8 := by
  intro i hi
  simpa [MachineState.getByte, ftsCopyPointers_mem] using encoded i hi

theorem messageReady_firstFts_hashInput (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer))
    (witnessPrefix : WitnessPrefix (firstFtsPointers state answer) pk)
    (secret : Digest)
    (secretEncoded : ∀ i, (hi : i < 20) →
      (firstFtsPointers state answer).getByte
        (BitVec.ofNat 64 (0x22cdc + i)) =
        secret.extractLsb' (8 * i) 8) :
    let pointers := firstFtsPointers state answer
    let advanced := ftsAdvanceState (copyRootState pointers)
    let final := ftsHashReadyState advanced
    OrdinarySteps SphincsImages.verify (writeHash state answer) 392 final ∧
      final.pc = 0x18c8 ∧
      hashInput final = toQuery (firstFtsInput pk
        (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest answer))
        (SphincsSecurity.Concrete.digestLeaves
          (SphincsSecurity.truncateMessageDigest answer) ⟨0, by decide⟩)
        secret) := by
  let pointers := firstFtsPointers state answer
  let advanced := ftsAdvanceState (copyRootState pointers)
  let index := SphincsSecurity.Concrete.digestIndex
    (SphincsSecurity.truncateMessageDigest answer)
  let leaf := SphincsSecurity.Concrete.digestLeaves
    (SphincsSecurity.truncateMessageDigest answer) ⟨0, by decide⟩
  obtain ⟨front, finalPc, _, _, _, _⟩ :=
    messageReady_admissible_ftsHashReady state pk message randomness
      ready pc answer admissible
  obtain ⟨_, _, source, destination, _, _⟩ :=
    messageReady_admissible_ftsCopyPointers state pk message randomness
      ready pc answer admissible
  obtain ⟨_, _, _, leafNat, treeIndex⟩ :=
    messageReady_admissible_ftsAdvance state pk message randomness
      ready pc answer admissible
  have layerZero : advanced.getMem 0x43000 = 0 :=
    messageReady_firstFts_layerZero state pk message randomness
      ready pc answer admissible
  have positionZero : advanced.getMem 0x43010 = 0 :=
    messageReady_firstFts_positionZero state pk message randomness
      ready pc answer
  have leafIndex : advanced.getMem 0x43018 = BitVec.ofNat 64 leaf.val := by
    apply BitVec.eq_of_toNat_eq
    have leafNat' : (advanced.getMem 0x43018).toNat = leaf.val := by
      simpa [advanced, pointers, firstFtsPointers, leaf, abstractLeaf] using leafNat
    have small : leaf.val < 2 ^ 64 := by
      have h := leaf.isLt
      simp only [SphincsSecurity.FtsLeaf, SphincsSecurity.ftsTreeHeight] at h
      omega
    rw [leafNat']
    simp [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by simpa using small)]
  have query := readyFirstFts_hashInput pointers pk index leaf secret
    source destination witnessPrefix secretEncoded layerZero positionZero
    treeIndex leafIndex
  exact ⟨front, finalPc, query⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsQuery.readyFirstFts_hashInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms readyFirstFts_hashInput

/-- info: 'SigGolfCandidate.SphincsVerifierFtsQuery.readyFirstFts_hashStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms readyFirstFts_hashStep

/-- info: 'SigGolfCandidate.SphincsVerifierFtsQuery.messageReady_firstFts_hashInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_firstFts_hashInput

end SigGolfCandidate.SphincsVerifierFtsQuery
