import SigGolfCandidate.SphincsVerifierFtsForestRoots
import SigGolfCandidate.SphincsVerifierFtsLoadedFirstTree

namespace SigGolfCandidate.SphincsVerifierFtsLeafQueryTree
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsHeader
open SigGolfCandidate.SphincsVerifierFtsHeaderFields
open SigGolfCandidate.SphincsVerifierFtsPayload
open SigGolfCandidate.SphincsVerifierFtsSetup
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierFtsGenericCopyData
open SigGolfCandidate.SphincsVerifierFtsAdvance
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierSecondHashBytes
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierFtsNextTreeSetup
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierFtsTreeControlStep
open SigGolfCandidate.SphincsVerifierFtsTreeWitnessStep
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsNextPointer
open SigGolfCandidate.SphincsVerifierFtsPersistentIndex
open SigGolfCandidate.SphincsVerifierFtsSelectorFrame
open SigGolfCandidate.SphincsVerifierFtsGenericInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsForestReady
open SigGolfCandidate.SphincsVerifierFtsForestRoots
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def leafInput (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf) (secret : Digest) : HashInput :=
  tweakableHashInput pk.parameter (.ftsLeaf index tree leaf)
    (bytesLE 20 secret)

theorem leafInput_first (pk : SphincsSecurity.PublicKey) (index : Index)
    (leaf : FtsLeaf) (secret : Digest) :
    leafInput pk ⟨0, by decide⟩ index leaf secret =
      SphincsVerifierFtsQuery.firstFtsInput pk index leaf secret := rfl

/-- The loader's certified first FORS query uses the same encoding as every
    later tree's query. -/
theorem loaded_honest_first_leaf_query
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
    ∃ final : MachineState,
      hashInput final = toQuery
        (leafInput inner ⟨0, by decide⟩
          (SphincsSecurity.Concrete.digestIndex
            (SphincsSecurity.truncateMessageDigest digestAnswer))
          (SphincsSecurity.Concrete.digestLeaves
            (SphincsSecurity.truncateMessageDigest digestAnswer)
            ⟨0, by decide⟩)
          (signature.ftsSecret ⟨0, by decide⟩)) := by
  obtain ⟨ready, final, _, _, _, _, _, _, _, query, _, _⟩ :=
    SphincsVerifierFtsEarlyFrame.loaded_honest_firstFts_query
      publicKey message inner signature state commitmentAnswer digestAnswer
      loaded answerMatches admissible
  exact ⟨final, by simpa only [leafInput_first] using query⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLeafQueryTree.loaded_honest_first_leaf_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_first_leaf_query

/-- The digest-entry trace establishes all persistent controls for tree zero. -/
theorem messageReady_first_controls (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : SphincsVerifierMessageHash.MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest answer)) :
    let digest := SphincsSecurity.truncateMessageDigest answer
    let index := SphincsSecurity.Concrete.digestIndex digest
    let leaves : FtsTree → FtsLeaf := fun slot =>
      SphincsSecurity.Concrete.digestLeaves digest
        (slot.castLE (Nat.sub_le ftsTrees 1))
    let initial := SphincsVerifierIndexStore.indexStoredState
      (SphincsVerifierIndexPrefix.indexValueState (writeHash state answer))
    let entered := SphincsVerifierFtsEntry.ftsEntryState
      (SphincsVerifierLastLeaf.lastAcceptState
        (SphincsVerifierLeavesTrace.leafStates initial 24 (by decide)))
    ReadyControls (nextTreeHashState entered) index leaves
      ⟨0, by decide⟩ := by
  let digest := SphincsSecurity.truncateMessageDigest answer
  let index := SphincsSecurity.Concrete.digestIndex digest
  let leaves : FtsTree → FtsLeaf := fun slot =>
    SphincsSecurity.Concrete.digestLeaves digest
      (slot.castLE (Nat.sub_le ftsTrees 1))
  let initial := SphincsVerifierIndexStore.indexStoredState
    (SphincsVerifierIndexPrefix.indexValueState (writeHash state answer))
  let entered := SphincsVerifierFtsEntry.ftsEntryState
    (SphincsVerifierLastLeaf.lastAcceptState
      (SphincsVerifierLeavesTrace.leafStates initial 24 (by decide)))
  obtain ⟨_, entryPc, counter, source, selectorNat⟩ :=
    SphincsVerifierFtsEntry.messageReady_admissible_ftsEntry
      state pk message randomness ready pc answer admissible
  have savedIndex : entered.getMem 0x43078 =
      BitVec.ofNat 64 index.val := by
    exact SphincsVerifierFtsEntry.messageReady_ftsEntry_msgIndex
      state pk message randomness ready pc answer
  have selectorByte (slot : FtsTree) :
      entered.getByte (BitVec.ofNat 64 (0x44800 + slot.val)) =
        BitVec.ofNat 8 (leaves slot).val := by
    apply BitVec.eq_of_toNat_eq
    rw [selectorNat slot]
    change (leaves slot).val = _
    simp only [BitVec.toNat_ofNat]
    have small := (leaves slot).isLt
    simp only [ftsTreeHeight] at small
    omega
  have controls := SphincsVerifierFtsNextReadyControls.nextTreeHashState_controls
    entered ⟨0, by decide⟩ index (leaves ⟨0, by decide⟩)
    entryPc counter source savedIndex (selectorByte ⟨0, by decide⟩)
  refine {
    pc := controls.1
    source := controls.2.1
    bits := controls.2.2.1
    destination := controls.2.2.2.1
    service := controls.2.2.2.2.1
    counter := controls.2.2.2.2.2.1
    treeCell := controls.2.2.2.2.2.2.1
    indexCell := controls.2.2.2.2.2.2.2.1
    selector := controls.2.2.2.2.2.2.2.2.1
    pointer := controls.2.2.2.2.2.2.2.2.2
    savedIndex := ?_
    selectorTable := ?_ }
  · exact (SphincsVerifierFtsPersistentIndex.nextTreeSetup_savedIndex_frame entered).trans
      savedIndex
  · intro slot
    exact (SphincsVerifierFtsSelectorFrame.nextTreeSetup_selector_byte_frame
      entered slot).trans (selectorByte slot)

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLeafQueryTree.messageReady_first_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_first_controls

private theorem ordinary_deterministic {image : Image}
    {start left right : MachineState} {n : Nat}
    (first : OrdinarySteps image start n left)
    (second : OrdinarySteps image start n right) : left = right := by
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

/-- A loaded honest signature enters the 24-tree forest with all query,
    control, and witness invariants. -/
theorem loaded_honest_firstReady
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (inner : SphincsSecurity.PublicKey) (signature : Signature)
    (state : MachineState) (commitmentAnswer digestAnswer : BitVec 256)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire inner signature) =
        some state)
    (answerMatches : ∀ index : Fin 2,
      commitmentAnswer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest digestAnswer)) :
    let digest := SphincsSecurity.truncateMessageDigest digestAnswer
    let index := SphincsSecurity.Concrete.digestIndex digest
    let leaves : FtsTree → FtsLeaf := fun slot =>
      SphincsSecurity.Concrete.digestLeaves digest
        (slot.castLE (Nat.sub_le ftsTrees 1))
    ∃ ready final,
      OrdinarySteps SphincsImages.verify
        (writeHash (SphincsVerifierHashSetup.firstHashState state)
          commitmentAnswer) 107 ready ∧
      OrdinarySteps SphincsImages.verify
        (writeHash ready digestAnswer) 392 final ∧
      ReadyInv final signature inner index leaves ⟨0, by decide⟩ ∧
      hashInput final = toQuery (leafInput inner ⟨0, by decide⟩ index
        (leaves ⟨0, by decide⟩)
        (signature.ftsSecret ⟨0, by decide⟩)) := by
  let digest := SphincsSecurity.truncateMessageDigest digestAnswer
  let index := SphincsSecurity.Concrete.digestIndex digest
  let leaves : FtsTree → FtsLeaf := fun slot =>
    SphincsSecurity.Concrete.digestLeaves digest
      (slot.castLE (Nat.sub_le ftsTrees 1))
  obtain ⟨ready, tr107, readyPc, messageReady, _, _⟩ :=
    SphincsVerifierFtsEarlyFrame.loaded_honest_message_ready_with_witness
      publicKey message inner signature state commitmentAnswer loaded
      answerMatches
  obtain ⟨otherReady, final, otherTr107, tr392, _, _, _, _, _, _, _, _, _,
    query, hprefix, witness⟩ :=
    SphincsVerifierFtsLoadedFirstTree.loaded_honest_firstFts_ready
      publicKey message inner signature state commitmentAnswer digestAnswer
      loaded answerMatches admissible
  have readyEq : otherReady = ready := ordinary_deterministic otherTr107 tr107
  subst otherReady
  let initial := SphincsVerifierIndexStore.indexStoredState
    (SphincsVerifierIndexPrefix.indexValueState (writeHash ready digestAnswer))
  let entered := SphincsVerifierFtsEntry.ftsEntryState
    (SphincsVerifierLastLeaf.lastAcceptState
      (SphincsVerifierLeavesTrace.leafStates initial 24 (by decide)))
  obtain ⟨tr293, entryPc, counter, source, _⟩ :=
    SphincsVerifierFtsEntry.messageReady_admissible_ftsEntry
      ready inner message signature.randomness messageReady readyPc
      digestAnswer admissible
  have tr99 := SphincsVerifierFtsNextTreeSetup.nextTreeSetup_block
    entered ⟨0, by decide⟩ entryPc counter source
  have tr392' : OrdinarySteps SphincsImages.verify
      (writeHash ready digestAnswer) 392 (nextTreeHashState entered) := by
    simpa only [show 293 + 99 = 392 by decide] using tr293.append tr99
  have finalEq : final = nextTreeHashState entered :=
    ordinary_deterministic tr392 tr392'
  have controls := messageReady_first_controls ready inner message
    signature.randomness messageReady readyPc digestAnswer admissible
  refine ⟨ready, final, tr107, tr392,
    { controls := ?_, witness := witness, publicKey := hprefix }, ?_⟩
  · simpa only [finalEq] using controls
  · simpa [leafInput_first, leaves, Fin.castLE] using query

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLeafQueryTree.loaded_honest_firstReady' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_firstReady

theorem leafInput_eq (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf) (secret : Digest) :
    leafInput pk tree index leaf secret =
      fieldBytes (tweakFields 9 tree.val index.val 0 leaf.val) ++
        bytesLE 20 pk.parameter ++ bytesLE 20 secret := rfl

theorem leafInput_length (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf) (secret : Digest) :
    (leafInput pk tree index leaf secret).length = 60 := by
  simp [leafInput_eq, fieldBytes, tweakFields, bytesLE]

theorem leafInput_header (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf) (secret : Digest)
    (i : Nat) (hi : i < 20) :
    ((leafInput pk tree index leaf secret).map UInt8.toBitVec)[i]'(by
      rw [List.length_map, leafInput_length]; omega) =
    ((fieldBytes (tweakFields 9 tree.val index.val 0 leaf.val)).map
      UInt8.toBitVec)[i]'(by simp [fieldBytes, bytesLE]; omega) := by
  simp only [leafInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega)]

theorem leafInput_parameter (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf) (secret : Digest)
    (i : Nat) (hi : i < 20) :
    ((leafInput pk tree index leaf secret).map UInt8.toBitVec)[20 + i]'(by
      rw [List.length_map, leafInput_length]; omega) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  simp only [leafInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [List.length_map, fieldBytes, bytesLE]
  rfl

theorem leafInput_secret (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf) (secret : Digest)
    (i : Nat) (hi : i < 20) :
    ((leafInput pk tree index leaf secret).map UInt8.toBitVec)[40 + i]'(by
      rw [List.length_map, leafInput_length]; omega) =
      secret.extractLsb' (8 * i) 8 := by
  simp only [leafInput_eq, List.map_append]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [List.length_map, List.length_append, fieldBytes, bytesLE]
  rfl

theorem tag_value_tree (state : MachineState) (tree : FtsTree)
    (treeCell : state.getMem 0x43000 = BitVec.ofNat 64 tree.val) :
    (tagState state).getWord32 0x40000 =
      BitVec.ofNat 32 (0x901 + 0x10000 * tree.val) := by
  simp [tagState, tagBeforeStore, execInstrBr, signExtend12,
    getWord32_setWord32_same,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  have value : state.getMem (274432#64) = BitVec.ofNat 64 tree.val := by
    have address : (274432#64) = (0x43000 : Word) := by decide
    rw [address]
    exact treeCell
  rw [value]
  fin_cases tree <;> decide

theorem ready_tag_tree (state : MachineState) (tree : FtsTree)
    (treeCell : state.getMem 0x43000 = BitVec.ofNat 64 tree.val) :
    (ftsHashReadyState state).getWord32 0x40000 =
      BitVec.ofNat 32 (0x901 + 0x10000 * tree.val) := by
  let tagged := tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  rw [ready_header_word_frame state 0x40000
    (by intro offset; fin_cases offset <;> decide)]
  change (SphincsVerifierHeader.indexState treed).getWord32 0x40000 = _
  rw [SphincsVerifierHashMemory.index_word_frame treed 0x40000 treePointer
      (by decide),
    SphincsVerifierHashMemory.tree_word_frame positioned 0x40000
      positionPointer (by decide),
    SphincsVerifierHashMemory.position_word_frame tagged 0x40000
      tagPointer (by decide)]
  exact tag_value_tree state tree treeCell

theorem ready_tag_byte_tree (state : MachineState) (tree : FtsTree)
    (treeCell : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (byte : Fin 4) :
    (ftsHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      (BitVec.ofNat 32 (0x901 + 0x10000 * tree.val)).extractLsb'
        (8 * byte.val) 8 := by
  have split := variableWord_byte (ftsHashReadyState state) 0x40000
    (by decide) (by decide) 0 byte
  have value := ready_tag_tree state tree treeCell
  simpa using split.trans (congrArg (fun result : BitVec 32 =>
    result.extractLsb' (8 * byte.val) 8) value)

theorem tag_byte_expected (tree : FtsTree) (index : Index)
    (leaf : FtsLeaf) (byte : Fin 4) :
    (BitVec.ofNat 32 (0x901 + 0x10000 * tree.val)).extractLsb'
      (8 * byte.val) 8 =
      ((fieldBytes (tweakFields 9 tree.val index.val 0 leaf.val)).map
        UInt8.toBitVec)[byte.val]'(by
          have h := byte.isLt
          simp [fieldBytes, tweakFields, bytesLE]
          omega) := by
  fin_cases tree <;> fin_cases byte <;>
    simp [fieldBytes, tweakFields, protocolDomainSep, bytesLE] <;> decide

set_option maxHeartbeats 0 in
theorem readyHeader_bytes_tree (state : MachineState) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf)
    (treeCell : state.getMem 0x43000 = BitVec.ofNat 64 tree.val)
    (positionZero : state.getMem 0x43010 = 0)
    (indexCell : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (byte : Fin 20) :
    (ftsHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      ((fieldBytes (tweakFields 9 tree.val index.val 0 leaf.val)).map
        UInt8.toBitVec)[byte.val]'(by
          simp [fieldBytes, tweakFields, bytesLE]) := by
  fin_cases byte <;>
    first
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        (ready_tag_byte_tree state tree treeCell 0).trans
        (tag_byte_expected tree index leaf 0)
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        (ready_tag_byte_tree state tree treeCell 1).trans
        (tag_byte_expected tree index leaf 1)
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        (ready_tag_byte_tree state tree treeCell 2).trans
        (tag_byte_expected tree index leaf 2)
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        (ready_tag_byte_tree state tree treeCell 3).trans
        (tag_byte_expected tree index leaf 3)
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_positionByte state positionZero 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_positionByte state positionZero 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_positionByte state positionZero 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_positionByte state positionZero 3
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_treeByte state index indexCell 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_treeByte state index indexCell 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_treeByte state index indexCell 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_treeByte state index indexCell 3
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_treeByte state index indexCell 4
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_treeByte state index indexCell 5
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_treeByte state index indexCell 6
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_treeByte state index indexCell 7
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_indexByte state leaf leafCell 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_indexByte state leaf leafCell 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_indexByte state leaf leafCell 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        SigGolfCandidate.SphincsVerifierFtsPayload.readyHeader_indexByte state leaf leafCell 3

theorem readySecret_bytes_variable (pointers : MachineState)
    (sourceBase : Nat) (small : sourceBase + 20 ≤ 0x40000)
    (aligned : sourceBase % 4 = 0)
    (source : pointers.getReg .x6 = BitVec.ofNat 64 sourceBase)
    (destination : pointers.getReg .x7 = 0x40028)
    (secret : Digest)
    (encoded : ∀ i, (hi : i < 20) →
      pointers.getByte (BitVec.ofNat 64 (sourceBase + i)) =
        secret.extractLsb' (8 * i) 8)
    (i : Nat) (hi : i < 20) :
    (ftsHashReadyState (ftsAdvanceState (copyRootState pointers))).getByte
      (BitVec.ofNat 64 (0x40028 + i)) =
      secret.extractLsb' (8 * i) 8 := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  calc
    _ = (ftsHashReadyState (ftsAdvanceState (copyRootState pointers))).getByte
          (BitVec.ofNat 64 (0x40028 + 4 * index.val + byte.val)) := by
      simpa only [Nat.add_assoc, split]
    _ = ((ftsHashReadyState (ftsAdvanceState (copyRootState pointers))).getWord32
          (BitVec.ofNat 64 (0x40028 + 4 * index.val))).extractLsb'
            (8 * byte.val) 8 :=
      word32_byte _ 0x40028 (Or.inr (Or.inl rfl)) index byte
    _ = (pointers.getWord32
          (BitVec.ofNat 64 (sourceBase + 4 * index.val))).extractLsb'
            (8 * byte.val) 8 := by
      rw [ready_secret_word_frame, advanced_secret_word_frame]
      exact congrArg (fun word : BitVec 32 =>
        word.extractLsb' (8 * byte.val) 8)
        (copyRoot_data_belowHash pointers sourceBase 0x40028 small
          (Or.inl rfl) source destination index)
    _ = pointers.getByte
          (BitVec.ofNat 64 (sourceBase + 4 * index.val + byte.val)) :=
      (variableWord_byte pointers sourceBase (by omega) aligned index byte).symm
    _ = secret.extractLsb' (8 * i) 8 := by
      simpa only [Nat.add_assoc, split] using encoded i hi

theorem readyLeaf_hashInput (pointers : MachineState)
    (pk : SphincsSecurity.PublicKey) (tree : FtsTree)
    (index : Index) (leaf : FtsLeaf) (secret : Digest)
    (source : pointers.getReg .x6 =
      BitVec.ofNat 64 (0x22cdc + 180 * tree.val))
    (destination : pointers.getReg .x7 = 0x40028)
    (witnessPrefix : WitnessPrefix pointers pk)
    (secretEncoded : ∀ i, (hi : i < 20) →
      pointers.getByte
        (BitVec.ofNat 64 (0x22cdc + 180 * tree.val + i)) =
          secret.extractLsb' (8 * i) 8)
    (treeCell : (ftsAdvanceState (copyRootState pointers)).getMem
      0x43000 = BitVec.ofNat 64 tree.val)
    (positionZero : (ftsAdvanceState (copyRootState pointers)).getMem
      0x43010 = 0)
    (indexCell : (ftsAdvanceState (copyRootState pointers)).getMem
      0x43008 = BitVec.ofNat 64 index.val)
    (leafCell : (ftsAdvanceState (copyRootState pointers)).getMem
      0x43018 = BitVec.ofNat 64 leaf.val) :
    hashInput
        (ftsHashReadyState (ftsAdvanceState (copyRootState pointers))) =
      toQuery (leafInput pk tree index leaf secret) := by
  let advanced := ftsAdvanceState (copyRootState pointers)
  let ready := ftsHashReadyState advanced
  apply Serialization.hashInput_of_list ready 0x40000
    ((leafInput pk tree index leaf secret).map UInt8.toBitVec)
  · exact (ftsHashReady_regs advanced).1
  · rw [(ftsHashReady_regs advanced).2.1,
      List.length_map, leafInput_length]
    rfl
  · intro i hi
    have hi60 : i < 60 := by
      simpa [leafInput_length] using hi
    by_cases header : i < 20
    · let byte : Fin 20 := ⟨i, header⟩
      have actual := readyHeader_bytes_tree advanced tree index leaf
        treeCell positionZero indexCell leafCell byte
      have expected := leafInput_header pk tree index leaf secret i header
      simpa [ready, advanced, byte] using actual.trans expected.symm
    · by_cases parameter : i < 40
      · have smaller : i - 20 < 20 := by omega
        have split : 20 + (i - 20) = i := by omega
        have actual := readyParameter_bytes pointers destination pk witnessPrefix
          (i - 20) smaller
        have expected := leafInput_parameter pk tree index leaf secret
          (i - 20) smaller
        have joined := actual.trans expected.symm
        simp only [split] at joined
        have address : 0x40014 + (i - 20) = 0x40000 + i := by omega
        rw [address] at joined
        simpa only [ready, advanced] using joined
      · have smaller : i - 40 < 20 := by omega
        have split : 40 + (i - 40) = i := by omega
        have sourceSmall : 0x22cdc + 180 * tree.val + 20 ≤ 0x40000 := by
          have bound := tree.isLt
          norm_num [ftsTrees] at bound
          omega
        have sourceAligned : (0x22cdc + 180 * tree.val) % 4 = 0 := by
          omega
        have actual := readySecret_bytes_variable pointers
          (0x22cdc + 180 * tree.val) sourceSmall sourceAligned source
          destination secret secretEncoded (i - 40) smaller
        have expected := leafInput_secret pk tree index leaf secret
          (i - 40) smaller
        have joined := actual.trans expected.symm
        simp only [split] at joined
        have address : 0x40028 + (i - 40) = 0x40000 + i := by omega
        rw [address] at joined
        simpa only [ready, advanced] using joined

private theorem low_ne (read written : Word)
    (low : read.toNat < 0x40000)
    (high : 0x40000 ≤ written.toNat) : read ≠ written := by
  intro equal
  have same := congrArg BitVec.toNat equal
  omega

theorem nextTreePointers_low_mem_frame (state : MachineState)
    (read : Word) (low : read.toNat < 0x40000) :
    (ftsCopyPointers (ftsSelectState (ftsTreeHeaderState state))).getMem
      read = state.getMem read := by
  let header := ftsTreeHeaderState state
  let selected := ftsSelectState header
  rw [ftsCopyPointers_mem selected read,
    ftsSelect_mem_frame header read
      (low_ne read 0x43010 low (by decide))
      (low_ne read 0x43020 low (by decide))
      (low_ne read 0x43070 low (by decide)),
    ftsTreeHeader_mem_frame state read
      (low_ne read 0x43000 low (by decide))
      (low_ne read 0x43008 low (by decide))]

theorem nextTreePointers_low_byte_frame (state : MachineState)
    (i : Nat) (hi : i < SphincsWire.signatureBytes) :
    (ftsCopyPointers (ftsSelectState (ftsTreeHeaderState state))).getByte
      (BitVec.ofNat 64 (0x22ca0 + i)) =
      state.getByte (BitVec.ofNat 64 (0x22ca0 + i)) := by
  simp only [MachineState.getByte]
  rw [nextTreePointers_low_mem_frame state _
    (witnessByte_aligned_low i hi)]

theorem nextTreePointers_prefix (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (hprefix : WitnessPrefix state pk) :
    WitnessPrefix
      (ftsCopyPointers (ftsSelectState (ftsTreeHeaderState state))) pk := by
  constructor
  · intro i hi
    exact (nextTreePointers_low_byte_frame state i (by
      rw [SphincsWire.signatureBytes_eq]; omega)).trans (hprefix.root i hi)
  · intro i hi
    have frame := nextTreePointers_low_byte_frame state (20 + i) (by
      rw [SphincsWire.signatureBytes_eq]; omega)
    have address : 0x22ca0 + (20 + i) = 0x22cb4 + i := by omega
    rw [address] at frame
    exact frame.trans (hprefix.parameter i hi)

theorem nextTreePointers_secret (state : MachineState)
    (signature : Signature) (tree : FtsTree)
    (witness : FtsWitness state signature)
    (i : Nat) (hi : i < 20) :
    (ftsCopyPointers (ftsSelectState (ftsTreeHeaderState state))).getByte
      (BitVec.ofNat 64 (0x22cdc + 180 * tree.val + i)) =
      (signature.ftsSecret tree).extractLsb' (8 * i) 8 := by
  have offset : 0x22cdc + 180 * tree.val + i =
      0x22ca0 + (60 + tree.val * SphincsWire.ftsOpeningBytes + i) := by
    simp [SphincsWire.ftsOpeningBytes, SphincsWire.digestBytes,
      ftsTreeHeight]
    omega
  rw [offset]
  have bound : 60 + tree.val * SphincsWire.ftsOpeningBytes + i <
      SphincsWire.signatureBytes := by
    have htree := tree.isLt
    rw [SphincsWire.signatureBytes_eq]
    norm_num [ftsTrees, SphincsWire.ftsOpeningBytes,
      SphincsWire.digestBytes, ftsTreeHeight] at *
    omega
  exact (nextTreePointers_low_byte_frame state _ bound).trans
    (witness.secret tree i hi)

theorem nextTreeSetup_hashInput (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (signature : Signature)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (source : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x22cdc + 180 * tree.val))
    (savedIndex : state.getMem 0x43078 = BitVec.ofNat 64 index.val)
    (selectorByte : state.getByte
      (BitVec.ofNat 64 (0x44800 + tree.val)) =
        BitVec.ofNat 8 leaf.val)
    (hprefix : WitnessPrefix state pk)
    (witness : FtsWitness state signature) :
    hashInput (nextTreeHashState state) =
      toQuery (leafInput pk tree index leaf (signature.ftsSecret tree)) := by
  let header := ftsTreeHeaderState state
  let selected := ftsSelectState header
  let pointers := ftsCopyPointers selected
  let copied := copyRootState pointers
  let advanced := ftsAdvanceState copied
  have headerCounter : header.getMem 0x43040 =
      BitVec.ofNat 64 tree.val := by
    rw [ftsTreeHeader_mem_frame state 0x43040 (by decide) (by decide)]
    exact counter
  have headerCells := ftsTreeHeader_cells state
  have selectedLeaf := ftsSelect_leaf header tree headerCounter
  have sourceReg : pointers.getReg .x6 =
      BitVec.ofNat 64 (0x22cdc + 180 * tree.val) := by
    rw [(ftsCopyPointers_regs selected).1,
      ftsSelect_mem_frame header 0x43028 (by decide) (by decide) (by decide),
      ftsTreeHeader_mem_frame state 0x43028 (by decide) (by decide)]
    exact source
  have destinationReg : pointers.getReg .x7 = 0x40028 :=
    (ftsCopyPointers_regs selected).2
  have copiedFrame (address : Word)
      (outside : ∀ offset : Fin 5,
        address ≠ alignToDword
          (pointers.getReg .x7 + signExtend12
            (4#12 * BitVec.ofNat 12 offset.val))) :
      copied.getMem address = selected.getMem address := by
    rw [SphincsVerifierCopyMemory.copyRoot_mem_frame pointers address outside,
      ftsCopyPointers_mem selected address]
  have outside (address : Word)
      (admissible : address = 0x43000 ∨ address = 0x43008 ∨
        address = 0x43010 ∨ address = 0x43020) :
      ∀ offset : Fin 5,
        address ≠ alignToDword
          (pointers.getReg .x7 + signExtend12
            (4#12 * BitVec.ofNat 12 offset.val)) := by
    rcases admissible with h | h | h | h <;> subst address
    all_goals intro offset
    all_goals rw [destinationReg]
    all_goals fin_cases offset <;> decide
  have treeCell : advanced.getMem 0x43000 =
      BitVec.ofNat 64 tree.val := by
    rw [ftsAdvance_mem_frame copied 0x43000 (by decide) (by decide),
      copiedFrame 0x43000 (outside 0x43000 (Or.inl rfl)),
      ftsSelect_mem_frame header 0x43000 (by decide) (by decide) (by decide),
      headerCells.1, counter]
  have positionZero : advanced.getMem 0x43010 = 0 := by
    rw [ftsAdvance_mem_frame copied 0x43010 (by decide) (by decide),
      copiedFrame 0x43010 (outside 0x43010 (Or.inr (Or.inr (Or.inl rfl))))]
    exact ftsSelect_position header
  have indexCell : advanced.getMem 0x43008 =
      BitVec.ofNat 64 index.val := by
    rw [ftsAdvance_mem_frame copied 0x43008 (by decide) (by decide),
      copiedFrame 0x43008 (outside 0x43008 (Or.inr (Or.inl rfl))),
      ftsSelect_mem_frame header 0x43008 (by decide) (by decide) (by decide),
      headerCells.2, savedIndex]
  have leafCell : advanced.getMem 0x43018 =
      BitVec.ofNat 64 leaf.val := by
    rw [(ftsAdvance_cells copied).2,
      copiedFrame 0x43020 (outside 0x43020 (Or.inr (Or.inr (Or.inr rfl)))),
      selectedLeaf.1, ftsTreeHeader_selector_byte state tree, selectorByte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have h := leaf.isLt
    simp only [ftsTreeHeight] at h
    omega
  have pointersPrefix := nextTreePointers_prefix state pk hprefix
  have pointersSecret := nextTreePointers_secret state signature tree witness
  exact readyLeaf_hashInput pointers pk tree index leaf
    (signature.ftsSecret tree) sourceReg destinationReg pointersPrefix
    pointersSecret treeCell positionZero indexCell leafCell

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLeafQueryTree.nextTreeSetup_hashInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nextTreeSetup_hashInput

theorem ReadyInv.next_leaf_query (hash : Hash) (state : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf) (tree : FtsTree)
    (inv : ReadyInv state signature pk index leaves tree)
    (next : tree.val + 1 < ftsTrees - 1) :
    let successor : FtsTree := ⟨tree.val + 1, next⟩
    hashInput
        (nextReadyState hash state signature pk tree index (leaves tree)) =
      toQuery (leafInput pk successor index (leaves successor)
        (signature.ftsSecret successor)) := by
  let leaf := leaves tree
  let answer := hash (hashInput state)
  let start := firstLeafStartState state answer
  let path := (parentPathRun hash pk signature tree index leaf start
    (truncateHash answer) 8).1
  let finished := treeFinishState path
  let successor : FtsTree := ⟨tree.val + 1, next⟩
  have initial := leafInitialInv state answer signature pk tree index leaf
    inv.controls.pc inv.controls.source inv.controls.bits
    inv.controls.destination inv.controls.pointer inv.controls.selector
    inv.controls.treeCell inv.controls.indexCell inv.publicKey inv.witness
  have pathProof := parentPathRun_finish hash pk signature tree index leaf
    start (truncateHash answer) initial
  have pathCounter : path.getMem 0x43040 =
      BitVec.ofNat 64 tree.val := by
    calc
      _ = start.getMem 0x43040 :=
        parentPathRun_counter_frame hash pk signature tree index leaf start
          (truncateHash answer) 8
      _ = state.getMem 0x43040 :=
        SphincsVerifierFtsLevelInit.levelStart_counter_frame state answer
          inv.controls.destination
      _ = BitVec.ofNat 64 tree.val := inv.controls.counter
  have finishedCounter : finished.getMem 0x43040 =
      BitVec.ofNat 64 successor.val :=
    treeFinish_counter path tree pathCounter
  have finishedSource : finished.getMem 0x43028 =
      BitVec.ofNat 64 (0x22cdc + 180 * successor.val) :=
    treeFinish_next_source hash state signature pk tree index leaf
      inv.controls.counter inv.controls.destination inv.controls.pointer
  have finishedIndex : finished.getMem 0x43078 =
      BitVec.ofNat 64 index.val :=
    (treeProcess_savedIndex_frame hash state signature pk tree index leaf
      inv.controls.counter inv.controls.destination).trans inv.controls.savedIndex
  have finishedSelector : finished.getByte
      (BitVec.ofNat 64 (0x44800 + successor.val)) =
        BitVec.ofNat 8 (leaves successor).val :=
    (treeProcess_selector_byte_frame hash state signature pk tree index leaf
      inv.controls.counter inv.controls.destination successor).trans
        (inv.controls.selectorTable successor)
  have finishedWitness : FtsWitness finished signature :=
    treeFinish_witness path signature tree pathCounter pathProof.2.2.1
  have finishedPrefix : WitnessPrefix finished pk :=
    treeFinish_prefix path pk tree pathCounter pathProof.2.2.2
  exact nextTreeSetup_hashInput finished pk signature successor index
    (leaves successor) finishedCounter finishedSource finishedIndex
    finishedSelector finishedPrefix finishedWitness

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLeafQueryTree.ReadyInv.next_leaf_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ReadyInv.next_leaf_query

theorem forestReady_leaf_query (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩)
    (initialQuery : hashInput initial =
      toQuery (leafInput pk ⟨0, by decide⟩ index
        (leaves ⟨0, by decide⟩)
        (signature.ftsSecret ⟨0, by decide⟩)))
    (n : Nat) (hn : n < ftsTrees - 1) :
    let tree : FtsTree := ⟨n, hn⟩
    hashInput (forestReady hash initial signature pk index leaves n) =
      toQuery (leafInput pk tree index (leaves tree)
        (signature.ftsSecret tree)) := by
  cases n with
  | zero =>
      simpa only [forestReady] using initialQuery
  | succ n =>
      have before : n < ftsTrees - 1 := by omega
      let state := forestReady hash initial signature pk index leaves n
      let tree : FtsTree := ⟨n, before⟩
      have inv := forestReady_inv hash initial signature pk index leaves
        initialInv n before
      have query := ReadyInv.next_leaf_query hash state signature pk index
        leaves tree inv hn
      have treeEq :
          (⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩ : FtsTree) =
            tree := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt before
      change hashInput
          (nextReadyState hash state signature pk
            ⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩ index
            (leaves ⟨n % (ftsTrees - 1), Nat.mod_lt _ (by decide)⟩)) =
        toQuery (leafInput pk ⟨n + 1, hn⟩ index
          (leaves ⟨n + 1, hn⟩)
          (signature.ftsSecret ⟨n + 1, hn⟩))
      rw [treeEq]
      exact query

def schemeTreeValue (hash : Hash) (signature : Signature)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (leaves : FtsTree → FtsLeaf) (tree : FtsTree) : Digest :=
  SphincsSecurity.Concrete.ftsFoldValue (adaptOracle hash) pk.parameter
    index tree (leaves tree) (signature.ftsPath tree)
    (truncateHash (adaptOracle hash
      (leafInput pk tree index (leaves tree) (signature.ftsSecret tree)))) 8

theorem treeValue_eq_scheme (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩)
    (initialQuery : hashInput initial =
      toQuery (leafInput pk ⟨0, by decide⟩ index
        (leaves ⟨0, by decide⟩)
        (signature.ftsSecret ⟨0, by decide⟩)))
    (tree : FtsTree) :
    treeValue hash initial signature pk index leaves tree =
      schemeTreeValue hash signature pk index leaves tree := by
  have query := forestReady_leaf_query hash initial signature pk index leaves
    initialInv initialQuery tree.val tree.isLt
  change SphincsSecurity.Concrete.ftsFoldValue (adaptOracle hash) pk.parameter
      index tree (leaves tree) (signature.ftsPath tree)
        (truncateHash (hash (hashInput
          (forestReady hash initial signature pk index leaves tree.val)))) 8 =
    SphincsSecurity.Concrete.ftsFoldValue (adaptOracle hash) pk.parameter
      index tree (leaves tree) (signature.ftsPath tree)
        (truncateHash (adaptOracle hash
          (leafInput pk tree index (leaves tree)
            (signature.ftsSecret tree)))) 8
  have query' : hashInput
      (forestReady hash initial signature pk index leaves tree.val) =
        toQuery (leafInput pk tree index (leaves tree)
          (signature.ftsSecret tree)) := by
    simpa only using query
  rw [query']
  rfl

/-- Every stored root equals the abstract forest fold for that tree. -/
theorem forestEnd_scheme_roots (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩)
    (initialQuery : hashInput initial =
      toQuery (leafInput pk ⟨0, by decide⟩ index
        (leaves ⟨0, by decide⟩)
        (signature.ftsSecret ⟨0, by decide⟩)))
    (tree : FtsTree) (i : Nat) (hi : i < 20) :
    (forestEndState hash initial signature pk index leaves).getByte
        (BitVec.ofNat 64 (0x44100 + 20 * tree.val + i)) =
      (schemeTreeValue hash signature pk index leaves tree).extractLsb'
        (8 * i) 8 := by
  rw [forestEnd_all_roots hash initial signature pk index leaves
    initialInv tree i hi]
  rw [treeValue_eq_scheme hash initial signature pk index leaves
    initialInv initialQuery tree]

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLeafQueryTree.forestEnd_scheme_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestEnd_scheme_roots

end SigGolfCandidate.SphincsVerifierFtsLeafQueryTree
