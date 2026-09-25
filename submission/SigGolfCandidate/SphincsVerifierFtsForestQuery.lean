import SigGolfCandidate.SphincsVerifierFtsForestHeaderBytes
import SigGolfCandidate.SphincsVerifierFtsRootsPayload
import SigGolfCandidate.SphincsVerifierFtsForestHash

namespace SigGolfCandidate.SphincsVerifierFtsForestQuery
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsForestHashReady
open SigGolfCandidate.SphincsVerifierFtsForestHeaderBytes
open SigGolfCandidate.SphincsVerifierFtsForestPayloadFrame
open SigGolfCandidate.SphincsVerifierFtsLeafQueryTree
open SigGolfCandidate.SphincsVerifierFtsForestHash
open SigGolfCandidate.SphincsVerifierFtsRootsPayload
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierFtsForestRoots
open SigGolfCandidate.SphincsVerifierFtsForestReady
open SigGolfCandidate.SphincsVerifierFtsTreeWitnessStep
open SigGolfCandidate.SphincsVerifierFtsPersistentIndex
open SigGolfCandidate.SphincsVerifierFtsInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsGenericInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsTreeWitnessStep
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierFtsPostForestCopy
open SigGolfCandidate.SphincsVerifierFtsRootCopySetup
open SigGolfCandidate.SphincsVerifierFtsForestPayloadFrame
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem forestInput_header (pk : SphincsSecurity.PublicKey)
    (index : Index) (roots : FtsTree → Digest)
    (i : Nat) (hi : i < 20) :
    ((forestInput pk index roots).map UInt8.toBitVec)[i]'(by
      rw [List.length_map, forestInput_length]; omega) =
      ((fieldBytes (tweakFields 11 0 index.val 0 0)).map
        UInt8.toBitVec)[i]'(by simp [fieldBytes, bytesLE]; omega) := by
  simp only [forestInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega)]

theorem forestInput_parameter (pk : SphincsSecurity.PublicKey)
    (index : Index) (roots : FtsTree → Digest)
    (i : Nat) (hi : i < 20) :
    ((forestInput pk index roots).map UInt8.toBitVec)[20 + i]'(by
      rw [List.length_map, forestInput_length]; omega) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  simp only [forestInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [fieldBytes, bytesLE]
  rfl

theorem forestInput_payload (pk : SphincsSecurity.PublicKey)
    (index : Index) (roots : FtsTree → Digest)
    (i : Nat) (hi : i < 480) :
    ((forestInput pk index roots).map UInt8.toBitVec)[40 + i]'(by
      rw [List.length_map, forestInput_length]; omega) =
      ((SphincsSecurity.Concrete.ftsRootsPayload roots).map
        UInt8.toBitVec)[i]'(by
          rw [rootsPayload_flat, List.length_map, List.length_ofFn]
          omega) := by
  simp only [forestInput_eq, List.map_append]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp [fieldBytes, bytesLE]

/-- The exact 520-byte HASH buffer represents the scheme forest-root query. -/
theorem readyForest_hashInput (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (roots : FtsTree → Digest)
    (layerZero : state.getMem 0x43000 = 0)
    (positionZero : state.getMem 0x43010 = 0)
    (treeIndex : state.getMem 0x43008 = BitVec.ofNat 64 index.val)
    (nodeZero : state.getMem 0x43018 = 0)
    (parameterEncoded : WitnessPrefix state pk)
    (payload : ∀ i, (hi : i < 480) →
      (forestHashReadyState state).getByte
        (BitVec.ofNat 64 (0x40028 + i)) =
        ((SphincsSecurity.Concrete.ftsRootsPayload roots).map
          UInt8.toBitVec)[i]'(by
            rw [rootsPayload_flat, List.length_map, List.length_ofFn]
            omega)) :
    hashInput (forestHashReadyState state) =
      toQuery (forestInput pk index roots) := by
  let ready := forestHashReadyState state
  have source : ready.getReg .x10 = 0x40000 := by
    simp [ready, forestHashReadyState, forestHashRegistersState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  have bits : ready.getReg .x11 = 4160 := by
    simp [ready, forestHashReadyState, forestHashRegistersState, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  apply forestHash_query ready pk index roots
  · exact source
  · exact bits
  · intro i hi
    by_cases header : i < 20
    · let byte : Fin 20 := ⟨i, header⟩
      have actual := forestHeader_bytes state index ⟨0, by decide⟩
        layerZero positionZero treeIndex nodeZero byte
      have expected := forestInput_header pk index roots i header
      simpa [ready, byte] using actual.trans expected.symm
    · by_cases parameter : i < 40
      · have smaller : i - 20 < 20 := by omega
        have actual := forestHashReady_parameter_byte state pk
          parameterEncoded (i - 20) smaller
        have expected := forestInput_parameter pk index roots
          (i - 20) smaller
        have joined := actual.trans expected.symm
        have split : 20 + (i - 20) = i := by omega
        have address : 0x40014 + (i - 20) = 0x40000 + i := by omega
        simpa only [ready, split, address] using joined


      · have smaller : i - 40 < 480 := by omega
        have actual := payload (i - 40) smaller
        have expected := forestInput_payload pk index roots
          (i - 40) smaller
        have joined := actual.trans expected.symm
        have split : 40 + (i - 40) = i := by omega
        have address : 0x40028 + (i - 40) = 0x40000 + i := by omega
        simpa only [ready, split, address] using joined

theorem forestEnd_savedIndex (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩) :
    (forestEndState hash initial signature pk index leaves).getMem
      0x43078 = BitVec.ofNat 64 index.val := by
  let last : FtsTree := ⟨23, by decide⟩
  let state := forestReady hash initial signature pk index leaves 23
  have inv := forestReady_inv hash initial signature pk index leaves
    initialInv 23 (by decide)
  change (treeFinishState
    (parentPathRun hash pk signature last index (leaves last)
      (firstLeafStartState state (hash (hashInput state)))
      (truncateHash (hash (hashInput state))) 8).1).getMem 0x43078 = _
  exact (treeProcess_savedIndex_frame hash state signature pk last index
    (leaves last) inv.controls.counter inv.controls.destination).trans
    inv.controls.savedIndex

theorem forestEnd_prefix (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩) :
    WitnessPrefix (forestEndState hash initial signature pk index leaves)
      pk := by
  let last : FtsTree := ⟨23, by decide⟩
  let state := forestReady hash initial signature pk index leaves 23
  let answer := hash (hashInput state)
  let start := firstLeafStartState state answer
  let path := (parentPathRun hash pk signature last index (leaves last)
    start (truncateHash answer) 8).1
  have inv := forestReady_inv hash initial signature pk index leaves
    initialInv 23 (by decide)
  have initialPath := leafInitialInv state answer signature pk last index
    (leaves last) inv.controls.pc inv.controls.source inv.controls.bits
    inv.controls.destination inv.controls.pointer inv.controls.selector
    inv.controls.treeCell inv.controls.indexCell inv.publicKey inv.witness
  have pathProof := parentPathRun_finish hash pk signature last index
    (leaves last) start (truncateHash answer) initialPath
  have pathCounter : path.getMem 0x43040 =
      BitVec.ofNat 64 last.val := by
    calc
      _ = start.getMem 0x43040 :=
        parentPathRun_counter_frame hash pk signature last index
          (leaves last) start (truncateHash answer) 8
      _ = state.getMem 0x43040 :=
        levelStart_counter_frame state answer inv.controls.destination
      _ = BitVec.ofNat 64 last.val := inv.controls.counter
  change WitnessPrefix (treeFinishState path) pk
  exact treeFinish_prefix path pk last pathCounter pathProof.2.2.2

/-- The actual 24-tree forest execution supplies the next HASH input. -/
theorem forestEnd_hashInput (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩)
    (initialQuery : hashInput initial =
      toQuery (leafInput pk ⟨0, by decide⟩ index
        (leaves ⟨0, by decide⟩)
        (signature.ftsSecret ⟨0, by decide⟩))) :
    let endState := forestEndState hash initial signature pk index leaves
    ∃ copied,
      OrdinarySteps SphincsImages.verify endState 387 copied ∧
      copied.pc = 0x1c8c ∧
      hashInput (forestHashReadyState copied) =
        toQuery (forestInput pk index
          (schemeTreeValue hash signature pk index leaves)) := by
  let endState := forestEndState hash initial signature pk index leaves
  let roots := schemeTreeValue hash signature pk index leaves
  have endPc : endState.pc = 0x1c08 := by
    simpa only [endState, forestEndState] using
      (forest_final_exit hash initial signature pk index leaves
        initialInv).2.1
  obtain ⟨copied, trace, copiedPc, copiedBytes, low, high⟩ :=
    forestPostCopy_full endState endPc
  have cells := rootCopyEntry_header_cells endState
  have layerZero : copied.getMem 0x43000 = 0 :=
    (high 0x43000 (by decide)).trans cells.1
  have positionZero : copied.getMem 0x43010 = 0 :=
    (high 0x43010 (by decide)).trans cells.2.1
  have nodeZero : copied.getMem 0x43018 = 0 :=
    (high 0x43018 (by decide)).trans cells.2.2.1
  have treeIndex : copied.getMem 0x43008 =
      BitVec.ofNat 64 index.val := by
    exact ((high 0x43008 (by decide)).trans cells.2.2.2).trans
      (forestEnd_savedIndex hash initial signature pk index leaves
        initialInv)
  have encoded : WitnessPrefix copied pk :=
    witnessPrefix_of_low_mem_frame endState copied pk
      (forestEnd_prefix hash initial signature pk index leaves initialInv)
      low
  have payload : ∀ i, (hi : i < 480) →
      (forestHashReadyState copied).getByte
        (BitVec.ofNat 64 (0x40028 + i)) =
        ((SphincsSecurity.Concrete.ftsRootsPayload roots).map
          UInt8.toBitVec)[i]'(by
            rw [rootsPayload_flat, List.length_map, List.length_ofFn]
            omega) := by
    intro i hi
    let tree : FtsTree := ⟨i / 20, by
      change i / 20 < 24
      omega⟩
    let byte := i % 20
    have hb : byte < 20 := by dsimp [byte]; omega
    have split : 20 * tree.val + byte = i := by
      dsimp [tree, byte]
      omega
    have source := forestEnd_payload_bytes hash initial signature pk
      index leaves initialInv initialQuery tree byte hb
    have copy := copiedBytes i hi
    have ready := forestHashReady_payload_byte_frame copied i hi
    simpa only [roots, Nat.add_assoc, split] using
      ready.trans (copy.trans (by
        simpa only [endState, roots, Nat.add_assoc, split] using source))
  refine ⟨copied, trace, copiedPc, ?_⟩
  exact readyForest_hashInput copied pk index roots layerZero positionZero
    treeIndex nodeZero encoded payload

theorem forestEnd_hash_ready (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩)
    (initialQuery : hashInput initial =
      toQuery (leafInput pk ⟨0, by decide⟩ index
        (leaves ⟨0, by decide⟩)
        (signature.ftsSecret ⟨0, by decide⟩))) :
    let endState := forestEndState hash initial signature pk index leaves
    ∃ ready,
      OrdinarySteps SphincsImages.verify endState 430 ready ∧
      ready.pc = 0x1d38 ∧
      ready.getReg .x10 = 0x40000 ∧
      ready.getReg .x11 = 4160 ∧
      ready.getReg .x12 = 0x42000 ∧
      ready.getReg .x5 = 1 ∧
      hashInput ready = toQuery (forestInput pk index
        (schemeTreeValue hash signature pk index leaves)) := by
  let endState := forestEndState hash initial signature pk index leaves
  obtain ⟨copied, copyTrace, copiedPc, query⟩ :=
    forestEnd_hashInput hash initial signature pk index leaves
      initialInv initialQuery
  have header := forestHashReady_block copied copiedPc
  refine ⟨forestHashReadyState copied, ?_, header.2.1,
    header.2.2.1, header.2.2.2.1, header.2.2.2.2.1,
    header.2.2.2.2.2, query⟩
  simpa only [show 387 + 43 = 430 by decide] using
    copyTrace.append header.1

theorem forestEnd_hash_executes (hash : Hash) (initial : MachineState)
    (signature : Signature) (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaves : FtsTree → FtsLeaf)
    (initialInv : ReadyInv initial signature pk index leaves
      ⟨0, by decide⟩)
    (initialQuery : hashInput initial =
      toQuery (leafInput pk ⟨0, by decide⟩ index
        (leaves ⟨0, by decide⟩)
        (signature.ftsSecret ⟨0, by decide⟩)))
    (steps : Nat) (result : Execution)
    (tail : ∀ ready,
      OrdinarySteps SphincsImages.verify
        (forestEndState hash initial signature pk index leaves) 430 ready →
      hashInput ready = toQuery (forestInput pk index
        (schemeTreeValue hash signature pk index leaves)) →
      Executes hash SphincsImages.verify
        (writeHash ready
          (hash (toQuery (forestInput pk index
            (schemeTreeValue hash signature pk index leaves)))))
        steps result) :
    Executes hash SphincsImages.verify
      (forestEndState hash initial signature pk index leaves)
      (steps + 431) (result.charge 502 1 9) := by
  obtain ⟨ready, ordinary, pc, source, bits, destination, service, query⟩ :=
    forestEnd_hash_ready hash initial signature pk index leaves
      initialInv initialQuery
  have tail' : Executes hash SphincsImages.verify
      (writeHash ready (hash (hashInput ready))) steps result := by
    rw [query]
    exact tail ready ordinary query
  have step := hash_step hash ready pc source bits destination service
    steps result tail'
  have all := ordinary.then_executes step
  simpa [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using all

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestQuery.readyForest_hashInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms readyForest_hashInput

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestQuery.forestEnd_savedIndex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestEnd_savedIndex

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestQuery.forestEnd_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestEnd_prefix

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestQuery.forestEnd_hashInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestEnd_hashInput

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestQuery.forestEnd_hash_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestEnd_hash_ready

/-- info: 'SigGolfCandidate.SphincsVerifierFtsForestQuery.forestEnd_hash_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms forestEnd_hash_executes

end SigGolfCandidate.SphincsVerifierFtsForestQuery
