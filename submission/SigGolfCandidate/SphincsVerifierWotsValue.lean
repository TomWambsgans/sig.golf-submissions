import SigGolfCandidate.SphincsVerifierWotsEndpointAll
import SigGolfCandidate.SphincsVerifierMessageAnswer
import SigGolfCandidate.SphincsVerifierFtsGenericBytes
import SigGolfCandidate.SphincsBridge

namespace SigGolfCandidate.SphincsVerifierWotsValue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsEndpointCopy
open SigGolfCandidate.SphincsVerifierWotsStepNext
open SigGolfCandidate.SphincsVerifierWotsStepIteration
open SigGolfCandidate.SphincsVerifierWotsStepHashReady
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierCopyMemory
open SphincsSecurity
open SigGolfCandidate.SphincsVerifierCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem stepAnswerCopy_word (state : MachineState)
    (index : Fin 5) :
    (stepAnswerCopyState state).getWord32 (word 0x44b00 index) =
      state.getWord32 (word 0x42000 index) := by
  let pre := stepAnswerPointersState state
  have source : pre.getReg .x6 = 0x42000 := by
    simp [pre, stepAnswerPointersState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  have destination : pre.getReg .x7 = 0x44b00 := by
    simp [pre, stepAnswerPointersState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have copied := copy20_data pre 0x42000 0x44b00 source destination
    (by intro i j; fin_cases i <;> fin_cases j <;> decide)
    (by intro i j different
        fin_cases i <;> fin_cases j <;>
          first | exact (different rfl).elim | decide)
    index
  have preFrame : pre.getWord32 (word 0x42000 index) =
      state.getWord32 (word 0x42000 index) := by
    simp [pre, stepAnswerPointersState, execInstrBr,
      MachineState.getWord32]
  exact copied.trans preFrame

theorem stepReturn_valueFrame (state : MachineState)
    (index : Fin 5) :
    (stepReturnState state).getWord32 (word 0x44b00 index) =
      state.getWord32 (word 0x44b00 index) := by
  fin_cases index <;>
    simp [stepReturnState, stepAdvanceState, execInstrBr,
      MachineState.getWord32, signExtend12,
      MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, word, alignToDword,
      byteOffset]

theorem writeHash_word32 (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000)
    (index : Fin 5) :
    (writeHash state answer).getWord32 (word 0x42000 index) =
      answer.extractLsb' (32 * index.val) 32 := by
  fin_cases index <;>
    simp [writeHash, MachineState.writeWords_cons,
      MachineState.getWord32, word, destination,
      MachineState.getMem_setMem_ne,
      MachineState.getMem_setMem_eq,
      extractWord32, alignToDword,
      byteOffset] <;>
    (ext bit (hbit : bit < 32);
      simp;
      first
      | omega
      | have hb : 32 + bit < 64 := by omega
        simp [hb, show 64 + (32 + bit) = 96 + bit by omega])

theorem stepNext_value (hash : Hash) (state : MachineState)
    (index : Fin 5) :
    (stepNext hash state).getWord32 (word 0x44b00 index) =
      (hash (hashInput (stepReady state))).extractLsb'
        (32 * index.val) 32 := by
  let answer := hash (hashInput (stepReady state))
  have destination : (stepReady state).getReg .x12 = 0x42000 := by
    simp [stepReady, stepHashReadyState, stepHashRegistersState,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  change (stepReturnState
      (stepAnswerCopyState (writeHash (stepReady state) answer))).getWord32
        (word 0x44b00 index) = _
  rw [stepReturn_valueFrame,
    stepAnswerCopy_word,
    writeHash_word32 (stepReady state) answer destination]

theorem stepNext_valueByte (hash : Hash) (state : MachineState)
    (i : Nat) (hi : i < 20) :
    (stepNext hash state).getByte (BitVec.ofNat 64 (0x44b00 + i)) =
      (hash (hashInput (stepReady state))).extractLsb' (8 * i) 8 := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  rw [← split,
    show 0x44b00 + (4 * index.val + byte.val) =
      0x44b00 + 4 * index.val + byte.val by omega,
    variableWord_byte _ 0x44b00 (by decide) (by decide) index byte]
  have value := stepNext_value hash state index
  simp only [word] at value
  rw [value]
  ext bit (hbit : bit < 8)
  simp
  have hb : 8 * byte.val + bit < 32 := by have := byte.isLt; omega
  simp [hb, show 32 * index.val + (8 * byte.val + bit) =
    8 * (4 * index.val + byte.val) + bit by omega]

theorem stepNext_valueByte_of_query (hash : Hash) (state : MachineState)
    (input : HashInput)
    (query : hashInput (stepReady state) = toQuery input)
    (i : Nat) (hi : i < 20) :
    (stepNext hash state).getByte (BitVec.ofNat 64 (0x44b00 + i)) =
      (truncateHash (hash (toQuery input))).extractLsb' (8 * i) 8 := by
  rw [stepNext_valueByte hash state i hi, query]
  exact
    (BitVec.extractLsb'_extractLsb'_of_le
      (x := hash (toQuery input))
      (start := 8 * i) (len := 8) (len' := digestBits)
      (by unfold digestBits; omega)).symm

def chainInput (parameter : PublicParameter) (layer : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) : HashInput :=
  tweakableHashInput parameter (.chain layer tree leaf chain step)
    (bytesLE 20 value)

theorem chainInput_length (parameter : PublicParameter) (layer : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    (chainInput parameter layer tree leaf chain step value).length = 60 := by
  simp [chainInput, tweakableHashInput, tweakBytes, fieldBytes, bytesLE]

theorem chainHeader_eq (layer : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (position : Nat) :
    fieldBytes (tweakFields 1 layer.val tree.val position leaf.val) =
      bytesLE 4 (BitVec.ofNat 32 (257 + 2 ^ 16 * layer.val)) ++
      bytesLE 4 (BitVec.ofNat 32 position) ++
      bytesLE 8 (BitVec.ofNat 64 tree.val) ++
      bytesLE 4 (BitVec.ofNat 32 leaf.val) := by
  fin_cases layer <;>
    simp [fieldBytes, tweakFields, protocolDomainSep, bytesLE]

theorem chainInput_header (parameter : PublicParameter) (layer : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest)
    (i : Nat) (hi : i < 20) :
    ((chainInput parameter layer tree leaf chain step value).map
      UInt8.toBitVec)[i]'(by rw [List.length_map, chainInput_length]; omega) =
    ((fieldBytes (tweakFields 1 layer.val tree.val
      (chainLength * chain.val + step.val) leaf.val)).map
      UInt8.toBitVec)[i]'(by simp [fieldBytes, bytesLE]; omega) := by
  simp only [chainInput, tweakableHashInput, tweakBytes,
    hashDomainFields, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega)]

theorem chainInput_parameter (parameter : PublicParameter) (layer : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest)
    (i : Nat) (hi : i < 20) :
    ((chainInput parameter layer tree leaf chain step value).map
      UInt8.toBitVec)[20 + i]'(by rw [List.length_map, chainInput_length]; omega) =
    parameter.extractLsb' (8 * i) 8 := by
  simp only [chainInput, tweakableHashInput, tweakBytes,
    hashDomainFields, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [fieldBytes, bytesLE]
  rfl

theorem chainInput_value (parameter : PublicParameter) (layer : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest)
    (i : Nat) (hi : i < 20) :
    ((chainInput parameter layer tree leaf chain step value).map
      UInt8.toBitVec)[40 + i]'(by rw [List.length_map, chainInput_length]; omega) =
    value.extractLsb' (8 * i) 8 := by
  simp only [chainInput, tweakableHashInput, tweakBytes,
    hashDomainFields, List.map_append]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [fieldBytes, bytesLE]
  rfl

theorem stepReady_chainQuery_of_bytes (state : MachineState)
    (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep)
    (value : Digest)
    (bytes : ∀ i, (hi : i < 60) →
      (stepReady state).getByte (BitVec.ofNat 64 (0x40000 + i)) =
        ((chainInput parameter layer tree leaf chain step value).map
          UInt8.toBitVec)[i]'(by
            rw [List.length_map, chainInput_length]; exact hi)) :
    hashInput (stepReady state) =
      toQuery (chainInput parameter layer tree leaf chain step value) := by
  apply Serialization.hashInput_of_list (stepReady state) 0x40000
    ((chainInput parameter layer tree leaf chain step value).map UInt8.toBitVec)
  · simp [stepReady, stepHashReadyState, stepHashRegistersState,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  · simp [stepReady, stepHashReadyState, stepHashRegistersState,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, chainInput_length]
  · intro i hi
    exact bytes i (by simpa [chainInput_length] using hi)

theorem stepValueCopied_data (state : MachineState) (index : Fin 5) :
    (SphincsVerifierWotsStepBody.stepValueCopied state).getWord32
      (word 0x40028 index) = state.getWord32 (word 0x44b00 index) := by
  let pre := SphincsVerifierWotsStepBody.stepValuePointers state
  have source : pre.getReg .x6 = 0x44b00 := by
    simp [pre, SphincsVerifierWotsStepBody.stepValuePointers,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  have destination : pre.getReg .x7 = 0x40028 := by
    simp [pre, SphincsVerifierWotsStepBody.stepValuePointers,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq]
  have copied := copy20_data pre 0x44b00 0x40028 source destination
    (by intro i j; fin_cases i <;> fin_cases j <;> decide)
    (by intro i j different
        fin_cases i <;> fin_cases j <;>
          first | exact (different rfl).elim | decide)
    index
  have preFrame : pre.getWord32 (word 0x44b00 index) =
      state.getWord32 (word 0x44b00 index) := by
    simp [pre, SphincsVerifierWotsStepBody.stepValuePointers,
      execInstrBr, MachineState.getWord32]
  exact copied.trans preFrame

theorem stepPrefix_parameterSourceFrame (state : MachineState)
    (index : Fin 5) :
    (SphincsVerifierWotsStepBody.stepHashPrefixState state).getWord32
      (word 0x22cb4 index) = state.getWord32 (word 0x22cb4 index) := by
  let pointers := SphincsVerifierWotsStepBody.stepValuePointers state
  have destination : pointers.getReg .x7 = 0x40028 := by
    simp [pointers, SphincsVerifierWotsStepBody.stepValuePointers,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq]
  have copyFrame :
      (SphincsVerifierWotsStepBody.stepValueCopied state).getWord32
        (word 0x22cb4 index) = state.getWord32 (word 0x22cb4 index) := by
    change (copyRootState pointers).getWord32 _ = _
    rw [copyRoot_getWord32_frame pointers _ (by
      intro offset
      rw [destination]
      fin_cases offset <;> fin_cases index <;> decide)]
    simp [pointers, SphincsVerifierWotsStepBody.stepValuePointers,
      execInstrBr, MachineState.getWord32]
  have positionFrame :
      (SphincsVerifierWotsStepBody.stepPositionState
        (SphincsVerifierWotsStepBody.stepValueCopied state)).getWord32
          (word 0x22cb4 index) =
        (SphincsVerifierWotsStepBody.stepValueCopied state).getWord32
          (word 0x22cb4 index) := by
    fin_cases index <;>
      simp [SphincsVerifierWotsStepBody.stepPositionState,
        execInstrBr, MachineState.getWord32,
        MachineState.getMem_setMem_ne, word, alignToDword,
        signExtend12, MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne]
  exact positionFrame.trans copyFrame

theorem stepPrefix_controlCell (state : MachineState) (address : Word)
    (positionOutside : address ≠ 0x43010)
    (payloadOutside : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x40028 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val))) :
    (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      address = state.getMem address := by
  let pointers := SphincsVerifierWotsStepBody.stepValuePointers state
  have destination : pointers.getReg .x7 = 0x40028 := by
    simp [pointers, SphincsVerifierWotsStepBody.stepValuePointers,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq]
  have copied :
      (SphincsVerifierWotsStepBody.stepValueCopied state).getMem address =
        state.getMem address := by
    change (copyRootState pointers).getMem address = _
    rw [copyRoot_mem_frame pointers address (by
      intro offset
      rw [destination]
      exact payloadOutside offset)]
    simp [pointers, SphincsVerifierWotsStepBody.stepValuePointers,
      execInstrBr]
  have position :
      (SphincsVerifierWotsStepBody.stepPositionState
        (SphincsVerifierWotsStepBody.stepValueCopied state)).getMem
          address =
        (SphincsVerifierWotsStepBody.stepValueCopied state).getMem
          address := by
    have outside : address ≠ (274448#64) := by
      simpa using positionOutside
    simp [SphincsVerifierWotsStepBody.stepPositionState,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_ne, outside]
  exact position.trans copied

theorem stepValueCopied_controlCell (state : MachineState)
    (address : Word)
    (payloadOutside : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x40028 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val))) :
    (SphincsVerifierWotsStepBody.stepValueCopied state).getMem address =
      state.getMem address := by
  let pointers := SphincsVerifierWotsStepBody.stepValuePointers state
  have destination : pointers.getReg .x7 = 0x40028 := by
    simp [pointers, SphincsVerifierWotsStepBody.stepValuePointers,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq]
  change (copyRootState pointers).getMem address = _
  rw [copyRoot_mem_frame pointers address (by
    intro offset
    rw [destination]
    exact payloadOutside offset)]
  simp [pointers, SphincsVerifierWotsStepBody.stepValuePointers,
    execInstrBr]

theorem stepPosition_payloadFrame (state : MachineState)
    (index : Fin 5) :
    (SphincsVerifierWotsStepBody.stepPositionState state).getWord32
      (word 0x40028 index) = state.getWord32 (word 0x40028 index) := by
  fin_cases index <;>
    simp [SphincsVerifierWotsStepBody.stepPositionState,
      execInstrBr, MachineState.getWord32,
      MachineState.getMem_setMem_ne, word, alignToDword,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

theorem stepPosition_value (state : MachineState) (chain : ChainIndex)
    (step : ChainStep)
    (chainCell : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (stepCell : state.getMem 0x43058 = BitVec.ofNat 64 step.val) :
    (SphincsVerifierWotsStepBody.stepPositionState state).getMem 0x43010 =
      BitVec.ofNat 64 (chainLength * chain.val + step.val) := by
  simp [SphincsVerifierWotsStepBody.stepPositionState, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  have hc : state.getMem (274512#64) = BitVec.ofNat 64 chain.val := by
    simpa using chainCell
  have hs : state.getMem (274520#64) = BitVec.ofNat 64 step.val := by
    simpa using stepCell
  rw [hc, hs]
  have shift : (BitVec.ofNat 64 chain.val <<< 3) =
      BitVec.ofNat 64 (8 * chain.val) := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.shiftLeft_eq]
    omega
  rw [shift, BitVec.ofNat_add_ofNat]
  simp [chainLength, winternitzBits]

theorem stepTag_payloadFrame (state : MachineState) (index : Fin 5) :
    (stepTagState state).getWord32 (word 0x40028 index) =
      state.getWord32 (word 0x40028 index) := by
  fin_cases index <;>
    simp [stepTagState, execInstrBr, MachineState.getWord32,
      setWord32_eq,
      MachineState.getMem_setMem_ne, word, alignToDword,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

theorem stepTag_value (state : MachineState) (layer : Layer)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val) :
    (stepTagState state).getWord32 0x40000 =
      BitVec.ofNat 32 (257 + 2 ^ 16 * layer.val) := by
  simp [stepTagState, execInstrBr, signExtend12,
    getWord32_setWord32_same,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  have cell : state.getMem (274432#64) = BitVec.ofNat 64 layer.val := by
    simpa using layerCell
  rw [cell]
  fin_cases layer <;> decide

theorem stepHeader_payloadFrame (state : MachineState) (index : Fin 5) :
    (stepHeaderState state).getWord32 (word 0x40028 index) =
      state.getWord32 (word 0x40028 index) := by
  let tagged := stepTagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer : tagged.getReg .x7 = 0x40000 := by
    simp [tagged, stepTagState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
  rw [index_word_frame treed _ treePointer
      (by fin_cases index <;> decide),
    tree_word_frame positioned _ positionPointer
      (by fin_cases index <;> decide),
    position_word_frame tagged _ tagPointer
      (by fin_cases index <;> decide),
    stepTag_payloadFrame]

theorem stepHeader_parameterSourceFrame (state : MachineState)
    (index : Fin 5) :
    (stepHeaderState state).getWord32 (word 0x22cb4 index) =
      state.getWord32 (word 0x22cb4 index) := by
  let tagged := stepTagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer : tagged.getReg .x7 = 0x40000 := by
    simp [tagged, stepTagState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
  rw [index_word_frame treed _ treePointer
      (by fin_cases index <;> decide),
    tree_word_frame positioned _ positionPointer
      (by fin_cases index <;> decide),
    position_word_frame tagged _ tagPointer
      (by fin_cases index <;> decide)]
  fin_cases index <;>
    simp [tagged, stepTagState, execInstrBr,
      MachineState.getWord32, setWord32_eq,
      MachineState.getMem_setMem_ne, word, alignToDword,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

theorem stepHeader_tree (state : MachineState) :
    (stepHeaderState state).getMem 0x40008 = state.getMem 0x43008 := by
  simp [stepHeaderState, stepTagState,
    SphincsVerifierHeader.positionState,
    SphincsVerifierHeader.positionBeforeStore,
    SphincsVerifierHeader.treeState,
    SphincsVerifierHeader.treeBeforeStore,
    SphincsVerifierHeader.indexState,
    SphincsVerifierHeader.indexBeforeStore,
    execInstrBr, signExtend12, setWord32_eq,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,
    MachineState.getMem_setMem_ne, alignToDword, byteOffset]

theorem stepHeader_tag (state : MachineState) (layer : Layer)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val) :
    (stepHeaderState state).getWord32 0x40000 =
      BitVec.ofNat 32 (257 + 2 ^ 16 * layer.val) := by
  let tagged := stepTagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer : tagged.getReg .x7 = 0x40000 := by
    simp [tagged, stepTagState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
  rw [index_word_frame treed _ treePointer (by decide),
    tree_word_frame positioned _ positionPointer (by decide),
    position_word_frame tagged _ tagPointer (by decide)]
  exact stepTag_value state layer layerCell

theorem stepHeader_position (state : MachineState)
    (position : Nat)
    (positionCell : state.getMem 0x43010 = BitVec.ofNat 64 position) :
    (stepHeaderState state).getWord32 0x40004 =
      BitVec.ofNat 32 position := by
  let tagged := stepTagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer : tagged.getReg .x7 = 0x40000 := by
    simp [tagged, stepTagState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  have taggedCell : tagged.getMem 0x43010 = BitVec.ofNat 64 position := by
    have frame : tagged.getMem 0x43010 = state.getMem 0x43010 := by
      simp [tagged, stepTagState, execInstrBr, setWord32_eq,
        MachineState.getMem_setMem_ne, signExtend12,
        MachineState.getReg_setReg_eq, alignToDword]
    exact frame.trans positionCell
  change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
  rw [index_word_frame treed _ treePointer (by decide),
    tree_word_frame positioned _ positionPointer (by decide)]
  simpa using
    SphincsVerifierFtsGenericHeader.parentPosition_value_generic tagged
      tagPointer (BitVec.ofNat 64 position) taggedCell

theorem stepHeader_index (state : MachineState) :
    (stepHeaderState state).getWord32 0x40010 =
      (state.getMem 0x43018).truncate 32 := by
  simp [stepHeaderState, stepTagState,
    SphincsVerifierHeader.positionState,
    SphincsVerifierHeader.positionBeforeStore,
    SphincsVerifierHeader.treeState,
    SphincsVerifierHeader.treeBeforeStore,
    SphincsVerifierHeader.indexState,
    SphincsVerifierHeader.indexBeforeStore,
    execInstrBr, signExtend12, setWord32_eq,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,
    MachineState.getMem_setMem_ne,
    alignToDword, byteOffset, MachineState.getWord32,
    extractWord32, replaceWord32]

theorem stepReady_payloadWords (state : MachineState) (index : Fin 5) :
    (stepReady state).getWord32 (word 0x40028 index) =
      state.getWord32 (word 0x44b00 index) := by
  let copied := SphincsVerifierWotsStepBody.stepValueCopied state
  let positioned := SphincsVerifierWotsStepBody.stepPositionState copied
  let headed := stepHeaderState positioned
  let pointers := stepParameterPointers headed
  have destination : pointers.getReg .x7 = 0x40014 := by
    simp [pointers, stepParameterPointers, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq]
  have registers (s : MachineState) (address : Word) :
      (stepHashRegistersState s).getWord32 address =
        s.getWord32 address := by
    simp [stepHashRegistersState, MachineState.getWord32, execInstrBr]
  change (stepHashRegistersState (copyRootState pointers)).getWord32 _ = _
  rw [registers,
    copyRoot_getWord32_frame pointers _ (by
      intro offset
      rw [destination]
      fin_cases offset <;> fin_cases index <;> decide)]
  have pointersFrame : pointers.getWord32 (word 0x40028 index) =
      headed.getWord32 (word 0x40028 index) := by
    simp [pointers, stepParameterPointers, execInstrBr,
      MachineState.getWord32]
  rw [pointersFrame, stepHeader_payloadFrame,
    stepPosition_payloadFrame, stepValueCopied_data]

theorem stepReady_headerWords (state : MachineState) (index : Fin 5) :
    (stepReady state).getWord32 (word 0x40000 index) =
      (stepHeaderState
        (SphincsVerifierWotsStepBody.stepHashPrefixState state)).getWord32
          (word 0x40000 index) := by
  let headed := stepHeaderState
    (SphincsVerifierWotsStepBody.stepHashPrefixState state)
  let pointers := stepParameterPointers headed
  have destination : pointers.getReg .x7 = 0x40014 := by
    simp [pointers, stepParameterPointers, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq]
  have registers (s : MachineState) (address : Word) :
      (stepHashRegistersState s).getWord32 address =
        s.getWord32 address := by
    simp [stepHashRegistersState, MachineState.getWord32, execInstrBr]
  change (stepHashRegistersState (copyRootState pointers)).getWord32 _ = _
  rw [registers,
    copyRoot_getWord32_frame pointers _ (by
      intro offset
      rw [destination]
      fin_cases offset <;> fin_cases index <;> decide)]
  simpa only [headed] using (by
    simp [pointers, stepParameterPointers, execInstrBr,
      MachineState.getWord32] :
      pointers.getWord32 (word 0x40000 index) =
        headed.getWord32 (word 0x40000 index))

theorem stepReady_tagPosition (state : MachineState)
    (layer : Layer) (position : Nat)
    (layerCell : (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      0x43000 = BitVec.ofNat 64 layer.val)
    (positionCell : (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      0x43010 = BitVec.ofNat 64 position) :
    (stepReady state).getWord32 0x40000 =
        BitVec.ofNat 32 (257 + 2 ^ 16 * layer.val) ∧
      (stepReady state).getWord32 0x40004 =
        BitVec.ofNat 32 position := by
  constructor
  · simpa [word] using
      (stepReady_headerWords state (0 : Fin 5)).trans
        (stepHeader_tag _ layer layerCell)
  · simpa [word] using
      (stepReady_headerWords state (1 : Fin 5)).trans
      (stepHeader_position _ position positionCell)

theorem stepReady_tree (state : MachineState) :
    (stepReady state).getMem 0x40008 =
      (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
        0x43008 := by
  let prefixed := SphincsVerifierWotsStepBody.stepHashPrefixState state
  let headed := stepHeaderState prefixed
  let pointers := stepParameterPointers headed
  have destination : pointers.getReg .x7 = 0x40014 := by
    simp [pointers, stepParameterPointers, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq]
  have registers (s : MachineState) (address : Word) :
      (stepHashRegistersState s).getMem address = s.getMem address := by
    simp [stepHashRegistersState, execInstrBr]
  change (stepHashRegistersState (copyRootState pointers)).getMem _ = _
  rw [registers, copyRoot_mem_frame pointers 0x40008 (by
    intro offset
    rw [destination]
    fin_cases offset <;> decide)]
  have pointerFrame : pointers.getMem 0x40008 = headed.getMem 0x40008 := by
    simp [pointers, stepParameterPointers, execInstrBr]
  rw [pointerFrame, stepHeader_tree]

theorem stepReady_index (state : MachineState) :
    (stepReady state).getWord32 0x40010 =
      ((SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
        0x43018).truncate 32 := by
  simpa [word] using
    (stepReady_headerWords state (4 : Fin 5)).trans
      (stepHeader_index (SphincsVerifierWotsStepBody.stepHashPrefixState state))

theorem stepReady_tagByte (state : MachineState) (layer : Layer)
    (layerCell : (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      0x43000 = BitVec.ofNat 64 layer.val)
    (byte : Fin 4) :
    (stepReady state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      (BitVec.ofNat 32 (257 + 2 ^ 16 * layer.val)).extractLsb'
        (8 * byte.val) 8 := by
  have actual := variableWord_byte (stepReady state) 0x40000
    (by decide) (by decide) (0 : Fin 5) byte
  have value : (stepReady state).getWord32 0x40000 =
      BitVec.ofNat 32 (257 + 2 ^ 16 * layer.val) := by
    simpa [word] using
      (stepReady_headerWords state (0 : Fin 5)).trans
        (stepHeader_tag _ layer layerCell)
  simpa using actual.trans
    (congrArg (fun word : BitVec 32 =>
      word.extractLsb' (8 * byte.val) 8) value)

theorem stepReady_positionByte (state : MachineState) (position : Nat)
    (positionCell : (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      0x43010 = BitVec.ofNat 64 position)
    (byte : Fin 4) :
    (stepReady state).getByte
      (BitVec.ofNat 64 (0x40004 + byte.val)) =
      (BitVec.ofNat 32 position).extractLsb' (8 * byte.val) 8 := by
  have actual := variableWord_byte (stepReady state) 0x40004
    (by decide) (by decide) (0 : Fin 5) byte
  have value : (stepReady state).getWord32 0x40004 =
      BitVec.ofNat 32 position := by
    simpa [word] using
      (stepReady_headerWords state (1 : Fin 5)).trans
        (stepHeader_position _ position positionCell)
  simpa using actual.trans
    (congrArg (fun word : BitVec 32 =>
      word.extractLsb' (8 * byte.val) 8) value)

theorem stepReady_treeByte (state : MachineState) (tree : TreeIndex)
    (treeCell :
      (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
        0x43008 = BitVec.ofNat 64 tree.val)
    (byte : Fin 8) :
    (stepReady state).getByte
      (BitVec.ofNat 64 (0x40008 + byte.val)) =
      (BitVec.ofNat 64 tree.val).extractLsb' (8 * byte.val) 8 := by
  have cell : (stepReady state).getMem 0x40008 =
      BitVec.ofNat 64 tree.val := (stepReady_tree state).trans treeCell
  have cell' : (stepReady state).getMem (262152#64) =
      BitVec.ofNat 64 tree.val := by simpa using cell
  fin_cases byte <;>
    simp [MachineState.getByte, alignToDword, byteOffset, cell',
      extractByte, BitVec.setWidth_ushiftRight_eq_extractLsb]
  have small : tree.val < 2 ^ 64 := by
    have := tree.isLt
    unfold totalHeight at this
    omega
  simp [BitVec.extractLsb']
  rw [Nat.mod_eq_of_lt (by simpa using small)]

theorem stepReady_indexByte (state : MachineState) (leaf : LeafIndex)
    (leafCell :
      (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
        0x43018 = BitVec.ofNat 64 leaf.val)
    (byte : Fin 4) :
    (stepReady state).getByte
      (BitVec.ofNat 64 (0x40010 + byte.val)) =
      (BitVec.ofNat 32 leaf.val).extractLsb' (8 * byte.val) 8 := by
  have actual := variableWord_byte (stepReady state) 0x40010
    (by decide) (by decide) (0 : Fin 5) byte
  have value : (stepReady state).getWord32 0x40010 =
      BitVec.ofNat 32 leaf.val := by
    rw [stepReady_index, leafCell]
    simp
  simpa using actual.trans
    (congrArg (fun word : BitVec 32 =>
      word.extractLsb' (8 * byte.val) 8) value)

theorem stepReady_headerBytes (state : MachineState)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (position : Nat)
    (layerCell : (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      0x43000 = BitVec.ofNat 64 layer.val)
    (positionCell : (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      0x43010 = BitVec.ofNat 64 position)
    (treeCell : (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      0x43018 = BitVec.ofNat 64 leaf.val)
    (byte : Fin 20) :
    (stepReady state).getByte (BitVec.ofNat 64 (0x40000 + byte.val)) =
      ((fieldBytes (tweakFields 1 layer.val tree.val position leaf.val)).map
        UInt8.toBitVec)[byte.val]'(by simp [fieldBytes, bytesLE]) := by
  fin_cases byte <;>
    first
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_tagByte state layer layerCell (0 : Fin 4)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_tagByte state layer layerCell (1 : Fin 4)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_tagByte state layer layerCell (2 : Fin 4)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_tagByte state layer layerCell (3 : Fin 4)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_positionByte state position positionCell (0 : Fin 4)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_positionByte state position positionCell (1 : Fin 4)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_positionByte state position positionCell (2 : Fin 4)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_positionByte state position positionCell (3 : Fin 4)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_treeByte state tree treeCell (0 : Fin 8)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_treeByte state tree treeCell (1 : Fin 8)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_treeByte state tree treeCell (2 : Fin 8)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_treeByte state tree treeCell (3 : Fin 8)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_treeByte state tree treeCell (4 : Fin 8)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_treeByte state tree treeCell (5 : Fin 8)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_treeByte state tree treeCell (6 : Fin 8)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_treeByte state tree treeCell (7 : Fin 8)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_indexByte state leaf leafCell (0 : Fin 4)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_indexByte state leaf leafCell (1 : Fin 4)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_indexByte state leaf leafCell (2 : Fin 4)
    | simpa [chainHeader_eq, bytesLE] using
        stepReady_indexByte state leaf leafCell (3 : Fin 4)

theorem stepReady_parameterWords (state : MachineState) (index : Fin 5) :
    (stepReady state).getWord32 (word 0x40014 index) =
      (stepHeaderState
        (SphincsVerifierWotsStepBody.stepHashPrefixState state)).getWord32
          (word 0x22cb4 index) := by
  let headed := stepHeaderState
    (SphincsVerifierWotsStepBody.stepHashPrefixState state)
  let pointers := stepParameterPointers headed
  have source : pointers.getReg .x6 = 0x22cb4 := by
    simp [pointers, stepParameterPointers, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  have destination : pointers.getReg .x7 = 0x40014 := by
    simp [pointers, stepParameterPointers, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq]
  have registers (s : MachineState) (address : Word) :
      (stepHashRegistersState s).getWord32 address =
        s.getWord32 address := by
    simp [stepHashRegistersState, MachineState.getWord32, execInstrBr]
  change (stepHashRegistersState (copyRootState pointers)).getWord32 _ = _
  rw [registers]
  have copied := copy20_data pointers 0x22cb4 0x40014 source destination
    (by intro i j; fin_cases i <;> fin_cases j <;> decide)
    (by intro i j different
        fin_cases i <;> fin_cases j <;>
          first | exact (different rfl).elim | decide)
    index
  rw [copied]
  simpa only [headed] using (by
    simp [pointers, stepParameterPointers, execInstrBr,
      MachineState.getWord32] :
      pointers.getWord32 (word 0x22cb4 index) =
        headed.getWord32 (word 0x22cb4 index))

theorem stepReady_parameterWords_from_state (state : MachineState)
    (index : Fin 5) :
    (stepReady state).getWord32 (word 0x40014 index) =
      state.getWord32 (word 0x22cb4 index) := by
  exact (stepReady_parameterWords state index).trans
    ((stepHeader_parameterSourceFrame
      (SphincsVerifierWotsStepBody.stepHashPrefixState state) index).trans
      (stepPrefix_parameterSourceFrame state index))

theorem stepReady_parameterBytes (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (encoded : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (i : Nat) (hi : i < 20) :
    (stepReady state).getByte (BitVec.ofNat 64 (0x40014 + i)) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  apply SphincsVerifierSecondHashBytes.parameter_bytes_of_words
    (stepReady state) state pk
      (fun index => by
        simpa only [word] using
          stepReady_parameterWords_from_state state index)
      encoded i hi

theorem stepReady_payloadBytes (state : MachineState)
    (i : Nat) (hi : i < 20) :
    (stepReady state).getByte (BitVec.ofNat 64 (0x40028 + i)) =
      state.getByte (BitVec.ofNat 64 (0x44b00 + i)) := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  have ready := variableWord_byte (stepReady state) 0x40028
    (by decide) (by decide) index byte
  have original := variableWord_byte state 0x44b00
    (by decide) (by decide) index byte
  have words := stepReady_payloadWords state index
  simpa only [Nat.add_assoc, split] using
    ready.trans ((congrArg (fun value : BitVec 32 =>
      value.extractLsb' (8 * byte.val) 8) words).trans original.symm)

theorem stepReady_chainQuery (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) (value : Digest)
    (layerCell : (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      0x43000 = BitVec.ofNat 64 layer.val)
    (positionCell : (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      0x43010 = BitVec.ofNat 64
        (chainLength * chain.val + step.val))
    (treeCell : (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
      0x43018 = BitVec.ofNat 64 leaf.val)
    (parameterEncoded : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (valueEncoded : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x44b00 + i)) =
        value.extractLsb' (8 * i) 8) :
    hashInput (stepReady state) =
      toQuery (chainInput pk.parameter layer tree leaf chain step value) := by
  apply stepReady_chainQuery_of_bytes state pk.parameter layer tree leaf
    chain step value
  intro i hi
  have hi60 : i < 60 := by
    simpa [chainInput_length] using hi
  by_cases header : i < 20
  · let byte : Fin 20 := ⟨i, header⟩
    have actual := stepReady_headerBytes state layer tree leaf
      (chainLength * chain.val + step.val) layerCell positionCell
      treeCell leafCell byte
    have expected := chainInput_header pk.parameter layer tree leaf
      chain step value i header
    simpa [byte] using actual.trans expected.symm
  · by_cases parameter : i < 40
    · have smaller : i - 20 < 20 := by omega
      have split : 20 + (i - 20) = i := by omega
      have actual := stepReady_parameterBytes state pk parameterEncoded
        (i - 20) smaller
      have expected := chainInput_parameter pk.parameter layer tree leaf
        chain step value (i - 20) smaller
      have joined := actual.trans expected.symm
      simp only [split] at joined
      have address : 0x40014 + (i - 20) = 0x40000 + i := by omega
      rw [address] at joined
      exact joined

    · have smaller : i - 40 < 20 := by omega
      have split : 40 + (i - 40) = i := by omega
      have actual := (stepReady_payloadBytes state (i - 40) smaller).trans
        (valueEncoded (i - 40) smaller)
      have expected := chainInput_value pk.parameter layer tree leaf
        chain step value (i - 40) smaller
      have joined := actual.trans expected.symm
      simp only [split] at joined
      have address : 0x40028 + (i - 40) = 0x40000 + i := by omega
      rw [address] at joined
      exact joined

theorem stepReady_chainQuery_from_state (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) (value : Digest)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (chainCell : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (stepCell : state.getMem 0x43058 = BitVec.ofNat 64 step.val)
    (parameterEncoded : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (valueEncoded : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x44b00 + i)) =
        value.extractLsb' (8 * i) 8) :
    hashInput (stepReady state) =
      toQuery (chainInput pk.parameter layer tree leaf chain step value) := by
  have prefixLayer :
      (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
        0x43000 = BitVec.ofNat 64 layer.val := by
    rw [stepPrefix_controlCell state 0x43000
      (by decide) (by intro offset; fin_cases offset <;> decide)]
    exact layerCell
  have prefixTree :
      (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
        0x43008 = BitVec.ofNat 64 tree.val := by
    rw [stepPrefix_controlCell state 0x43008
      (by decide) (by intro offset; fin_cases offset <;> decide)]
    exact treeCell
  have prefixLeaf :
      (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
        0x43018 = BitVec.ofNat 64 leaf.val := by
    rw [stepPrefix_controlCell state 0x43018
      (by decide) (by intro offset; fin_cases offset <;> decide)]
    exact leafCell
  have copiedChain :
      (SphincsVerifierWotsStepBody.stepValueCopied state).getMem
        0x43050 = BitVec.ofNat 64 chain.val := by
    rw [stepValueCopied_controlCell state 0x43050
      (by intro offset; fin_cases offset <;> decide)]
    exact chainCell
  have copiedStep :
      (SphincsVerifierWotsStepBody.stepValueCopied state).getMem
        0x43058 = BitVec.ofNat 64 step.val := by
    rw [stepValueCopied_controlCell state 0x43058
      (by intro offset; fin_cases offset <;> decide)]
    exact stepCell
  have prefixPosition :
      (SphincsVerifierWotsStepBody.stepHashPrefixState state).getMem
        0x43010 = BitVec.ofNat 64
          (chainLength * chain.val + step.val) := by
    exact stepPosition_value
      (SphincsVerifierWotsStepBody.stepValueCopied state)
      chain step copiedChain copiedStep
  exact stepReady_chainQuery state pk layer tree leaf chain step value
    prefixLayer prefixPosition prefixTree prefixLeaf parameterEncoded
    valueEncoded

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepNext_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepNext_value

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepNext_valueByte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepNext_valueByte

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepNext_valueByte_of_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepNext_valueByte_of_query

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_chainQuery_of_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepReady_chainQuery_of_bytes

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.chainHeader_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chainHeader_eq

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepValueCopied_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepValueCopied_data

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepPrefix_parameterSourceFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepPrefix_parameterSourceFrame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepPosition_payloadFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepPosition_payloadFrame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepPosition_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepPosition_value

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepHeader_payloadFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepHeader_payloadFrame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepHeader_parameterSourceFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepHeader_parameterSourceFrame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepHeader_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepHeader_tree

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepHeader_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepHeader_tag

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepHeader_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepHeader_position

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepHeader_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepHeader_index

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_payloadWords' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepReady_payloadWords

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_headerWords' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepReady_headerWords

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_tagPosition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepReady_tagPosition

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepReady_tree

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepReady_index

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_parameterWords' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepReady_parameterWords

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_parameterWords_from_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepReady_parameterWords_from_state

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_parameterBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepReady_parameterBytes

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_payloadBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepReady_payloadBytes

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepTag_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepTag_value

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_chainQuery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepReady_chainQuery

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_chainQuery_from_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepReady_chainQuery_from_state

end SigGolfCandidate.SphincsVerifierWotsValue
