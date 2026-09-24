import SigGolfCandidate.SphincsVerifierFtsParentPayload

/-! The first FORS parent HASH domain tag and level position reach the ECALL buffer. -/

namespace SigGolfCandidate.SphincsVerifierFtsParentFields
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierFtsParentTag
open SigGolfCandidate.SphincsVerifierFtsParentHeader
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierFtsParentSetup
set_option maxRecDepth 16384

theorem header_tag_position (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0)
    (positionOne : state.getMem 0x43010 = 1) :
    (parentHeaderState state).getWord32 0x40000 = 0xa01 ∧
      (parentHeaderState state).getWord32 0x40004 = 1 := by
  let prefixed := parentPrefixState state
  let treed := SphincsVerifierHeader.treeState prefixed
  have prefixPointer : prefixed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer (parentTagState state)).trans
      (parentTag_hash_pointer state)
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer prefixed).trans prefixPointer
  have values := parentPrefix_values state layerZero positionOne
  constructor
  · change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
    rw [index_word_frame treed _ treePointer (by decide),
      tree_word_frame prefixed _ prefixPointer (by decide)]
    exact values.1
  · change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
    rw [index_word_frame treed _ treePointer (by decide),
      tree_word_frame prefixed _ prefixPointer (by decide)]
    exact values.2

private theorem ready_word_frame (state : MachineState) (read : Word)
    (outside : ∀ offset : Fin 5,
      alignToDword (0x40014 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) ≠ alignToDword read ∨
      byteOffset (0x40014 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) / 4 ≠
          byteOffset read / 4) :
    (parentHashReadyState state).getWord32 read =
      (parentHeaderState state).getWord32 read := by
  let headed := parentHeaderState state
  let pointers := parameterPointers headed
  change (hashRegistersState (copyRootState pointers)).getWord32 read =
    headed.getWord32 read
  have registers (s : MachineState) (address : Word) :
      (hashRegistersState s).getWord32 address = s.getWord32 address := by
    simp [MachineState.getWord32, hashRegistersState, execInstrBr]
  rw [registers]
  rw [copyRoot_getWord32_frame pointers read outside]
  simp [pointers, parameterPointers, execInstrBr, MachineState.getWord32]

theorem ready_tag_position (state : MachineState)
    (layerZero : state.getMem 0x43000 = 0)
    (positionOne : state.getMem 0x43010 = 1) :
    (parentHashReadyState state).getWord32 0x40000 = 0xa01 ∧
      (parentHashReadyState state).getWord32 0x40004 = 1 := by
  have values := header_tag_position state layerZero positionOne
  constructor
  · rw [ready_word_frame state 0x40000 (by intro offset; fin_cases offset <;> decide)]
    exact values.1
  · rw [ready_word_frame state 0x40004 (by intro offset; fin_cases offset <;> decide)]
    exact values.2

/-- info: 'SigGolfCandidate.SphincsVerifierFtsParentFields.ready_tag_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ready_tag_position

end SigGolfCandidate.SphincsVerifierFtsParentFields
