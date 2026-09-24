import SigGolfCandidate.SphincsVerifierMessageHash

/-!
# The second HASH domain header

With four zero scratch slots, the 22 header instructions write the message
domain tag and zero position, tree, and index fields. The following parameter
copy preserves those header words, including the index word that shares its
doubleword with the first parameter word.
-/

namespace SigGolfCandidate.SphincsVerifierSecondHashHeader
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierSecondHashTag
open SigGolfCandidate.SphincsVerifierSecondHashParameter
open SigGolfCandidate.SphincsVerifierSecondHashSetup
open SigGolfCandidate.SphincsVerifierSecondHashFrame

def ScratchZero (state : MachineState) : Prop :=
  ∀ slot : Fin 4,
    state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) = 0

private theorem tag_scratch (state : MachineState) (slot : Fin 4) :
    (tagState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  simp only [tagState, execInstrBr, MachineState.getMem_setPC]
  rw [tagBeforeStore_pointer, setWord32_eq]
  rw [MachineState.getMem_setMem_ne (by fin_cases slot <;> decide)]
  exact tagBeforeStore_memory state _

private theorem position_scratch (state : MachineState) (slot : Fin 4)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.positionState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  simp only [SphincsVerifierHeader.positionState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.positionBeforeStore_pointer, destination]
  rw [setWord32_eq]
  rw [MachineState.getMem_setMem_ne (by fin_cases slot <;> decide)]
  exact SphincsVerifierHeader.positionBeforeStore_memory state _

private theorem tree_scratch (state : MachineState) (slot : Fin 4)
    (destination : state.getReg .x7 = 0x40000) :
    (SphincsVerifierHeader.treeState state).getMem
      (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) =
      state.getMem (BitVec.ofNat 64 (0x43000 + 8 * slot.val)) := by
  simp only [SphincsVerifierHeader.treeState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.treeBeforeStore_pointer, destination]
  rw [MachineState.getMem_setMem_ne (by fin_cases slot <;> decide)]
  exact SphincsVerifierHeader.treeBeforeStore_memory state _

theorem header_tag (state : MachineState) (zero : ScratchZero state) :
    (headerState state).getWord32 0x40000 = 0xc01 := by
  let tagged := tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 0x40000 = 0xc01
  rw [SphincsVerifierHashMemory.index_word_frame treed 0x40000 treePointer
      (by decide),
    SphincsVerifierHashMemory.tree_word_frame positioned 0x40000
      positionPointer (by decide),
    SphincsVerifierHashMemory.position_word_frame tagged 0x40000
      tagPointer (by decide)]
  exact tag_value state (by simpa using zero 0)

theorem header_position (state : MachineState) (zero : ScratchZero state) :
    (headerState state).getWord32 0x40004 = 0 := by
  let tagged := tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 0x40004 = 0
  rw [SphincsVerifierHashMemory.index_word_frame treed 0x40004 treePointer
      (by decide),
    SphincsVerifierHashMemory.tree_word_frame positioned 0x40004
      positionPointer (by decide)]
  apply SphincsVerifierHeader.position_value tagged tagPointer
  have cell : tagged.getMem (0x43010#64) = state.getMem (0x43010#64) := by
    simpa [tagged] using tag_scratch state 2
  rw [cell]
  simpa using zero 2

theorem header_tree (state : MachineState) (zero : ScratchZero state) :
    (headerState state).getMem 0x40008 = 0 := by
  let tagged := tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getMem 0x40008 = 0
  simp only [SphincsVerifierHeader.indexState, execInstrBr,
    MachineState.getMem_setPC]
  rw [SphincsVerifierHeader.indexBeforeStore_pointer, treePointer,
    setWord32_eq]
  rw [MachineState.getMem_setMem_ne (by decide),
    SphincsVerifierHeader.indexBeforeStore_memory]
  apply SphincsVerifierHeader.tree_value positioned positionPointer
  have cell1 : positioned.getMem (0x43008#64) = tagged.getMem (0x43008#64) := by
    simpa [positioned] using position_scratch tagged 1 tagPointer
  have cell0 : tagged.getMem (0x43008#64) = state.getMem (0x43008#64) := by
    simpa [tagged] using tag_scratch state 1
  rw [cell1, cell0]
  simpa using zero 1

theorem header_index (state : MachineState) (zero : ScratchZero state) :
    (headerState state).getWord32 0x40010 = 0 := by
  let tagged := tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagPointer := tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  change (SphincsVerifierHeader.indexState treed).getWord32 0x40010 = 0
  apply SphincsVerifierHeader.index_value treed treePointer
  have cell2 : treed.getMem (0x43018#64) = positioned.getMem (0x43018#64) := by
    simpa [treed] using tree_scratch positioned 3 positionPointer
  have cell1 : positioned.getMem (0x43018#64) = tagged.getMem (0x43018#64) := by
    simpa [positioned] using position_scratch tagged 3 tagPointer
  have cell0 : tagged.getMem (0x43018#64) = state.getMem (0x43018#64) := by
    simpa [tagged] using tag_scratch state 3
  rw [cell2, cell1, cell0]
  simpa using zero 3

theorem ready_header_word_frame (state : MachineState) (read : Word)
    (outside : ∀ offset : Fin 5,
      alignToDword (0x40014 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) ≠ alignToDword read ∨
      byteOffset (0x40014 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) / 4 ≠
          byteOffset read / 4) :
    (secondHashReadyState state).getWord32 read =
      (headerState state).getWord32 read := by
  change (hashRegistersState
    (copyRootState (parameterPointers (headerState state)))).getWord32 read =
      (headerState state).getWord32 read
  have registers : (hashRegistersState
      (copyRootState (parameterPointers (headerState state)))).getWord32 read =
      (copyRootState (parameterPointers (headerState state))).getWord32 read := by
    simp [MachineState.getWord32, hashRegisters_memory]
  rw [registers]
  have destination := (parameterPointers_regs (headerState state)).2
  rw [copyRoot_getWord32_frame
    (parameterPointers (headerState state)) read (by
      intro offset
      rw [destination]
      exact outside offset)]
  simp [MachineState.getWord32, parameterPointers_memory]

theorem ready_tag (state : MachineState) (zero : ScratchZero state) :
    (secondHashReadyState state).getWord32 0x40000 = 0xc01 := by
  rw [ready_header_word_frame state 0x40000 (by intro offset; fin_cases offset <;> decide)]
  exact header_tag state zero

theorem ready_position (state : MachineState) (zero : ScratchZero state) :
    (secondHashReadyState state).getWord32 0x40004 = 0 := by
  rw [ready_header_word_frame state 0x40004 (by intro offset; fin_cases offset <;> decide)]
  exact header_position state zero

theorem ready_index (state : MachineState) (zero : ScratchZero state) :
    (secondHashReadyState state).getWord32 0x40010 = 0 := by
  rw [ready_header_word_frame state 0x40010 (by intro offset; fin_cases offset <;> decide)]
  exact header_index state zero

theorem ready_tree (state : MachineState) (zero : ScratchZero state) :
    (secondHashReadyState state).getMem 0x40008 = 0 := by
  change (hashRegistersState
    (copyRootState (parameterPointers (headerState state)))).getMem 0x40008 = 0
  rw [hashRegisters_memory]
  have destination := (parameterPointers_regs (headerState state)).2
  rw [copyRoot_mem_frame (parameterPointers (headerState state)) 0x40008
      (by intro offset; rw [destination]; fin_cases offset <;> decide),
    parameterPointers_memory]
  exact header_tree state zero

private theorem extractByte_of_extractWord32 (word : Word) (lane : Fin 2)
    (byte : Fin 4) :
    extractByte word (4 * lane.val + byte.val) =
      (extractWord32 word lane.val).extractLsb' (8 * byte.val) 8 := by
  ext i (hi : i < 8)
  simp [extractByte, extractWord32, BitVec.truncate_eq_setWidth]
  have within : 8 * byte.val + i < 32 := by
    have := byte.isLt
    omega
  simp only [within]
  simp only [decide_true, Bool.true_and]
  congr 1
  omega

private theorem extractByte_from_word32 (word : Word) (position : Fin 8) :
    extractByte word position.val =
      (extractWord32 word (position.val / 4)).extractLsb'
        (8 * (position.val % 4)) 8 := by
  fin_cases position <;>
    first
    | exact extractByte_of_extractWord32 word 0 0
    | exact extractByte_of_extractWord32 word 0 1
    | exact extractByte_of_extractWord32 word 0 2
    | exact extractByte_of_extractWord32 word 0 3
    | exact extractByte_of_extractWord32 word 1 0
    | exact extractByte_of_extractWord32 word 1 1
    | exact extractByte_of_extractWord32 word 1 2
    | exact extractByte_of_extractWord32 word 1 3

private theorem headerWordByte (state : MachineState) (base : Nat)
    (supported : base = 0x40000 ∨ base = 0x40004 ∨ base = 0x40010)
    (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64 (base + byte.val)) =
      (state.getWord32 (BitVec.ofNat 64 base)).extractLsb'
        (8 * byte.val) 8 := by
  have split := extractByte_from_word32
    (state.getMem (alignToDword (BitVec.ofNat 64 (base + byte.val))))
    ⟨(base + byte.val) % 8, Nat.mod_lt _ (by decide)⟩
  rcases supported with h | h | h <;> subst base <;> fin_cases byte <;>
    simpa [MachineState.getByte, MachineState.getWord32,
      alignToDword, byteOffset] using split

theorem ready_tag_byte (state : MachineState) (zero : ScratchZero state)
    (byte : Fin 4) :
    (secondHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      (0xc01#32).extractLsb' (8 * byte.val) 8 := by
  rw [headerWordByte _ 0x40000 (Or.inl rfl) byte]
  have address : BitVec.ofNat 64 0x40000 = (0x40000 : Word) := by decide
  rw [address, ready_tag state zero]
  congr 1

theorem ready_position_byte (state : MachineState) (zero : ScratchZero state)
    (byte : Fin 4) :
    (secondHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40004 + byte.val)) = 0 := by
  rw [headerWordByte _ 0x40004 (Or.inr (Or.inl rfl)) byte]
  have address : BitVec.ofNat 64 0x40004 = (0x40004 : Word) := by decide
  rw [address, ready_position state zero]
  simp

theorem ready_tree_byte (state : MachineState) (zero : ScratchZero state)
    (byte : Fin 8) :
    (secondHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40008 + byte.val)) = 0 := by
  have tree : (secondHashReadyState state).getMem (262152#64) = 0 := by
    simpa using ready_tree state zero
  fin_cases byte <;>
    simp [MachineState.getByte, alignToDword, byteOffset, tree, extractByte]

theorem ready_index_byte (state : MachineState) (zero : ScratchZero state)
    (byte : Fin 4) :
    (secondHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40010 + byte.val)) = 0 := by
  rw [headerWordByte _ 0x40010 (Or.inr (Or.inr rfl)) byte]
  have address : BitVec.ofNat 64 0x40010 = (0x40010 : Word) := by decide
  rw [address, ready_index state zero]
  simp

theorem ready_header_byte (state : MachineState) (zero : ScratchZero state)
    (index : Fin 20) :
    (secondHashReadyState state).getByte
      (BitVec.ofNat 64 (0x40000 + index.val)) =
      ((SphincsSecurity.fieldBytes
        (SphincsSecurity.tweakFields 12 0 0 0 0)).map UInt8.toBitVec)[index.val]'(by
          simp [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
            SphincsSecurity.bytesLE]) := by
  fin_cases index <;>
    first
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_tag_byte state zero 0
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_tag_byte state zero 1
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_tag_byte state zero 2
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_tag_byte state zero 3
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_position_byte state zero 0
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_position_byte state zero 1
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_position_byte state zero 2
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_position_byte state zero 3
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_tree_byte state zero 0
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_tree_byte state zero 1
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_tree_byte state zero 2
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_tree_byte state zero 3
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_tree_byte state zero 4
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_tree_byte state zero 5
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_tree_byte state zero 6
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_tree_byte state zero 7
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_index_byte state zero 0
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_index_byte state zero 1
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_index_byte state zero 2
    | simpa [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields,
        SphincsSecurity.protocolDomainSep, SphincsSecurity.bytesLE] using
        ready_index_byte state zero 3

/-- info: 'SigGolfCandidate.SphincsVerifierSecondHashHeader.ready_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ready_index

end SigGolfCandidate.SphincsVerifierSecondHashHeader
