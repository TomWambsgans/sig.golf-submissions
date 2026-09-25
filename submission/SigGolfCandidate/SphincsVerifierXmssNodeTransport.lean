import SigGolfCandidate.SphincsVerifierXmssNodeHeader

namespace SigGolfCandidate.SphincsVerifierXmssNodeTransport
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssRound
open SigGolfCandidate.SphincsVerifierXmssPairSemantic
open SigGolfCandidate.SphincsVerifierXmssNodeHeader
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsParentExecution
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierFtsPair
open SigGolfCandidate.SphincsVerifierXmssPrefix
open SigGolfCandidate.SphincsVerifierFtsPostForestCopy
open SigGolfCandidate.SphincsVerifierLoader
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierXmssNodeReady
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem pairState_eq_generic (s : MachineState) :
    SphincsVerifierXmssRound.pairState s =
      SphincsVerifierFtsPair.pairState s := by
  simp [SphincsVerifierXmssRound.pairState,
    SphincsVerifierFtsPair.pairState,
    SphincsVerifierXmssPairSemantic.leftPairState',
    SphincsVerifierXmssPairSemantic.rightPairState,
    SphincsVerifierXmssParity.nodeBranchState,
    SphincsVerifierXmssParity.nodeParity_reg,
    SphincsVerifierFtsLevelBranch.branchState]

theorem prefixState_eq_generic (s : MachineState) :
    nodePrefixState (SphincsVerifierXmssRound.pairState s) =
      firstPositionedState s := by
  rw [pairState_eq_generic]
  rfl

theorem prefix_low_mem (s : MachineState) (read : Word)
    (low : read.toNat < 0x40000) :
    (nodePrefixState (SphincsVerifierXmssRound.pairState s)).getMem read =
      s.getMem read := by
  rw [prefixState_eq_generic]
  exact positioned_low_mem_frame s read low

theorem prefix_scratch_mem (s : MachineState) (read : Word)
    (notPtr : read ≠ 0x43028)
    (notBit : read ≠ 0x43070)
    (notIndex : read ≠ 0x43018)
    (notLevel : read ≠ 0x43010)
    (outsideLeft : ∀ offset : Fin 5,
      read ≠ alignToDword
        (0x40028 + signExtend12 (4#12 * BitVec.ofNat 12 offset.val)))
    (outsideRight : ∀ offset : Fin 5,
      read ≠ alignToDword
        (0x4003c + signExtend12 (4#12 * BitVec.ofNat 12 offset.val))) :
    (nodePrefixState (SphincsVerifierXmssRound.pairState s)).getMem read =
      s.getMem read := by
  rw [prefixState_eq_generic]
  change (levelPositionState
    (shiftIndexState (advancePointerState (SphincsVerifierFtsPair.pairState s)))).getMem read = _
  rw [levelPosition_mem_frame _ read notLevel,
    shiftIndex_mem_frame _ read notBit notIndex,
    advancePointer_mem_frame _ read notPtr,
    pair_scratch_frame s read outsideLeft outsideRight]

theorem prefix_layer_cell (s : MachineState) :
    (nodePrefixState (SphincsVerifierXmssRound.pairState s)).getMem 0x43000 =
      s.getMem 0x43000 := by
  apply prefix_scratch_mem s 0x43000 <;> decide

theorem prefix_tree_cell (s : MachineState) :
    (nodePrefixState (SphincsVerifierXmssRound.pairState s)).getMem 0x43008 =
      s.getMem 0x43008 := by
  apply prefix_scratch_mem s 0x43008 <;> decide

theorem prefix_level_cell (s : MachineState) :
    (nodePrefixState (SphincsVerifierXmssRound.pairState s)).getMem 0x43010 =
      s.getMem 0x43048 := by
  rw [prefixState_eq_generic]
  change (levelPositionState (shiftIndexState
    (advancePointerState (SphincsVerifierFtsPair.pairState s)))).getMem 0x43010 = _
  rw [levelPosition_cell,
    shiftIndex_mem_frame _ 0x43048 (by decide) (by decide),
    advancePointer_mem_frame _ 0x43048 (by decide)]
  apply pair_scratch_frame
  · intro offset; fin_cases offset <;> decide
  · intro offset; fin_cases offset <;> decide

theorem prefix_index_cell (s : MachineState) :
    (nodePrefixState (SphincsVerifierXmssRound.pairState s)).getMem 0x43018 =
      s.getMem 0x43070 >>> 1 := by
  rw [prefixState_eq_generic]
  change (levelPositionState (shiftIndexState
    (advancePointerState (SphincsVerifierFtsPair.pairState s)))).getMem 0x43018 = _
  rw [levelPosition_mem_frame _ 0x43018 (by decide),
    (shiftIndex_cells _).2,
    advancePointer_mem_frame _ 0x43070 (by decide)]
  congr 1
  apply pair_scratch_frame
  · intro offset; fin_cases offset <;> decide
  · intro offset; fin_cases offset <;> decide

theorem prefix_WitnessPrefix (s : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (encoded : WitnessPrefix s pk) :
    WitnessPrefix
      (nodePrefixState (SphincsVerifierXmssRound.pairState s)) pk := by
  apply witnessPrefix_of_low_mem_frame s _ pk encoded
  exact fun read low => prefix_low_mem s read low

theorem prefix_pair_words (s : MachineState) (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (index : Fin 5) :
    let p := nodePrefixState (SphincsVerifierXmssRound.pairState s)
    if s.getMem 0x43070 &&& 1 = 0 then
      p.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) ∧
      p.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        s.getWord32 (BitVec.ofNat 64 (pointer.toNat + 4 * index.val))
    else
      p.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        s.getWord32 (BitVec.ofNat 64 (pointer.toNat + 4 * index.val)) ∧
      p.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  let pair := SphincsVerifierXmssRound.pairState s
  let advanced := advancePointerState pair
  let shifted := shiftIndexState advanced
  let positioned := levelPositionState shifted
  have positionWords := levelPosition_pair_data shifted index
  have shiftWords := shiftIndex_pair_data advanced index
  have advanceWords := advancePointer_pair_data pair index
  have first : positioned.getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
        pair.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) :=
    (positionWords.1.trans shiftWords.1).trans advanceWords.1
  have second : positioned.getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * index.val)) =
        pair.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * index.val)) :=
    (positionWords.2.trans shiftWords.2).trans advanceWords.2
  by_cases even : s.getMem 0x43070 &&& 1 = 0
  · have pairWords := leftPair_words s pointer pointerValue small index
    simp only [even, if_true, pair, SphincsVerifierXmssRound.pairState] at first second
    simp only [even, if_true]
    exact ⟨first.trans pairWords.1, second.trans pairWords.2⟩
  · have pairWords := rightPair_words s pointer pointerValue small index
    simp only [even, if_false, pair, SphincsVerifierXmssRound.pairState] at first second
    simp only [even, if_false]
    exact ⟨first.trans pairWords.1, second.trans pairWords.2⟩

theorem prefix_pair_bytes (s : MachineState) (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0)
    (i : Nat) (hi : i < 20) :
    let p := nodePrefixState (SphincsVerifierXmssRound.pairState s)
    if s.getMem 0x43070 &&& 1 = 0 then
      p.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        s.getByte (BitVec.ofNat 64 (0x44a00 + i)) ∧
      p.getByte (BitVec.ofNat 64 (0x4003c + i)) =
        s.getByte (BitVec.ofNat 64 (pointer.toNat + i))
    else
      p.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        s.getByte (BitVec.ofNat 64 (pointer.toNat + i)) ∧
      p.getByte (BitVec.ofNat 64 (0x4003c + i)) =
        s.getByte (BitVec.ofNat 64 (0x44a00 + i)) := by
  let p := nodePrefixState (SphincsVerifierXmssRound.pairState s)
  have words := prefix_pair_words s pointer pointerValue small
  by_cases even : s.getMem 0x43070 &&& 1 = 0
  · simp only [even, if_true]
    constructor
    · apply transfer_words_to_bytes _ _ 0x40028 0x44a00
        (by decide) (by decide) (by decide) (by decide) _ i hi
      intro index
      have pair := words index
      simp only [even, if_true] at pair
      exact pair.1
    · apply transfer_words_to_bytes _ _ 0x4003c pointer.toNat
        (by decide) (by omega) (by decide) aligned _ i hi
      intro index
      have pair := words index
      simp only [even, if_true] at pair
      exact pair.2
  · simp only [even, if_false]
    constructor
    · apply transfer_words_to_bytes _ _ 0x40028 pointer.toNat
        (by decide) (by omega) (by decide) aligned _ i hi
      intro index
      have pair := words index
      simp only [even, if_false] at pair
      exact pair.1
    · apply transfer_words_to_bytes _ _ 0x4003c 0x44a00
        (by decide) (by decide) (by decide) (by decide) _ i hi
      intro index
      have pair := words index
      simp only [even, if_false] at pair
      exact pair.2

theorem ready_hashInput_from_pair (s : MachineState)
    (pk : SphincsSecurity.PublicKey) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) (current sibling : Digest) (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0)
    (layerCell : s.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (treeCell : s.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (levelCell : s.getMem 0x43048 = BitVec.ofNat 64 level)
    (indexCell : s.getMem 0x43070 >>> 1 = BitVec.ofNat 64 nodeIdx)
    (parameterEncoded : WitnessPrefix s pk)
    (currentEncoded : ∀ i, (hi : i < 20) →
      s.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        current.extractLsb' (8 * i) 8)
    (siblingEncoded : ∀ i, (hi : i < 20) →
      s.getByte (BitVec.ofNat 64 (pointer.toNat + i)) =
        sibling.extractLsb' (8 * i) 8) :
    hashInput (readyState s) =
      toQuery (nodeInput pk lay tree level nodeIdx
        (if s.getMem 0x43070 &&& 1 = 0 then current else sibling)
        (if s.getMem 0x43070 &&& 1 = 0 then sibling else current)) := by
  let p := nodePrefixState (SphincsVerifierXmssRound.pairState s)
  have hLayer : p.getMem 0x43000 = BitVec.ofNat 64 lay.val := by
    rw [prefix_layer_cell]
    exact layerCell
  have hTree : p.getMem 0x43008 = BitVec.ofNat 64 tree.val := by
    rw [prefix_tree_cell]
    exact treeCell
  have hLevel : p.getMem 0x43010 = BitVec.ofNat 64 level := by
    rw [prefix_level_cell]
    exact levelCell
  have hIndex : p.getMem 0x43018 = BitVec.ofNat 64 nodeIdx := by
    rw [prefix_index_cell]
    exact indexCell
  have hParameter : WitnessPrefix p pk :=
    prefix_WitnessPrefix s pk parameterEncoded
  by_cases even : s.getMem 0x43070 &&& 1 = 0
  · simp only [even, if_true]
    change hashInput (nodeReadyState p) = _
    apply ready_hashInput_node p pk lay tree level nodeIdx current sibling
      hLayer hLevel hTree hIndex hParameter
    · intro i hi
      have pair := prefix_pair_bytes s pointer pointerValue small aligned i hi
      simp only [even, if_true] at pair
      exact pair.1.trans (currentEncoded i hi)
    · intro i hi
      have pair := prefix_pair_bytes s pointer pointerValue small aligned i hi
      simp only [even, if_true] at pair
      exact pair.2.trans (siblingEncoded i hi)
  · simp only [even, if_false]
    change hashInput (nodeReadyState p) = _
    apply ready_hashInput_node p pk lay tree level nodeIdx sibling current
      hLayer hLevel hTree hIndex hParameter
    · intro i hi
      have pair := prefix_pair_bytes s pointer pointerValue small aligned i hi
      simp only [even, if_false] at pair
      exact pair.1.trans (siblingEncoded i hi)
    · intro i hi
      have pair := prefix_pair_bytes s pointer pointerValue small aligned i hi
      simp only [even, if_false] at pair
      exact pair.2.trans (currentEncoded i hi)

#print axioms pairState_eq_generic
#print axioms prefix_low_mem
#print axioms prefix_scratch_mem
#print axioms prefix_layer_cell
#print axioms prefix_tree_cell
#print axioms prefix_level_cell
#print axioms prefix_index_cell
#print axioms prefix_WitnessPrefix
#print axioms prefix_pair_words
#print axioms prefix_pair_bytes
/-- info: 'SigGolfCandidate.SphincsVerifierXmssNodeTransport.ready_hashInput_from_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ready_hashInput_from_pair

end SigGolfCandidate.SphincsVerifierXmssNodeTransport
