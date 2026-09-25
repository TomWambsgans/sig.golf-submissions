import SigGolfCandidate.SphincsVerifierXmssRound
import SigGolfCandidate.SphincsVerifierFtsParentPayload

namespace SigGolfCandidate.SphincsVerifierXmssNodeValue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssNodeReady
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierHashMemory
open SigGolfCandidate.SphincsVerifierMessageFields
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierFtsParentSetup
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem tag_mem_frame (s : MachineState) (address : Word)
    (outside : address ≠ alignToDword (0x40000#64)) :
    (nodeTagState s).getMem address = s.getMem address := by
  simp [nodeTagState, execInstrBr, signExtend12, setWord32_eq, outside,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem tag_word_frame (s : MachineState) (address : Word)
    (outside : alignToDword address ≠ alignToDword (0x40000#64)) :
    (nodeTagState s).getWord32 address = s.getWord32 address := by
  simp only [MachineState.getWord32]
  rw [tag_mem_frame s (alignToDword address) outside]

theorem tag_value (lay : Layer) (s : MachineState)
    (layerCell : s.getMem 0x43000 = BitVec.ofNat 64 lay.val) :
    (nodeTagState s).getWord32 0x40000 =
      BitVec.ofNat 32 (0x301 + 0x10000 * lay.val) := by
  change s.getMem (274432#64) = _ at layerCell
  simp [nodeTagState, execInstrBr, signExtend12,
    getWord32_setWord32_same, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  rw [layerCell]
  fin_cases lay <;> decide

theorem header_pair_words (s : MachineState) (i : Fin 5) :
    (nodeHeaderState (nodeTagState s)).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * i.val)) ∧
    (nodeHeaderState (nodeTagState s)).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * i.val)) := by
  let tagged := nodeTagState s
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagDst := tag_pointer s
  have posDst : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagDst
  have treeDst : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans posDst
  constructor
  · change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
    rw [index_word_frame treed _ treeDst (by fin_cases i <;> decide),
      tree_word_frame positioned _ posDst (by fin_cases i <;> decide),
      position_word_frame tagged _ tagDst (by fin_cases i <;> decide),
      tag_word_frame s _ (by fin_cases i <;> decide)]

  · change (SphincsVerifierHeader.indexState treed).getWord32 _ = _
    rw [index_word_frame treed _ treeDst (by fin_cases i <;> decide),
      tree_word_frame positioned _ posDst (by fin_cases i <;> decide),
      position_word_frame tagged _ tagDst (by fin_cases i <;> decide),
      tag_word_frame s _ (by fin_cases i <;> decide)]

theorem ready_pair_words (s : MachineState) (i : Fin 5) :
    (nodeReadyState s).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * i.val)) ∧
    (nodeReadyState s).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x4003c + 4 * i.val)) := by
  let headed := nodeHeaderState (nodeTagState s)
  let pointers := SphincsVerifierFtsParentParameter.parameterPointers headed
  have destination :=
    (SphincsVerifierFtsParentParameter.parameterPointers_regs headed).2
  have pair := header_pair_words s i
  have registers (t : MachineState) (address : Word) :
      (hashRegistersState t).getWord32 address = t.getWord32 address := by
    simp [MachineState.getWord32, hashRegistersState, execInstrBr]
  constructor
  · change (hashRegistersState (copyRootState pointers)).getWord32 _ = _
    rw [registers]
    rw [copyRoot_getWord32_frame pointers _ (by
      intro offset
      rw [destination]
      fin_cases offset <;> fin_cases i <;> decide)]
    simp [pointers, SphincsVerifierFtsParentParameter.parameterPointers,
      execInstrBr, MachineState.getWord32]
    exact pair.1
  · change (hashRegistersState (copyRootState pointers)).getWord32 _ = _
    rw [registers]
    rw [copyRoot_getWord32_frame pointers _ (by
      intro offset
      rw [destination]
      fin_cases offset <;> fin_cases i <;> decide)]
    simp [pointers, SphincsVerifierFtsParentParameter.parameterPointers,
      execInstrBr, MachineState.getWord32]
    exact pair.2

theorem ready_header_word_frame (s : MachineState) (read : Word)
    (outside : ∀ offset : Fin 5,
      alignToDword (0x40014 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) ≠ alignToDword read ∨
      byteOffset (0x40014 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) / 4 ≠
          byteOffset read / 4) :
    (nodeReadyState s).getWord32 read =
      (nodeHeaderState (nodeTagState s)).getWord32 read := by
  let headed := nodeHeaderState (nodeTagState s)
  let pointers := SphincsVerifierFtsParentParameter.parameterPointers headed
  change (hashRegistersState (copyRootState pointers)).getWord32 read =
    headed.getWord32 read
  have registers (t : MachineState) (address : Word) :
      (hashRegistersState t).getWord32 address = t.getWord32 address := by
    simp [MachineState.getWord32, hashRegistersState, execInstrBr]
  rw [registers]
  rw [copyRoot_getWord32_frame pointers read outside]
  simp [pointers, SphincsVerifierFtsParentParameter.parameterPointers,
    execInstrBr, MachineState.getWord32]

theorem ready_tag_word (lay : Layer) (s : MachineState)
    (layerCell : s.getMem 0x43000 = BitVec.ofNat 64 lay.val) :
    (nodeReadyState s).getWord32 0x40000 =
      BitVec.ofNat 32 (0x301 + 0x10000 * lay.val) := by
  let tagged := nodeTagState s
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  have tagDst := tag_pointer s
  have posDst : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagDst
  have treeDst : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans posDst
  rw [ready_header_word_frame s 0x40000
    (by intro offset; fin_cases offset <;> decide)]
  change (SphincsVerifierHeader.indexState treed).getWord32 0x40000 = _
  rw [index_word_frame treed _ treeDst (by decide),
    tree_word_frame positioned _ posDst (by decide),
    position_word_frame tagged _ tagDst (by decide)]
  exact tag_value lay s layerCell

/-- info: 'SigGolfCandidate.SphincsVerifierXmssNodeValue.tag_mem_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tag_mem_frame
/-- info: 'SigGolfCandidate.SphincsVerifierXmssNodeValue.tag_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tag_value
/-- info: 'SigGolfCandidate.SphincsVerifierXmssNodeValue.header_pair_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms header_pair_words
/-- info: 'SigGolfCandidate.SphincsVerifierXmssNodeValue.ready_pair_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ready_pair_words
/-- info: 'SigGolfCandidate.SphincsVerifierXmssNodeValue.ready_header_word_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ready_header_word_frame
/-- info: 'SigGolfCandidate.SphincsVerifierXmssNodeValue.ready_tag_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ready_tag_word

end SigGolfCandidate.SphincsVerifierXmssNodeValue
