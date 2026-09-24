import SigGolfCandidate.SphincsVerifierLeafCode

/-! Memory frame properties for the repeated FORS selectors. -/

namespace SigGolfCandidate.SphincsVerifierLeavesFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierLeafCode
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierDigestDecode
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierLeaf0
open SigGolfCandidate.SphincsVerifierMessageHash
open SigGolfCandidate.SphincsVerifierMessageAnswer
open SigGolfCandidate.Hypertree.Signing

private theorem getByte_setPC (s : MachineState) (pc a : Word) :
    (s.setPC pc).getByte a = s.getByte a := by
  simp [MachineState.getByte]

set_option maxHeartbeats 0 in
theorem leafState_frame (tree : Fin 24) (state : MachineState)
    (address : Word)
    (different : address ≠ BitVec.ofNat 64 (0x44800 + tree.val)) :
    (leafState tree state).getByte address = state.getByte address := by
  fin_cases tree <;>
    simp at different <;>
    simp [leafState, execInstrBr, signExtend12, getByte_setByte,
      Memory.getByte_setReg, getByte_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      different]

theorem leafState_answer_byte (tree : Fin 24) (index : Fin 30)
    (state : MachineState) :
    (leafState tree state).getByte
      (BitVec.ofNat 64 (0x42000 + index.val)) =
      state.getByte (BitVec.ofNat 64 (0x42000 + index.val)) := by
  apply leafState_frame
  intro equal
  have value := congrArg BitVec.toNat equal
  have indexSmall : 0x42000 + index.val < 2 ^ 64 := by
    have bound := index.isLt
    omega
  have treeSmall : 0x44800 + tree.val < 2 ^ 64 := by
    have bound := tree.isLt
    omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexSmall,
    Nat.mod_eq_of_lt treeSmall] at value
  omega

theorem leafState_other_leaf (tree other : Fin 24)
    (state : MachineState) (different : other ≠ tree) :
    (leafState tree state).getByte
      (BitVec.ofNat 64 (0x44800 + other.val)) =
      state.getByte (BitVec.ofNat 64 (0x44800 + other.val)) := by
  apply leafState_frame
  intro equal
  have value := congrArg BitVec.toNat equal
  have otherSmall : 0x44800 + other.val < 2 ^ 64 := by
    have bound := other.isLt
    omega
  have treeSmall : 0x44800 + tree.val < 2 ^ 64 := by
    have bound := tree.isLt
    omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt otherSmall,
    Nat.mod_eq_of_lt treeSmall] at value
  have : other.val = tree.val := by omega
  exact different (Fin.ext this)

set_option maxHeartbeats 0 in
theorem indexStored_answer_byte (state : MachineState) (index : Fin 30) :
    (indexStoredState state).getByte
      (BitVec.ofNat 64 (0x42000 + index.val)) =
      state.getByte (BitVec.ofNat 64 (0x42000 + index.val)) := by
  fin_cases index <;>
    simp [indexStoredState, execInstrBr, signExtend12,
      MachineState.getByte, MachineState.getMem_setPC,
      MachineState.getMem_setReg, MachineState.getMem_setMem_ne,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      alignToDword]

theorem leafSelector_correct (tree : Fin 24) (state : MachineState)
    (answer : BitVec 256)
    (answerBytes : ∀ index : Fin 30,
      state.getByte (BitVec.ofNat 64 (0x42000 + index.val)) =
        answer.extractLsb' (8 * index.val) 8) :
    ((leafState tree state).getByte
      (BitVec.ofNat 64 (0x44800 + tree.val))).toNat =
      (SphincsSecurity.Concrete.digestLeaves
        (SphincsSecurity.truncateMessageDigest answer)
        ⟨tree.val, by
          have bound := tree.isLt
          simp [SphincsSecurity.ftsTrees]
          omega⟩).val := by
  rw [leaf_byte_nat]
  have first := answerBytes ⟨4 + tree.val, by
    have bound := tree.isLt
    omega⟩
  have second := answerBytes ⟨5 + tree.val, by
    have bound := tree.isLt
    omega⟩
  have address4 : 0x42000 + (4 + tree.val) = 0x42004 + tree.val := by omega
  have address5 : 0x42000 + (5 + tree.val) = 0x42005 + tree.val := by omega
  rw [address4] at first
  rw [address5] at second
  rw [first, second]
  exact leaf_from_answer_bytes_eq_digestLeaves answer
    ⟨tree.val, by
      have bound := tree.isLt
      simp [SphincsSecurity.ftsTrees]
      omega⟩

theorem messageReady_indexStored_answerBytes (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (answer : BitVec 256) (index : Fin 30) :
    (indexStoredState (indexValueState (writeHash state answer))).getByte
      (BitVec.ofNat 64 (0x42000 + index.val)) =
      answer.extractLsb' (8 * index.val) 8 := by
  rw [indexStored_answer_byte, indexValue_answer_byte]
  exact messageReady_answer_byte state pk message randomness ready answer
    index.val (by have bound := index.isLt; omega)

/-- info: 'SigGolfCandidate.SphincsVerifierLeavesFrame.leafSelector_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms leafSelector_correct

/-- info: 'SigGolfCandidate.SphincsVerifierLeavesFrame.messageReady_indexStored_answerBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_indexStored_answerBytes

end SigGolfCandidate.SphincsVerifierLeavesFrame
