import SigGolfCandidate.SphincsVerifierWotsSemanticLoop
import SigGolfCandidate.SphincsSecurity.Proof.Ots.ExtractChain

namespace SigGolfCandidate.SphincsVerifierWotsSemanticWalk
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierWotsValue
open SigGolfCandidate.SphincsVerifierWotsStepIteration
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- A verifier hash step is precisely one abstract WOTS chain step. -/
theorem stepNext_walkByte (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (step : ChainStep)
    (start offset : Nat) (initial : Digest)
    (stepEq : step.val = start + offset)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (chainCell : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (stepCell : state.getMem 0x43058 = BitVec.ofNat 64 step.val)
    (parameterEncoded : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (valueEncoded : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x44b00 + i)) =
        (Concrete.walkValue (adaptOracle hash) pk.parameter layer tree leaf
          chain start initial offset).extractLsb' (8 * i) 8)
    (i : Nat) (hi : i < 20) :
    (stepNext hash state).getByte (BitVec.ofNat 64 (0x44b00 + i)) =
      (Concrete.walkValue (adaptOracle hash) pk.parameter layer tree leaf
        chain start initial (offset + 1)).extractLsb' (8 * i) 8 := by
  have range : start + offset < chainLength - 1 := by
    rw [← stepEq]
    exact step.isLt
  have next := stepNext_abstractValueByte hash state pk layer tree leaf chain step
    (Concrete.walkValue (adaptOracle hash) pk.parameter layer tree leaf
      chain start initial offset)
    layerCell treeCell leafCell chainCell stepCell parameterEncoded valueEncoded i hi
  rw [Concrete.walkValue_succ (adaptOracle hash) pk.parameter layer tree leaf
    chain start initial offset range]
  have stepSame : (⟨start + offset, range⟩ : ChainStep) = step := by
    apply Fin.ext
    exact stepEq.symm
  rw [stepSame]
  simpa only [adaptOracle, chainInput] using next

theorem stepCheck_mem (state : MachineState) (address : Word) :
    (SphincsVerifierWotsStepCheck.stepCheckState state).getMem address =
      state.getMem address := by
  simp [SphincsVerifierWotsStepCheck.stepCheckState, execInstrBr]

theorem stepCheck_byte (state : MachineState) (address : Word) :
    (SphincsVerifierWotsStepCheck.stepCheckState state).getByte address =
      state.getByte address := by
  simp [MachineState.getByte, stepCheck_mem]

theorem stepRound_walkByte (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (step : ChainStep)
    (start offset : Nat) (initial : Digest)
    (stepEq : step.val = start + offset)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (chainCell : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (stepCell : state.getMem 0x43058 = BitVec.ofNat 64 step.val)
    (parameterEncoded : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (valueEncoded : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x44b00 + i)) =
        (Concrete.walkValue (adaptOracle hash) pk.parameter layer tree leaf
          chain start initial offset).extractLsb' (8 * i) 8)
    (i : Nat) (hi : i < 20) :
    (stepRound hash state).getByte (BitVec.ofNat 64 (0x44b00 + i)) =
      (Concrete.walkValue (adaptOracle hash) pk.parameter layer tree leaf
        chain start initial (offset + 1)).extractLsb' (8 * i) 8 := by
  have checkedPrefix : SphincsVerifierHashBytes.WitnessPrefix
      (SphincsVerifierWotsStepCheck.stepCheckState state) pk := by
    apply SphincsVerifierFtsPostForestCopy.witnessPrefix_of_low_mem_frame
      state (SphincsVerifierWotsStepCheck.stepCheckState state) pk parameterEncoded
    intro address _
    exact stepCheck_mem state address
  have checkedValue : ∀ j, (hj : j < 20) →
      (SphincsVerifierWotsStepCheck.stepCheckState state).getByte
        (BitVec.ofNat 64 (0x44b00 + j)) =
        (Concrete.walkValue (adaptOracle hash) pk.parameter layer tree leaf
          chain start initial offset).extractLsb' (8 * j) 8 := by
    intro j hj
    rw [stepCheck_byte]
    exact valueEncoded j hj
  change (stepNext hash (SphincsVerifierWotsStepCheck.stepCheckState state)).getByte
    (BitVec.ofNat 64 (0x44b00 + i)) = _
  apply stepNext_walkByte hash (SphincsVerifierWotsStepCheck.stepCheckState state)
    pk layer tree leaf chain step start offset initial stepEq
  · rw [stepCheck_mem]; exact layerCell
  · rw [stepCheck_mem]; exact treeCell
  · rw [stepCheck_mem]; exact leafCell
  · rw [stepCheck_mem]; exact chainCell
  · rw [stepCheck_mem]; exact stepCell
  · exact checkedPrefix
  · exact checkedValue
  · exact hi

#print axioms stepNext_walkByte
#print axioms stepRound_walkByte

end SigGolfCandidate.SphincsVerifierWotsSemanticWalk
