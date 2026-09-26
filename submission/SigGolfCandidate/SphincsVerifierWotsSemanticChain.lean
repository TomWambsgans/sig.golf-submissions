import SigGolfCandidate.SphincsVerifierWotsSemanticWalk

namespace SigGolfCandidate.SphincsVerifierWotsSemanticChain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity OracleComp
open SigGolfCandidate.SphincsVerifierWotsSemanticLoop
open SigGolfCandidate.SphincsVerifierWotsSemanticWalk
open SigGolfCandidate.SphincsVerifierWotsStepIteration
open SigGolfCandidate.SphincsVerifierWotsLoop
open SigGolfCandidate.SphincsBridge
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem stepRound_witnessPrefix (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk) :
    SphincsVerifierHashBytes.WitnessPrefix (stepRound hash state) pk := by
  have checked : SphincsVerifierHashBytes.WitnessPrefix
      (SphincsVerifierWotsStepCheck.stepCheckState state) pk := by
    apply SphincsVerifierFtsPostForestCopy.witnessPrefix_of_low_mem_frame
      state (SphincsVerifierWotsStepCheck.stepCheckState state) pk hprefix
    intro address _
    exact stepCheck_mem state address
  exact stepNext_witnessPrefix hash _ pk checked

theorem stepRound_controlCells (hash : Hash) (state : MachineState) :
    (stepRound hash state).getMem 0x43000 = state.getMem 0x43000 ∧
    (stepRound hash state).getMem 0x43008 = state.getMem 0x43008 ∧
    (stepRound hash state).getMem 0x43018 = state.getMem 0x43018 ∧
    (stepRound hash state).getMem 0x43050 = state.getMem 0x43050 := by
  obtain ⟨layer, tree, leaf, chain⟩ :=
    stepNext_controlCells hash (SphincsVerifierWotsStepCheck.stepCheckState state)
  exact ⟨layer.trans (stepCheck_mem state _),
    tree.trans (stepCheck_mem state _),
    leaf.trans (stepCheck_mem state _),
    chain.trans (stepCheck_mem state _)⟩

theorem stepRound_pointerCell (hash : Hash) (state : MachineState) :
    (stepRound hash state).getMem 0x43028 = state.getMem 0x43028 := by
  rw [stepRound]
  have preserved := SphincsVerifierWotsSemanticFrame.stepNext_safeFrame hash
    (SphincsVerifierWotsStepCheck.stepCheckState state) 0x43028
    (Or.inr ⟨by decide, by decide, by decide, by decide⟩)
  exact preserved.trans (stepCheck_mem state 0x43028)

/-- Semantic and execution invariant for the remainder of one WOTS chain. -/
structure WalkInv (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (start : Fin 8) (initial : Digest)
    (sourceBase : Nat)
    (i : Nat) (state : MachineState) : Prop where
  pc : state.pc = 0x2774
  stepCell : state.getMem 0x43058 = BitVec.ofNat 64 (start.val + i)
  layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val
  treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val
  leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val
  chainCell : state.getMem 0x43050 = BitVec.ofNat 64 chain.val
  pointerCell : state.getMem 0x43028 =
    BitVec.ofNat 64 (sourceBase + 20 * chain.val)
  publicKey : SphincsVerifierHashBytes.WitnessPrefix state pk
  value : ∀ j, (hj : j < 20) →
    state.getByte (BitVec.ofNat 64 (0x44b00 + j)) =
      (Concrete.walkValue (adaptOracle hash) pk.parameter layer tree leaf
        chain start.val initial i).extractLsb' (8 * j) 8

theorem walkInv_step (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (start : Fin 8) (initial : Digest)
    (sourceBase : Nat)
    (i : Nat) (state : MachineState)
    (small : i < 7 - start.val)
    (inv : WalkInv hash pk layer tree leaf chain start initial sourceBase i state) :
    WalkInv hash pk layer tree leaf chain start initial sourceBase (i + 1)
      (stepRound hash state) := by
  let step : Fin 8 := ⟨start.val + i, by have := start.isLt; omega⟩
  have stepSmall : step.val < 7 := by dsimp [step]; omega
  have stepCell : state.getMem 0x43058 = BitVec.ofNat 64 step.val := inv.stepCell
  have frame := stepRound_controlCells hash state
  constructor
  · exact stepRound_pc hash state step inv.pc stepCell stepSmall
  · rw [stepRound_cell, inv.stepCell]
    change BitVec.ofNat 64 (start.val + i) + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (start.val + (i + 1))
    rw [← BitVec.ofNat_add]
    congr 1
  · rw [frame.1]; exact inv.layerCell
  · rw [frame.2.1]; exact inv.treeCell
  · rw [frame.2.2.1]; exact inv.leafCell
  · rw [frame.2.2.2]; exact inv.chainCell
  · rw [stepRound_pointerCell hash state]; exact inv.pointerCell
  · exact stepRound_witnessPrefix hash state pk inv.publicKey
  · intro j hj
    exact stepRound_walkByte hash state pk layer tree leaf chain
      ⟨start.val + i, by simp [chainLength, winternitzBits]; omega⟩
      start.val i initial (by rfl) inv.layerCell inv.treeCell inv.leafCell
      inv.chainCell stepCell inv.publicKey inv.value j hj

/-- The entire remaining WOTS chain executes with its abstract recovered endpoint. -/
theorem walkInv_loop (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (start : Fin 8) (initial : Digest)
    (sourceBase : Nat)
    (state : MachineState)
    (initialInv : WalkInv hash pk layer tree leaf chain start initial sourceBase 0 state) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      WalkInv hash pk layer tree leaf chain start initial sourceBase
        (7 - start.val) final ∧
      steps ≤ 94 * (7 - start.val) ∧
      cycles ≤ 101 * (7 - start.val) ∧
      calls ≤ 7 - start.val ∧
      blocks ≤ 7 - start.val ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  let Inv := WalkInv hash pk layer tree leaf chain start initial sourceBase
  have next (i : Nat) (current : MachineState)
      (small : i < 7 - start.val) (inv : Inv i current) :
      ∃ (following : MachineState) (steps cycles calls blocks : Nat),
        Inv (i + 1) following ∧
        steps ≤ 94 ∧ cycles ≤ 101 ∧ calls ≤ 1 ∧ blocks ≤ 1 ∧
        ∀ (tailSteps : Nat) (result : Execution),
          Executes hash SphincsImages.verify following tailSteps result →
          Executes hash SphincsImages.verify current (tailSteps + steps)
            (result.charge cycles calls blocks) := by
    let digit : Fin 8 := ⟨start.val + i, by have := start.isLt; omega⟩
    have digitSmall : digit.val < 7 := by dsimp [digit]; omega
    have currentCell : current.getMem 0x43058 =
        BitVec.ofNat 64 digit.val := inv.stepCell
    refine ⟨stepRound hash current, 94, 101, 1, 1,
      walkInv_step hash pk layer tree leaf chain start initial sourceBase i current
        small inv, by decide, by decide, by decide, by decide, ?_⟩
    intro tailSteps result tail
    exact stepRound_exec hash current digit inv.pc currentCell
      digitSmall tailSteps result tail
  simpa [Inv] using
    (bounded_loop hash SphincsImages.verify Inv (7 - start.val)
      94 101 1 1 next 0 (7 - start.val) state
      (by omega) initialInv)

theorem walkInv_recoverChain (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (start : Fin 8) (initial : Digest)
    (sourceBase : Nat)
    (state : MachineState)
    (inv : WalkInv hash pk layer tree leaf chain start initial sourceBase
      (7 - start.val) state) (i : Nat) (hi : i < 20) :
    state.getByte (BitVec.ofNat 64 (0x44b00 + i)) =
      (evalWithAnswerFn (adaptOracle hash)
        (Concrete.recoverChain pk.parameter layer tree leaf chain start initial)).extractLsb'
          (8 * i) 8 := by
  simpa [Concrete.walkValue, Concrete.recoverChain, chainLength,
    winternitzBits] using inv.value i hi

#print axioms stepRound_pointerCell
#print axioms stepRound_witnessPrefix
#print axioms walkInv_step
#print axioms walkInv_loop
#print axioms walkInv_recoverChain

end SigGolfCandidate.SphincsVerifierWotsSemanticChain
