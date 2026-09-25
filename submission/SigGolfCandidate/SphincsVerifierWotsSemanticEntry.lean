import SigGolfCandidate.SphincsVerifierWotsSemanticChain
import SigGolfCandidate.SphincsVerifierWotsEndpointCopy
import SigGolfCandidate.SphincsVerifierFtsGenericBytes

namespace SigGolfCandidate.SphincsVerifierWotsSemanticEntry
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsChainEntry
open SigGolfCandidate.SphincsVerifierWotsEndpointCopy
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
open SigGolfCandidate.SphincsVerifierWotsSemanticFrame
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierWotsSemanticChain
open SigGolfCandidate.SphincsBridge
open SphincsSecurity OracleComp
open SigGolfCandidate.SphincsVerifierWotsSemanticWalk
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- The exact chain entry copies the signed 20-byte chain value into VALUE. -/
theorem chainValueCopied_word (state : MachineState) (chain : Fin 52)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val))
    (index : Fin 5) :
    (chainValueCopied state).getWord32 (word 0x44b00 index) =
      state.getWord32 (word (0x2547c + 20 * chain.val) index) := by
  have source : (chainValuePointers state).getReg .x6 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val) := by
    simpa [chainValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] using pointer
  have destination : (chainValuePointers state).getReg .x7 = 0x44b00 := by
    simp [chainValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have disjoint : ∀ i j : Fin 5,
      alignToDword (word (0x2547c + 20 * chain.val) j) ≠
        alignToDword (word 0x44b00 i) := by
    intro i j
    fin_cases chain <;> fin_cases i <;> fin_cases j <;> decide
  have separate : ∀ i j : Fin 5, i ≠ j →
      alignToDword (word 0x44b00 i) ≠
        alignToDword (word 0x44b00 j) ∨
      byteOffset (word 0x44b00 i) / 4 ≠
        byteOffset (word 0x44b00 j) / 4 := by
    intro i j different
    fin_cases i <;> fin_cases j <;> simp_all [word, alignToDword, byteOffset]
  have copied := copy20_data (chainValuePointers state)
    (0x2547c + 20 * chain.val) 0x44b00 source destination
    disjoint separate index
  have pointerFrame : (chainValuePointers state).getWord32
      (word (0x2547c + 20 * chain.val) index) =
      state.getWord32 (word (0x2547c + 20 * chain.val) index) := by
    simp [chainValuePointers, execInstrBr, MachineState.getWord32]
  exact copied.trans pointerFrame

theorem chainValueCopied_byte (state : MachineState) (chain : Fin 52)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val))
    (i : Nat) (hi : i < 20) :
    (chainValueCopied state).getByte (BitVec.ofNat 64 (0x44b00 + i)) =
      state.getByte (BitVec.ofNat 64 (0x2547c + 20 * chain.val + i)) := by
  apply transfer_words_to_bytes (chainValueCopied state) state
    0x44b00 (0x2547c + 20 * chain.val)
    (by decide) (by have := chain.isLt; omega)
    (by decide) (by have := chain.isLt; omega)
    (fun index => chainValueCopied_word state chain pointer index) i hi

theorem chainDigit_mem (state : MachineState) (address : Word)
    (different : address ≠ 0x43058) :
    (chainDigitState state).getMem address = state.getMem address := by
  simp [chainDigitState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  intro equal
  exact (different equal).elim

theorem chainEntry_valueByte (state : MachineState) (chain : Fin 52)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val))
    (i : Nat) (hi : i < 20) :
    (chainEntryState state).getByte (BitVec.ofNat 64 (0x44b00 + i)) =
      state.getByte (BitVec.ofNat 64 (0x2547c + 20 * chain.val + i)) := by
  have frame : (chainDigitState (chainValueCopied state)).getByte
      (BitVec.ofNat 64 (0x44b00 + i)) =
      (chainValueCopied state).getByte
        (BitVec.ofNat 64 (0x44b00 + i)) := by
    simp only [MachineState.getByte]
    rw [chainDigit_mem (chainValueCopied state) _ (by interval_cases i <;> decide)]
  exact frame.trans (chainValueCopied_byte state chain pointer i hi)

theorem chainEntry_safeFrame (state : MachineState) (address : Word)
    (inside : SafeAddr address) :
    (chainEntryState state).getMem address = state.getMem address := by
  have destination : (chainValuePointers state).getReg .x7 = 0x44b00 := by
    simp [chainValuePointers, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have copied : (chainValueCopied state).getMem address =
      state.getMem address := by
    have frame := copyRoot_mem_frame (chainValuePointers state) address
      (by
        intro offset
        rw [destination]
        apply safe_ne address inside
        right
        left
        fin_cases offset <;> decide)
    have pointerFrame : (chainValuePointers state).getMem address =
        state.getMem address := by
      simp [chainValuePointers, execInstrBr]
    exact frame.trans pointerFrame
  have different : address ≠ 0x43058 := by
    rcases inside with low | ⟨_, _, _, noStep⟩
    · intro equal
      have := congrArg BitVec.toNat equal
      simp at this
      omega
    · exact noStep
  exact (chainDigit_mem (chainValueCopied state) address different).trans copied

theorem chainEntry_witnessPrefix (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk) :
    SphincsVerifierHashBytes.WitnessPrefix (chainEntryState state) pk := by
  apply SphincsVerifierFtsPostForestCopy.witnessPrefix_of_low_mem_frame
    state (chainEntryState state) pk hprefix
  intro address low
  exact chainEntry_safeFrame state address (Or.inl low)

theorem chainEntry_controlCells (state : MachineState) :
    (chainEntryState state).getMem 0x43000 = state.getMem 0x43000 ∧
    (chainEntryState state).getMem 0x43008 = state.getMem 0x43008 ∧
    (chainEntryState state).getMem 0x43018 = state.getMem 0x43018 ∧
    (chainEntryState state).getMem 0x43050 = state.getMem 0x43050 := by
  constructor
  · exact chainEntry_safeFrame state _ (Or.inr ⟨by decide, by decide, by decide, by decide⟩)
  constructor
  · exact chainEntry_safeFrame state _ (Or.inr ⟨by decide, by decide, by decide, by decide⟩)
  constructor
  · exact chainEntry_safeFrame state _ (Or.inr ⟨by decide, by decide, by decide, by decide⟩)
  · exact chainEntry_safeFrame state _ (Or.inr ⟨by decide, by decide, by decide, by decide⟩)

theorem chainEntry_walkInv (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (layer : Layer)
    (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (digit : Fin 8) (initial : Digest)
    (pc : state.pc = 0x2710)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val))
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (decoded : state.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
      BitVec.ofNat 8 digit.val)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (value : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x2547c + 20 * chain.val + i)) =
        initial.extractLsb' (8 * i) 8) :
    WalkInv hash pk layer tree leaf chain digit initial 0
      (chainEntryState state) := by
  have frame := chainEntry_controlCells state
  constructor
  · exact (chainEntry_block state chain pc pointer counter).2
  · rw [chainEntry_step state chain counter, decoded]
    fin_cases digit <;> decide
  · rw [frame.1]; exact layerCell
  · rw [frame.2.1]; exact treeCell
  · rw [frame.2.2.1]; exact leafCell
  · rw [frame.2.2.2]; exact counter
  · rw [SphincsVerifierWotsChainRound.chainEntry_controlFrame state 0x43028 (Or.inr rfl)]
    exact pointer
  · exact chainEntry_witnessPrefix state pk hprefix
  · intro i hi
    rw [chainEntry_valueByte state chain pointer i hi, value i hi]
    simp [Concrete.walkValue, Concrete.chainWalk]

/-- A complete chain reaches the abstract recovered endpoint at the copy-out PC. -/
theorem chainEntry_recover (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (layer : Layer)
    (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (digit : Fin 8) (initial : Digest)
    (pc : state.pc = 0x2710)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x2547c + 20 * chain.val))
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (decoded : state.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
      BitVec.ofNat 8 digit.val)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (value : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x2547c + 20 * chain.val + i)) =
        initial.extractLsb' (8 * i) 8) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc = 0x28ec ∧
      final.getMem 0x43050 = BitVec.ofNat 64 chain.val ∧
      final.getMem 0x43028 =
        BitVec.ofNat 64 (0x2547c + 20 * chain.val) ∧
      SphincsVerifierHashBytes.WitnessPrefix final pk ∧
      (∀ i, (hi : i < 20) →
        final.getByte (BitVec.ofNat 64 (0x44b00 + i)) =
          (evalWithAnswerFn (adaptOracle hash)
            (Concrete.recoverChain pk.parameter layer tree leaf chain digit initial)).extractLsb'
              (8 * i) 8) ∧
      steps ≤ 94 * (7 - digit.val) + 30 ∧
      cycles ≤ 101 * (7 - digit.val) + 30 ∧
      calls ≤ 7 - digit.val ∧
      blocks ≤ 7 - digit.val ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  have entry := chainEntry_block state chain pc pointer counter
  have initialInv := chainEntry_walkInv hash state pk layer tree leaf chain
    digit initial pc pointer counter decoded layerCell treeCell leafCell
    hprefix value
  obtain ⟨seven, steps, cycles, calls, blocks, finalInv,
    stepBound, cycleBound, callBound, blockBound, run⟩ :=
    walkInv_loop hash pk layer tree leaf chain digit initial
      (chainEntryState state) initialInv
  have cell : seven.getMem 0x43058 = 7 := by
    simpa [show digit.val + (7 - digit.val) = 7 by
      have := digit.isLt; omega] using finalInv.stepCell
  have checked := SphincsVerifierWotsStepCheck.stepCheck_block
    seven ⟨7, by decide⟩ finalInv.pc (by simpa using cell)
  refine ⟨SphincsVerifierWotsStepCheck.stepCheckState seven,
    steps + 30, cycles + 30, calls, blocks,
    by simpa using checked.2, ?_, ?_, ?_, ?_, by omega, by omega,
    callBound, blockBound, ?_⟩
  · rw [stepCheck_mem]; exact finalInv.chainCell
  · rw [stepCheck_mem]; exact finalInv.pointerCell
  · apply SphincsVerifierFtsPostForestCopy.witnessPrefix_of_low_mem_frame
      seven (SphincsVerifierWotsStepCheck.stepCheckState seven) pk
      finalInv.publicKey
    intro address _
    exact stepCheck_mem seven address
  · intro i hi
    rw [stepCheck_byte]
    exact walkInv_recoverChain hash pk layer tree leaf chain digit
      initial seven finalInv i hi
  · intro tailSteps result tail
    have after := checked.1.then_executes tail
    have before := run (tailSteps + 5) (result.charge 5 0 0) after
    have full := entry.1.then_executes before
    simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using full

#print axioms chainEntry_recover

#print axioms chainEntry_walkInv

#print axioms chainValueCopied_word
#print axioms chainValueCopied_byte
#print axioms chainEntry_valueByte
#print axioms chainEntry_safeFrame
#print axioms chainEntry_witnessPrefix

end SigGolfCandidate.SphincsVerifierWotsSemanticEntry
