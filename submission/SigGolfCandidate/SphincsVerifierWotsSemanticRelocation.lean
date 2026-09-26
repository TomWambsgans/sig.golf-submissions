import SigGolfCandidate.SphincsVerifierXmssTransition
import SigGolfCandidate.SphincsMaskedKeygenPadding
import SigGolfCandidate.SphincsWireEncoding

namespace SigGolfCandidate.SphincsVerifierWotsSemanticRelocation
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open OracleComp
open SigGolfCandidate.SphincsVerifierWotsSemanticChain
open SigGolfCandidate.SphincsVerifierWotsSemanticAllChains
open SigGolfCandidate.SphincsVerifierWotsChainEnd
open SigGolfCandidate.SphincsVerifierWotsChainEndGeneral
open SigGolfCandidate.SphincsVerifierWotsEndpointCopy
open SigGolfCandidate.SphincsVerifierWotsEndpointFrame
open SigGolfCandidate.SphincsVerifierWotsSemanticFrame
open SigGolfCandidate.SphincsVerifierWotsDigitFrame
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierWotsStepIteration
open SigGolfCandidate.SphincsVerifierWotsChainEntry
open SigGolfCandidate.SphincsVerifierWotsStepTrace
open SigGolfCandidate.SphincsVerifierWotsInterior
open SigGolfCandidate.SphincsVerifierWotsRelocationTrace
open SigGolfCandidate.SphincsMaskedSignOtsShift
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- Bytes needed by the XMSS path, excluding leaf-copy's position scratch word. -/
def LeafPathRetained (read : Word) : Prop :=
  read.toNat < 0x40000 ∨
    (0x43000 ≤ read.toNat ∧ read.toNat < 0x43048 ∧ read ≠ 0x43010)

/-- The semantically identified WOTS walk stays inside the relocatable code segment. -/
theorem walk_inside (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (start : Fin 8) (initial : Digest)
    (sourceBase : Nat) (state : MachineState)
    (initialInv : WalkInv hash pk layer tree leaf chain start initial sourceBase 0 state) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat)
      (run : Trace hash SphincsImages.verify state steps cycles calls blocks final),
      WalkInv hash pk layer tree leaf chain start initial sourceBase
        (7 - start.val) final ∧
      (∀ address, StableAddr address →
        final.getMem address = state.getMem address) ∧
      steps ≤ 94 * (7 - start.val) ∧
      cycles ≤ 101 * (7 - start.val) ∧
      calls ≤ 7 - start.val ∧ blocks ≤ 7 - start.val ∧
      SegmentInterior hash run := by
  let Inv : Nat → MachineState → Prop := fun i current =>
    WalkInv hash pk layer tree leaf chain start initial sourceBase i current ∧
    ∀ address, StableAddr address →
      current.getMem address = state.getMem address
  have next (i : Nat) (current : MachineState)
      (small : i < 7 - start.val) (inv : Inv i current) :
      ∃ (following : MachineState) (steps cycles calls blocks : Nat)
        (run : Trace hash SphincsImages.verify current steps cycles calls blocks following),
        Inv (i + 1) following ∧
        steps ≤ 94 ∧ cycles ≤ 101 ∧ calls ≤ 1 ∧ blocks ≤ 1 ∧
        SegmentInterior hash run := by
    let digit : Fin 8 := ⟨start.val + i, by have := start.isLt; omega⟩
    have digitSmall : digit.val < 7 := by dsimp [digit]; omega
    have currentCell : current.getMem 0x43058 =
      BitVec.ofNat 64 digit.val := inv.1.stepCell
    let run := step_round_trace hash current digit inv.1.pc currentCell digitSmall
    refine ⟨stepRound hash current, 94, 101, 1, 1, run,
      ⟨walkInv_step hash pk layer tree leaf chain start initial sourceBase i
        current small inv.1, ?_⟩,
      by decide, by decide, by decide, by decide, ?_⟩
    · intro address stable
      exact (stepRound_stableFrame hash current address stable).trans
        (inv.2 address stable)
    · exact step_round_inside hash current digit inv.1.pc currentCell digitSmall
  obtain ⟨final, steps, cycles, calls, blocks, run, finalInv,
    stepBound, cycleBound, callBound, blockBound, inside⟩ :=
    bounded_loop_interior hash Inv (7 - start.val) 94 101 1 1
      next 0 (7 - start.val) state (by omega)
      ⟨initialInv, by intro address _; rfl⟩
  refine ⟨final, steps, cycles, calls, blocks, run,
    by simpa only [Nat.zero_add] using finalInv.1,
    finalInv.2, stepBound, cycleBound, ?_, ?_, inside⟩
  · simpa only [one_mul] using callBound
  · simpa only [one_mul] using blockBound

/-- A complete semantic chain prefix is safe to relocate before endpoint copy-out. -/
theorem chain_prefix_inside (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (layer : Layer)
    (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (digit : Fin 8) (initial : Digest)
    (base : Nat) (baseBound : base + 20 * 52 ≤ 0x40000)
    (baseAligned : base % 4 = 0)
    (pc : state.pc = 0x2710)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (base + 20 * chain.val))
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (decoded : state.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
      BitVec.ofNat 8 digit.val)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (value : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (base + 20 * chain.val + i)) =
        initial.extractLsb' (8 * i) 8) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat)
      (run : Trace hash SphincsImages.verify state steps cycles calls blocks final),
      final.pc = 0x28ec ∧
      final.getMem 0x43050 = BitVec.ofNat 64 chain.val ∧
      final.getMem 0x43028 = BitVec.ofNat 64 (base + 20 * chain.val) ∧
      final.getMem 0x43000 = BitVec.ofNat 64 layer.val ∧
      final.getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
      final.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
      SphincsVerifierHashBytes.WitnessPrefix final pk ∧
      (∀ i, (hi : i < 20) →
        final.getByte (BitVec.ofNat 64 (0x44b00 + i)) =
          (evalWithAnswerFn (SphincsBridge.adaptOracle hash)
            (Concrete.recoverChain pk.parameter layer tree leaf chain digit initial)).extractLsb'
              (8 * i) 8) ∧
      (∀ address, StableAddr address →
        final.getMem address = state.getMem address) ∧
      steps ≤ 94 * (7 - digit.val) + 30 ∧
      cycles ≤ 101 * (7 - digit.val) + 30 ∧
      calls ≤ 7 - digit.val ∧ blocks ≤ 7 - digit.val ∧
      SegmentInterior hash run := by
  have sourceBound : base + 20 * chain.val + 20 ≤ 0x40000 := by
    have h := chain.isLt
    change chain.val < 52 at h
    omega
  have sourceAligned : (base + 20 * chain.val) % 4 = 0 := by omega
  have entry := SphincsVerifierWotsChainEntryGeneral.chainEntry_block_general
    state chain (base + 20 * chain.val) sourceBound sourceAligned pc pointer counter
  have initialInv := SphincsVerifierWotsSemanticEntryGeneral.chainEntry_walkInv_general
    hash state pk layer tree leaf chain digit initial base baseBound baseAligned
    pc pointer counter decoded layerCell treeCell leafCell hprefix value
  obtain ⟨seven, steps, cycles, calls, blocks, middleTrace, finalInv,
    stable, stepBound, cycleBound, callBound, blockBound, middleInside⟩ :=
    walk_inside hash pk layer tree leaf chain digit initial base
      (chainEntryState state) initialInv
  have cell : seven.getMem 0x43058 = 7 := by
    simpa [show digit.val + (7 - digit.val) = 7 by
      have := digit.isLt; omega] using finalInv.stepCell
  have checked := SphincsVerifierWotsStepCheck.stepCheck_block
    seven ⟨7, by decide⟩ finalInv.pc (by simpa using cell)
  let entryTrace := entry.1.trace (hash := hash)
  let finishTrace := checked.1.trace (hash := hash)
  have entryInside : SegmentInterior hash entryTrace := by
    apply SphincsVerifierWotsRank.trace_inside_of_rank
    rw [pc]
    decide
  have finishInside : SegmentInterior hash finishTrace := by
    apply SphincsVerifierWotsRank.trace_inside_of_rank
    rw [finalInv.pc]
    decide
  let run := (entryTrace.trans middleTrace).trans finishTrace
  have inside : SegmentInterior hash run :=
    SphincsVerifierWotsStepTrace.segment_interior_trans hash
      (entryTrace.trans middleTrace) finishTrace
      (SphincsVerifierWotsStepTrace.segment_interior_trans hash
        entryTrace middleTrace entryInside middleInside) finishInside
  refine ⟨SphincsVerifierWotsStepCheck.stepCheckState seven,
    25 + steps + 5, 25 + cycles + 5, 0 + calls + 0, 0 + blocks + 0, run,
    by simpa using checked.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, by omega, by omega, by omega, by omega, ?_⟩
  · rw [SphincsVerifierWotsSemanticWalk.stepCheck_mem]; exact finalInv.chainCell
  · rw [SphincsVerifierWotsSemanticWalk.stepCheck_mem]; exact finalInv.pointerCell
  · rw [SphincsVerifierWotsSemanticWalk.stepCheck_mem]; exact finalInv.layerCell
  · rw [SphincsVerifierWotsSemanticWalk.stepCheck_mem]; exact finalInv.treeCell
  · rw [SphincsVerifierWotsSemanticWalk.stepCheck_mem]; exact finalInv.leafCell
  · apply SphincsVerifierFtsPostForestCopy.witnessPrefix_of_low_mem_frame
      seven (SphincsVerifierWotsStepCheck.stepCheckState seven) pk finalInv.publicKey
    intro address _
    exact SphincsVerifierWotsSemanticWalk.stepCheck_mem seven address
  · intro i hi
    rw [SphincsVerifierWotsSemanticWalk.stepCheck_byte]
    exact walkInv_recoverChain hash pk layer tree leaf chain digit initial
      base seven finalInv i hi
  · intro address stableAddr
    exact (SphincsVerifierWotsSemanticWalk.stepCheck_mem seven address).trans
      ((stable address stableAddr).trans
        (chainEntry_stableFrame state address stableAddr))
  · simpa [run, entryTrace, finishTrace, Nat.add_assoc] using inside

theorem chain_end_global_index_cell (state : MachineState)
    (chain : Fin 52)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val) :
    (SphincsVerifierWotsChainEnd.chainEndState state).getMem 0x43078 =
      state.getMem 0x43078 := by
  let pointers := SphincsVerifierWotsChainEnd.endpointSourceState
    (SphincsVerifierWotsChainEnd.endpointPointersState state)
  have destination : pointers.getReg .x7 =
      BitVec.ofNat 64 (0x44300 + 20 * chain.val) := by
    simpa [pointers, SphincsVerifierWotsChainEnd.endpointSourceState, execInstrBr,
      MachineState.getReg_setReg_ne] using
        SphincsVerifierWotsChainEnd.endpointPointers_regs state chain counter
  have copyFrame := SphincsVerifierCopyMemory.copyRoot_mem_frame pointers
    0x43078 (by
      intro offset
      rw [destination]
      fin_cases chain <;> fin_cases offset <;> decide)
  have pointerFrame : pointers.getMem 0x43078 = state.getMem 0x43078 := by
    simp [pointers, SphincsVerifierWotsChainEnd.endpointSourceState,
      SphincsVerifierWotsChainEnd.endpointPointersState, execInstrBr]
  have advanceFrame :
      (SphincsVerifierWotsChainEnd.chainBranchState
        (SphincsVerifierWotsChainEnd.chainAdvanceState
          (SphincsVerifierWotsChainEnd.pointerAdvanceState
            (SphincsVerifierCopy.copyRootState pointers)))).getMem 0x43078 =
          (SphincsVerifierCopy.copyRootState pointers).getMem 0x43078 := by
    simp [SphincsVerifierWotsChainEnd.chainBranchState,
      SphincsVerifierWotsChainEnd.chainAdvanceState,
      SphincsVerifierWotsChainEnd.pointerAdvanceState,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  exact advanceFrame.trans (copyFrame.trans pointerFrame)


/-- One recovered chain keeps the witness and earlier endpoints intact during relocation. -/
theorem chain_round_semantic_inside (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (layer : Layer)
    (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (digit : Fin 8) (initial : Digest)
    (base : Nat) (baseBound : base + 20 * 52 ≤ 0x40000)
    (baseAligned : base % 4 = 0)
    (pc : state.pc = 0x2710)
    (pointer : state.getMem 0x43028 =
      BitVec.ofNat 64 (base + 20 * chain.val))
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (decoded : state.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
      BitVec.ofNat 8 digit.val)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (value : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (base + 20 * chain.val + i)) =
        initial.extractLsb' (8 * i) 8) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat)
      (run : Trace hash SphincsImages.verify state steps cycles calls blocks final),
      final.pc = (if chain.val + 1 = 52 then 0x298c else 0x2710) ∧
      final.getMem 0x43050 = BitVec.ofNat 64 (chain.val + 1) ∧
      final.getMem 0x43028 = BitVec.ofNat 64 (base + 20 * (chain.val + 1)) ∧
      final.getMem 0x43000 = BitVec.ofNat 64 layer.val ∧
      final.getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
      final.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
      final.getMem 0x43020 = state.getMem 0x43020 ∧
      final.getMem 0x43078 = state.getMem 0x43078 ∧
      (∀ address, address.toNat < 0x40000 →
        final.getMem address = state.getMem address) ∧
      (∀ address, DigitAddr address →
        final.getMem address = state.getMem address) ∧
      (∀ (other : Fin 52) (index : Fin 5), chain ≠ other →
        final.getWord32 (word (0x44300 + 20 * other.val) index) =
          state.getWord32 (word (0x44300 + 20 * other.val) index)) ∧
      (∀ i, (hi : i < 20) →
        final.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + i)) =
          (evalWithAnswerFn (adaptOracle hash)
            (Concrete.recoverChain pk.parameter layer tree leaf chain digit initial)).extractLsb'
              (8 * i) 8) ∧
      steps ≤ 94 * (7 - digit.val) + 70 ∧
      cycles ≤ 101 * (7 - digit.val) + 70 ∧
      calls ≤ 7 - digit.val ∧ blocks ≤ 7 - digit.val ∧
      SegmentInterior hash run := by
  obtain ⟨middle, preSteps, preCycles, preCalls, preBlocks, preTrace,
    middlePc, middleCounter, middlePointer, middleLayer, middleTree,
    middleLeaf, _middlePrefix, middleValue, middleFrame,
    stepBound, cycleBound, callBound, blockBound, preInside⟩ :=
    chain_prefix_inside hash state pk layer tree leaf chain digit initial
      base baseBound baseAligned pc pointer counter decoded layerCell treeCell
      leafCell hprefix value
  obtain ⟨endTrace, endPc, endCounter⟩ :=
    chainEnd_block middle chain middlePc middleCounter
  have endPointer := chainEnd_pointer_general middle chain base
    middleCounter middlePointer
  have context (address : Word) (inside : ContextAddr address) :
      (chainEndState middle).getMem address = middle.getMem address :=
    chainEnd_contextFrame middle chain middleCounter address inside
  have lowFrame (address : Word) (low : address.toNat < 0x40000) :
      (chainEndState middle).getMem address = state.getMem address :=
    (chainEnd_lowFrame middle chain middleCounter address low).trans
      (middleFrame address (Or.inl (Or.inl low)))
  have digitFrame (address : Word) (inside : DigitAddr address) :
      (chainEndState middle).getMem address = state.getMem address := by
    have scratch : ScratchAddr address := by
      dsimp [ScratchAddr, DigitAddr] at *
      omega
    exact (chainEnd_digitFrame middle chain middleCounter address inside).trans
      (middleFrame address (Or.inr scratch))
  have otherFrame (other : Fin 52) (index : Fin 5)
      (different : chain ≠ other) :
      (chainEndState middle).getWord32
        (word (0x44300 + 20 * other.val) index) =
          state.getWord32 (word (0x44300 + 20 * other.val) index) := by
    rw [chainEnd_otherWord middle chain other different middleCounter index]
    unfold MachineState.getWord32
    rw [middleFrame _ (Or.inr (endpoint_address other index))]
  have endpointByte (i : Nat) (hi : i < 20) :
      (chainEndState middle).getByte
        (BitVec.ofNat 64 (0x44300 + 20 * chain.val + i)) =
          (evalWithAnswerFn (adaptOracle hash)
            (Concrete.recoverChain pk.parameter layer tree leaf chain digit initial)).extractLsb'
              (8 * i) 8 := by
    have copied := transfer_words_to_bytes (chainEndState middle) middle
      (0x44300 + 20 * chain.val) 0x44b00
      (by
        have hc : chain.val < 52 := by exact chain.isLt
        omega) (by decide)
      (by simp [Nat.add_mod, Nat.mul_mod]) (by decide)
      (fun index => chainEnd_word middle chain middleCounter index) i hi
    exact copied.trans (middleValue i hi)
  let tailTrace := endTrace.trace (hash := hash)
  have tailInside : SegmentInterior hash tailTrace := by
    apply SphincsVerifierWotsRank.trace_inside_of_rank
    rw [middlePc]
    decide
  let run := preTrace.trans tailTrace
  have inside : SegmentInterior hash run :=
    SphincsVerifierWotsStepTrace.segment_interior_trans hash
      preTrace tailTrace preInside tailInside
  refine ⟨chainEndState middle, preSteps + 40, preCycles + 40,
    preCalls + 0, preBlocks + 0, run,
    endPc, endCounter, endPointer, ?_, ?_, ?_, ?_,
    ?_, lowFrame, digitFrame, otherFrame, endpointByte,
    by omega, by omega, by omega, by omega, ?_⟩
  · rw [context 0x43000 (Or.inl rfl)]; exact middleLayer
  · rw [context 0x43008 (Or.inr (Or.inl rfl))]; exact middleTree
  · rw [context 0x43018 (Or.inr (Or.inr (Or.inl rfl)))]; exact middleLeaf
  · rw [context 0x43020 (Or.inr (Or.inr (Or.inr rfl)))]
    exact middleFrame 0x43020
      (Or.inl (Or.inr ⟨by decide, by decide, by decide, by decide⟩))
  · exact (chain_end_global_index_cell middle chain middleCounter).trans
      (middleFrame 0x43078 (Or.inl (Or.inr
        ⟨by decide, by decide, by decide, by decide⟩)))
  · simpa [run, tailTrace] using inside

private structure History (hash : Hash)
    (initial : MachineState) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (digits : ChainIndex → Fin 8) (values : ChainIndex → Digest)
    (base : Nat) (i : Nat) (current : MachineState) : Prop where
  pc : current.pc = (if i = 52 then 0x298c else 0x2710)
  counter : current.getMem 0x43050 = BitVec.ofNat 64 i
  pointer : current.getMem 0x43028 = BitVec.ofNat 64 (base + 20 * i)
  layerCell : current.getMem 0x43000 = BitVec.ofNat 64 layer.val
  treeCell : current.getMem 0x43008 = BitVec.ofNat 64 tree.val
  leafCell : current.getMem 0x43018 = BitVec.ofNat 64 leaf.val
  bitCell : current.getMem 0x43020 = initial.getMem 0x43020
  globalIndex : current.getMem 0x43078 = initial.getMem 0x43078
  lowFrame : ∀ address, address.toNat < 0x40000 →
    current.getMem address = initial.getMem address
  digitFrame : ∀ address, DigitAddr address →
    current.getMem address = initial.getMem address
  endpoints : ∀ chain : ChainIndex, chain.val < i → ∀ j, (hj : j < 20) →
    current.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + j)) =
      (evalWithAnswerFn (adaptOracle hash)
        (Concrete.recoverChain pk.parameter layer tree leaf chain
          (digits chain) (values chain))).extractLsb' (8 * j) 8

/-- All 52 recovered endpoints have an exact trace in the relocatable WOTS segment. -/
theorem all_chains_inside_semantics (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (layer : Layer)
    (tree : TreeIndex) (leaf : LeafIndex)
    (digits : ChainIndex → Fin 8) (values : ChainIndex → Digest)
    (base : Nat) (baseBound : base + 20 * 52 ≤ 0x40000)
    (baseAligned : base % 4 = 0)
    (pc : state.pc = 0x2710)
    (counter : state.getMem 0x43050 = 0)
    (pointer : state.getMem 0x43028 = BitVec.ofNat 64 base)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (decoded : ∀ chain : ChainIndex,
      state.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
        BitVec.ofNat 8 (digits chain).val)
    (source : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      state.getByte (BitVec.ofNat 64 (base + 20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat)
      (run : Trace hash SphincsImages.verify state steps cycles calls blocks final),
      final.pc = 0x298c ∧
      final.getMem 0x43050 = 52 ∧
      final.getMem 0x43028 = BitVec.ofNat 64 (base + 20 * 52) ∧
      final.getMem 0x43000 = BitVec.ofNat 64 layer.val ∧
      final.getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
      final.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
      final.getMem 0x43020 = state.getMem 0x43020 ∧
      final.getMem 0x43078 = state.getMem 0x43078 ∧
      (∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
        final.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + j)) =
          (evalWithAnswerFn (adaptOracle hash)
            (Concrete.recoverChain pk.parameter layer tree leaf chain
              (digits chain) (values chain))).extractLsb' (8 * j) 8) ∧
      (∀ address, address.toNat < 0x40000 →
        final.getMem address = state.getMem address) ∧
      steps ≤ 728 * 52 ∧ cycles ≤ 777 * 52 ∧
      calls ≤ 7 * 52 ∧ blocks ≤ 7 * 52 ∧
      SegmentInterior hash run := by
  let Inv := History hash state pk layer tree leaf digits values base
  have next (i : Nat) (current : MachineState)
      (small : i < 52) (inv : Inv i current) :
      ∃ (following : MachineState) (steps cycles calls blocks : Nat)
        (run : Trace hash SphincsImages.verify current steps cycles calls blocks following),
        Inv (i + 1) following ∧
        steps ≤ 728 ∧ cycles ≤ 777 ∧ calls ≤ 7 ∧ blocks ≤ 7 ∧
        SegmentInterior hash run := by
    let chain : ChainIndex := ⟨i, by simpa [numChains] using small⟩
    let digit := digits chain
    have currentPc : current.pc = 0x2710 := by
      simpa [Inv, History, show i ≠ 52 by omega] using inv.pc
    have currentCounter : current.getMem 0x43050 =
        BitVec.ofNat 64 chain.val := by simpa [chain] using inv.counter
    have currentPointer : current.getMem 0x43028 =
        BitVec.ofNat 64 (base + 20 * chain.val) := by
      simpa [chain] using inv.pointer
    have currentPrefix : SphincsVerifierHashBytes.WitnessPrefix current pk := by
      apply SphincsVerifierFtsPostForestCopy.witnessPrefix_of_low_mem_frame
        state current pk hprefix
      exact inv.lowFrame
    have currentDigit : current.getByte
        (BitVec.ofNat 64 (0x44000 + chain.val)) =
          BitVec.ofNat 8 digit.val := by
      rw [digitByteFrame state current inv.digitFrame chain]
      exact decoded chain
    have currentValue : ∀ j, (hj : j < 20) →
        current.getByte (BitVec.ofNat 64 (base + 20 * chain.val + j)) =
          (values chain).extractLsb' (8 * j) 8 := by
      intro j hj
      rw [lowByteFrame state current inv.lowFrame _
        (sourceByteSmall base baseBound chain j hj)]
      exact source chain j hj
    obtain ⟨following, a, b, c, d, trace, nextPc, nextCounter,
      nextPointer, nextLayer, nextTree, nextLeaf, nextBit, nextGlobal,
      nextLow, nextDigit,
      otherSlots, newEndpoint, stepBound, cycleBound, callBound,
      blockBound, inside⟩ :=
      chain_round_semantic_inside hash current pk layer tree leaf chain digit
        (values chain) base baseBound baseAligned currentPc currentPointer
        currentCounter currentDigit inv.layerCell inv.treeCell inv.leafCell
        currentPrefix currentValue
    refine ⟨following, a, b, c, d, trace, ?_, by
      have hd := digit.isLt; omega, by
      have hd := digit.isLt; omega, by omega, by omega, inside⟩
    constructor
    · simpa [Inv, History, chain] using nextPc
    · simpa [chain] using nextCounter
    · simpa [chain] using nextPointer
    · exact nextLayer
    · exact nextTree
    · exact nextLeaf
    · exact nextBit.trans inv.bitCell
    · exact nextGlobal.trans inv.globalIndex
    · intro address low
      exact (nextLow address low).trans (inv.lowFrame address low)
    · intro address inside
      exact (nextDigit address inside).trans
        (inv.digitFrame address inside)
    · intro other before j hj
      by_cases same : other = chain
      · subst other
        exact newEndpoint j hj
      · have old : other.val < i := by
          have unequal : other.val ≠ i := by
            intro equal
            exact same (Fin.ext (by simpa [chain] using equal))
          omega
        have oldValue := inv.endpoints other old j hj
        have transferred := transfer_words_to_bytes following current
          (0x44300 + 20 * other.val) (0x44300 + 20 * other.val)
          (by have ho : other.val < 52 := by simpa [numChains] using other.isLt
              omega)
          (by have ho : other.val < 52 := by simpa [numChains] using other.isLt
              omega)
          (by simp [Nat.add_mod, Nat.mul_mod])
          (by simp [Nat.add_mod, Nat.mul_mod])
          (fun index => otherSlots other index (by
            intro eq
            exact same eq.symm)) j hj
        exact transferred.trans oldValue
  obtain ⟨final, steps, cycles, calls, blocks, run, inv,
    stepBound, cycleBound, callBound, blockBound, inside⟩ :=
    bounded_loop_interior hash Inv 52 728 777 7 7 next 0 52 state
      (by decide)
      ⟨by simpa [Inv, History] using pc,
       by simpa [Inv, History] using counter,
       by simpa [Inv, History] using pointer,
       layerCell, treeCell, leafCell, rfl, rfl,
       by intro address _; rfl,
       by intro address _; rfl,
       by intro chain impossible; omega⟩
  refine ⟨final, steps, cycles, calls, blocks, run,
    by simpa [Inv, History] using inv.pc,
    by simpa using inv.counter,
    by simpa using inv.pointer,
    inv.layerCell, inv.treeCell, inv.leafCell, inv.bitCell,
    inv.globalIndex,
    ?_, inv.lowFrame, stepBound, cycleBound,
    callBound, blockBound, inside⟩
  intro chain j hj
  exact inv.endpoints chain (by
    have h := chain.isLt
    simpa [numChains] using h) j hj

/-- Each relocated upper-layer WOTS segment recovers the same abstract endpoints. -/
theorem upper_chains_semantics (target : Fin 5) (hash : Hash)
    (state : MachineState) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (digits : ChainIndex → Fin 8) (values : ChainIndex → Digest)
    (base : Nat) (baseBound : base + 20 * 52 ≤ 0x40000)
    (baseAligned : base % 4 = 0)
    (pc : state.pc = 0x2710)
    (counter : state.getMem 0x43050 = 0)
    (pointer : state.getMem 0x43028 = BitVec.ofNat 64 base)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (decoded : ∀ chain : ChainIndex,
      state.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
        BitVec.ofNat 8 (digits chain).val)
    (source : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      state.getByte (BitVec.ofNat 64 (base + 20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      Trace hash SphincsImages.verify (shift (delta target) state)
        steps cycles calls blocks final ∧
      final.pc = 0x298c + delta target ∧
      final.getMem 0x43050 = 52 ∧
      final.getMem 0x43028 = BitVec.ofNat 64 (base + 20 * 52) ∧
      final.getMem 0x43000 = BitVec.ofNat 64 layer.val ∧
      final.getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
      final.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
      final.getMem 0x43020 = state.getMem 0x43020 ∧
      final.getMem 0x43078 = state.getMem 0x43078 ∧
      (∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
        final.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + j)) =
          (evalWithAnswerFn (adaptOracle hash)
            (Concrete.recoverChain pk.parameter layer tree leaf chain
              (digits chain) (values chain))).extractLsb' (8 * j) 8) ∧
      (∀ address, address.toNat < 0x40000 →
        final.getMem address = state.getMem address) ∧
      steps ≤ 728 * 52 ∧ cycles ≤ 777 * 52 ∧
      calls ≤ 7 * 52 ∧ blocks ≤ 7 * 52 := by
  obtain ⟨final, steps, cycles, calls, blocks, run, done, count,
    sourcePointer, layerFinal, treeFinal, leafFinal, bitFinal, globalIndex,
    valuesDone, lowFrame,
    stepBound, cycleBound, callBound, blockBound, inside⟩ :=
    all_chains_inside_semantics hash state pk layer tree leaf digits values
      base baseBound baseAligned pc counter pointer layerCell treeCell
      leafCell hprefix decoded source
  refine ⟨shift (delta target) final, steps, cycles, calls, blocks,
    trace_shift target hash run inside, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    stepBound, cycleBound, callBound, blockBound⟩
  · simp [shift_pc, done]
  · simpa using count
  · simpa using sourcePointer
  · simpa using layerFinal
  · simpa using treeFinal
  · simpa using leafFinal
  · simpa using bitFinal
  · simpa using globalIndex
  · intro chain j hj
    simpa using valuesDone chain j hj
  · intro address low
    simpa using lowFrame address low

/-- A frame on low memory preserves the encoded public-key witness prefix. -/
theorem witnessPrefix_frame (state final : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (frame : ∀ address, address.toNat < 0x40000 →
      final.getMem address = state.getMem address) :
    SphincsVerifierHashBytes.WitnessPrefix final pk := by
  constructor
  · intro i hi
    have low : (BitVec.ofNat 64 (0x22ca0 + i)).toNat < 0x40000 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 0x22ca0 + i < 2 ^ 64)]
      omega
    rw [SphincsVerifierWotsSemanticAllChains.lowByteFrame state final
      frame _ low]
    exact hprefix.root i hi
  · intro i hi
    have low : (BitVec.ofNat 64 (0x22cb4 + i)).toNat < 0x40000 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 0x22cb4 + i < 2 ^ 64)]
      omega
    rw [SphincsVerifierWotsSemanticAllChains.lowByteFrame state final
      frame _ low]
    exact hprefix.parameter i hi

/-- The upper-layer WOTS block recovers semantic endpoints at its actual PC. -/
theorem upper_chains_from_ready (target : Fin 5) (hash : Hash)
    (ready : MachineState) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (digits : ChainIndex → Fin 8) (values : ChainIndex → Digest)
    (pc : ready.pc = BitVec.ofNat 64
      (SigGolfCandidate.SphincsVerifierWotsRelocation.chainPc target))
    (counter : ready.getMem 0x43050 = 0)
    (pointer : ready.getMem 0x43028 = BitVec.ofNat 64
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target))
    (layerCell : ready.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : ready.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : ready.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix ready pk)
    (decoded : ∀ chain : ChainIndex,
      ready.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
        BitVec.ofNat 8 (digits chain).val)
    (source : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      ready.getByte (BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      Trace hash SphincsImages.verify ready steps cycles calls blocks final ∧
      final.pc = 0x298c + delta target ∧
      final.getMem 0x43028 = BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * 52) ∧
      final.getMem 0x43000 = BitVec.ofNat 64 layer.val ∧
      final.getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
      final.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
      final.getMem 0x43020 = ready.getMem 0x43020 ∧
      final.getMem 0x43078 = ready.getMem 0x43078 ∧
      SphincsVerifierHashBytes.WitnessPrefix final pk ∧
      (∀ address, address.toNat < 0x40000 →
        final.getMem address = ready.getMem address) ∧
      (∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
        final.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + j)) =
          (evalWithAnswerFn (adaptOracle hash)
            (Concrete.recoverChain pk.parameter layer tree leaf chain
              (digits chain) (values chain))).extractLsb' (8 * j) 8) ∧
      steps ≤ 728 * 52 ∧ cycles ≤ 777 * 52 ∧
      calls ≤ 7 * 52 ∧ blocks ≤ 7 * 52 := by
  let base := shift (-delta target) ready
  have basePc : base.pc = 0x2710 := by
    fin_cases target <;> simp [base, pc, shift_pc,
      SigGolfCandidate.SphincsVerifierWotsRelocation.chainPc, delta]
  have shiftedStart : shift (delta target) base = ready := by
    simp [base, shift, MachineState.setPC]
  obtain ⟨final, steps, cycles, calls, blocks, run, finalPc,
    _counter, pointerFinal, layerFinal, treeFinal, leafFinal, bitFinal,
    globalIndex,
    endpoints, lowFrame,
    stepBound, cycleBound, callBound, blockBound⟩ :=
    upper_chains_semantics target hash base pk layer tree leaf digits values
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target)
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase_bound target)
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase_aligned target)
      basePc (by simpa [base] using counter)
      (by simpa [base] using pointer)
      (by simpa [base] using layerCell)
      (by simpa [base] using treeCell)
      (by simpa [base] using leafCell)
      (by
        constructor
        · intro i hi
          simpa [base] using hprefix.root i hi
        · intro i hi
          simpa [base] using hprefix.parameter i hi)
      (by intro chain; simpa [base] using decoded chain)
      (by intro chain j hj; simpa [base] using source chain j hj)
  have lowFrameReady : ∀ address, address.toNat < 0x40000 →
      final.getMem address = ready.getMem address := by
    intro address low
    simpa [base] using lowFrame address low
  refine ⟨final, steps, cycles, calls, blocks, ?_, finalPc, pointerFinal,
    layerFinal, treeFinal, leafFinal, by simpa [base] using bitFinal,
    by simpa [base] using globalIndex,
    witnessPrefix_frame ready final pk hprefix lowFrameReady, lowFrameReady,
    endpoints,
    stepBound, cycleBound, callBound, blockBound⟩
  simpa only [shiftedStart] using run

/-- Digit decoding and WOTS setup form a fixed-cost prefix before each upper layer. -/
theorem upper_prepare_trace (target : Fin 5) (hash : Hash)
    (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64
      (0x1f20 + 4 * SigGolfCandidate.SphincsVerifierWotsRelocationTrace.wordOffset target))
    (checksum : state.getReg .x15 +
      SigGolfCandidate.SphincsVerifierWotsDecodeData.answerSum 52 state = 194) :
    Trace hash SphincsImages.verify state 507 507 0 0
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.setupState target
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState
          target state)) ∧
    (SigGolfCandidate.SphincsVerifierDecoderRelocation.setupState target
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState
        target state)).pc =
      BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierWotsRelocation.chainPc target) ∧
    (SigGolfCandidate.SphincsVerifierDecoderRelocation.setupState target
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState
        target state)).getMem 0x43050 = 0 ∧
    (SigGolfCandidate.SphincsVerifierDecoderRelocation.setupState target
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState
        target state)).getMem 0x43028 = BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target) := by
  obtain ⟨decoderRun, decodedPc, decodedChecksum⟩ :=
    SigGolfCandidate.SphincsVerifierDecoderRelocation.decoder_upper target state pc
  let decoded :=
    SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState target state
  have goodChecksum : decoded.getReg .x15 = 194 := by
    rw [decodedChecksum]
    exact checksum
  have setupRun := SigGolfCandidate.SphincsVerifierDecoderRelocation.setup_block
    target decoded decodedPc goodChecksum
  obtain ⟨done, counter, pointer⟩ :=
    SigGolfCandidate.SphincsVerifierDecoderRelocation.setup_final
      target decoded decodedPc goodChecksum
  refine ⟨?_, done, counter, pointer⟩
  have all := (decoderRun.trace (hash := hash)).trans
    (setupRun.trace (hash := hash))
  simpa [decoded] using all

/-- Digit decoding writes only its scratch digit array, never the input witness. -/
theorem upper_decoder_low_byte_frame (target : Fin 5) (state : MachineState)
    (address : Word) (low : address.toNat < 0x40000) :
    (SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState
      target state).getByte address = state.getByte address := by
  let base := shift (-delta target) state
  have decoded (count : Nat) (within : count ≤ 52) :
      (SigGolfCandidate.SphincsVerifierWotsDecodeData.decoderRun count base).getByte
        address = base.getByte address := by
    induction count with
    | zero => rfl
    | succ count ih =>
        have small : count < 52 := by omega
        let i : Fin 52 := ⟨count, small⟩
        have stepEq :
            SigGolfCandidate.SphincsVerifierWotsDecodeData.decoderRun (count + 1) base =
              SigGolfCandidate.SphincsVerifierWotsDecode.decoderState i
                (SigGolfCandidate.SphincsVerifierWotsDecodeData.decoderRun count base) := by
          simp [SigGolfCandidate.SphincsVerifierWotsDecodeData.decoderRun,
            i, Nat.mod_eq_of_lt small]
        rw [stepEq,
          SigGolfCandidate.SphincsVerifierWotsDecodeData.decoder_memory]
        have different : address ≠ BitVec.ofNat 64 (0x44000 + i.val) := by
          intro eq
          have equality := congrArg BitVec.toNat eq
          have smallAddress : 0x44000 + i.val < 2 ^ 64 := by
            have := i.isLt
            omega
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt smallAddress] at equality
          omega
        simp only [if_neg different]
        exact ih (by omega)
  simpa [SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState,
    shift_byte, base] using decoded 52 (by decide)

/-- The upper-layer setup changes control words only, preserving the witness. -/
theorem upper_setup_low_byte_frame (target : Fin 5) (state : MachineState)
    (address : Word) (low : address.toNat < 0x40000) :
    (SigGolfCandidate.SphincsVerifierDecoderRelocation.setupState
      target state).getByte address = state.getByte address := by
  let aligned := alignToDword address
  have alignedLow : aligned.toNat < 0x40000 := by
    have le : aligned.toNat ≤ address.toNat := by
      unfold aligned alignToDword
      rw [BitVec.toNat_and]
      exact Nat.and_le_left
    omega
  have notCounter : aligned ≠ 0x43050 := by
    intro equal
    have value := congrArg BitVec.toNat equal
    have high : (0x43050 : Word).toNat = 0x43050 := by decide
    rw [high] at value
    omega
  have notPointer : aligned ≠ 0x43028 := by
    intro equal
    have value := congrArg BitVec.toNat equal
    have high : (0x43028 : Word).toNat = 0x43028 := by decide
    rw [high] at value
    omega
  have frame := SigGolfCandidate.SphincsVerifierDecoderRelocation.setup_mem_other
    target state aligned notCounter notPointer
  simpa only [MachineState.getByte, aligned] using
    congrArg (fun value : Word => extractByte value (byteOffset address)) frame

/-- Upper-layer decoding and setup leave every witness byte unchanged. -/
theorem upper_ready_low_byte_frame (target : Fin 5) (state : MachineState)
    (address : Word) (low : address.toNat < 0x40000) :
    (SigGolfCandidate.SphincsVerifierDecoderRelocation.setupState target
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState
        target state)).getByte address = state.getByte address := by
  rw [upper_setup_low_byte_frame target _ address low,
    upper_decoder_low_byte_frame target state address low]

/-- The public-key witness prefix survives upper-layer decoding and setup. -/
theorem upper_ready_prefix (target : Fin 5) (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk) :
    SphincsVerifierHashBytes.WitnessPrefix
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.setupState target
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState
          target state)) pk := by
  constructor
  · intro i hi
    have low : (BitVec.ofNat 64 (0x22ca0 + i)).toNat < 0x40000 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 0x22ca0 + i < 2 ^ 64)]
      omega
    rw [upper_ready_low_byte_frame target state _ low]
    exact hprefix.root i hi
  · intro i hi
    have low : (BitVec.ofNat 64 (0x22cb4 + i)).toNat < 0x40000 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 0x22cb4 + i < 2 ^ 64)]
      omega
    rw [upper_ready_low_byte_frame target state _ low]
    exact hprefix.parameter i hi

/-- The signature source for every WOTS chain survives upper-layer preparation. -/
theorem upper_ready_source (target : Fin 5) (state : MachineState)
    (values : ChainIndex → Digest)
    (source : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      state.getByte (BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8) :
    ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.setupState target
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState
          target state)).getByte (BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8 := by
  intro chain j hj
  rw [upper_ready_low_byte_frame target state _
    (sourceByteSmall _
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase_bound target)
      chain j hj)]
  exact source chain j hj

/-- The full upper-layer decoder and WOTS chains recover from the original witness. -/
theorem upper_decoder_chains_semantics (target : Fin 5) (hash : Hash)
    (state ready : MachineState) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (digits : ChainIndex → Fin 8) (values : ChainIndex → Digest)
    (readyEq : ready =
      SigGolfCandidate.SphincsVerifierDecoderRelocation.setupState target
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState
          target state))
    (pc : state.pc = BitVec.ofNat 64
      (0x1f20 + 4 * SigGolfCandidate.SphincsVerifierWotsRelocationTrace.wordOffset target))
    (checksum : state.getReg .x15 +
      SigGolfCandidate.SphincsVerifierWotsDecodeData.answerSum 52 state = 194)
    (layerCell : ready.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : ready.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : ready.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (decoded : ∀ chain : ChainIndex,
      ready.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
        BitVec.ofNat 8 (digits chain).val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (source : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      state.getByte (BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      Trace hash SphincsImages.verify state steps cycles calls blocks final ∧
      final.pc = 0x298c + delta target ∧
      final.getMem 0x43028 = BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * 52) ∧
      final.getMem 0x43000 = BitVec.ofNat 64 layer.val ∧
      final.getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
      final.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
      final.getMem 0x43020 = ready.getMem 0x43020 ∧
      final.getMem 0x43078 = ready.getMem 0x43078 ∧
      SphincsVerifierHashBytes.WitnessPrefix final pk ∧
      (∀ address, address.toNat < 0x40000 →
        final.getMem address = ready.getMem address) ∧
      (∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
        final.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + j)) =
          (evalWithAnswerFn (adaptOracle hash)
            (Concrete.recoverChain pk.parameter layer tree leaf chain
              (digits chain) (values chain))).extractLsb' (8 * j) 8) ∧
      steps ≤ 507 + 728 * 52 ∧ cycles ≤ 507 + 777 * 52 ∧
      calls ≤ 7 * 52 ∧ blocks ≤ 7 * 52 := by
  obtain ⟨pre, preparedPc, preparedCounter, preparedPointer⟩ :=
    upper_prepare_trace target hash state pc checksum
  have preRun : Trace hash SphincsImages.verify state 507 507 0 0 ready := by
    simpa only [← readyEq] using pre
  have readyPrefix : SphincsVerifierHashBytes.WitnessPrefix ready pk := by
    simpa only [readyEq] using upper_ready_prefix target state pk hprefix
  have readySource : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      ready.getByte (BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8 := by
    simpa only [readyEq] using upper_ready_source target state values source
  obtain ⟨final, steps, cycles, calls, blocks, wotsRun,
    done, pointerFinal, layerFinal, treeFinal, leafFinal, bitFinal,
    globalIndex,
    finalPrefix, lowFrame, endpoints,
    stepBound, cycleBound, callBound, blockBound⟩ :=
    upper_chains_from_ready target hash ready pk layer tree leaf digits values
      (by simpa only [readyEq] using preparedPc)
      (by simpa only [readyEq] using preparedCounter)
      (by simpa only [readyEq] using preparedPointer)
      layerCell treeCell leafCell readyPrefix decoded readySource
  refine ⟨final, 507 + steps, 507 + cycles, calls, blocks,
    ?_, done, pointerFinal, layerFinal, treeFinal, leafFinal, bitFinal,
    globalIndex,
    finalPrefix, lowFrame, endpoints,
    by omega, by omega, callBound, blockBound⟩
  simpa [Nat.add_assoc] using preRun.trans wotsRun

/-- The leaf-copy setup changes only the scratch position word. -/
theorem rootCopySetup_mem_other (state : MachineState) (address : Word)
    (different : address ≠ 0x43010) :
    (SphincsVerifierWotsRootCopy.rootCopySetupState state).getMem address =
      state.getMem address := by
  simp [SphincsVerifierWotsRootCopy.rootCopySetupState, execInstrBr,
    signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  intro equal
  exact (different (by simpa using equal)).elim

theorem rootCopySetup_position_zero (state : MachineState) :
    (SphincsVerifierWotsRootCopy.rootCopySetupState state).getMem 0x43010 = 0 := by
  simp [SphincsVerifierWotsRootCopy.rootCopySetupState, execInstrBr,
    signExtend12, MachineState.getMem_setMem_eq,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

/-- The relocated upper-layer copy serializes recovered WOTS endpoints as a leaf. -/
theorem upper_rootCopy_payload (target : Fin 5) (hash : Hash)
    (state : MachineState) (values : ChainIndex → Digest)
    (pc : state.pc = 0x298c + delta target)
    (endpoints : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      state.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8) :
    ∃ (final : MachineState),
      Trace hash SphincsImages.verify state 789 789 0 0 final ∧
      final.pc = 0x29c8 + delta target ∧
      (∀ i, (hi : i < 1040) →
        final.getByte (BitVec.ofNat 64 (0x40028 + i)) =
          ((Concrete.leafPayload values).map UInt8.toBitVec)[i]'(by
            rw [List.length_map,
              SphincsVerifierWotsSemanticLeaf.leafPayload_length]
            exact hi)) ∧
      (∀ address, address ≠ 0x43010 →
        (∀ i, i < 130 → address ≠ BitVec.ofNat 64 (0x40028 + 8 * i)) →
        final.getMem address = state.getMem address) ∧
      final.getMem 0x43010 = 0 := by
  let base := shift (-delta target) state
  have basePc : base.pc = 0x298c := by
    change state.pc + -delta target = 0x298c
    rw [pc]
    bv_decide
  have baseEndpoints : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      base.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8 := by
    intro chain j hj
    simpa [base] using endpoints chain j hj
  obtain ⟨copied, copy, done, payload⟩ :=
    SphincsVerifierWotsSemanticLeaf.rootCopy_payload base basePc values
      baseEndpoints
  obtain ⟨setup, setupPc, sourceReg, destination, count⟩ :=
    SigGolfCandidate.SphincsVerifierWotsRootCopy.rootCopySetup_block base basePc
  have setupTrace := setup.trace (hash := hash)
  have setupInside := SigGolfCandidate.SphincsVerifierWotsRank.trace_inside_of_rank
    hash setupTrace (by rw [basePc]; decide)
  obtain ⟨insideFinal, loopTrace, _loopPc, _words, loopFrame, loopInside⟩ :=
    SigGolfCandidate.SphincsVerifierWotsLeafInterior.root_copy_inside hash
      (SigGolfCandidate.SphincsVerifierWotsRootCopy.rootCopySetupState base)
      setupPc sourceReg destination count
  have fullInside : Trace hash SphincsImages.verify base 789 789 0 0
      insideFinal := by
    simpa [setupTrace, Nat.add_assoc] using setupTrace.trans loopTrace
  have interior : SegmentInterior hash fullInside := by
    simpa [setupTrace, Nat.add_assoc] using
      segment_interior_trans hash setupTrace loopTrace setupInside loopInside
  have sameFinal : copied = insideFinal :=
    SigGolfCandidate.SphincsMaskedKeygenPadding.trace_unique
      (copy.trace (hash := hash)) fullInside
  have shiftedStart : shift (delta target) base = state := by
    simp [base, shift, MachineState.setPC]
  refine ⟨shift (delta target) insideFinal, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [shiftedStart] using trace_shift target hash
      fullInside interior
  · rw [shift_pc, ← sameFinal, done]
  · intro i hi
    rw [← sameFinal]
    simpa using payload i hi
  · intro address different outside
    rw [shift_mem, loopFrame address outside,
      rootCopySetup_mem_other base address different]
    simp [base]
  · have outside : ∀ i, i < 130 →
        (0x43010 : Word) ≠ BitVec.ofNat 64 (0x40028 + 8 * i) := by
      intro i hi equal
      have value := congrArg BitVec.toNat equal
      have left : (0x43010 : Word).toNat = 0x43010 := by decide
      have right : 0x40028 + 8 * i < 2 ^ 64 := by omega
      rw [left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt right] at value
      omega
    rw [shift_mem, loopFrame 0x43010 outside,
      rootCopySetup_position_zero]

/-- The leaf payload destination is disjoint from the witness and context cells. -/
theorem leaf_copy_dest_other (address : Word)
    (outside : address.toNat < 0x40000 ∨ 0x43000 ≤ address.toNat)
    (i : Nat) (hi : i < 130) :
    address ≠ BitVec.ofNat 64 (0x40028 + 8 * i) := by
  intro equal
  have value := congrArg BitVec.toNat equal
  have small : 0x40028 + 8 * i < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at value
  omega

theorem leaf_copy_path_frame (state final : MachineState)
    (frame : ∀ address, address ≠ 0x43010 →
      (∀ i, i < 130 → address ≠ BitVec.ofNat 64 (0x40028 + 8 * i)) →
        final.getMem address = state.getMem address)
    (read : Word) (retained : LeafPathRetained read) :
    final.getMem read = state.getMem read := by
  apply frame read
  · rcases retained with low | high
    · intro equal
      subst read
      have impossible : ¬ ((0x43010 : Word).toNat < 0x40000) := by decide
      exact impossible low
    · exact high.2.2
  · intro i hi
    exact leaf_copy_dest_other read
      (by rcases retained with low | high
          · exact Or.inl low
          · exact Or.inr high.1) i hi

theorem leaf_copy_global_index_cell (state final : MachineState)
    (frame : ∀ address, address ≠ 0x43010 →
      (∀ i, i < 130 → address ≠ BitVec.ofNat 64 (0x40028 + 8 * i)) →
        final.getMem address = state.getMem address) :
    final.getMem 0x43078 = state.getMem 0x43078 := by
  apply frame 0x43078 (by decide)
  intro i hi
  exact leaf_copy_dest_other 0x43078 (Or.inr (by decide)) i hi

/-- A completed leaf copy preserves the public-key prefix and XMSS coordinates. -/
theorem leaf_copy_context_of_frame (state final : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (frame : ∀ address, address ≠ 0x43010 →
      (∀ i, i < 130 → address ≠ BitVec.ofNat 64 (0x40028 + 8 * i)) →
      final.getMem address = state.getMem address) :
    final.getMem 0x43000 = BitVec.ofNat 64 layer.val ∧
    final.getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
    final.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
    SphincsVerifierHashBytes.WitnessPrefix final pk := by
  have lowFrame : ∀ address, address.toNat < 0x40000 →
      final.getMem address = state.getMem address := by
    intro address low
    apply frame address
    · intro equal
      have value := congrArg BitVec.toNat equal
      have high : (0x43010 : Word).toNat = 0x43010 := by decide
      rw [high] at value
      omega
    · intro i hi
      exact leaf_copy_dest_other address (Or.inl low) i hi
  refine ⟨(frame 0x43000 (by decide)
      (fun i hi => leaf_copy_dest_other 0x43000 (Or.inr (by decide)) i hi)).trans
      layerCell,
    (frame 0x43008 (by decide)
      (fun i hi => leaf_copy_dest_other 0x43008 (Or.inr (by decide)) i hi)).trans
      treeCell,
    (frame 0x43018 (by decide)
      (fun i hi => leaf_copy_dest_other 0x43018 (Or.inr (by decide)) i hi)).trans
      leafCell, ?_⟩
  constructor
  · intro i hi
    have low : (BitVec.ofNat 64 (0x22ca0 + i)).toNat < 0x40000 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 0x22ca0 + i < 2 ^ 64)]
      omega
    rw [SphincsVerifierWotsSemanticAllChains.lowByteFrame state final
      lowFrame _ low]
    exact hprefix.root i hi
  · intro i hi
    have low : (BitVec.ofNat 64 (0x22cb4 + i)).toNat < 0x40000 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 0x22cb4 + i < 2 ^ 64)]
      omega
    rw [SphincsVerifierWotsSemanticAllChains.lowByteFrame state final
      lowFrame _ low]
    exact hprefix.parameter i hi

/-- A relocated leaf copy prepares the exact abstract leaf-hash query. -/
theorem upper_leaf_query (target : Fin 5) (hash : Hash)
    (state : MachineState) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (values : ChainIndex → Digest)
    (pc : state.pc = 0x298c + delta target)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (endpoints : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      state.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8) :
    ∃ (final : MachineState),
      Trace hash SphincsImages.verify state 789 789 0 0 final ∧
      final.pc = 0x29c8 + delta target ∧
      hashInput (SphincsVerifierWotsLeafHashReady.leafHashReadyState final) =
        SphincsBridge.toQuery
          (SphincsVerifierWotsLeafQuery.leafInput pk.parameter layer tree leaf values) ∧
      final.getMem 0x43000 = BitVec.ofNat 64 layer.val ∧
      final.getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
      final.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
      SphincsVerifierHashBytes.WitnessPrefix final pk ∧
      final.getMem 0x43078 = state.getMem 0x43078 ∧
      (∀ read, LeafPathRetained read →
        final.getMem read = state.getMem read) := by
  obtain ⟨final, run, done, payload, frame, positionZero⟩ :=
    upper_rootCopy_payload target hash state values pc endpoints
  obtain ⟨layerFinal, treeFinal, leafFinal, prefixFinal⟩ :=
    leaf_copy_context_of_frame state final pk layer tree leaf
      layerCell treeCell leafCell hprefix frame
  have query := SphincsVerifierWotsLeafHeader.leafReady_fullQuery
    final pk layer tree leaf values layerFinal positionZero
      treeFinal leafFinal prefixFinal payload
  exact ⟨final, run, done, query,
    layerFinal, treeFinal, leafFinal, prefixFinal,
    leaf_copy_global_index_cell state final frame,
    fun read retained => leaf_copy_path_frame state final frame read retained⟩

/-- XMSS initialization does not change the freshly computed leaf digest. -/
theorem xmssInit_current_byte (state : MachineState)
    (i : Nat) (hi : i < 20) :
    (SphincsVerifierXmssInit.xmssInitState state).getByte
      (BitVec.ofNat 64 (0x44a00 + i)) =
      state.getByte (BitVec.ofNat 64 (0x44a00 + i)) := by
  have ha : ((BitVec.ofNat 64 0x44a00).toNat % 8 = 0) := by decide
  have hover : (BitVec.ofNat 64 0x44a00).toNat + i < 2 ^ 64 := by
    simp only [BitVec.toNat_ofNat]
    omega
  have aligned : alignToDword (BitVec.ofNat 64 (0x44a00 + i)) =
      BitVec.ofNat 64 (0x44a00 + 8 * (i / 8)) := by
    simpa only [BitVec.ofNat_add] using
      (alignToDword_add_ofNat_of_aligned ha hover)
  have inside : 0x44a00 ≤
      (alignToDword (BitVec.ofNat 64 (0x44a00 + i))).toNat ∧
      (alignToDword (BitVec.ofNat 64 (0x44a00 + i))).toNat < 0x44a18 := by
    rw [aligned, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x44a00 + 8 * (i / 8) < 2 ^ 64)]
    omega
  have frame := SphincsVerifierXmssInit.xmssInit_current state
    (alignToDword (BitVec.ofNat 64 (0x44a00 + i))) inside
  simpa only [MachineState.getByte] using
    congrArg (fun value : Word => extractByte value
      (byteOffset (BitVec.ofNat 64 (0x44a00 + i)))) frame

/-- The leaf HASH and answer copy keep the witness and XMSS controls. -/
theorem leafHashNext_frame (hash : Hash) (state : MachineState)
    (read : Word)
    (retained : read.toNat < 0x40000 ∨
      (0x43000 ≤ read.toNat ∧ read.toNat < 0x43048)) :
    (SphincsVerifierWotsLeafResult.leafHashNext hash state).getMem read =
      state.getMem read := by
  let ready := SphincsVerifierWotsLeafHashReady.leafHashReadyState state
  have belowCopy : read.toNat < 0x44a00 := by omega
  have readyFrame : ready.getMem read = state.getMem read := by
    apply SphincsVerifierWotsLeafHashReady.leafHashReady_mem_frame
    rcases retained with low | high
    · exact Or.inl low
    · exact Or.inr (by omega)
  have outsideHash (address : Word)
      (range : 0x40000 ≤ address.toNat ∧ address.toNat < 0x43000) :
      read ≠ address := by
    intro equal
    subst read
    rcases retained with low | high <;> omega
  rw [SphincsVerifierWotsLeafResult.leafHashNext,
    SphincsVerifierWotsLeafResult.leafAnswerCopy_mem_frame _ read belowCopy,
    SphincsVerifierFtsLevelInit.writeHash_mem_frame ready _
      (SphincsVerifierWotsLeafHashReady.leafHashReady_regs state).2.2.1 read
      (outsideHash 0x42000 (by decide))
      (outsideHash 0x42008 (by decide))
      (outsideHash 0x42010 (by decide))
      (outsideHash 0x42018 (by decide)),
    readyFrame]

theorem leafHashNext_global_index_cell (hash : Hash)
    (state : MachineState) :
    (SphincsVerifierWotsLeafResult.leafHashNext hash state).getMem 0x43078 =
      state.getMem 0x43078 := by
  let ready := SphincsVerifierWotsLeafHashReady.leafHashReadyState state
  have readyFrame : ready.getMem 0x43078 = state.getMem 0x43078 :=
    SphincsVerifierWotsLeafHashReady.leafHashReady_mem_frame state 0x43078
      (Or.inr (by decide))
  rw [SphincsVerifierWotsLeafResult.leafHashNext,
    SphincsVerifierWotsLeafResult.leafAnswerCopy_mem_frame _ 0x43078
      (by decide),
    SphincsVerifierFtsLevelInit.writeHash_mem_frame ready _
      (SphincsVerifierWotsLeafHashReady.leafHashReady_regs state).2.2.1
      0x43078 (by decide) (by decide) (by decide) (by decide),
    readyFrame]

theorem xmssInit_global_index_cell (state : MachineState) :
    (SphincsVerifierXmssInit.xmssInitState state).getMem 0x43078 =
      state.getMem 0x43078 := by
  simp [SphincsVerifierXmssInit.xmssInitState,
    SphincsVerifierXmssInit.xmssInitSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem leaf_finish_global_index_cell (hash : Hash)
    (state : MachineState) :
    (SphincsVerifierXmssInit.xmssInitState
      (SphincsVerifierWotsLeafResult.leafHashNext hash state)).getMem
        0x43078 = state.getMem 0x43078 :=
  (xmssInit_global_index_cell _).trans
    (leafHashNext_global_index_cell hash state)

/-- XMSS initialization also keeps the witness and input controls. -/
theorem leaf_finish_frame (hash : Hash) (state : MachineState)
    (read : Word)
    (retained : read.toNat < 0x40000 ∨
      (0x43000 ≤ read.toNat ∧ read.toNat < 0x43048)) :
    (SphincsVerifierXmssInit.xmssInitState
      (SphincsVerifierWotsLeafResult.leafHashNext hash state)).getMem read =
      state.getMem read := by
  have belowInit : read.toNat < 0x43048 := by
    rcases retained with low | high <;> omega
  exact (SphincsVerifierXmssInit.xmssInit_below_frame _ read belowInit).trans
    (leafHashNext_frame hash state read retained)

theorem leaf_finish_bit (hash : Hash) (state : MachineState) :
    (SphincsVerifierXmssInit.xmssInitState
      (SphincsVerifierWotsLeafResult.leafHashNext hash state)).getMem
        0x43070 = state.getMem 0x43020 := by
  let middle := SphincsVerifierWotsLeafResult.leafHashNext hash state
  have bit : (SphincsVerifierXmssInit.xmssInitState middle).getMem 0x43070 =
      middle.getMem 0x43020 := SphincsVerifierXmssInit.xmssInit_bit middle
  have frame : middle.getMem 0x43020 = state.getMem 0x43020 :=
    leafHashNext_frame hash state 0x43020 (Or.inr (by decide))
  exact bit.trans frame


/-- The base-layer leaf segment leaves the abstract leaf digest as XMSS's root. -/
theorem leaf_finish_semantic (hash : Hash) (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest)
    (pc : state.pc = 0x29c8)
    (query : hashInput
      (SphincsVerifierWotsLeafHashReady.leafHashReadyState state) =
        SphincsBridge.toQuery
          (SphincsVerifierWotsLeafQuery.leafInput
            pk.parameter layer tree leaf endpoints)) :
    ∃ (final : MachineState)
      (run : Trace hash SphincsImages.verify state 67 202 1 17 final),
      final.pc = 0x2ad4 ∧
      (∀ i, (hi : i < 20) →
        final.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (evalWithAnswerFn (adaptOracle hash)
            (Concrete.leafHash pk.parameter layer tree leaf endpoints)).extractLsb'
              (8 * i) 8) ∧
      final.getMem 0x43048 = 1 ∧
      final.getMem 0x43070 = state.getMem 0x43020 ∧
      final.getMem 0x43078 = state.getMem 0x43078 ∧
      (∀ read, read.toNat < 0x40000 ∨
        (0x43000 ≤ read.toNat ∧ read.toNat < 0x43048) →
          final.getMem read = state.getMem read) ∧
      SegmentInterior hash run := by
  obtain ⟨final, run, done, exact, inside⟩ :=
    SigGolfCandidate.SphincsVerifierWotsLeafInterior.leaf_finish_trace
      hash state pc
  have abstract : evalWithAnswerFn (adaptOracle hash)
      (Concrete.leafHash pk.parameter layer tree leaf endpoints) =
      truncateHash (hash (SphincsBridge.toQuery
        (SphincsVerifierWotsLeafQuery.leafInput
          pk.parameter layer tree leaf endpoints))) := by
    simpa only [Concrete.leafHash,
      SphincsVerifierWotsLeafQuery.leafInput] using
      SigGolfCandidate.SphincsMaskedChainDomain.eval_hash hash
        pk.parameter (.leaf layer tree leaf) (Concrete.leafPayload endpoints)
  refine ⟨final, run, done, ?_, ?_, ?_, ?_, ?_, inside⟩
  · intro i hi
    rw [exact, xmssInit_current_byte _ i hi,
      SphincsVerifierWotsLeafResult.leafHashNext_byte_of_query
        hash state _ query i hi, abstract]
  · rw [exact]
    exact SphincsVerifierXmssInit.xmssInit_level _
  · rw [exact]
    exact leaf_finish_bit hash state
  · rw [exact]
    exact leaf_finish_global_index_cell hash state
  · intro read retained
    rw [exact]
    exact leaf_finish_frame hash state read retained

/-- Rewriting schedule addresses does not change pure instruction execution. -/
theorem runSchedule_schedule (offset : Word)
    (code : List (Word × Instr)) (state : MachineState) :
    SphincsMaskedKeygenPrefix.runSchedule
      (SphincsMaskedSignOtsShift.schedule offset code) state =
    SphincsMaskedKeygenPrefix.runSchedule code state := by
  induction code generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      simpa [SphincsMaskedSignOtsShift.schedule,
        SphincsMaskedKeygenPrefix.runSchedule] using
        ih (execInstrBr state entry.2)

theorem leafHashSchedule_supported :
    ∀ entry ∈ SphincsVerifierWotsLeafHashReady.leafHashSchedule,
      SphincsMaskedSignOtsShift.Supported entry.2 := by decide

/-- Leaf-hash preparation commutes with a program-counter translation. -/
theorem leafHashReady_shift (offset : Word) (state : MachineState) :
    SphincsVerifierWotsLeafHashReady.leafHashReadyState
      (shift offset state) =
    shift offset
      (SphincsVerifierWotsLeafHashReady.leafHashReadyState state) := by
  change SphincsMaskedKeygenPrefix.runSchedule
      SphincsVerifierWotsLeafHashReady.leafHashSchedule
      (shift offset state) =
    shift offset (SphincsMaskedKeygenPrefix.runSchedule
      SphincsVerifierWotsLeafHashReady.leafHashSchedule state)
  rw [← runSchedule_schedule offset
    SphincsVerifierWotsLeafHashReady.leafHashSchedule (shift offset state)]
  exact SphincsMaskedSignOtsShift.run_shift offset
    SphincsVerifierWotsLeafHashReady.leafHashSchedule
    leafHashSchedule_supported state

/-- The relocated leaf HASH stores the abstract digest as the XMSS current root. -/
theorem upper_leaf_finish_semantic (target : Fin 5) (hash : Hash)
    (state : MachineState) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest)
    (pc : state.pc = 0x29c8 + delta target)
    (query : hashInput
      (SphincsVerifierWotsLeafHashReady.leafHashReadyState state) =
        SphincsBridge.toQuery
          (SphincsVerifierWotsLeafQuery.leafInput
            pk.parameter layer tree leaf endpoints)) :
    ∃ (final : MachineState),
      Trace hash SphincsImages.verify state 67 202 1 17 final ∧
      final.pc = 0x2ad4 + delta target ∧
      (∀ i, (hi : i < 20) →
        final.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (evalWithAnswerFn (adaptOracle hash)
            (Concrete.leafHash pk.parameter layer tree leaf endpoints)).extractLsb'
              (8 * i) 8) ∧
      final.getMem 0x43048 = 1 ∧
      final.getMem 0x43070 = state.getMem 0x43020 ∧
      final.getMem 0x43078 = state.getMem 0x43078 ∧
      (∀ read, read.toNat < 0x40000 ∨
        (0x43000 ≤ read.toNat ∧ read.toNat < 0x43048) →
          final.getMem read = state.getMem read) := by
  let base := shift (-delta target) state
  have basePc : base.pc = 0x29c8 := by
    change state.pc + -delta target = 0x29c8
    rw [pc]
    bv_decide
  have restored : shift (delta target) base = state := by
    simp [base, shift, MachineState.setPC]
  have baseQuery : hashInput
      (SphincsVerifierWotsLeafHashReady.leafHashReadyState base) =
        SphincsBridge.toQuery
          (SphincsVerifierWotsLeafQuery.leafInput
            pk.parameter layer tree leaf endpoints) := by
    have shifted : hashInput
        (SphincsVerifierWotsLeafHashReady.leafHashReadyState
          (shift (delta target) base)) =
          SphincsBridge.toQuery
            (SphincsVerifierWotsLeafQuery.leafInput
              pk.parameter layer tree leaf endpoints) := by
      simpa only [restored] using query
    simpa only [leafHashReady_shift, hashInput_shift] using shifted
  obtain ⟨finish, run, done, digest, level, bit, globalIndex,
    frame, inside⟩ :=
    leaf_finish_semantic hash base pk layer tree leaf endpoints basePc baseQuery
  refine ⟨shift (delta target) finish, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [restored] using trace_shift target hash run inside
  · rw [shift_pc, done]
  · intro i hi
    simpa using digest i hi
  · simpa only [shift_mem] using level
  · simpa only [shift_mem, base] using bit
  · simpa only [shift_mem, base] using globalIndex
  · intro read retained
    simpa only [shift_mem, base] using frame read retained

/-- From recovered WOTS endpoints to the XMSS starting root in an upper layer. -/
theorem upper_leaf_from_endpoints (target : Fin 5) (hash : Hash)
    (state : MachineState) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest)
    (pc : state.pc = 0x298c + delta target)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (values : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      state.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + j)) =
        (endpoints chain).extractLsb' (8 * j) 8) :
    ∃ (final : MachineState),
      Trace hash SphincsImages.verify state 856 991 1 17 final ∧
      final.pc = 0x2ad4 + delta target ∧
      (∀ i, (hi : i < 20) →
        final.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (evalWithAnswerFn (adaptOracle hash)
            (Concrete.leafHash pk.parameter layer tree leaf endpoints)).extractLsb'
              (8 * i) 8) ∧
      final.getMem 0x43048 = 1 ∧
      final.getMem 0x43070 = state.getMem 0x43020 ∧
      final.getMem 0x43078 = state.getMem 0x43078 ∧
      (∀ read, LeafPathRetained read →
        final.getMem read = state.getMem read) := by
  obtain ⟨copied, copyRun, copiedPc, query,
    _layerFinal, _treeFinal, _leafFinal, _prefixFinal, copyGlobal,
    copyFrame⟩ :=
    upper_leaf_query target hash state pk layer tree leaf endpoints
      pc layerCell treeCell leafCell hprefix values
  obtain ⟨final, finishRun, done, digest, level, bit, finishGlobal,
    finishFrame⟩ :=
    upper_leaf_finish_semantic target hash copied pk layer tree leaf endpoints
      copiedPc query
  refine ⟨final, ?_, done, digest, level, ?_,
    finishGlobal.trans copyGlobal, ?_⟩
  · simpa [Nat.add_assoc] using copyRun.trans finishRun
  · exact bit.trans (copyFrame 0x43020 (Or.inr (by decide)))
  · intro read retained
    have simple : read.toNat < 0x40000 ∨
        (0x43000 ≤ read.toNat ∧ read.toNat < 0x43048) := by
      rcases retained with low | high
      · exact Or.inl low
      · exact Or.inr ⟨high.1, high.2.1⟩
    exact (finishFrame read simple).trans (copyFrame read retained)

/-- An authentication path stays valid when the verifier leaves low memory intact. -/
theorem pathWitness_of_low_frame (initial final : MachineState)
    (signature : SphincsSecurity.Signature) (lay : Layer)
    (pointer : Word)
    (bound : pointer.toNat + 20 * layerHeight lay ≤ 0x40000)
    (frame : ∀ address, address.toNat < 0x40000 →
      final.getMem address = initial.getMem address)
    (witness : SphincsVerifierXmssPathControl.PathWitness
      initial signature lay pointer) :
    SphincsVerifierXmssPathControl.PathWitness
      final signature lay pointer := by
  constructor
  intro level hlevel i hi
  let address : Word := BitVec.ofNat 64 (pointer.toNat + 20 * level + i)
  have small : pointer.toNat + 20 * level + i < 0x40000 := by omega
  have low : address.toNat < 0x40000 := by
    simp only [address, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : pointer.toNat + 20 * level + i < 2 ^ 64)]
    exact small
  rw [SphincsVerifierWotsSemanticAllChains.lowByteFrame initial final
    frame address low]
  exact witness.bytes level hlevel i hi

theorem pathWitness_of_low_byte_frame (initial final : MachineState)
    (signature : SphincsSecurity.Signature) (lay : Layer)
    (pointer : Word)
    (bound : pointer.toNat + 20 * layerHeight lay ≤ 0x40000)
    (frame : ∀ address, address.toNat < 0x40000 →
      final.getByte address = initial.getByte address)
    (witness : SphincsVerifierXmssPathControl.PathWitness
      initial signature lay pointer) :
    SphincsVerifierXmssPathControl.PathWitness
      final signature lay pointer := by
  constructor
  intro level hlevel i hi
  let address : Word := BitVec.ofNat 64 (pointer.toNat + 20 * level + i)
  have low : address.toNat < 0x40000 := by
    simp only [address, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega :
      pointer.toNat + 20 * level + i < 2 ^ 64)]
    omega
  rw [frame address low]
  exact witness.bytes level hlevel i hi

theorem upper_path_pointer_bound (target : Fin 5) :
    (BitVec.ofNat 64
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
        20 * 52)).toNat +
      20 * layerHeight
        (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer target) ≤
      0x40000 := by
  fin_cases target <;> decide

theorem upper_path_pointer_aligned (target : Fin 5) :
    (BitVec.ofNat 64
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
        20 * 52)).toNat % 4 = 0 := by
  fin_cases target <;> decide

/-- The relocated WOTS block ends exactly where the encoded XMSS path begins. -/
theorem upper_path_source_address (target : Fin 5) :
    SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
      20 * 52 =
    0x22ca0 + SigGolfCandidate.SphincsWireEncoding.layerOffset
      (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer target) +
      SigGolfCandidate.SphincsWire.counterBytes +
      SphincsSecurity.numChains * SigGolfCandidate.SphincsWire.digestBytes := by
  fin_cases target <;> decide

theorem upper_chain_source_address (target : Fin 5) :
    SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target =
      0x22ca0 + SigGolfCandidate.SphincsWireEncoding.layerOffset
        (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer target) +
        SigGolfCandidate.SphincsWire.counterBytes := by
  fin_cases target <;> decide

/-- Each upper-layer WOTS value is already at the exact source address used
    by the relocated verifier. -/
theorem loaded_upper_chain_source (target : Fin 5)
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (state : MachineState)
    (loaded : initialState SigGolfCandidate.SphincsSubmission.submission
      .verify (message, publicKey,
        SigGolfCandidate.SphincsWireEncoding.wire pk signature) = some state)
    (chain : ChainIndex) (j : Nat) (hj : j < 20) :
    state.getByte (BitVec.ofNat 64
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
        20 * chain.val + j)) =
      (((signature.layers
        (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer target)).chainValues
          chain)).extractLsb' (8 * j) 8 := by
  let lay := SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer target
  have addressEq :
      SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
        20 * chain.val + j =
      0x22ca0 + SigGolfCandidate.SphincsWireEncoding.layerOffset lay +
        SigGolfCandidate.SphincsWire.counterBytes +
        chain.val * SigGolfCandidate.SphincsWire.digestBytes + j := by
    rw [upper_chain_source_address target]
    simp only [lay, SigGolfCandidate.SphincsWire.digestBytes]
    omega
  rw [addressEq]
  exact SigGolfCandidate.SphincsWireEncoding.loaded_honest_layerChain
    publicKey message pk signature state loaded lay chain j (by
      simpa [SigGolfCandidate.SphincsWire.digestBytes] using hj)

theorem loaded_upper_chain_source_after_frame (target : Fin 5)
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (initial final : MachineState)
    (loaded : initialState SigGolfCandidate.SphincsSubmission.submission
      .verify (message, publicKey,
        SigGolfCandidate.SphincsWireEncoding.wire pk signature) = some initial)
    (frame : ∀ address, address.toNat < 0x40000 →
      final.getByte address = initial.getByte address)
    (chain : ChainIndex) (j : Nat) (hj : j < 20) :
    final.getByte (BitVec.ofNat 64
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
        20 * chain.val + j)) =
      (((signature.layers
        (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer target)).chainValues
          chain)).extractLsb' (8 * j) 8 := by
  let address : Word := BitVec.ofNat 64
    (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
      20 * chain.val + j)
  have low : address.toNat < 0x40000 := by
    have bound := SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase_bound target
    have hc := chain.isLt
    change chain.val < 52 at hc
    have small : SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
        20 * chain.val + j < 2 ^ 64 := by omega
    simp only [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    omega
  exact (frame address low).trans
    (loaded_upper_chain_source target publicKey message pk signature initial
      loaded chain j hj)

/-- The public-key prefix and all later WOTS sources share the same low-byte
    frame invariant. -/
theorem loaded_upper_prefix_after_frame
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (initial final : MachineState)
    (loaded : initialState SigGolfCandidate.SphincsSubmission.submission
      .verify (message, publicKey,
        SigGolfCandidate.SphincsWireEncoding.wire pk signature) = some initial)
    (frame : ∀ address, address.toNat < 0x40000 →
      final.getByte address = initial.getByte address) :
    SphincsVerifierHashBytes.WitnessPrefix final pk := by
  have loadedPrefix : SphincsVerifierHashBytes.WitnessPrefix initial pk :=
    SphincsVerifierLoader.loaded_prefix publicKey message
      (SigGolfCandidate.SphincsWireEncoding.wire pk signature) pk initial
      loaded (SigGolfCandidate.SphincsWireEncoding.wire_encodedWitness pk signature)
  constructor
  · intro i hi
    have low : (BitVec.ofNat 64 (0x22ca0 + i)).toNat < 0x40000 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 0x22ca0 + i < 2 ^ 64)]
      omega
    exact (frame _ low).trans (loadedPrefix.root i hi)
  · intro i hi
    have low : (BitVec.ofNat 64 (0x22cb4 + i)).toNat < 0x40000 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : 0x22cb4 + i < 2 ^ 64)]
      omega
    exact (frame _ low).trans (loadedPrefix.parameter i hi)

/-- The freshly loaded verifier memory contains every upper-layer XMSS sibling. -/
theorem loaded_upper_path_witness (target : Fin 5)
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (state : MachineState)
    (loaded : initialState SigGolfCandidate.SphincsSubmission.submission
      .verify (message, publicKey,
        SigGolfCandidate.SphincsWireEncoding.wire pk signature) = some state) :
    SphincsVerifierXmssPathControl.PathWitness state signature
      (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer target)
      (BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * 52)) := by
  constructor
  intro level hlevel i hi
  let lay := SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer target
  let typedLevel : Fin (layerHeight lay) := ⟨level, hlevel⟩
  have pointerSmall :
      SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
        20 * 52 < 2 ^ 64 := by
    fin_cases target <;> decide
  have address :
      (BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * 52)).toNat + 20 * level + i =
      0x22ca0 + SigGolfCandidate.SphincsWireEncoding.layerOffset lay +
        SigGolfCandidate.SphincsWire.counterBytes +
        SphincsSecurity.numChains * SigGolfCandidate.SphincsWire.digestBytes +
        level * SigGolfCandidate.SphincsWire.digestBytes + i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerSmall]
    rw [upper_path_source_address target]
    simp only [lay, SigGolfCandidate.SphincsWire.digestBytes]
    omega
  rw [address]
  have loadedPath := SigGolfCandidate.SphincsWireEncoding.loaded_honest_layerPath
    publicKey message pk signature state loaded lay typedLevel i hi
  simpa [lay, typedLevel, SphincsSecurity.Concrete.signaturePath, hlevel]
    using loadedPath

/-- Any verifier prefix that preserves low bytes preserves the loaded path. -/
theorem loaded_upper_path_witness_after_frame (target : Fin 5)
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (initial final : MachineState)
    (loaded : initialState SigGolfCandidate.SphincsSubmission.submission
      .verify (message, publicKey,
        SigGolfCandidate.SphincsWireEncoding.wire pk signature) = some initial)
    (frame : ∀ address, address.toNat < 0x40000 →
      final.getByte address = initial.getByte address) :
    SphincsVerifierXmssPathControl.PathWitness final signature
      (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer target)
      (BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * 52)) := by
  exact pathWitness_of_low_byte_frame initial final signature
    (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer target)
    (BitVec.ofNat 64
      (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
        20 * 52)) (upper_path_pointer_bound target) frame
    (loaded_upper_path_witness target publicKey message pk signature initial loaded)

theorem upper_handoff_low_byte_frame (target : Fin 5) (state : MachineState)
    (address : Word) (low : address.toNat < 0x40000) :
    (SigGolfCandidate.SphincsVerifierXmssTransitionMessage.handoffState
      target state).getByte address = state.getByte address := by
  exact SphincsVerifierWotsSemanticAllChains.lowByteFrame state
    (SigGolfCandidate.SphincsVerifierXmssTransitionMessage.handoffState
      target state)
    (fun read small =>
      SigGolfCandidate.SphincsVerifierXmssTransitionMessage.handoff_low_mem
        target state read small) address low

/-- An inter-layer handoff leaves the authentication paths for later layers intact. -/
theorem upper_handoff_path_witness (target future : Fin 5)
    (state : MachineState) (signature : SphincsSecurity.Signature)
    (pointer : Word)
    (bound : pointer.toNat + 20 * layerHeight
      (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer future) ≤
        0x40000)
    (siblings : SphincsVerifierXmssPathControl.PathWitness state signature
      (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer future)
      pointer) :
    SphincsVerifierXmssPathControl.PathWitness
      (SigGolfCandidate.SphincsVerifierXmssTransitionMessage.handoffState
        target state) signature
      (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer future)
      pointer := by
  exact pathWitness_of_low_byte_frame state
    (SigGolfCandidate.SphincsVerifierXmssTransitionMessage.handoffState
      target state) signature
    (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer future)
    pointer bound
    (fun address low => upper_handoff_low_byte_frame target state address low)
    siblings

theorem upper_path_node_pc (target : Fin 5) :
    SphincsVerifierXmssParity.nodePc
      (SigGolfCandidate.SphincsVerifierXmssTransition.targetLayer target) =
        0x2ad4 + delta target := by
  fin_cases target <;> decide

/-- One upper-layer decoder, WOTS verifier, and leaf hash reach the XMSS path. -/
theorem upper_decoder_leaf_digest (target : Fin 5) (hash : Hash)
    (state ready : MachineState) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (digits : ChainIndex → Fin 8) (values : ChainIndex → Digest)
    (readyEq : ready =
      SigGolfCandidate.SphincsVerifierDecoderRelocation.setupState target
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState
          target state))
    (pc : state.pc = BitVec.ofNat 64
      (0x1f20 + 4 * SigGolfCandidate.SphincsVerifierWotsRelocationTrace.wordOffset target))
    (checksum : state.getReg .x15 +
      SigGolfCandidate.SphincsVerifierWotsDecodeData.answerSum 52 state = 194)
    (layerCell : ready.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : ready.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : ready.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (decoded : ∀ chain : ChainIndex,
      ready.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
        BitVec.ofNat 8 (digits chain).val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (source : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      state.getByte (BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      Trace hash SphincsImages.verify state steps cycles calls blocks final ∧
      final.pc = 0x2ad4 + delta target ∧
      final.getMem 0x43028 = BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * 52) ∧
      final.getMem 0x43000 = BitVec.ofNat 64 layer.val ∧
      final.getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
      (∀ i, (hi : i < 20) →
        final.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (evalWithAnswerFn (adaptOracle hash)
            (Concrete.leafHash pk.parameter layer tree leaf
              (fun chain => evalWithAnswerFn (adaptOracle hash)
                (Concrete.recoverChain pk.parameter layer tree leaf chain
                  (digits chain) (values chain))))).extractLsb' (8 * i) 8) ∧
      final.getMem 0x43048 = 1 ∧
      final.getMem 0x43070 = ready.getMem 0x43020 ∧
      final.getMem 0x43078 = ready.getMem 0x43078 ∧
      SphincsVerifierHashBytes.WitnessPrefix final pk ∧
      (∀ address, address.toNat < 0x40000 →
        final.getMem address = ready.getMem address) ∧
      steps ≤ 507 + 728 * 52 + 856 ∧
      cycles ≤ 507 + 777 * 52 + 991 ∧
      calls ≤ 7 * 52 + 1 ∧ blocks ≤ 7 * 52 + 17 := by
  obtain ⟨chains, chainSteps, chainCycles, chainCalls, chainBlocks,
    chainRun, chainsPc, pointerFinal, layerFinal, treeFinal, leafFinal, bitFinal,
    chainGlobal, prefixFinal, lowFrame, endpointBytes, stepBound, cycleBound,
    callBound, blockBound⟩ :=
    upper_decoder_chains_semantics target hash state ready pk layer tree leaf
      digits values readyEq pc checksum layerCell treeCell leafCell decoded
      hprefix source
  let recovered : ChainIndex → Digest := fun chain =>
    evalWithAnswerFn (adaptOracle hash)
      (Concrete.recoverChain pk.parameter layer tree leaf chain
        (digits chain) (values chain))
  obtain ⟨final, leafRun, done, digest, level, bitDone, leafGlobal,
    leafFrame⟩ :=
    upper_leaf_from_endpoints target hash chains pk layer tree leaf recovered
      chainsPc layerFinal treeFinal leafFinal prefixFinal
      (by intro chain j hj; exact endpointBytes chain j hj)
  refine ⟨final, chainSteps + 856, chainCycles + 991,
    chainCalls + 1, chainBlocks + 17, ?_, done, ?_, ?_, ?_, digest, level,
    bitDone.trans bitFinal, leafGlobal.trans chainGlobal, ?_, ?_,
    by omega, by omega, by omega, by omega⟩
  · simpa [Nat.add_assoc] using chainRun.trans leafRun
  · exact (leafFrame 0x43028 (Or.inr ⟨by decide, by decide, by decide⟩)).trans
      pointerFinal
  · exact (leafFrame 0x43000 (Or.inr ⟨by decide, by decide, by decide⟩)).trans
      layerFinal
  · exact (leafFrame 0x43008 (Or.inr ⟨by decide, by decide, by decide⟩)).trans
      treeFinal
  · exact witnessPrefix_frame chains final pk prefixFinal
      (fun address low => leafFrame address (Or.inl low))
  · intro address low
    exact (leafFrame address (Or.inl low)).trans (lowFrame address low)

theorem round_global_index_cell (hash : Hash) (lay : Layer)
    (state : MachineState) :
    (SphincsVerifierXmssRound.roundState hash lay state).getMem 0x43078 =
      state.getMem 0x43078 := by
  rw [SphincsVerifierXmssRoundFrame.round_mem_frame hash lay state 0x43078
    (Or.inr (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by intro offset; fin_cases offset <;> decide)
    (by decide),
    SphincsVerifierXmssNodeTransport.prefixState_eq_generic]
  change (SphincsVerifierFtsLevelPosition.levelPositionState
    (SphincsVerifierFtsLevelShift.shiftIndexState
      (SphincsVerifierFtsPairAdvance.advancePointerState
        (SphincsVerifierFtsPair.pairState state)))).getMem 0x43078 = _
  rw [SphincsVerifierFtsLevelPosition.levelPosition_mem_frame _ 0x43078
      (by decide),
    SphincsVerifierFtsLevelShift.shiftIndex_mem_frame _ 0x43078
      (by decide) (by decide),
    SphincsVerifierFtsPairAdvance.advancePointer_mem_frame _ 0x43078
      (by decide)]
  apply SphincsVerifierFtsPair.pair_scratch_frame
  · intro offset; fin_cases offset <;> decide
  · intro offset; fin_cases offset <;> decide

theorem path_global_index_cell (hash : Hash) (lay : Layer)
    (n : Nat) (state : MachineState) :
    (SphincsVerifierXmssPathControl.pathState hash lay n state).getMem
      0x43078 = state.getMem 0x43078 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      rw [SphincsVerifierXmssPathControl.pathState_succ, ih]
      exact round_global_index_cell hash lay state


/-- The recovered WOTS leaf and its authentication path reach the abstract XMSS root. -/
theorem upper_decoder_path_digest (target : Fin 5) (hash : Hash)
    (state ready : MachineState) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (signature : SphincsSecurity.Signature)
    (digits : ChainIndex → Fin 8) (values : ChainIndex → Digest)
    (layerEq : layer = SphincsVerifierXmssTransition.targetLayer target)
    (readyEq : ready =
      SigGolfCandidate.SphincsVerifierDecoderRelocation.setupState target
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.upperDecoderState
          target state))
    (pc : state.pc = BitVec.ofNat 64
      (0x1f20 + 4 * SigGolfCandidate.SphincsVerifierWotsRelocationTrace.wordOffset target))
    (checksum : state.getReg .x15 +
      SigGolfCandidate.SphincsVerifierWotsDecodeData.answerSum 52 state = 194)
    (layerCell : ready.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : ready.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : ready.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (indexCell : ready.getMem 0x43020 = BitVec.ofNat 64 leaf.val)
    (decoded : ∀ chain : ChainIndex,
      ready.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
        BitVec.ofNat 8 (digits chain).val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (source : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      state.getByte (BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8)
    (siblings : SphincsVerifierXmssPathControl.PathWitness state signature layer
      (BitVec.ofNat 64
        (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
          20 * 52))) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      Trace hash SphincsImages.verify state steps cycles calls blocks final ∧
      steps ≤ 507 + 728 * 52 + 856 ∧
      cycles ≤ 507 + 777 * 52 + 991 ∧
      calls ≤ 7 * 52 + 1 ∧ blocks ≤ 7 * 52 + 17 ∧
      (∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify
          (SphincsVerifierXmssPathControl.pathState hash layer
            (layerHeight layer) final) tailSteps result →
        Executes hash SphincsImages.verify state
          (steps + (tailSteps +
            SphincsVerifierXmssPathControl.pathInstructions hash layer
              (layerHeight layer) final))
          (result.charge
            (cycles + SphincsVerifierXmssPathControl.pathCycles hash layer
              (layerHeight layer) final)
            (calls + layerHeight layer)
            (blocks + 2 * layerHeight layer))) ∧
      let doneState := SphincsVerifierXmssPathControl.pathState hash layer
        (layerHeight layer) final
      doneState.pc = SphincsVerifierXmssNext.branchPc layer + 4 ∧
      (∀ i, (hi : i < 20) →
        doneState.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (Concrete.foldValue (adaptOracle hash) pk.parameter layer tree leaf
            (Concrete.signaturePath signature layer)
            (evalWithAnswerFn (adaptOracle hash)
              (Concrete.leafHash pk.parameter layer tree leaf
                (fun chain => evalWithAnswerFn (adaptOracle hash)
                  (Concrete.recoverChain pk.parameter layer tree leaf chain
                    (digits chain) (values chain)))))
            (layerHeight layer)).extractLsb' (8 * i) 8) ∧
      SphincsVerifierXmssPathControl.pathCycles hash layer
        (layerHeight layer) final ≤ 141 * layerHeight layer ∧
      doneState.getMem 0x43078 = ready.getMem 0x43078 ∧
      (∀ address, address.toNat < 0x40000 →
        doneState.getByte address = state.getByte address) := by
  let pointer : Word := BitVec.ofNat 64
    (SigGolfCandidate.SphincsVerifierDecoderRelocation.sourceBase target +
      20 * 52)
  let first : Digest := evalWithAnswerFn (adaptOracle hash)
    (Concrete.leafHash pk.parameter layer tree leaf
      (fun chain => evalWithAnswerFn (adaptOracle hash)
        (Concrete.recoverChain pk.parameter layer tree leaf chain
          (digits chain) (values chain))))
  have readySiblings : SphincsVerifierXmssPathControl.PathWitness
      ready signature layer pointer := by
    constructor
    intro level hlevel i hi
    let address : Word := BitVec.ofNat 64 (pointer.toNat + 20 * level + i)
    have bound : pointer.toNat + 20 * layerHeight layer ≤ 0x40000 := by
      rw [layerEq]
      exact upper_path_pointer_bound target
    have low : address.toNat < 0x40000 := by
      simp only [address, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega :
        pointer.toNat + 20 * level + i < 2 ^ 64)]
      omega
    rw [readyEq, upper_ready_low_byte_frame target state address low]
    exact siblings.bytes level hlevel i hi
  obtain ⟨final, steps, cycles, calls, blocks, run, done, pointerCell,
    layerFinal, treeFinal, current, level, bit, globalIndex,
    prefixFinal, lowFrame,
    stepBound, cycleBound, callBound, blockBound⟩ :=
    upper_decoder_leaf_digest target hash state ready pk layer tree leaf
      digits values readyEq pc checksum layerCell treeCell leafCell decoded
      hprefix source
  have bound : pointer.toNat + 20 * layerHeight layer ≤ 0x40000 := by
    rw [layerEq]
    exact upper_path_pointer_bound target
  have aligned : pointer.toNat % 4 = 0 := upper_path_pointer_aligned target
  have finalPc : final.pc = SphincsVerifierXmssParity.nodePc layer := by
    rw [layerEq, upper_path_node_pc]
    exact done
  have finalSiblings : SphincsVerifierXmssPathControl.PathWitness
      final signature layer pointer :=
    pathWitness_of_low_frame ready final signature layer pointer bound
      lowFrame readySiblings
  have path := SphincsVerifierXmssPathComplete.complete_path
    hash layer final pk tree leaf signature first pointer finalPc
    pointerCell bound aligned layerFinal treeFinal level
    (bit.trans indexCell) prefixFinal current finalSiblings
  have continuation (tailSteps : Nat) (result : Execution)
      (tail : Executes hash SphincsImages.verify
        (SphincsVerifierXmssPathControl.pathState hash layer
          (layerHeight layer) final) tailSteps result) :
      Executes hash SphincsImages.verify state
        (steps + (tailSteps +
          SphincsVerifierXmssPathControl.pathInstructions hash layer
            (layerHeight layer) final))
        (result.charge
          (cycles + SphincsVerifierXmssPathControl.pathCycles hash layer
            (layerHeight layer) final)
          (calls + layerHeight layer)
          (blocks + 2 * layerHeight layer)) := by
    have suffix := SphincsVerifierXmssPathComplete.complete_path_executes
      hash layer final pointer finalPc pointerCell bound aligned level
        tailSteps result tail
    simpa [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using run.then_executes suffix
  have endFrame (address : Word) (low : address.toNat < 0x40000) :
      (SphincsVerifierXmssPathControl.pathState hash layer
        (layerHeight layer) final).getByte address = state.getByte address := by
    have pathFrame := SphincsVerifierWotsSemanticAllChains.lowByteFrame
      final (SphincsVerifierXmssPathControl.pathState hash layer
        (layerHeight layer) final)
        (fun read small =>
          SphincsVerifierXmssPathControl.path_low_mem hash layer
            (layerHeight layer) final read small) address low
    have leafFrame := SphincsVerifierWotsSemanticAllChains.lowByteFrame
      ready final lowFrame address low
    exact pathFrame.trans (leafFrame.trans (by
      rw [readyEq]
      exact upper_ready_low_byte_frame target state address low))
  exact ⟨final, steps, cycles, calls, blocks, run,
    stepBound, cycleBound, callBound, blockBound, continuation,
    path.1, path.2.1, path.2.2,
    (path_global_index_cell hash layer (layerHeight layer) final).trans
      globalIndex,
    endFrame⟩

theorem upper_handoff_global_index_cell (target : Fin 5)
    (state : MachineState) :
    (SphincsVerifierXmssTransitionMessage.handoffState target state).getMem
      0x43078 = state.getMem 0x43078 := by
  let middle := SphincsVerifierXmssTransition.transitionState target state
  let pointers := SphincsVerifierXmssTransitionMessage.pointerState target middle
  change (SphincsVerifierCopy.copyRootState pointers).getMem 0x43078 = _
  rw [SphincsVerifierCopyMemory.copyRoot_mem_frame pointers 0x43078 (by
      intro offset
      rw [SphincsVerifierXmssTransitionMessage.pointer_destination]
      fin_cases offset <;> decide),
    SphincsVerifierXmssTransitionMessage.pointer_mem target middle 0x43078,
    SphincsVerifierXmssTransition.transition_global_index]


/-- A verified upper layer and the following 43 ordinary instructions form one
composable prefix. The resulting message is the XMSS root, while every later
authentication path remains available in the same low-memory input buffer. -/
theorem upper_decoder_path_handoff (target next : Fin 5) (hash : Hash)
    (state ready : MachineState) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (signature : SphincsSecurity.Signature)
    (digits : ChainIndex → Fin 8) (values : ChainIndex → Digest)
    (layerEq : layer = SphincsVerifierXmssTransition.targetLayer target)
    (handoffLayer : layer = SphincsVerifierXmssTransition.previousLayer next)
    (readyEq : ready =
      SphincsVerifierDecoderRelocation.setupState target
        (SphincsVerifierDecoderRelocation.upperDecoderState target state))
    (pc : state.pc = BitVec.ofNat 64
      (0x1f20 + 4 * SphincsVerifierWotsRelocationTrace.wordOffset target))
    (checksum : state.getReg .x15 +
      SphincsVerifierWotsDecodeData.answerSum 52 state = 194)
    (layerCell : ready.getMem 0x43000 = BitVec.ofNat 64 layer.val)
    (treeCell : ready.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : ready.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (indexCell : ready.getMem 0x43020 = BitVec.ofNat 64 leaf.val)
    (decoded : ∀ chain : ChainIndex,
      ready.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
        BitVec.ofNat 8 (digits chain).val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (source : ∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      state.getByte (BitVec.ofNat 64
        (SphincsVerifierDecoderRelocation.sourceBase target +
          20 * chain.val + j)) =
        (values chain).extractLsb' (8 * j) 8)
    (siblings : SphincsVerifierXmssPathControl.PathWitness state signature layer
      (BitVec.ofNat 64
        (SphincsVerifierDecoderRelocation.sourceBase target + 20 * 52))) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      let pathEnd := SphincsVerifierXmssPathControl.pathState hash layer
        (layerHeight layer) final
      let nextState := SphincsVerifierXmssTransitionMessage.handoffState next pathEnd
      Trace hash SphincsImages.verify state steps cycles calls blocks final ∧
      steps ≤ 507 + 728 * 52 + 856 ∧
      cycles ≤ 507 + 777 * 52 + 991 ∧
      calls ≤ 7 * 52 + 1 ∧ blocks ≤ 7 * 52 + 17 ∧
      OrdinarySteps SphincsImages.verify pathEnd 43 nextState ∧
      (∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify nextState tailSteps result →
          Executes hash SphincsImages.verify state
            (steps + ((tailSteps + 43) +
              SphincsVerifierXmssPathControl.pathInstructions hash layer
                (layerHeight layer) final))
            ((result.charge 43 0 0).charge
              (cycles + SphincsVerifierXmssPathControl.pathCycles hash layer
                (layerHeight layer) final)
              (calls + layerHeight layer)
              (blocks + 2 * layerHeight layer))) ∧
      (∀ i, (hi : i < 20) →
        nextState.getByte (BitVec.ofNat 64 (0x40028 + i)) =
          (Concrete.foldValue (adaptOracle hash) pk.parameter layer tree leaf
            (Concrete.signaturePath signature layer)
            (evalWithAnswerFn (adaptOracle hash)
              (Concrete.leafHash pk.parameter layer tree leaf
                (fun chain => evalWithAnswerFn (adaptOracle hash)
                  (Concrete.recoverChain pk.parameter layer tree leaf chain
                    (digits chain) (values chain)))))
            (layerHeight layer)).extractLsb' (8 * i) 8) ∧
      (∀ address, address.toNat < 0x40000 →
        nextState.getByte address = state.getByte address) ∧
      nextState.getMem 0x43078 = ready.getMem 0x43078 ∧
      (∀ future : Fin 5,
        SphincsVerifierXmssPathControl.PathWitness state signature
          (SphincsVerifierXmssTransition.targetLayer future)
          (BitVec.ofNat 64
            (SphincsVerifierDecoderRelocation.sourceBase future + 20 * 52)) →
        SphincsVerifierXmssPathControl.PathWitness nextState signature
          (SphincsVerifierXmssTransition.targetLayer future)
          (BitVec.ofNat 64
            (SphincsVerifierDecoderRelocation.sourceBase future + 20 * 52))) := by
  obtain ⟨final, steps, cycles, calls, blocks, run,
    stepBound, cycleBound, callBound, blockBound, continuation,
    donePc, rootBytes, _pathCycleBound, pathGlobal, pathFrame⟩ :=
    upper_decoder_path_digest target hash state ready pk layer tree leaf
      signature digits values layerEq readyEq pc checksum layerCell treeCell
      leafCell indexCell decoded hprefix source siblings
  let pathEnd := SphincsVerifierXmssPathControl.pathState hash layer
    (layerHeight layer) final
  let nextState := SphincsVerifierXmssTransitionMessage.handoffState next pathEnd
  have handoffPc : pathEnd.pc =
      SphincsVerifierXmssTransition.transitionPc next := by
    rw [donePc, handoffLayer]
    rfl
  have handoff : OrdinarySteps SphincsImages.verify pathEnd 43 nextState :=
    SphincsVerifierXmssTransitionMessage.handoff_block next pathEnd handoffPc
  have lowFrame (address : Word) (low : address.toNat < 0x40000) :
      nextState.getByte address = state.getByte address :=
    (upper_handoff_low_byte_frame next pathEnd address low).trans
      (pathFrame address low)
  refine ⟨final, steps, cycles, calls, blocks, run,
    stepBound, cycleBound, callBound, blockBound, handoff, ?_, ?_, lowFrame,
    (upper_handoff_global_index_cell next pathEnd).trans pathGlobal, ?_⟩
  · intro tailSteps result tail
    have afterHandoff : Executes hash SphincsImages.verify pathEnd
        (tailSteps + 43) (result.charge 43 0 0) :=
      handoff.then_executes tail
    exact continuation (tailSteps + 43) (result.charge 43 0 0)
      afterHandoff
  · intro i hi
    exact (SphincsVerifierXmssTransitionMessage.handoff_byte next pathEnd i hi).trans
      (rootBytes i hi)
  · intro future futureWitness
    have pathWitness := pathWitness_of_low_byte_frame state pathEnd signature
      (SphincsVerifierXmssTransition.targetLayer future)
      (BitVec.ofNat 64
        (SphincsVerifierDecoderRelocation.sourceBase future + 20 * 52))
      (upper_path_pointer_bound future) pathFrame futureWitness
    exact upper_handoff_path_witness next future pathEnd signature
      (BitVec.ofNat 64
        (SphincsVerifierDecoderRelocation.sourceBase future + 20 * 52))
      (upper_path_pointer_bound future) pathWitness

/-- The low-byte frame returned by an inter-layer handoff supplies every
    witness-backed semantic input of the next upper-layer decoder. -/
theorem loaded_next_upper_witness_inputs (next : Fin 5)
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (initial nextState : MachineState)
    (loaded : initialState SigGolfCandidate.SphincsSubmission.submission
      .verify (message, publicKey,
        SigGolfCandidate.SphincsWireEncoding.wire pk signature) = some initial)
    (frame : ∀ address, address.toNat < 0x40000 →
      nextState.getByte address = initial.getByte address) :
    let ready := SphincsVerifierDecoderRelocation.setupState next
      (SphincsVerifierDecoderRelocation.upperDecoderState next nextState)
    SphincsVerifierHashBytes.WitnessPrefix nextState pk ∧
    (∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      nextState.getByte (BitVec.ofNat 64
        (SphincsVerifierDecoderRelocation.sourceBase next +
          20 * chain.val + j)) =
        ((signature.layers
          (SphincsVerifierXmssTransition.targetLayer next)).chainValues
            chain).extractLsb' (8 * j) 8) ∧
    SphincsVerifierXmssPathControl.PathWitness nextState signature
      (SphincsVerifierXmssTransition.targetLayer next)
      (BitVec.ofNat 64
        (SphincsVerifierDecoderRelocation.sourceBase next + 20 * 52)) ∧
    SphincsVerifierHashBytes.WitnessPrefix ready pk ∧
    (∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
      ready.getByte (BitVec.ofNat 64
        (SphincsVerifierDecoderRelocation.sourceBase next +
          20 * chain.val + j)) =
        ((signature.layers
          (SphincsVerifierXmssTransition.targetLayer next)).chainValues
            chain).extractLsb' (8 * j) 8) := by
  have hprefix := loaded_upper_prefix_after_frame publicKey message pk
    signature initial nextState loaded frame
  have source := loaded_upper_chain_source_after_frame next publicKey
    message pk signature initial nextState loaded frame
  have path := loaded_upper_path_witness_after_frame next publicKey
    message pk signature initial nextState loaded frame
  exact ⟨hprefix, source, path,
    upper_ready_prefix next nextState pk hprefix,
    upper_ready_source next nextState _ source⟩

/-- The ordinary inter-layer handoff stops at the beginning of the next
    layer's counter-and-hash prefix, before digit decoding. -/
theorem upper_handoff_prefix_pc (next : Fin 5) (state : MachineState)
    (pc : state.pc =
      SphincsVerifierXmssTransition.transitionPc next) :
    (SphincsVerifierXmssTransitionMessage.handoffState next state).pc =
      SphincsVerifierXmssTransitionMessage.messagePc next + 56 := by
  let middle := SphincsVerifierXmssTransition.transitionState next state
  let pointers := SphincsVerifierXmssTransitionMessage.pointerState next middle
  have middlePc : middle.pc =
      SphincsVerifierXmssTransitionMessage.messagePc next := by
    simpa [middle, SphincsVerifierXmssTransitionMessage.messagePc] using
      SphincsVerifierXmssTransition.transition_pc next state pc
  have pointerPc : pointers.pc =
      SphincsVerifierXmssTransitionMessage.messagePc next + 16 :=
    SphincsVerifierXmssTransitionMessage.pointer_pc next middle middlePc
  have indexedPc : pointers.pc = BitVec.ofNat 64
      (0x1000 + 4 *
        ((SphincsVerifierXmssTransitionMessage.messagePc next + 16).toNat / 4 -
          0x400)) := by
    rw [pointerPc]
    fin_cases next <;> decide
  have copied := SphincsVerifierMessageCopy.copy20_final_pc pointers
    ((SphincsVerifierXmssTransitionMessage.messagePc next + 16).toNat / 4 -
      0x400) indexedPc
  change (SphincsVerifierXmssTransitionMessage.messageState next middle).pc =
      SphincsVerifierXmssTransitionMessage.messagePc next + 56
  simpa [SphincsVerifierXmssTransitionMessage.messageState, pointers] using
    (show (SphincsVerifierCopy.copyRootState pointers).pc =
      SphincsVerifierXmssTransitionMessage.messagePc next + 56 by
        rw [copied]
        fin_cases next <;> decide)

theorem upper_handoff_decoder_gap (next : Fin 5) (state : MachineState)
    (pc : state.pc =
      SphincsVerifierXmssTransition.transitionPc next) :
    (SphincsVerifierXmssTransitionMessage.handoffState next state).pc +
      256 = BitVec.ofNat 64
        (0x1f20 + 4 * SphincsVerifierWotsRelocationTrace.wordOffset next) := by
  rw [upper_handoff_prefix_pc next state pc]
  fin_cases next <;> decide

/-- The handoff installs the next layer's control words before the intervening
    counter/hash prefix. -/
theorem upper_handoff_control_cells (next : Fin 5)
    (state : MachineState) :
    let done := SphincsVerifierXmssTransitionMessage.handoffState next state
    let lay := SphincsVerifierXmssTransition.targetLayer next
    done.getMem 0x43000 = BitVec.ofNat 64 lay.val ∧
    done.getMem 0x43008 = state.getMem 0x43078 >>>
      (heightBelow lay + layerHeight lay) ∧
    done.getMem 0x43020 =
      (state.getMem 0x43078 >>> heightBelow lay) &&&
        BitVec.ofNat 64 (2 ^ layerHeight lay - 1) ∧
    done.getMem 0x43018 = done.getMem 0x43020 := by
  let middle := SphincsVerifierXmssTransition.transitionState next state
  let pointers := SphincsVerifierXmssTransitionMessage.pointerState next middle
  have unchanged (address : Word)
      (outside : ∀ offset : Fin 5,
        address ≠ alignToDword
          (pointers.getReg .x7 +
            signExtend12 (4#12 * BitVec.ofNat 12 offset.val))) :
      (SphincsVerifierXmssTransitionMessage.handoffState next state).getMem
        address = middle.getMem address := by
    have copy :=
      SphincsVerifierCopyMemory.copyRoot_mem_frame pointers address outside
    simpa [SphincsVerifierXmssTransitionMessage.handoffState,
      SphincsVerifierXmssTransitionMessage.messageState, pointers, middle] using
      copy.trans
        (SphincsVerifierXmssTransitionMessage.pointer_mem next middle address)
  have keepLayer : _ := unchanged 0x43000 (by
    intro offset
    rw [SphincsVerifierXmssTransitionMessage.pointer_destination]
    fin_cases offset <;> decide)
  have keepTree : _ := unchanged 0x43008 (by
    intro offset
    rw [SphincsVerifierXmssTransitionMessage.pointer_destination]
    fin_cases offset <;> decide)
  have keepIndex : _ := unchanged 0x43020 (by
    intro offset
    rw [SphincsVerifierXmssTransitionMessage.pointer_destination]
    fin_cases offset <;> decide)
  have keepLeaf : _ := unchanged 0x43018 (by
    intro offset
    rw [SphincsVerifierXmssTransitionMessage.pointer_destination]
    fin_cases offset <;> decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [keepLayer]
    exact SphincsVerifierXmssTransition.transition_layer next state
  · rw [keepTree]
    exact SphincsVerifierXmssTransition.transition_tree next state
  · rw [keepIndex]
    exact SphincsVerifierXmssTransition.transition_leaf next state
  · rw [keepLeaf, keepIndex]
    exact SphincsVerifierXmssTransition.transition_index next state

theorem upper_handoff_position_zero (next : Fin 5)
    (state : MachineState) :
    (SphincsVerifierXmssTransitionMessage.handoffState next state).getMem
      0x43010 = 0 := by
  let middle := SphincsVerifierXmssTransition.transitionState next state
  let pointers := SphincsVerifierXmssTransitionMessage.pointerState next middle
  have frame := SphincsVerifierCopyMemory.copyRoot_mem_frame pointers
    0x43010 (by
      intro offset
      rw [SphincsVerifierXmssTransitionMessage.pointer_destination]
      fin_cases offset <;> decide)
  have pointerFrame :=
    SphincsVerifierXmssTransitionMessage.pointer_mem next middle 0x43010
  have position := SphincsVerifierXmssTransition.transition_level next state
  simpa [SphincsVerifierXmssTransitionMessage.handoffState,
    SphincsVerifierXmssTransitionMessage.messageState, pointers, middle]
    using (frame.trans pointerFrame).trans position

/- The first upper layer begins at 0x6d1c after its XMSS-root handoff.
   Its signed 20-bit encoding counter is stored at witness address 0x23dbc. -/
private def firstUpperCounterSchedule : List (Word × Instr) := [
  (0x6d1c, .LUI .x6 0x24),
  (0x6d20, .ADDI .x6 .x6 (-580)),
  (0x6d24, .LWU .x10 .x6 0),
  (0x6d28, .SRLI .x11 .x10 20),
  (0x6d2c, .BEQ .x11 .x0 8),
  (0x6d34, .LUI .x7 0x40),
  (0x6d38, .ADDI .x7 .x7 0),
  (0x6d3c, .SW .x7 .x10 60)]

private theorem firstUpperCounter_code :
    ∀ entry ∈ firstUpperCounterSchedule,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by decide

/-- The five upper counter prefixes differ only in the source-address load. -/
private def upperPrefixPc (target : Fin 5) : Word :=
  BitVec.ofNat 64 (0x6d1c - 0xfcc * target.val)

private def upperCounterSource (target : Fin 5) : Word :=
  BitVec.ofNat 64 (0x22ca0 +
    SphincsWireEncoding.layerOffset
      (SphincsVerifierXmssTransition.targetLayer target))

private theorem upperCounterSource_num (target : Fin 5) :
    upperCounterSource target = BitVec.ofNat 64 (match target.val with
      | 0 => 0x23dbc | 1 => 0x242ac | 2 => 0x24724
      | 3 => 0x24b9c | _ => 0x25014) := by
  fin_cases target <;> decide

private def upperCounterLui (target : Fin 5) : BitVec 20 :=
  if target.val < 3 then 0x24 else 0x25

private def upperCounterAddi (target : Fin 5) : BitVec 12 :=
  match target.val with
  | 0 => -580
  | 1 => 684
  | 2 => 1828
  | 3 => -1124
  | _ => 20

private def upperCounterSchedule (target : Fin 5) : List (Word × Instr) :=
  let pc := upperPrefixPc target
  [ (pc, .LUI .x6 (upperCounterLui target)),
    (pc + 4, .ADDI .x6 .x6 (upperCounterAddi target)),
    (pc + 8, .LWU .x10 .x6 0),
    (pc + 12, .SRLI .x11 .x10 20),
    (pc + 16, .BEQ .x11 .x0 8),
    (pc + 24, .LUI .x7 0x40),
    (pc + 28, .ADDI .x7 .x7 0),
    (pc + 32, .SW .x7 .x10 60) ]

private theorem upperCounter_code (target : Fin 5) :
    ∀ entry ∈ upperCounterSchedule target,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by
  fin_cases target <;> decide

private def upperCounterState (target : Fin 5)
    (state : MachineState) : MachineState :=
  SphincsMaskedKeygenPrefix.runSchedule (upperCounterSchedule target) state

private theorem upperCounter_checked (target : Fin 5)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target)
    (small : BitVec.setWidth 64
      (state.getWord32 (upperCounterSource target)) >>> 20 = 0) :
    SphincsMaskedKeygenPrefix.Checked (upperCounterSchedule target) state := by
  fin_cases target <;>
    simp [SphincsMaskedKeygenPrefix.Checked, upperCounterSchedule,
      upperPrefixPc, upperCounterSource_num, upperCounterLui,
      upperCounterAddi,
      execInstrBr, ordinaryStep,
      memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
      signExtend12, signExtend13,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      MachineState.setWord32, alignToDword, byteOffset, pc] at small ⊢
  all_goals simp [small]

theorem upper_counter_block (target : Fin 5) (state : MachineState)
    (pc : state.pc = upperPrefixPc target)
    (small : BitVec.setWidth 64
      (state.getWord32 (upperCounterSource target)) >>> 20 = 0) :
    OrdinarySteps SphincsImages.verify state 8
      (upperCounterState target state) := by
  simpa only [upperCounterState, upperCounterSchedule,
    List.length_cons, List.length_nil, Nat.reduceAdd] using
      SphincsMaskedKeygenPrefix.checked_sound SphincsImages.verify
        (upperCounterSchedule target) (upperCounter_code target) state
        (upperCounter_checked target state pc small)

theorem upper_counter_pc (target : Fin 5) (state : MachineState)
    (pc : state.pc = upperPrefixPc target)
    (small : BitVec.setWidth 64
      (state.getWord32 (upperCounterSource target)) >>> 20 = 0) :
    (upperCounterState target state).pc = upperPrefixPc target + 36 := by
  fin_cases target <;>
    simp [upperCounterState, upperCounterSchedule, upperPrefixPc,
      upperCounterSource_num, upperCounterLui, upperCounterAddi,
      SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
      signExtend12, signExtend13,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      pc] at small ⊢
  all_goals simp [small]

theorem upper_counter_mem_frame (target : Fin 5)
    (state : MachineState) (read : Word)
    (outside : read ≠ 0x40038) :
    (upperCounterState target state).getMem read = state.getMem read := by
  fin_cases target <;>
    simp [upperCounterState, upperCounterSchedule,
      upperCounterLui, upperCounterAddi, upperPrefixPc,
      SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
      signExtend12, signExtend13, setWord32_eq, alignToDword,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      MachineState.getMem_setPC, MachineState.getMem_setReg]
  all_goals
    intro equal
    exact False.elim (outside equal)

theorem upper_counter_stored (target : Fin 5)
    (state : MachineState) :
    (upperCounterState target state).getWord32 0x4003c =
      state.getWord32 (upperCounterSource target) := by
  fin_cases target <;>
    simp [upperCounterState, upperCounterSchedule,
      upperCounterLui, upperCounterAddi, upperPrefixPc,
      upperCounterSource_num,
      SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
      SphincsVerifierCopyMemory.getWord32_setWord32_same,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

theorem upper_counter_payload_word (target : Fin 5)
    (state : MachineState) (index : Fin 5) :
    (upperCounterState target state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  fin_cases target <;> fin_cases index <;>
    simp [upperCounterState, upperCounterSchedule, upperCounterLui,
      upperCounterAddi, upperPrefixPc,
      SphincsMaskedKeygenPrefix.runSchedule, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] <;>
    (rw [SphincsVerifierCopyMemory.getWord32_setWord32_other
      _ _ _ _ (by decide)];
      split_ifs <;> simp [MachineState.getWord32,
        MachineState.getMem_setPC, MachineState.getMem_setReg])

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_counter_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_counter_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_counter_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_counter_pc

private def firstUpperCounterState (state : MachineState) : MachineState :=
  SphincsMaskedKeygenPrefix.runSchedule firstUpperCounterSchedule state

private theorem firstUpperCounter_checked (state : MachineState)
    (pc : state.pc = 0x6d1c)
    (small : BitVec.setWidth 64 (state.getWord32 0x23dbc) >>> 20 = 0) :
    SphincsMaskedKeygenPrefix.Checked firstUpperCounterSchedule state := by
  simp [SphincsMaskedKeygenPrefix.Checked, firstUpperCounterSchedule,
    execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
    rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]
  all_goals
    refine ⟨small, ?_⟩
    have small' : BitVec.setWidth 64 (state.getWord32 (146876#64)) >>> 20 = (0#64) := small
    rw [small']
    decide

theorem first_upper_counter_block (state : MachineState)
    (pc : state.pc = 0x6d1c)
    (small : BitVec.setWidth 64 (state.getWord32 0x23dbc) >>> 20 = 0) :
    OrdinarySteps SphincsImages.verify state 8
      (firstUpperCounterState state) := by
  simpa only [firstUpperCounterState, firstUpperCounterSchedule,
    List.length_cons, List.length_nil, Nat.reduceAdd] using
    SphincsMaskedKeygenPrefix.checked_sound SphincsImages.verify
      firstUpperCounterSchedule firstUpperCounter_code state
      (firstUpperCounter_checked state pc small)

theorem first_upper_counter_pc (state : MachineState)
    (pc : state.pc = 0x6d1c)
    (small : BitVec.setWidth 64 (state.getWord32 0x23dbc) >>> 20 = 0) :
    (firstUpperCounterState state).pc = 0x6d40 := by
  simp [firstUpperCounterState, firstUpperCounterSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr, signExtend12,
    signExtend13, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc]
  have small' : BitVec.setWidth 64 (state.getWord32 (146876#64)) >>> 20 = (0#64) := small
  rw [small']
  decide

theorem first_upper_counter_mem_frame (state : MachineState) (read : Word)
    (outside : read ≠ 0x40038) :
    (firstUpperCounterState state).getMem read = state.getMem read := by
  simp [firstUpperCounterState, firstUpperCounterSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
    signExtend12, signExtend13, setWord32_eq, alignToDword,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setPC, MachineState.getMem_setReg]
  intro equal
  exact False.elim (outside equal)

theorem first_upper_counter_payload_word (state : MachineState)
    (index : Fin 5) :
    (firstUpperCounterState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  fin_cases index <;>
    simp [firstUpperCounterState, firstUpperCounterSchedule,
      SphincsMaskedKeygenPrefix.runSchedule, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] <;>
    (rw [SphincsVerifierCopyMemory.getWord32_setWord32_other
      _ _ _ _ (by decide)];
      split_ifs <;> simp [MachineState.getWord32,
        MachineState.getMem_setPC, MachineState.getMem_setReg])

theorem first_upper_counter_stored (state : MachineState) :
    (firstUpperCounterState state).getWord32 0x4003c =
      state.getWord32 0x23dbc := by
  simp [firstUpperCounterState, firstUpperCounterSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
    SphincsVerifierCopyMemory.getWord32_setWord32_same, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

private def firstUpperHeaderSchedule : List (Word × Instr) := [
  (0x6d40, .ADDI .x6 .x0 1025),
  (0x6d44, .LUI .x28 0x43),
  (0x6d48, .ADDI .x28 .x28 0),
  (0x6d4c, .LD .x7 .x28 0),
  (0x6d50, .SLLI .x7 .x7 16),
  (0x6d54, .ADD .x6 .x6 .x7),
  (0x6d58, .LUI .x7 0x40),
  (0x6d5c, .ADDI .x7 .x7 0),
  (0x6d60, .SW .x7 .x6 0),
  (0x6d64, .LUI .x28 0x43),
  (0x6d68, .ADDI .x28 .x28 16),
  (0x6d6c, .LD .x6 .x28 0),
  (0x6d70, .SW .x7 .x6 4),
  (0x6d74, .LUI .x28 0x43),
  (0x6d78, .ADDI .x28 .x28 8),
  (0x6d7c, .LD .x6 .x28 0),
  (0x6d80, .SD .x7 .x6 8),
  (0x6d84, .LUI .x28 0x43),
  (0x6d88, .ADDI .x28 .x28 24),
  (0x6d8c, .LD .x6 .x28 0),
  (0x6d90, .SW .x7 .x6 16)]

private theorem firstUpperHeader_code :
    ∀ entry ∈ firstUpperHeaderSchedule,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by decide

private def upperHeaderSchedule (target : Fin 5) : List (Word × Instr) :=
  firstUpperHeaderSchedule.map (fun entry =>
    (entry.1 - BitVec.ofNat 64 (0xfcc * target.val), entry.2))

private theorem upperHeader_code (target : Fin 5) :
    ∀ entry ∈ upperHeaderSchedule target,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by
  fin_cases target <;> decide

private theorem runSchedule_map_pc (offset : Word)
    (code : List (Word × Instr)) (state : MachineState) :
    SphincsMaskedKeygenPrefix.runSchedule
      (code.map (fun entry => (entry.1 - offset, entry.2))) state =
    SphincsMaskedKeygenPrefix.runSchedule code state := by
  induction code generalizing state with
  | nil => rfl
  | cons entry tail ih =>
      simpa [SphincsMaskedKeygenPrefix.runSchedule] using
        ih (execInstrBr state entry.2)

private def firstUpperHeaderState (state : MachineState) : MachineState :=
  SphincsMaskedKeygenPrefix.runSchedule firstUpperHeaderSchedule state

private theorem firstUpperHeader_checked (state : MachineState)
    (pc : state.pc = 0x6d40) :
    SphincsMaskedKeygenPrefix.Checked firstUpperHeaderSchedule state := by
  simp [SphincsMaskedKeygenPrefix.Checked, firstUpperHeaderSchedule,
    execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
    rangeValid, MEMORY_BYTES, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

private theorem upperHeader_checked (target : Fin 5)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 36) :
    SphincsMaskedKeygenPrefix.Checked (upperHeaderSchedule target) state := by
  fin_cases target <;>
    simp [SphincsMaskedKeygenPrefix.Checked, upperHeaderSchedule,
      firstUpperHeaderSchedule, upperPrefixPc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      MachineState.setWord32, alignToDword, byteOffset, pc]

theorem upper_header_block (target : Fin 5) (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 36) :
    OrdinarySteps SphincsImages.verify state 21
      (firstUpperHeaderState state) := by
  have run := SphincsMaskedKeygenPrefix.checked_sound SphincsImages.verify
    (upperHeaderSchedule target) (upperHeader_code target) state
    (upperHeader_checked target state pc)
  simpa only [upperHeaderSchedule, firstUpperHeaderState,
    runSchedule_map_pc, List.length_map,
    firstUpperHeaderSchedule, List.length_cons, List.length_nil,
    Nat.reduceAdd] using run

theorem upper_header_pc (target : Fin 5) (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 36) :
    (firstUpperHeaderState state).pc = upperPrefixPc target + 120 := by
  fin_cases target <;>
    simp [firstUpperHeaderState, firstUpperHeaderSchedule,
      SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
      upperPrefixPc, pc]

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_header_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_header_block

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_header_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_header_pc

theorem first_upper_header_block (state : MachineState)
    (pc : state.pc = 0x6d40) :
    OrdinarySteps SphincsImages.verify state 21
      (firstUpperHeaderState state) := by
  simpa only [firstUpperHeaderState, firstUpperHeaderSchedule,
    List.length_cons, List.length_nil, Nat.reduceAdd] using
    SphincsMaskedKeygenPrefix.checked_sound SphincsImages.verify
      firstUpperHeaderSchedule firstUpperHeader_code state
      (firstUpperHeader_checked state pc)

theorem first_upper_header_pc (state : MachineState)
    (pc : state.pc = 0x6d40) :
    (firstUpperHeaderState state).pc = 0x6d94 := by
  simp [firstUpperHeaderState, firstUpperHeaderSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr, pc]

theorem first_upper_header_mem_frame (state : MachineState) (read : Word)
    (outside : read.toNat < 0x40000 ∨ 0x40018 ≤ read.toNat) :
    (firstUpperHeaderState state).getMem read = state.getMem read := by
  have ne (written : Word)
      (lo : 0x40000 ≤ written.toNat) (hi : written.toNat < 0x40018) :
      read ≠ written := by
    intro h
    have := congrArg BitVec.toNat h
    rcases outside with a | b <;> omega
  simp [firstUpperHeaderState, firstUpperHeaderSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
    signExtend12, setWord32_eq, alignToDword,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setPC, MachineState.getMem_setReg,
    MachineState.getMem_setMem_ne]
  have n0 : read ≠ (262144#64) := ne _ (by decide) (by decide)
  have n8 : read ≠ (262152#64) := ne _ (by decide) (by decide)
  have n10 : read ≠ (262160#64) := ne _ (by decide) (by decide)
  simp only [if_neg n10, if_neg n8, if_neg n0]

theorem first_upper_header_tag_word (state : MachineState) :
    (firstUpperHeaderState state).getWord32 0x40000 =
      ((1025#64) + (state.getMem 0x43000 <<< 16)).truncate 32 := by
  simp [firstUpperHeaderState, firstUpperHeaderSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getWord32, MachineState.getMem_setPC,
    MachineState.getMem_setReg, setWord32_eq,
    MachineState.getMem_setMem_ne, alignToDword, byteOffset]

theorem first_upper_header_position_word (state : MachineState) :
    (firstUpperHeaderState state).getWord32 0x40004 =
      (state.getMem 0x43010).truncate 32 := by
  simp [firstUpperHeaderState, firstUpperHeaderSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getWord32, MachineState.getMem_setPC,
    MachineState.getMem_setReg, setWord32_eq,
    MachineState.getMem_setMem_ne, alignToDword, byteOffset]

theorem first_upper_header_tree_word (state : MachineState) :
    (firstUpperHeaderState state).getMem 0x40008 = state.getMem 0x43008 := by
  simp [firstUpperHeaderState, firstUpperHeaderSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setPC,
    MachineState.getMem_setReg, setWord32_eq,
    MachineState.getMem_setMem_ne, alignToDword, byteOffset]

theorem first_upper_header_index_word (state : MachineState) :
    (firstUpperHeaderState state).getWord32 0x40010 =
      (state.getMem 0x43018).truncate 32 := by
  simp [firstUpperHeaderState, firstUpperHeaderSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getWord32, MachineState.getMem_setPC,
    MachineState.getMem_setReg, setWord32_eq,
    MachineState.getMem_setMem_ne, alignToDword, byteOffset]

theorem first_upper_header_tag_byte (state : MachineState) (lay : Layer)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (byte : Fin 4) :
    (firstUpperHeaderState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      (BitVec.ofNat 32 (0x401 + 0x10000 * lay.val)).extractLsb'
        (8 * byte.val) 8 := by
  have split := variableWord_byte (firstUpperHeaderState state) 0x40000
    (by decide) (by decide) (0 : Fin 5) byte
  have value := first_upper_header_tag_word state
  rw [layerCell] at value
  have tag : ((1025#64) + (BitVec.ofNat 64 lay.val <<< 16)).truncate 32 =
      BitVec.ofNat 32 (0x401 + 0x10000 * lay.val) := by
    fin_cases lay <;> decide
  have word : (firstUpperHeaderState state).getWord32 0x40000 =
      BitVec.ofNat 32 (0x401 + 0x10000 * lay.val) := value.trans tag
  have word' : (firstUpperHeaderState state).getWord32
      (BitVec.ofNat 64 (0x40000 + 4 * (0 : Fin 5).val)) =
      BitVec.ofNat 32 (0x401 + 0x10000 * lay.val) := by simpa using word
  rw [word'] at split
  simpa using split

theorem first_upper_header_position_byte (state : MachineState)
    (positionZero : state.getMem 0x43010 = 0) (byte : Fin 4) :
    (firstUpperHeaderState state).getByte
      (BitVec.ofNat 64 (0x40004 + byte.val)) = 0 := by
  have split := variableWord_byte (firstUpperHeaderState state) 0x40004
    (by decide) (by decide) (0 : Fin 5) byte
  have value := first_upper_header_position_word state
  rw [positionZero] at value
  have word : (firstUpperHeaderState state).getWord32
      (BitVec.ofNat 64 (0x40004 + 4 * (0 : Fin 5).val)) = 0 := by
    simpa using value
  rw [word] at split
  simpa using split

theorem first_upper_header_tree_byte (state : MachineState)
    (tree : TreeIndex)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (byte : Fin 8) :
    (firstUpperHeaderState state).getByte
      (BitVec.ofNat 64 (0x40008 + byte.val)) =
      (BitVec.ofNat 64 tree.val).extractLsb' (8 * byte.val) 8 := by
  have word : (firstUpperHeaderState state).getMem 0x40008 =
      BitVec.ofNat 64 tree.val := by
    rw [first_upper_header_tree_word, treeCell]
  have word' : (firstUpperHeaderState state).getMem (262152#64) =
      BitVec.ofNat 64 tree.val := by simpa using word
  fin_cases byte <;>
    simp [MachineState.getByte, alignToDword, byteOffset, word',
      extractByte, BitVec.setWidth_ushiftRight_eq_extractLsb]
  have small : tree.val < 2 ^ 64 := by
    have h := tree.isLt
    simp only [totalHeight] at h
    omega
  simp [BitVec.extractLsb']
  rw [Nat.mod_eq_of_lt (by simpa using small)]

theorem first_upper_header_index_byte (state : MachineState)
    (leaf : LeafIndex)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (byte : Fin 4) :
    (firstUpperHeaderState state).getByte
      (BitVec.ofNat 64 (0x40010 + byte.val)) =
      (BitVec.ofNat 32 leaf.val).extractLsb' (8 * byte.val) 8 := by
  have split := variableWord_byte (firstUpperHeaderState state) 0x40010
    (by decide) (by decide) (0 : Fin 5) byte
  have value := first_upper_header_index_word state
  rw [leafCell] at value
  have word : (firstUpperHeaderState state).getWord32
      (BitVec.ofNat 64 (0x40010 + 4 * (0 : Fin 5).val)) =
      BitVec.ofNat 32 leaf.val := by simpa using value
  rw [word] at split
  simpa using split

theorem first_upper_tag_field_byte (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (byte : Fin 4) :
    ((fieldBytes (tweakFields 4 lay.val tree.val 0 leaf.val)).map
      UInt8.toBitVec)[byte.val]'(by
        simp [fieldBytes, tweakFields, bytesLE]; omega) =
      (BitVec.ofNat 32 (0x401 + 0x10000 * lay.val)).extractLsb'
        (8 * byte.val) 8 := by
  fin_cases lay <;> fin_cases byte <;>
    simp [fieldBytes, tweakFields, protocolDomainSep, bytesLE]

theorem first_upper_header_bytes (state : MachineState)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (positionZero : state.getMem 0x43010 = 0)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (byte : Fin 20) :
    (firstUpperHeaderState state).getByte
      (BitVec.ofNat 64 (0x40000 + byte.val)) =
      ((fieldBytes (tweakFields 4 lay.val tree.val 0 leaf.val)).map
        UInt8.toBitVec)[byte.val]'(by
          simp [fieldBytes, tweakFields, bytesLE]) := by
  fin_cases byte <;>
    first
    | simpa using (first_upper_header_tag_byte state lay layerCell 0).trans
        (first_upper_tag_field_byte lay tree leaf 0).symm
    | simpa using (first_upper_header_tag_byte state lay layerCell 1).trans
        (first_upper_tag_field_byte lay tree leaf 1).symm
    | simpa using (first_upper_header_tag_byte state lay layerCell 2).trans
        (first_upper_tag_field_byte lay tree leaf 2).symm
    | simpa using (first_upper_header_tag_byte state lay layerCell 3).trans
        (first_upper_tag_field_byte lay tree leaf 3).symm
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_position_byte state positionZero 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_position_byte state positionZero 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_position_byte state positionZero 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_position_byte state positionZero 3
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_tree_byte state tree treeCell 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_tree_byte state tree treeCell 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_tree_byte state tree treeCell 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_tree_byte state tree treeCell 3
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_tree_byte state tree treeCell 4
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_tree_byte state tree treeCell 5
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_tree_byte state tree treeCell 6
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_tree_byte state tree treeCell 7
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_index_byte state leaf leafCell 0
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_index_byte state leaf leafCell 1
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_index_byte state leaf leafCell 2
    | simpa [fieldBytes, tweakFields, protocolDomainSep, bytesLE] using
        first_upper_header_index_byte state leaf leafCell 3

theorem first_upper_header_payload_word (state : MachineState)
    (index : Fin 5) :
    (firstUpperHeaderState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  fin_cases index <;>
    simp only [getWord32_eq] <;>
    rw [first_upper_header_mem_frame _ _ (Or.inr (by decide))]

theorem first_upper_header_counter_cell (state : MachineState) :
    (firstUpperHeaderState state).getMem 0x40038 = state.getMem 0x40038 := by
  simp [firstUpperHeaderState, firstUpperHeaderSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
    signExtend12, setWord32_eq, alignToDword,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setPC, MachineState.getMem_setReg,
    MachineState.getMem_setMem_ne]

theorem first_upper_header_counter_word (state : MachineState) :
    (firstUpperHeaderState state).getWord32 0x4003c = state.getWord32 0x4003c := by
  have aligned : alignToDword (0x4003c : Word) = 0x40038 := by decide
  simp only [getWord32_eq, aligned]
  exact congrArg (fun value : Word =>
    extractWord32 value (byteOffset (0x4003c : Word) / 4))
    (first_upper_header_counter_cell state)

theorem first_upper_counter_header_low_byte_frame (state : MachineState)
    (address : Word) (low : address.toNat < 0x40000) :
    (firstUpperHeaderState (firstUpperCounterState state)).getByte address =
      state.getByte address := by
  apply SphincsVerifierWotsSemanticAllChains.lowByteFrame state
    (firstUpperHeaderState (firstUpperCounterState state)) ?_ address low
  intro read small
  rw [first_upper_header_mem_frame _ read (Or.inl small),
    first_upper_counter_mem_frame]
  intro equal
  have value := congrArg BitVec.toNat equal
  have high : (0x40038 : Word).toNat = 0x40038 := by decide
  rw [high] at value
  omega

private def firstUpperParamPointers : List (Word × Instr) := [
  (0x6d94, .LUI .x6 0x23),
  (0x6d98, .ADDI .x6 .x6 (-844)),
  (0x6d9c, .LUI .x7 0x40),
  (0x6da0, .ADDI .x7 .x7 20)]

private theorem firstUpperParamPointers_code :
    ∀ entry ∈ firstUpperParamPointers,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by decide

private def upperParamPointers (target : Fin 5) : List (Word × Instr) :=
  firstUpperParamPointers.map (fun entry =>
    (entry.1 - BitVec.ofNat 64 (0xfcc * target.val), entry.2))

private theorem upperParamPointers_code (target : Fin 5) :
    ∀ entry ∈ upperParamPointers target,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by
  fin_cases target <;> decide

private def firstUpperParamPointerState (state : MachineState) : MachineState :=
  SphincsMaskedKeygenPrefix.runSchedule firstUpperParamPointers state

theorem first_upper_param_pointers_mem (state : MachineState) (read : Word) :
    (firstUpperParamPointerState state).getMem read = state.getMem read := by
  simp [firstUpperParamPointerState, firstUpperParamPointers,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr]

private theorem firstUpperParamPointers_checked (state : MachineState)
    (pc : state.pc = 0x6d94) :
    SphincsMaskedKeygenPrefix.Checked firstUpperParamPointers state := by
  simp [SphincsMaskedKeygenPrefix.Checked, firstUpperParamPointers,
    execInstrBr, ordinaryStep, memoryArgumentsValid,
    signExtend12, pc]

private theorem upperParamPointers_checked (target : Fin 5)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 120) :
    SphincsMaskedKeygenPrefix.Checked (upperParamPointers target) state := by
  fin_cases target <;>
    simp [SphincsMaskedKeygenPrefix.Checked, upperParamPointers,
      firstUpperParamPointers, upperPrefixPc,
      execInstrBr, ordinaryStep, memoryArgumentsValid,
      signExtend12, pc]

theorem upper_param_pointers_block (target : Fin 5)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 120) :
    OrdinarySteps SphincsImages.verify state 4
      (firstUpperParamPointerState state) := by
  have run := SphincsMaskedKeygenPrefix.checked_sound SphincsImages.verify
    (upperParamPointers target) (upperParamPointers_code target) state
    (upperParamPointers_checked target state pc)
  simpa only [upperParamPointers, firstUpperParamPointerState,
    runSchedule_map_pc, List.length_map, firstUpperParamPointers,
    List.length_cons, List.length_nil, Nat.reduceAdd] using run

theorem upper_param_pointers_pc (target : Fin 5)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 120) :
    (firstUpperParamPointerState state).pc = upperPrefixPc target + 136 := by
  fin_cases target <;>
    simp [firstUpperParamPointerState, firstUpperParamPointers,
      SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
      upperPrefixPc, pc]

private theorem firstUpperParamPointers_block (state : MachineState)
    (pc : state.pc = 0x6d94) :
    OrdinarySteps SphincsImages.verify state 4
      (firstUpperParamPointerState state) := by
  simpa only [firstUpperParamPointerState, firstUpperParamPointers,
    List.length_cons, List.length_nil, Nat.reduceAdd] using
    SphincsMaskedKeygenPrefix.checked_sound SphincsImages.verify
      firstUpperParamPointers firstUpperParamPointers_code state
      (firstUpperParamPointers_checked state pc)

private theorem firstUpperParamPointer_regs (state : MachineState) :
    (firstUpperParamPointerState state).getReg .x6 = 0x22cb4 ∧
    (firstUpperParamPointerState state).getReg .x7 = 0x40014 := by
  simp [firstUpperParamPointerState, firstUpperParamPointers,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

private theorem firstUpperParamPointer_pc (state : MachineState)
    (pc : state.pc = 0x6d94) :
    (firstUpperParamPointerState state).pc = 0x6da4 := by
  simp [firstUpperParamPointerState, firstUpperParamPointers,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr, pc]

private theorem firstUpperParamCopy_code :
    SphincsVerifierMessageCopy.Copy20Code SphincsImages.verify 5993 := by
  constructor <;> intro offset <;> fin_cases offset <;> decide

private def upperParamCopyIndex (target : Fin 5) : Nat :=
  5993 - 1011 * target.val

private theorem upperParamCopy_code (target : Fin 5) :
    SphincsVerifierMessageCopy.Copy20Code SphincsImages.verify
      (upperParamCopyIndex target) := by
  constructor <;> intro offset <;>
    fin_cases target <;> fin_cases offset <;> decide

private def firstUpperParamState (state : MachineState) : MachineState :=
  SphincsVerifierCopy.copyRootState (firstUpperParamPointerState state)

theorem first_upper_parameter_block (state : MachineState)
    (pc : state.pc = 0x6d94) :
    OrdinarySteps SphincsImages.verify state 14
      (firstUpperParamState state) := by
  have first := firstUpperParamPointers_block state pc
  have source := (firstUpperParamPointer_regs state).1
  have destination := (firstUpperParamPointer_regs state).2
  have second := SphincsVerifierFtsCopyAccess.copy20_block_general
    SphincsImages.verify 5993 firstUpperParamCopy_code
    (firstUpperParamPointerState state) 0x22cb4 0x40014
    (by simpa using firstUpperParamPointer_pc state pc)
    (by simpa using source) (by simpa using destination)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  simpa [firstUpperParamState] using first.append second

theorem upper_parameter_block (target : Fin 5)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 120) :
    OrdinarySteps SphincsImages.verify state 14
      (firstUpperParamState state) := by
  have first := upper_param_pointers_block target state pc
  have source := (firstUpperParamPointer_regs state).1
  have destination := (firstUpperParamPointer_regs state).2
  have copiedPc : (firstUpperParamPointerState state).pc =
      BitVec.ofNat 64 (0x1000 + 4 * upperParamCopyIndex target) := by
    rw [upper_param_pointers_pc target state pc]
    fin_cases target <;> decide
  have second := SphincsVerifierFtsCopyAccess.copy20_block_general
    SphincsImages.verify (upperParamCopyIndex target)
    (upperParamCopy_code target)
    (firstUpperParamPointerState state) 0x22cb4 0x40014
    copiedPc (by simpa using source) (by simpa using destination)
    (by fin_cases target <;> decide) (by fin_cases target <;> decide) (by fin_cases target <;> decide) (by fin_cases target <;> decide) (by fin_cases target <;> decide)
  simpa [firstUpperParamState] using first.append second

theorem first_upper_parameter_pc (state : MachineState)
    (pc : state.pc = 0x6d94) :
    (firstUpperParamState state).pc = 0x6dcc := by
  change (SphincsVerifierCopy.copyRootState
    (firstUpperParamPointerState state)).pc = 0x6dcc
  have start := firstUpperParamPointer_pc state pc
  have finish := SphincsVerifierMessageCopy.copy20_final_pc
    (firstUpperParamPointerState state) 5993 (by simpa using start)
  simpa using finish

theorem upper_parameter_pc (target : Fin 5)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 120) :
    (firstUpperParamState state).pc = upperPrefixPc target + 176 := by
  have start : (firstUpperParamPointerState state).pc =
      BitVec.ofNat 64 (0x1000 + 4 * upperParamCopyIndex target) := by
    rw [upper_param_pointers_pc target state pc]
    fin_cases target <;> decide
  have finish := SphincsVerifierMessageCopy.copy20_final_pc
    (firstUpperParamPointerState state) (upperParamCopyIndex target) start
  simpa [firstUpperParamState] using
    (show (SphincsVerifierCopy.copyRootState
      (firstUpperParamPointerState state)).pc =
      upperPrefixPc target + 176 by
      rw [finish]
      fin_cases target <;> decide)

theorem first_upper_parameter_copied_words (state : MachineState)
    (index : Fin 5) :
    (firstUpperParamState state).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * index.val)) =
    state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
  have copied := SphincsVerifierWotsEndpointCopy.copy20_data
    (firstUpperParamPointerState state) 0x22cb4 0x40014
    (firstUpperParamPointer_regs state).1
    (firstUpperParamPointer_regs state).2
    (by intro i j; fin_cases i <;> fin_cases j <;> decide)
    (by intro i j different; fin_cases i <;> fin_cases j <;> simp_all <;> decide)
    index
  have source : (firstUpperParamPointerState state).getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * index.val)) := by
    simp [firstUpperParamPointerState, firstUpperParamPointers,
      SphincsMaskedKeygenPrefix.runSchedule, execInstrBr]
  simpa only [firstUpperParamState, SphincsVerifierWotsEndpointCopy.word] using
    copied.trans source

theorem first_upper_parameter_copied_bytes (state : MachineState)
    (i : Nat) (hi : i < 20) :
    (firstUpperParamState state).getByte (BitVec.ofNat 64 (0x40014 + i)) =
    state.getByte (BitVec.ofNat 64 (0x22cb4 + i)) := by
  apply SphincsVerifierFtsGenericBytes.transfer_words_to_bytes
    (firstUpperParamState state) state 0x40014 0x22cb4
    (by decide) (by decide) (by decide) (by decide)
    (first_upper_parameter_copied_words state) i hi

theorem first_upper_parameter_header_word (state : MachineState)
    (index : Fin 5) :
    (firstUpperParamState state).getWord32
      (BitVec.ofNat 64 (0x40000 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40000 + 4 * index.val)) := by
  have frame := SphincsVerifierFtsPriorRoots.copyRoot_word_frame
    (firstUpperParamPointerState state)
    (BitVec.ofNat 64 (0x40000 + 4 * index.val)) (by
      intro offset
      rw [(firstUpperParamPointer_regs state).2]
      fin_cases offset <;> fin_cases index <;> decide)
  rw [show firstUpperParamState state =
      SphincsVerifierCopy.copyRootState (firstUpperParamPointerState state) from rfl,
    frame]
  simp [firstUpperParamPointerState, firstUpperParamPointers,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr]

theorem first_upper_parameter_payload_word (state : MachineState)
    (index : Fin 5) :
    (firstUpperParamState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  have frame := SphincsVerifierFtsPriorRoots.copyRoot_word_frame
    (firstUpperParamPointerState state)
    (BitVec.ofNat 64 (0x40028 + 4 * index.val)) (by
      intro offset
      rw [(firstUpperParamPointer_regs state).2]
      fin_cases offset <;> fin_cases index <;> decide)
  rw [show firstUpperParamState state =
      SphincsVerifierCopy.copyRootState (firstUpperParamPointerState state) from rfl,
    frame]
  simp [firstUpperParamPointerState, firstUpperParamPointers,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr]

theorem first_upper_parameter_counter_word (state : MachineState) :
    (firstUpperParamState state).getWord32 0x4003c = state.getWord32 0x4003c := by
  have frame := SphincsVerifierFtsPriorRoots.copyRoot_word_frame
    (firstUpperParamPointerState state) 0x4003c (by
      intro offset
      rw [(firstUpperParamPointer_regs state).2]
      fin_cases offset <;> decide)
  rw [show firstUpperParamState state =
      SphincsVerifierCopy.copyRootState (firstUpperParamPointerState state) from rfl,
    frame]
  simp [firstUpperParamPointerState, firstUpperParamPointers,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
    MachineState.getReg_setReg_eq]

private def firstUpperServiceSchedule : List (Word × Instr) := [
  (0x6dcc, .LUI .x10 0x40),
  (0x6dd0, .ADDI .x10 .x10 0),
  (0x6dd4, .ADDI .x11 .x0 512),
  (0x6dd8, .LUI .x12 0x42),
  (0x6ddc, .ADDI .x12 .x12 0),
  (0x6de0, .ADDI .x5 .x0 1)]

private theorem firstUpperService_code :
    ∀ entry ∈ firstUpperServiceSchedule,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by decide

private def upperServiceSchedule (target : Fin 5) : List (Word × Instr) :=
  firstUpperServiceSchedule.map (fun entry =>
    (entry.1 - BitVec.ofNat 64 (0xfcc * target.val), entry.2))

private theorem upperService_code (target : Fin 5) :
    ∀ entry ∈ upperServiceSchedule target,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by
  fin_cases target <;> decide

private def firstUpperServiceState (state : MachineState) : MachineState :=
  SphincsMaskedKeygenPrefix.runSchedule firstUpperServiceSchedule state

private theorem firstUpperService_checked (state : MachineState)
    (pc : state.pc = 0x6dcc) :
    SphincsMaskedKeygenPrefix.Checked firstUpperServiceSchedule state := by
  simp [SphincsMaskedKeygenPrefix.Checked, firstUpperServiceSchedule,
    execInstrBr, ordinaryStep, memoryArgumentsValid,
    signExtend12, pc]

private theorem upperService_checked (target : Fin 5)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 176) :
    SphincsMaskedKeygenPrefix.Checked (upperServiceSchedule target) state := by
  fin_cases target <;>
    simp [SphincsMaskedKeygenPrefix.Checked, upperServiceSchedule,
      firstUpperServiceSchedule, upperPrefixPc,
      execInstrBr, ordinaryStep, memoryArgumentsValid,
      signExtend12, pc]

theorem upper_service_setup_block (target : Fin 5)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 176) :
    OrdinarySteps SphincsImages.verify state 6
      (firstUpperServiceState state) := by
  have run := SphincsMaskedKeygenPrefix.checked_sound SphincsImages.verify
    (upperServiceSchedule target) (upperService_code target) state
    (upperService_checked target state pc)
  simpa only [upperServiceSchedule, firstUpperServiceState,
    runSchedule_map_pc, List.length_map, firstUpperServiceSchedule,
    List.length_cons, List.length_nil, Nat.reduceAdd] using run

theorem upper_service_ready (target : Fin 5)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 176) :
    let ready := firstUpperServiceState state
    ready.pc = upperPrefixPc target + 200 ∧
    ready.getReg .x10 = 0x40000 ∧ ready.getReg .x11 = 512 ∧
    ready.getReg .x12 = 0x42000 ∧ ready.getReg .x5 = 1 := by
  fin_cases target <;>
    simp [firstUpperServiceState, firstUpperServiceSchedule,
      SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, upperPrefixPc, pc]

theorem first_upper_service_setup_block (state : MachineState)
    (pc : state.pc = 0x6dcc) :
    OrdinarySteps SphincsImages.verify state 6
      (firstUpperServiceState state) := by
  simpa only [firstUpperServiceState, firstUpperServiceSchedule,
    List.length_cons, List.length_nil, Nat.reduceAdd] using
    SphincsMaskedKeygenPrefix.checked_sound SphincsImages.verify
      firstUpperServiceSchedule firstUpperService_code state
      (firstUpperService_checked state pc)

theorem first_upper_service_ready (state : MachineState)
    (pc : state.pc = 0x6dcc) :
    let ready := firstUpperServiceState state
    ready.pc = 0x6de4 ∧ ready.getReg .x10 = 0x40000 ∧
    ready.getReg .x11 = 512 ∧ ready.getReg .x12 = 0x42000 ∧
    ready.getReg .x5 = 1 := by
  simp [firstUpperServiceState, firstUpperServiceSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc]

theorem first_upper_service_mem (state : MachineState) (read : Word) :
    (firstUpperServiceState state).getMem read = state.getMem read := by
  simp [firstUpperServiceState, firstUpperServiceSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr]

theorem first_upper_service_header_word (state : MachineState)
    (index : Fin 5) :
    (firstUpperServiceState state).getWord32
      (BitVec.ofNat 64 (0x40000 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40000 + 4 * index.val)) := by
  simp only [getWord32_eq]
  rw [first_upper_service_mem]

theorem first_upper_service_payload_word (state : MachineState)
    (index : Fin 5) :
    (firstUpperServiceState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  simp only [getWord32_eq]
  rw [first_upper_service_mem]

theorem first_upper_service_counter_word (state : MachineState) :
    (firstUpperServiceState state).getWord32 0x4003c = state.getWord32 0x4003c := by
  simp [firstUpperServiceState, firstUpperServiceSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr]

private def firstUpperPrehashState (state : MachineState) : MachineState :=
  firstUpperServiceState (firstUpperParamState
    (firstUpperHeaderState (firstUpperCounterState state)))

theorem first_upper_prehash_parameter_byte (state : MachineState)
    (i : Nat) (hi : i < 20) :
    (firstUpperPrehashState state).getByte (BitVec.ofNat 64 (0x40014 + i)) =
      (firstUpperHeaderState (firstUpperCounterState state)).getByte
        (BitVec.ofNat 64 (0x22cb4 + i)) := by
  have service : (firstUpperPrehashState state).getByte
      (BitVec.ofNat 64 (0x40014 + i)) =
      (firstUpperParamState
        (firstUpperHeaderState (firstUpperCounterState state))).getByte
          (BitVec.ofNat 64 (0x40014 + i)) := by
    simp [firstUpperPrehashState, MachineState.getByte,
      first_upper_service_mem]
  exact service.trans (first_upper_parameter_copied_bytes _ i hi)

theorem first_upper_prehash_parameter (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (witness : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (i : Nat) (hi : i < 20) :
    (firstUpperPrehashState state).getByte (BitVec.ofNat 64 (0x40014 + i)) =
      pk.parameter.extractLsb' (8*i) 8 := by
  have low : (BitVec.ofNat 64 (0x22cb4 + i)).toNat < 0x40000 := by
    simp only [BitVec.toNat_ofNat]
    omega
  exact (first_upper_prehash_parameter_byte state i hi).trans
    ((first_upper_counter_header_low_byte_frame state _ low).trans
      (witness.parameter i hi))

theorem first_upper_prehash_header_word (state : MachineState)
    (index : Fin 5) :
    (firstUpperPrehashState state).getWord32
      (BitVec.ofNat 64 (0x40000 + 4 * index.val)) =
      (firstUpperHeaderState (firstUpperCounterState state)).getWord32
        (BitVec.ofNat 64 (0x40000 + 4 * index.val)) := by
  rw [show firstUpperPrehashState state = firstUpperServiceState
    (firstUpperParamState (firstUpperHeaderState (firstUpperCounterState state)))
      from rfl,
    first_upper_service_header_word,
    first_upper_parameter_header_word]

theorem first_upper_prehash_payload_word (state : MachineState)
    (index : Fin 5) :
    (firstUpperPrehashState state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  rw [show firstUpperPrehashState state = firstUpperServiceState
    (firstUpperParamState (firstUpperHeaderState (firstUpperCounterState state)))
      from rfl,
    first_upper_service_payload_word,
    first_upper_parameter_payload_word,
    first_upper_header_payload_word,
    first_upper_counter_payload_word]

theorem first_upper_prehash_header_byte (state : MachineState)
    (i : Nat) (hi : i < 20) :
    (firstUpperPrehashState state).getByte (BitVec.ofNat 64 (0x40000 + i)) =
      (firstUpperHeaderState (firstUpperCounterState state)).getByte
        (BitVec.ofNat 64 (0x40000 + i)) := by
  apply SphincsVerifierFtsGenericBytes.transfer_words_to_bytes
    (firstUpperPrehashState state)
    (firstUpperHeaderState (firstUpperCounterState state))
    0x40000 0x40000 (by decide) (by decide) (by decide) (by decide)
    (first_upper_prehash_header_word state) i hi

theorem first_upper_prehash_header (state : MachineState)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (positionZero : state.getMem 0x43010 = 0)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (i : Nat) (hi : i < 20) :
    (firstUpperPrehashState state).getByte (BitVec.ofNat 64 (0x40000 + i)) =
      ((fieldBytes (tweakFields 4 lay.val tree.val 0 leaf.val)).map
        UInt8.toBitVec)[i]'(by simp [fieldBytes, tweakFields, bytesLE]; omega) := by
  have controls :
      (firstUpperCounterState state).getMem 0x43000 = BitVec.ofNat 64 lay.val ∧
      (firstUpperCounterState state).getMem 0x43010 = 0 ∧
      (firstUpperCounterState state).getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
      (firstUpperCounterState state).getMem 0x43018 = BitVec.ofNat 64 leaf.val := by
    rw [first_upper_counter_mem_frame _ _ (by decide), layerCell,
      first_upper_counter_mem_frame _ _ (by decide), positionZero,
      first_upper_counter_mem_frame _ _ (by decide), treeCell,
      first_upper_counter_mem_frame _ _ (by decide), leafCell]
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact (first_upper_prehash_header_byte state i hi).trans
    (first_upper_header_bytes (firstUpperCounterState state)
      lay tree leaf controls.1 controls.2.1 controls.2.2.1 controls.2.2.2
      ⟨i, hi⟩)

theorem first_upper_prehash_payload_byte (state : MachineState)
    (i : Nat) (hi : i < 20) :
    (firstUpperPrehashState state).getByte (BitVec.ofNat 64 (0x40028 + i)) =
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) := by
  apply SphincsVerifierFtsGenericBytes.transfer_words_to_bytes
    (firstUpperPrehashState state) state 0x40028 0x40028
    (by decide) (by decide) (by decide) (by decide)
    (first_upper_prehash_payload_word state) i hi

theorem first_upper_prehash_counter_word (state : MachineState) :
    (firstUpperPrehashState state).getWord32 0x4003c =
      state.getWord32 0x23dbc := by
  rw [show firstUpperPrehashState state = firstUpperServiceState
    (firstUpperParamState (firstUpperHeaderState (firstUpperCounterState state)))
      from rfl,
    first_upper_service_counter_word,
    first_upper_parameter_counter_word,
    first_upper_header_counter_word,
    first_upper_counter_stored]

theorem first_upper_prehash_counter_bytes (state : MachineState)
    (counter : Counter)
    (counterWord : state.getWord32 0x23dbc =
      BitVec.ofNat 32 counter.toNat)
    (i : Nat) (hi : i < 4) :
    (firstUpperPrehashState state).getByte (BitVec.ofNat 64 (0x4003c + i)) =
      (BitVec.ofNat 32 counter.toNat).extractLsb' (8*i) 8 := by
  let byte : Fin 4 := ⟨i, hi⟩
  have split := variableWord_byte (firstUpperPrehashState state) 0x4003c
    (by decide) (by decide) (0 : Fin 5) byte
  have word : (firstUpperPrehashState state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * (0 : Fin 5).val)) =
      BitVec.ofNat 32 counter.toNat := by
    calc
      _ = state.getWord32 0x23dbc := by
        simpa using first_upper_prehash_counter_word state
      _ = _ := counterWord
  rw [word] at split
  simpa [byte] using split

theorem first_upper_prehash_block (state : MachineState)
    (pc : state.pc = 0x6d1c)
    (small : BitVec.setWidth 64 (state.getWord32 0x23dbc) >>> 20 = 0) :
    OrdinarySteps SphincsImages.verify state 49
      (firstUpperPrehashState state) ∧
    (firstUpperPrehashState state).pc = 0x6de4 ∧
    (firstUpperPrehashState state).getReg .x10 = 0x40000 ∧
    (firstUpperPrehashState state).getReg .x11 = 512 ∧
    (firstUpperPrehashState state).getReg .x12 = 0x42000 ∧
    (firstUpperPrehashState state).getReg .x5 = 1 := by
  let counter := firstUpperCounterState state
  let header := firstUpperHeaderState counter
  let parameter := firstUpperParamState header
  have c := first_upper_counter_block state pc small
  have cp := first_upper_counter_pc state pc small
  have h := first_upper_header_block counter cp
  have hp := first_upper_header_pc counter cp
  have p := first_upper_parameter_block header hp
  have pp := first_upper_parameter_pc header hp
  have s := first_upper_service_setup_block parameter pp
  have ready := first_upper_service_ready parameter pp
  refine ⟨?_, ready⟩
  simpa [firstUpperPrehashState, counter, header, parameter,
    Nat.add_assoc] using ((c.append h).append p).append s

private def upperPrehashState (target : Fin 5)
    (state : MachineState) : MachineState :=
  firstUpperServiceState (firstUpperParamState
    (firstUpperHeaderState (upperCounterState target state)))

theorem upper_prehash_block (target : Fin 5) (state : MachineState)
    (pc : state.pc = upperPrefixPc target)
    (small : BitVec.setWidth 64
      (state.getWord32 (upperCounterSource target)) >>> 20 = 0) :
    OrdinarySteps SphincsImages.verify state 49
      (upperPrehashState target state) ∧
    (upperPrehashState target state).pc = upperPrefixPc target + 200 ∧
    (upperPrehashState target state).getReg .x10 = 0x40000 ∧
    (upperPrehashState target state).getReg .x11 = 512 ∧
    (upperPrehashState target state).getReg .x12 = 0x42000 ∧
    (upperPrehashState target state).getReg .x5 = 1 := by
  let counter := upperCounterState target state
  let header := firstUpperHeaderState counter
  let parameter := firstUpperParamState header
  have c := upper_counter_block target state pc small
  have cp := upper_counter_pc target state pc small
  have h := upper_header_block target counter cp
  have hp := upper_header_pc target counter cp
  have p := upper_parameter_block target header hp
  have pp := upper_parameter_pc target header hp
  have s := upper_service_setup_block target parameter pp
  have ready := upper_service_ready target parameter pp
  refine ⟨?_, ready⟩
  simpa [upperPrehashState, counter, header, parameter,
    Nat.add_assoc] using ((c.append h).append p).append s

theorem first_upper_hash_site (state : MachineState)
    (pc : state.pc = 0x6de4) :
    fetch SphincsImages.verify state = some (.base .ECALL) := by
  rw [SphincsVerifierMessageCopy.fetch_index SphincsImages.verify state
    6009 (by decide) (by simpa using pc)]
  decide

theorem upper_hash_site (target : Fin 5) (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 200) :
    fetch SphincsImages.verify state = some (.base .ECALL) := by
  rw [SphincsVerifierMessageCopy.fetch_index SphincsImages.verify state
    (6009 - 1011 * target.val)
    (by fin_cases target <;> decide)
    (by rw [pc]; fin_cases target <;> decide)]
  fin_cases target <;> decide

theorem upper_hash_step (target : Fin 5) (hash : Hash)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 200)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 512)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1) :
    Trace hash SphincsImages.verify state 1 8 1 1
      (writeHash state (hash (hashInput state))) := by
  have valid : hashArgumentsValid state = true := by
    simp [hashArgumentsValid, source, bits, destination,
      accessValid, rangeValid, MEMORY_BYTES]
  have cost : compressions (hashInput state).1 = 1 := by
    simp [hashInput, source, bits, compressions]
  have run := Trace.hash state
    (writeHash state (hash (hashInput state))) 0 0 0 0
    (upper_hash_site target state pc) service valid
    (Trace.refl _)
  simpa [cost] using run

theorem upper_hash_prefix (target : Fin 5) (hash : Hash)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target)
    (small : BitVec.setWidth 64
      (state.getWord32 (upperCounterSource target)) >>> 20 = 0) :
    Trace hash SphincsImages.verify state 50 57 1 1
      (writeHash (upperPrehashState target state)
        (hash (hashInput (upperPrehashState target state)))) := by
  obtain ⟨ordinary, readyPc, source, bits, destination, service⟩ :=
    upper_prehash_block target state pc small
  have hashed := upper_hash_step target hash (upperPrehashState target state)
    readyPc source bits destination service
  simpa using (ordinary.trace (hash := hash)).trans hashed

theorem first_upper_hash_step (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x6de4)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 512)
    (destination : state.getReg .x12 = 0x42000)
    (service : state.getReg .x5 = 1) :
    Trace hash SphincsImages.verify state 1 8 1 1
      (writeHash state (hash (hashInput state))) := by
  have valid : hashArgumentsValid state = true := by
    simp [hashArgumentsValid, source, bits, destination,
      accessValid, rangeValid, MEMORY_BYTES]
  have cost : compressions (hashInput state).1 = 1 := by
    simp [hashInput, source, bits, compressions]
  have run := Trace.hash state
    (writeHash state (hash (hashInput state))) 0 0 0 0
    (first_upper_hash_site state pc) service valid
    (Trace.refl _)
  simpa [cost] using run

theorem first_upper_hash_prefix (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x6d1c)
    (small : BitVec.setWidth 64 (state.getWord32 0x23dbc) >>> 20 = 0) :
    Trace hash SphincsImages.verify state 50 57 1 1
      (writeHash (firstUpperPrehashState state)
        (hash (hashInput (firstUpperPrehashState state)))) := by
  obtain ⟨ordinary, readyPc, source, bits, destination, service⟩ :=
    first_upper_prehash_block state pc small
  have hashed := first_upper_hash_step hash (firstUpperPrehashState state)
    readyPc source bits destination service
  simpa using (ordinary.trace (hash := hash)).trans hashed

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_hash_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_hash_prefix

private def firstUpperPaddingSchedule : List (Word × Instr) := [
  (0x6de8, .LUI .x6 0x42),
  (0x6dec, .ADDI .x6 .x6 0),
  (0x6df0, .LBU .x10 .x6 9),
  (0x6df4, .ANDI .x10 .x10 192),
  (0x6df8, .BEQ .x10 .x0 8),
  (0x6e00, .LUI .x6 0x42),
  (0x6e04, .ADDI .x6 .x6 0),
  (0x6e08, .LBU .x10 .x6 19),
  (0x6e0c, .ANDI .x10 .x10 192),
  (0x6e10, .BEQ .x10 .x0 8),
  (0x6e18, .ADDI .x15 .x0 0)]

private theorem firstUpperPadding_code :
    ∀ entry ∈ firstUpperPaddingSchedule,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by decide

private def upperPaddingSchedule (target : Fin 5) : List (Word × Instr) :=
  firstUpperPaddingSchedule.map (fun entry =>
    (entry.1 - BitVec.ofNat 64 (0xfcc * target.val), entry.2))

private theorem upperPadding_code (target : Fin 5) :
    ∀ entry ∈ upperPaddingSchedule target,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by
  fin_cases target <;> decide

private def firstUpperPaddingState (state : MachineState) : MachineState :=
  SphincsMaskedKeygenPrefix.runSchedule firstUpperPaddingSchedule state

private theorem firstUpperPadding_checked (state : MachineState)
    (pc : state.pc = 0x6de8)
    (first : BitVec.setWidth 64 (state.getByte 0x42009) &&& 192 = (0 : Word))
    (second : BitVec.setWidth 64 (state.getByte 0x42013) &&& 192 = (0 : Word)) :
    SphincsMaskedKeygenPrefix.Checked firstUpperPaddingSchedule state := by
  have first' : BitVec.setWidth 64 (state.getByte (270345#64)) &&& (192#64) = (0#64) := first
  have second' : BitVec.setWidth 64 (state.getByte (270355#64)) &&& (192#64) = (0#64) := second
  simp only [MachineState.getByte] at first' second'
  simp [SphincsMaskedKeygenPrefix.Checked, firstUpperPaddingSchedule,
    execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
    rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq,
    MachineState.getByte, MachineState.getMem_setPC,
    MachineState.getMem_setReg, pc, first', second']

theorem first_upper_padding_block (state : MachineState)
    (pc : state.pc = 0x6de8)
    (first : BitVec.setWidth 64 (state.getByte 0x42009) &&& 192 = (0 : Word))
    (second : BitVec.setWidth 64 (state.getByte 0x42013) &&& 192 = (0 : Word)) :
    OrdinarySteps SphincsImages.verify state 11
      (firstUpperPaddingState state) := by
  simpa only [firstUpperPaddingState, firstUpperPaddingSchedule,
    List.length_cons, List.length_nil, Nat.reduceAdd] using
    SphincsMaskedKeygenPrefix.checked_sound SphincsImages.verify
      firstUpperPaddingSchedule firstUpperPadding_code state
      (firstUpperPadding_checked state pc first second)

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_padding_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_padding_block

theorem first_upper_padding_ready (state : MachineState)
    (pc : state.pc = 0x6de8)
    (first : BitVec.setWidth 64 (state.getByte 0x42009) &&& 192 = (0 : Word))
    (second : BitVec.setWidth 64 (state.getByte 0x42013) &&& 192 = (0 : Word)) :
    (firstUpperPaddingState state).pc = 0x6e1c ∧
    (firstUpperPaddingState state).getReg .x15 = 0 := by
  have first' : BitVec.setWidth 64 (state.getByte (270345#64)) &&& (192#64) = (0#64) := first
  have second' : BitVec.setWidth 64 (state.getByte (270355#64)) &&& (192#64) = (0#64) := second
  simp only [MachineState.getByte] at first' second'
  simp [firstUpperPaddingState, firstUpperPaddingSchedule,
    SphincsMaskedKeygenPrefix.runSchedule, execInstrBr, signExtend12,
    signExtend13, MachineState.getReg_setReg_eq,
    MachineState.getByte,
    MachineState.getMem_setPC, MachineState.getMem_setReg,
    pc, first', second']

private theorem upperPadding_checked (target : Fin 5)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 204)
    (first : BitVec.setWidth 64 (state.getByte 0x42009) &&& 192 = (0 : Word))
    (second : BitVec.setWidth 64 (state.getByte 0x42013) &&& 192 = (0 : Word)) :
    SphincsMaskedKeygenPrefix.Checked (upperPaddingSchedule target) state := by
  have first' : BitVec.setWidth 64 (state.getByte (270345#64)) &&& (192#64) =
      (0#64) := first
  have second' : BitVec.setWidth 64 (state.getByte (270355#64)) &&& (192#64) =
      (0#64) := second
  simp only [MachineState.getByte] at first' second'
  fin_cases target <;>
    simp [SphincsMaskedKeygenPrefix.Checked, upperPaddingSchedule,
      firstUpperPaddingSchedule, upperPrefixPc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
      MachineState.getReg_setReg_eq,
      MachineState.getByte, MachineState.getMem_setPC,
      MachineState.getMem_setReg, pc, first', second']

theorem upper_padding_block (target : Fin 5) (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 204)
    (first : BitVec.setWidth 64 (state.getByte 0x42009) &&& 192 = (0 : Word))
    (second : BitVec.setWidth 64 (state.getByte 0x42013) &&& 192 = (0 : Word)) :
    OrdinarySteps SphincsImages.verify state 11
      (firstUpperPaddingState state) := by
  have run := SphincsMaskedKeygenPrefix.checked_sound SphincsImages.verify
    (upperPaddingSchedule target) (upperPadding_code target) state
    (upperPadding_checked target state pc first second)
  simpa only [upperPaddingSchedule, firstUpperPaddingState,
    runSchedule_map_pc, List.length_map, firstUpperPaddingSchedule,
    List.length_cons, List.length_nil, Nat.reduceAdd] using run

theorem upper_padding_ready (target : Fin 5) (state : MachineState)
    (pc : state.pc = upperPrefixPc target + 204)
    (first : BitVec.setWidth 64 (state.getByte 0x42009) &&& 192 = (0 : Word))
    (second : BitVec.setWidth 64 (state.getByte 0x42013) &&& 192 = (0 : Word)) :
    (firstUpperPaddingState state).pc = upperPrefixPc target + 256 ∧
    (firstUpperPaddingState state).getReg .x15 = 0 := by
  have first' : BitVec.setWidth 64 (state.getByte (270345#64)) &&& (192#64) =
      (0#64) := first
  have second' : BitVec.setWidth 64 (state.getByte (270355#64)) &&& (192#64) =
      (0#64) := second
  simp only [MachineState.getByte] at first' second'
  fin_cases target <;>
    simp [firstUpperPaddingState, firstUpperPaddingSchedule,
      SphincsMaskedKeygenPrefix.runSchedule, execInstrBr, signExtend12,
      signExtend13, MachineState.getReg_setReg_eq,
      MachineState.getByte,
      MachineState.getMem_setPC, MachineState.getMem_setReg,
      upperPrefixPc, pc, first', second']

private theorem firstUpperTopBitsZero : ∀ b : BitVec 8,
    b.getLsbD 6 = false → b.getLsbD 7 = false →
      (BitVec.setWidth 64 b &&& (192#64)) = 0#64 := by
  decide

theorem first_upper_decoded_padding (answer : BitVec 256)
    (encoding : Encoding)
    (decoded : TargetSum.decodeDigest (truncateHash answer) = some encoding) :
    (BitVec.setWidth 64 (answer.extractLsb' 72 8) &&& (192#64)) = 0#64 ∧
    (BitVec.setWidth 64 (answer.extractLsb' 152 8) &&& (192#64)) = 0#64 := by
  have bits : (truncateHash answer).getLsbD 78 = false ∧
      (truncateHash answer).getLsbD 79 = false ∧
      (truncateHash answer).getLsbD 158 = false ∧
      (truncateHash answer).getLsbD 159 = false := by
    unfold TargetSum.decodeDigest at decoded
    split_ifs at decoded with h
    · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  rcases bits with ⟨h78, h79, h158, h159⟩
  have project (i : Nat) (hi : i < 160) :
      (truncateHash answer).getLsbD i = answer.getLsbD i := by
    change (BitVec.extractLsb' 0 160 answer)[i] = answer.getLsbD i
    simpa only [Nat.zero_add] using
      (BitVec.getElem_extractLsb' (start := 0) (len := 160) (x := answer) hi)
  rw [project 78 (by decide)] at h78
  rw [project 79 (by decide)] at h79
  rw [project 158 (by decide)] at h158
  rw [project 159 (by decide)] at h159
  have lo6 : (answer.extractLsb' 72 8).getLsbD 6 = false := by
    simpa [BitVec.getLsbD_extractLsb'] using h78
  have lo7 : (answer.extractLsb' 72 8).getLsbD 7 = false := by
    simpa [BitVec.getLsbD_extractLsb'] using h79
  have hi6 : (answer.extractLsb' 152 8).getLsbD 6 = false := by
    simpa [BitVec.getLsbD_extractLsb'] using h158
  have hi7 : (answer.extractLsb' 152 8).getLsbD 7 = false := by
    simpa [BitVec.getLsbD_extractLsb'] using h159
  exact ⟨firstUpperTopBitsZero _ lo6 lo7,
    firstUpperTopBitsZero _ hi6 hi7⟩

theorem first_upper_hash_padding (state : MachineState)
    (destination : state.getReg .x12 = 0x42000)
    (answer : BitVec 256) (encoding : Encoding)
    (decoded : TargetSum.decodeDigest (truncateHash answer) = some encoding) :
    let answered := writeHash state answer
    BitVec.setWidth 64 (answered.getByte 0x42009) &&& 192 = (0 : Word) ∧
    BitVec.setWidth 64 (answered.getByte 0x42013) &&& 192 = (0 : Word) := by
  have firstByte := SphincsVerifierFtsResult.hashAnswer_byte state answer
    destination 9 (by decide)
  have secondByte := SphincsVerifierFtsResult.hashAnswer_byte state answer
    destination 19 (by decide)
  have padding := first_upper_decoded_padding answer encoding decoded
  change
    BitVec.setWidth 64 ((writeHash state answer).getByte
      (BitVec.ofNat 64 (0x42000 + 9))) &&& 192 = (0 : Word) ∧
    BitVec.setWidth 64 ((writeHash state answer).getByte
      (BitVec.ofNat 64 (0x42000 + 19))) &&& 192 = (0 : Word)
  rw [firstByte, secondByte]
  change
    (BitVec.setWidth 64 (answer.extractLsb' 72 8) &&& (192#64)) = 0#64 ∧
    (BitVec.setWidth 64 (answer.extractLsb' 152 8) &&& (192#64)) = 0#64
  exact padding

theorem first_upper_decoder_prefix (hash : Hash) (state : MachineState)
    (pc : state.pc = 0x6d1c)
    (small : BitVec.setWidth 64 (state.getWord32 0x23dbc) >>> 20 = 0)
    (encoding : Encoding)
    (decoded : TargetSum.decodeDigest
      (truncateHash (hash (hashInput (firstUpperPrehashState state)))) =
        some encoding) :
    let hashed := writeHash (firstUpperPrehashState state)
      (hash (hashInput (firstUpperPrehashState state)))
    Trace hash SphincsImages.verify state 61 68 1 1
      (firstUpperPaddingState hashed) ∧
    (firstUpperPaddingState hashed).pc = 0x6e1c ∧
    (firstUpperPaddingState hashed).getReg .x15 = 0 := by
  obtain ⟨_preRun, readyPc, _source, _bits, destination, _service⟩ :=
    first_upper_prehash_block state pc small
  let ready := firstUpperPrehashState state
  let answer := hash (hashInput ready)
  let hashed := writeHash ready answer
  have hashedPc : hashed.pc = 0x6de8 := by
    change ready.pc + 4 = 0x6de8
    rw [show ready.pc = 0x6de4 from readyPc]
    decide
  have padding := first_upper_hash_padding ready destination answer encoding decoded
  have tail := first_upper_padding_block hashed hashedPc padding.1 padding.2
  have final := first_upper_padding_ready hashed hashedPc padding.1 padding.2
  refine ⟨?_, final⟩
  have preRun := first_upper_hash_prefix hash state pc small
  simpa [ready, answer, hashed, Nat.add_assoc] using
    preRun.trans (tail.trace (hash := hash))

theorem upper_decoder_prefix (target : Fin 5) (hash : Hash)
    (state : MachineState)
    (pc : state.pc = upperPrefixPc target)
    (small : BitVec.setWidth 64
      (state.getWord32 (upperCounterSource target)) >>> 20 = 0)
    (encoding : Encoding)
    (decoded : TargetSum.decodeDigest
      (truncateHash (hash (hashInput (upperPrehashState target state)))) =
        some encoding) :
    let hashed := writeHash (upperPrehashState target state)
      (hash (hashInput (upperPrehashState target state)))
    Trace hash SphincsImages.verify state 61 68 1 1
      (firstUpperPaddingState hashed) ∧
    (firstUpperPaddingState hashed).pc = upperPrefixPc target + 256 ∧
    (firstUpperPaddingState hashed).getReg .x15 = 0 := by
  obtain ⟨_preRun, readyPc, _source, _bits, destination, _service⟩ :=
    upper_prehash_block target state pc small
  let ready := upperPrehashState target state
  let answer := hash (hashInput ready)
  let hashed := writeHash ready answer
  have hashedPc : hashed.pc = upperPrefixPc target + 204 := by
    change ready.pc + 4 = upperPrefixPc target + 204
    rw [show ready.pc = upperPrefixPc target + 200 from readyPc]
    fin_cases target <;> decide
  have padding := first_upper_hash_padding ready destination answer encoding decoded
  have tail := upper_padding_block target hashed hashedPc padding.1 padding.2
  have final := upper_padding_ready target hashed hashedPc padding.1 padding.2
  refine ⟨?_, final⟩
  have preRun := upper_hash_prefix target hash state pc small
  simpa [ready, answer, hashed, Nat.add_assoc] using
    preRun.trans (tail.trace (hash := hash))

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_decoder_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_decoder_prefix

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_decoder_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_decoder_prefix


def firstUpperEncodingInput (pk : SphincsSecurity.PublicKey)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) : HashInput :=
  tweakableHashInput pk.parameter (.encoding lay tree leaf)
    (bytesLE 20 message ++ bytesLE 4 (BitVec.ofNat 32 counter.toNat))

theorem firstUpperEncodingInput_eq (pk : SphincsSecurity.PublicKey)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) :
    firstUpperEncodingInput pk lay tree leaf message counter =
      fieldBytes (tweakFields 4 lay.val tree.val 0 leaf.val) ++
        bytesLE 20 pk.parameter ++ bytesLE 20 message ++
        bytesLE 4 (BitVec.ofNat 32 counter.toNat) := by rfl

theorem firstUpperEncodingInput_length (pk : SphincsSecurity.PublicKey)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) :
    (firstUpperEncodingInput pk lay tree leaf message counter).length = 64 := by
  simp [firstUpperEncodingInput, tweakableHashInput, tweakBytes, hashDomainFields,
    fieldBytes, bytesLE]

theorem firstUpperEncodingInput_header (pk : SphincsSecurity.PublicKey)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter)
    (i : Nat) (hi : i < 20) :
    ((firstUpperEncodingInput pk lay tree leaf message counter).map UInt8.toBitVec)[i]'(by
      rw [List.length_map, firstUpperEncodingInput_length]; omega) =
      ((fieldBytes (tweakFields 4 lay.val tree.val 0 leaf.val)).map
        UInt8.toBitVec)[i]'(by simp [fieldBytes, bytesLE]; omega) := by
  simp only [firstUpperEncodingInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega)]

theorem firstUpperEncodingInput_parameter (pk : SphincsSecurity.PublicKey)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter)
    (i : Nat) (hi : i < 20) :
    ((firstUpperEncodingInput pk lay tree leaf message counter).map UInt8.toBitVec)[20+i]'(by
      rw [List.length_map, firstUpperEncodingInput_length]; omega) =
      pk.parameter.extractLsb' (8*i) 8 := by
  simp only [firstUpperEncodingInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [fieldBytes, bytesLE]
  rfl

theorem firstUpperEncodingInput_message (pk : SphincsSecurity.PublicKey)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter)
    (i : Nat) (hi : i < 20) :
    ((firstUpperEncodingInput pk lay tree leaf message counter).map UInt8.toBitVec)[40+i]'(by
      rw [List.length_map, firstUpperEncodingInput_length]; omega) =
      message.extractLsb' (8*i) 8 := by
  simp only [firstUpperEncodingInput_eq, List.map_append]
  rw [List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [fieldBytes, bytesLE]
  rfl

theorem firstUpperEncodingInput_counter (pk : SphincsSecurity.PublicKey)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter)
    (i : Nat) (hi : i < 4) :
    ((firstUpperEncodingInput pk lay tree leaf message counter).map UInt8.toBitVec)[60+i]'(by
      rw [List.length_map, firstUpperEncodingInput_length]; omega) =
      (BitVec.ofNat 32 counter.toNat).extractLsb' (8*i) 8 := by
  simp only [firstUpperEncodingInput_eq, List.map_append]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [fieldBytes, bytesLE]

theorem first_upper_encoding_query_of_parts (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 512)
    (header : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x40000 + i)) =
        ((fieldBytes (tweakFields 4 lay.val tree.val 0 leaf.val)).map
          UInt8.toBitVec)[i]'(by simp [fieldBytes, bytesLE]; omega))
    (parameter : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x40014 + i)) =
        pk.parameter.extractLsb' (8*i) 8)
    (payload : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        message.extractLsb' (8*i) 8)
    (counterBytes : ∀ i, (hi : i < 4) →
      state.getByte (BitVec.ofNat 64 (0x4003c + i)) =
        (BitVec.ofNat 32 counter.toNat).extractLsb' (8*i) 8) :
    hashInput state = toQuery (firstUpperEncodingInput pk lay tree leaf message counter) := by
  apply SigGolfCandidate.Serialization.hashInput_of_list state 0x40000
    ((firstUpperEncodingInput pk lay tree leaf message counter).map UInt8.toBitVec)
  · exact source
  · rw [bits, List.length_map, firstUpperEncodingInput_length]
    rfl
  · intro i hi
    have bound : i < 64 := by simpa [firstUpperEncodingInput_length] using hi
    by_cases h0 : i < 20
    · exact (header i h0).trans (firstUpperEncodingInput_header pk lay tree leaf message counter i h0).symm
    by_cases h1 : i < 40
    · let j := i - 20
      have hj : j < 20 := by dsimp [j]; omega
      have ieq : i = 20 + j := by dsimp [j]; omega
      have addr : 0x40000 + i = 0x40014 + j := by omega
      calc
        state.getByte (BitVec.ofNat 64 (0x40000 + i)) =
          state.getByte (BitVec.ofNat 64 (0x40014 + j)) := by rw [addr]
        _ = pk.parameter.extractLsb' (8*j) 8 := parameter j hj
        _ = ((firstUpperEncodingInput pk lay tree leaf message counter).map UInt8.toBitVec)[i]'hi := by
          simpa [ieq] using (firstUpperEncodingInput_parameter pk lay tree leaf message counter j hj).symm
    by_cases h2 : i < 60
    · let j := i - 40
      have hj : j < 20 := by dsimp [j]; omega
      have ieq : i = 40 + j := by dsimp [j]; omega
      have addr : 0x40000 + i = 0x40028 + j := by omega
      calc
        state.getByte (BitVec.ofNat 64 (0x40000 + i)) =
          state.getByte (BitVec.ofNat 64 (0x40028 + j)) := by rw [addr]
        _ = message.extractLsb' (8*j) 8 := payload j hj
        _ = ((firstUpperEncodingInput pk lay tree leaf message counter).map UInt8.toBitVec)[i]'hi := by
          simpa [ieq] using (firstUpperEncodingInput_message pk lay tree leaf message counter j hj).symm
    · let j := i - 60
      have hj : j < 4 := by dsimp [j]; omega
      have ieq : i = 60 + j := by dsimp [j]; omega
      have addr : 0x40000 + i = 0x4003c + j := by omega
      calc
        state.getByte (BitVec.ofNat 64 (0x40000 + i)) =
          state.getByte (BitVec.ofNat 64 (0x4003c + j)) := by rw [addr]
        _ = (BitVec.ofNat 32 counter.toNat).extractLsb' (8*j) 8 := counterBytes j hj
        _ = ((firstUpperEncodingInput pk lay tree leaf message counter).map UInt8.toBitVec)[i]'hi := by
          simpa [ieq] using (firstUpperEncodingInput_counter pk lay tree leaf message counter j hj).symm

theorem upper_prehash_header_word (target : Fin 5)
    (state : MachineState) (index : Fin 5) :
    (upperPrehashState target state).getWord32
      (BitVec.ofNat 64 (0x40000 + 4 * index.val)) =
      (firstUpperHeaderState (upperCounterState target state)).getWord32
        (BitVec.ofNat 64 (0x40000 + 4 * index.val)) := by
  rw [show upperPrehashState target state = firstUpperServiceState
    (firstUpperParamState (firstUpperHeaderState
      (upperCounterState target state))) from rfl,
    first_upper_service_header_word,
    first_upper_parameter_header_word]

theorem upper_prehash_payload_word (target : Fin 5)
    (state : MachineState) (index : Fin 5) :
    (upperPrehashState target state).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) := by
  rw [show upperPrehashState target state = firstUpperServiceState
    (firstUpperParamState (firstUpperHeaderState
      (upperCounterState target state))) from rfl,
    first_upper_service_payload_word,
    first_upper_parameter_payload_word,
    first_upper_header_payload_word,
    upper_counter_payload_word]

theorem upper_prehash_counter_word (target : Fin 5)
    (state : MachineState) :
    (upperPrehashState target state).getWord32 0x4003c =
      state.getWord32 (upperCounterSource target) := by
  rw [show upperPrehashState target state = firstUpperServiceState
    (firstUpperParamState (firstUpperHeaderState
      (upperCounterState target state))) from rfl,
    first_upper_service_counter_word,
    first_upper_parameter_counter_word,
    first_upper_header_counter_word,
    upper_counter_stored]

theorem upper_prehash_header_byte (target : Fin 5)
    (state : MachineState) (i : Nat) (hi : i < 20) :
    (upperPrehashState target state).getByte
      (BitVec.ofNat 64 (0x40000 + i)) =
      (firstUpperHeaderState (upperCounterState target state)).getByte
        (BitVec.ofNat 64 (0x40000 + i)) := by
  apply SphincsVerifierFtsGenericBytes.transfer_words_to_bytes
    (upperPrehashState target state)
    (firstUpperHeaderState (upperCounterState target state))
    0x40000 0x40000 (by decide) (by decide) (by decide) (by decide)
    (upper_prehash_header_word target state) i hi

theorem upper_prehash_payload_byte (target : Fin 5)
    (state : MachineState) (i : Nat) (hi : i < 20) :
    (upperPrehashState target state).getByte
      (BitVec.ofNat 64 (0x40028 + i)) =
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) := by
  apply SphincsVerifierFtsGenericBytes.transfer_words_to_bytes
    (upperPrehashState target state) state 0x40028 0x40028
    (by decide) (by decide) (by decide) (by decide)
    (upper_prehash_payload_word target state) i hi

theorem upper_prehash_parameter_byte (target : Fin 5)
    (state : MachineState) (i : Nat) (hi : i < 20) :
    (upperPrehashState target state).getByte
      (BitVec.ofNat 64 (0x40014 + i)) =
      (firstUpperHeaderState (upperCounterState target state)).getByte
        (BitVec.ofNat 64 (0x22cb4 + i)) := by
  have service : (upperPrehashState target state).getByte
      (BitVec.ofNat 64 (0x40014 + i)) =
      (firstUpperParamState
        (firstUpperHeaderState (upperCounterState target state))).getByte
          (BitVec.ofNat 64 (0x40014 + i)) := by
    simp [upperPrehashState, MachineState.getByte,
      first_upper_service_mem]
  exact service.trans (first_upper_parameter_copied_bytes _ i hi)

theorem upper_counter_header_low_byte_frame (target : Fin 5)
    (state : MachineState) (address : Word)
    (low : address.toNat < 0x40000) :
    (firstUpperHeaderState (upperCounterState target state)).getByte address =
      state.getByte address := by
  apply SphincsVerifierWotsSemanticAllChains.lowByteFrame state
    (firstUpperHeaderState (upperCounterState target state)) ?_ address low
  intro read small
  rw [first_upper_header_mem_frame _ read (Or.inl small),
    upper_counter_mem_frame]
  intro equal
  have value := congrArg BitVec.toNat equal
  have high : (0x40038 : Word).toNat = 0x40038 := by decide
  rw [high] at value
  omega

theorem upper_prehash_counter_bytes (target : Fin 5)
    (state : MachineState) (counter : Counter)
    (counterWord : state.getWord32 (upperCounterSource target) =
      BitVec.ofNat 32 counter.toNat)
    (i : Nat) (hi : i < 4) :
    (upperPrehashState target state).getByte
      (BitVec.ofNat 64 (0x4003c + i)) =
      (BitVec.ofNat 32 counter.toNat).extractLsb' (8*i) 8 := by
  let byte : Fin 4 := ⟨i, hi⟩
  have split := variableWord_byte (upperPrehashState target state) 0x4003c
    (by decide) (by decide) (0 : Fin 5) byte
  have word : (upperPrehashState target state).getWord32
      (BitVec.ofNat 64 (0x4003c + 4 * (0 : Fin 5).val)) =
      BitVec.ofNat 32 counter.toNat := by
    calc
      _ = state.getWord32 (upperCounterSource target) := by
        simpa using upper_prehash_counter_word target state
      _ = _ := counterWord
  rw [word] at split
  simpa [byte] using split

theorem upper_prehash_header (target : Fin 5)
    (state : MachineState)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (positionZero : state.getMem 0x43010 = 0)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (i : Nat) (hi : i < 20) :
    (upperPrehashState target state).getByte
      (BitVec.ofNat 64 (0x40000 + i)) =
      ((fieldBytes (tweakFields 4 lay.val tree.val 0 leaf.val)).map
        UInt8.toBitVec)[i]'(by simp [fieldBytes, tweakFields, bytesLE]; omega) := by
  have controls :
      (upperCounterState target state).getMem 0x43000 =
        BitVec.ofNat 64 lay.val ∧
      (upperCounterState target state).getMem 0x43010 = 0 ∧
      (upperCounterState target state).getMem 0x43008 =
        BitVec.ofNat 64 tree.val ∧
      (upperCounterState target state).getMem 0x43018 =
        BitVec.ofNat 64 leaf.val := by
    rw [upper_counter_mem_frame _ _ _ (by decide), layerCell,
      upper_counter_mem_frame _ _ _ (by decide), positionZero,
      upper_counter_mem_frame _ _ _ (by decide), treeCell,
      upper_counter_mem_frame _ _ _ (by decide), leafCell]
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact (upper_prehash_header_byte target state i hi).trans
    (first_upper_header_bytes (upperCounterState target state)
      lay tree leaf controls.1 controls.2.1 controls.2.2.1
      controls.2.2.2 ⟨i, hi⟩)

theorem upper_prehash_parameter (target : Fin 5)
    (state : MachineState) (pk : SphincsSecurity.PublicKey)
    (witness : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (i : Nat) (hi : i < 20) :
    (upperPrehashState target state).getByte
      (BitVec.ofNat 64 (0x40014 + i)) =
      pk.parameter.extractLsb' (8*i) 8 := by
  have low : (BitVec.ofNat 64 (0x22cb4 + i)).toNat < 0x40000 := by
    simp only [BitVec.toNat_ofNat]
    omega
  exact (upper_prehash_parameter_byte target state i hi).trans
    ((upper_counter_header_low_byte_frame target state _ low).trans
      (witness.parameter i hi))

theorem upper_encoding_query (target : Fin 5)
    (state : MachineState) (pk : SphincsSecurity.PublicKey)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter)
    (pc : state.pc = upperPrefixPc target)
    (small : BitVec.setWidth 64
      (state.getWord32 (upperCounterSource target)) >>> 20 = 0)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (positionZero : state.getMem 0x43010 = 0)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (witness : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (payload : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        message.extractLsb' (8*i) 8)
    (counterWord : state.getWord32 (upperCounterSource target) =
      BitVec.ofNat 32 counter.toNat) :
    hashInput (upperPrehashState target state) =
      toQuery (firstUpperEncodingInput pk lay tree leaf message counter) := by
  obtain ⟨_run, _pc, source, bits, _destination, _service⟩ :=
    upper_prehash_block target state pc small
  apply first_upper_encoding_query_of_parts
    (upperPrehashState target state) pk lay tree leaf message counter
    source bits
  · exact upper_prehash_header target state lay tree leaf
      layerCell positionZero treeCell leafCell
  · exact upper_prehash_parameter target state pk witness
  · intro i hi
    exact (upper_prehash_payload_byte target state i hi).trans
      (payload i hi)
  · exact upper_prehash_counter_bytes target state counter counterWord

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_encoding_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_encoding_query

private theorem wire_counter_of_split_local
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (lay : Layer)
    (offset : Nat) (before after : List Byte)
    (split : SphincsWireEncoding.encodeBytes pk signature =
      before ++ ((SphincsWire.layerEncoding signature lay).map UInt8.toBitVec) ++
        after)
    (beforeLength : before.length = offset)
    (i : Nat) (hi : i < SphincsWire.counterBytes) :
    (SphincsWireEncoding.wire pk signature).extractLsb'
      (8 * (offset + i)) 8 =
      (BitVec.ofNat 32 (signature.layers lay).counter.toNat).extractLsb'
        (8*i) 8 := by
  have inner : i <
      ((SphincsWire.layerEncoding signature lay).map UInt8.toBitVec).length := by
    rw [List.length_map, SphincsWire.layerEncoding_length]
    have positive : SphincsWire.counterBytes ≤ SphincsWire.layerBytes lay := by
      fin_cases lay <;> decide
    omega
  have full : offset + i < SphincsWire.signatureBytes := by
    rw [← SphincsWireEncoding.encodeBytes_length pk signature, split]
    simp only [List.length_append, List.length_map, beforeLength]
    simp only [List.length_map] at inner
    omega
  rw [SphincsWireEncoding.wire_byte pk signature (offset + i) full]
  simp only [split, List.append_assoc]
  rw [List.getElem_append_right (by rw [beforeLength]; omega)]
  simp only [beforeLength, Nat.add_sub_cancel_left]
  rw [List.getElem_append_left inner]
  exact SphincsWireEncoding.layerEncoding_counterByte signature lay i hi

private def upperWireBase (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) : List UInt8 :=
  bytesLE SphincsWire.digestBytes pk.root ++
    bytesLE SphincsWire.digestBytes pk.parameter ++
    bytesLE SphincsWire.digestBytes signature.randomness ++
    SphincsWire.concatFields (ftsTrees - 1) (SphincsWire.ftsOpening signature)

private def upperWireBefore (target : Fin 5)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) : List Byte :=
  (upperWireBase pk signature ++
    (if target.val ≥ 1 then SphincsWire.layerEncoding signature topLayer else []) ++
    (if target.val ≥ 2 then SphincsWire.layerEncoding signature middleLayer else []) ++
    (if target.val ≥ 3 then SphincsWire.layerEncoding signature middle2Layer else []) ++
    (if target.val ≥ 4 then SphincsWire.layerEncoding signature middle3Layer else [])).map
      UInt8.toBitVec

private def upperWireAfter (target : Fin 5)
    (signature : SphincsSecurity.Signature) : List Byte :=
  ((if target.val < 1 then SphincsWire.layerEncoding signature middleLayer else []) ++
    (if target.val < 2 then SphincsWire.layerEncoding signature middle2Layer else []) ++
    (if target.val < 3 then SphincsWire.layerEncoding signature middle3Layer else []) ++
    (if target.val < 4 then SphincsWire.layerEncoding signature middle4Layer else []) ++
    SphincsWire.layerEncoding signature bottomLayer).map UInt8.toBitVec

private theorem upperWire_split (target : Fin 5)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) :
    SphincsWireEncoding.encodeBytes pk signature =
      upperWireBefore target pk signature ++
        (SphincsWire.layerEncoding signature
          (SphincsVerifierXmssTransition.targetLayer target)).map
            UInt8.toBitVec ++
        upperWireAfter target signature := by
  fin_cases target <;>
    simp [upperWireBefore, upperWireAfter, upperWireBase,
      SphincsWireEncoding.encodeBytes, SphincsWire.encodeSignature,
      SphincsVerifierXmssTransition.targetLayer,
      topLayer, middleLayer, middle2Layer, middle3Layer, middle4Layer,
      List.map_append, List.append_assoc]

private theorem upperWireBefore_length (target : Fin 5)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) :
    (upperWireBefore target pk signature).length =
      SphincsWireEncoding.layerOffset
        (SphincsVerifierXmssTransition.targetLayer target) := by
  have ftsLength :
      (SphincsWire.concatFields (ftsTrees - 1)
        (SphincsWire.ftsOpening signature)).length =
          (ftsTrees - 1) * SphincsWire.ftsOpeningBytes :=
    SphincsWire.concatFields_length _ _ _
      (SphincsWire.ftsOpening_length signature)
  fin_cases target <;>
    simp [upperWireBefore, upperWireBase,
      SphincsWireEncoding.layerOffset,
      SphincsVerifierXmssTransition.targetLayer,
      SphincsWire.topOffset, SphincsWire.middleOffset,
      SphincsWire.middle2Offset, SphincsWire.middle3Offset,
      SphincsWire.middle4Offset,
      SphincsWire.layerEncoding_length,
      List.length_map, List.length_append,
      bytesLE, ftsLength,
      SphincsWire.ftsOffset, SphincsWire.randomizerOffset,
      SphincsWire.parameterOffset, SphincsWire.rootOffset]
  all_goals omega

theorem upper_wire_counter (target : Fin 5)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (i : Nat) (hi : i < SphincsWire.counterBytes) :
    (SphincsWireEncoding.wire pk signature).extractLsb'
      (8 * (SphincsWireEncoding.layerOffset
        (SphincsVerifierXmssTransition.targetLayer target) + i)) 8 =
      (BitVec.ofNat 32
        (signature.layers (SphincsVerifierXmssTransition.targetLayer target)).counter.toNat).extractLsb'
          (8*i) 8 := by
  exact wire_counter_of_split_local pk signature
    (SphincsVerifierXmssTransition.targetLayer target)
    (SphincsWireEncoding.layerOffset
      (SphincsVerifierXmssTransition.targetLayer target))
    (upperWireBefore target pk signature)
    (upperWireAfter target signature)
    (upperWire_split target pk signature)
    (upperWireBefore_length target pk signature) i hi

theorem loaded_upper_counter_byte (target : Fin 5)
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire pk signature) = some state)
    (i : Nat) (hi : i < SphincsWire.counterBytes) :
    state.getByte (BitVec.ofNat 64
      (0x22ca0 + SphincsWireEncoding.layerOffset
        (SphincsVerifierXmssTransition.targetLayer target) + i)) =
      (BitVec.ofNat 32
        (signature.layers (SphincsVerifierXmssTransition.targetLayer target)).counter.toNat).extractLsb'
          (8*i) 8 := by
  have full : SphincsWireEncoding.layerOffset
      (SphincsVerifierXmssTransition.targetLayer target) + i <
      SphincsWire.signatureBytes := by
    have fits : SphincsWireEncoding.layerOffset
        (SphincsVerifierXmssTransition.targetLayer target) +
        SphincsWire.counterBytes ≤ SphincsWire.signatureBytes := by
      fin_cases target <;> decide
    omega
  rw [show 0x22ca0 + SphincsWireEncoding.layerOffset
      (SphincsVerifierXmssTransition.targetLayer target) + i =
      0x22ca0 + (SphincsWireEncoding.layerOffset
        (SphincsVerifierXmssTransition.targetLayer target) + i) by omega]
  rw [SphincsVerifierLoader.loaded_witness publicKey message
    (SphincsWireEncoding.wire pk signature) state loaded _ full]
  exact upper_wire_counter target pk signature i hi

theorem loaded_upper_counter_word (target : Fin 5)
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire pk signature) = some state) :
    state.getWord32 (upperCounterSource target) =
      BitVec.ofNat 32
        (signature.layers (SphincsVerifierXmssTransition.targetLayer target)).counter.toNat := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro bit hbit
  let byte : Fin 4 := ⟨bit / 8, by omega⟩
  let base := 0x22ca0 + SphincsWireEncoding.layerOffset
    (SphincsVerifierXmssTransition.targetLayer target)
  have split := variableWord_byte state base
    (by dsimp [base]; fin_cases target <;> decide)
    (by dsimp [base]; fin_cases target <;> decide)
    (0 : Fin 5) byte
  have value := loaded_upper_counter_byte target publicKey message pk
    signature state loaded byte.val
      (by simpa only [SphincsWire.counterBytes] using byte.isLt)
  have address : base + 4 * (0 : Fin 5).val + byte.val =
      0x22ca0 + SphincsWireEncoding.layerOffset
        (SphincsVerifierXmssTransition.targetLayer target) + byte.val := by
    simp [base]
  rw [address] at split
  have bytes :
      (state.getWord32 (upperCounterSource target)).extractLsb' (8 * byte.val) 8 =
      (BitVec.ofNat 32
        (signature.layers (SphincsVerifierXmssTransition.targetLayer target)).counter.toNat).extractLsb'
          (8 * byte.val) 8 := by
    have word : BitVec.ofNat 64 (base + 4 * (0 : Fin 5).val) =
        upperCounterSource target := by
      simp [base, upperCounterSource]
    rw [word] at split
    exact split.symm.trans value
  have bitEq := congrArg
    (fun value : BitVec 8 => value.getLsbD (bit % 8)) bytes
  have offset : 8 * byte.val + bit % 8 = bit := by
    dsimp [byte]
    omega
  simpa only [BitVec.getLsbD_extractLsb', show bit % 8 < 8 by omega,
    decide_true, Bool.true_and, offset] using bitEq

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_wire_counter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_wire_counter

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.loaded_upper_counter_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_upper_counter_byte

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.loaded_upper_counter_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_upper_counter_word

theorem upper_counter_word_after_frame (target : Fin 5)
    (initial final : MachineState)
    (frame : ∀ address, address.toNat < 0x40000 →
      final.getByte address = initial.getByte address) :
    final.getWord32 (upperCounterSource target) =
      initial.getWord32 (upperCounterSource target) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro bit hbit
  let byte : Fin 4 := ⟨bit / 8, by omega⟩
  let base := 0x22ca0 + SphincsWireEncoding.layerOffset
    (SphincsVerifierXmssTransition.targetLayer target)
  have small : base + 20 ≤ 0x50000 := by
    dsimp [base]
    fin_cases target <;> decide
  have aligned : base % 4 = 0 := by
    dsimp [base]
    fin_cases target <;> decide
  have baseBound : base + 4 < 0x40000 := by
    dsimp [base]
    fin_cases target <;> decide
  have finalByte := variableWord_byte final base small aligned
    (0 : Fin 5) byte
  have initialByte := variableWord_byte initial base small aligned
    (0 : Fin 5) byte
  have address : base + 4 * (0 : Fin 5).val + byte.val =
      base + byte.val := by simp
  rw [address] at finalByte initialByte
  have low : (BitVec.ofNat 64 (base + byte.val)).toNat < 0x40000 := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : base + byte.val < 2 ^ 64)]
    omega
  have bytes :
      (final.getWord32 (upperCounterSource target)).extractLsb' (8 * byte.val) 8 =
      (initial.getWord32 (upperCounterSource target)).extractLsb' (8 * byte.val) 8 := by
    have word : BitVec.ofNat 64 (base + 4 * (0 : Fin 5).val) =
        upperCounterSource target := by
      simp [base, upperCounterSource]
    rw [word] at finalByte initialByte
    calc
      _ = final.getByte (BitVec.ofNat 64 (base + byte.val)) := finalByte.symm
      _ = initial.getByte (BitVec.ofNat 64 (base + byte.val)) := frame _ low
      _ = _ := initialByte
  have bitEq := congrArg
    (fun value : BitVec 8 => value.getLsbD (bit % 8)) bytes
  have offset : 8 * byte.val + bit % 8 = bit := by
    dsimp [byte]
    omega
  simpa only [BitVec.getLsbD_extractLsb', show bit % 8 < 8 by omega,
    decide_true, Bool.true_and, offset] using bitEq

theorem honest_upper_counter_word_after_frame (target : Fin 5)
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (initial final : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire pk signature) = some initial)
    (frame : ∀ address, address.toNat < 0x40000 →
      final.getByte address = initial.getByte address) :
    final.getWord32 (upperCounterSource target) =
      BitVec.ofNat 32
        (signature.layers (SphincsVerifierXmssTransition.targetLayer target)).counter.toNat := by
  exact (upper_counter_word_after_frame target initial final frame).trans
    (loaded_upper_counter_word target publicKey message pk signature initial loaded)

theorem upper_encoding_query_after_frame (target : Fin 5)
    (publicKey : SigGolf.PublicKey) (inputMessage : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (initial state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (inputMessage, publicKey, SphincsWireEncoding.wire pk signature) = some initial)
    (frame : ∀ address, address.toNat < 0x40000 →
      state.getByte address = initial.getByte address)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest)
    (pc : state.pc = upperPrefixPc target)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (positionZero : state.getMem 0x43010 = 0)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (witness : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (payload : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        message.extractLsb' (8*i) 8) :
    hashInput (upperPrehashState target state) =
      toQuery (firstUpperEncodingInput pk lay tree leaf message
        (signature.layers (SphincsVerifierXmssTransition.targetLayer target)).counter) := by
  have counterWord := honest_upper_counter_word_after_frame target
    publicKey inputMessage pk signature initial state loaded frame
  have small : BitVec.setWidth 64
      (state.getWord32 (upperCounterSource target)) >>> 20 = 0 := by
    rw [counterWord]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight]
    rw [BitVec.toNat_setWidth_of_le (by decide)]
    simp only [BitVec.toNat_ofNat]
    have below :
        (signature.layers (SphincsVerifierXmssTransition.targetLayer target)).counter.toNat <
          2 ^ 20 := (signature.layers
            (SphincsVerifierXmssTransition.targetLayer target)).counter.isLt
    rw [Nat.mod_eq_of_lt (by omega :
      (signature.layers (SphincsVerifierXmssTransition.targetLayer target)).counter.toNat <
        2 ^ 32)]
    exact Nat.shiftRight_eq_zero _ 20 below
  exact upper_encoding_query target state pk lay tree leaf message
    (signature.layers (SphincsVerifierXmssTransition.targetLayer target)).counter
    pc small layerCell positionZero treeCell leafCell witness payload
    counterWord

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_counter_word_after_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_counter_word_after_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.honest_upper_counter_word_after_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_upper_counter_word_after_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_encoding_query_after_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_encoding_query_after_frame

theorem loaded_first_upper_counter_word
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature) (state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire pk signature) = some state) :
    state.getWord32 0x23dbc =
      BitVec.ofNat 32 (signature.layers topLayer).counter.toNat := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro bit hbit
  let byte : Fin 4 := ⟨bit / 8, by omega⟩
  have split := variableWord_byte state 0x23dbc
    (by decide) (by decide) (0 : Fin 5) byte
  have value := SphincsWireEncoding.loaded_honest_topCounter
    publicKey message pk signature state loaded byte.val (by simpa only [SphincsWire.counterBytes] using byte.isLt)
  have address : 0x22ca0 + SphincsWire.topOffset + byte.val =
      0x23dbc + byte.val := by
    have base : 0x22ca0 + SphincsWire.topOffset = 0x23dbc := by decide
    omega
  rw [address] at value
  have bytes : (state.getWord32 0x23dbc).extractLsb' (8 * byte.val) 8 =
      (BitVec.ofNat 32 (signature.layers topLayer).counter.toNat).extractLsb'
        (8 * byte.val) 8 := by
    have word : (state.getWord32
        (BitVec.ofNat 64 (0x23dbc + 4 * (0 : Fin 5).val))) =
        state.getWord32 0x23dbc := by rfl
    rw [word] at split
    simpa [byte] using split.symm.trans value
  have bitEq := congrArg (fun value : BitVec 8 => value.getLsbD (bit % 8)) bytes
  have offset : 8 * byte.val + bit % 8 = bit := by
    dsimp [byte]
    omega
  simpa only [BitVec.getLsbD_extractLsb', show bit % 8 < 8 by omega,
    decide_true, Bool.true_and, offset] using bitEq

theorem first_upper_counter_word_after_frame (initial final : MachineState)
    (frame : ∀ address, address.toNat < 0x40000 →
      final.getByte address = initial.getByte address) :
    final.getWord32 0x23dbc = initial.getWord32 0x23dbc := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro bit hbit
  let byte : Fin 4 := ⟨bit / 8, by omega⟩
  have finalByte := variableWord_byte final 0x23dbc
    (by decide) (by decide) (0 : Fin 5) byte
  have initialByte := variableWord_byte initial 0x23dbc
    (by decide) (by decide) (0 : Fin 5) byte
  have low : (BitVec.ofNat 64 (0x23dbc + byte.val)).toNat < 0x40000 := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : 0x23dbc + byte.val < 2 ^ 64)]
    omega
  have byteEq : (final.getWord32 0x23dbc).extractLsb' (8 * byte.val) 8 =
      (initial.getWord32 0x23dbc).extractLsb' (8 * byte.val) 8 := by
    have address : 0x23dbc + 4 * (0 : Fin 5).val + byte.val =
        0x23dbc + byte.val := by simp
    rw [address] at finalByte initialByte
    calc
      _ = final.getByte (BitVec.ofNat 64 (0x23dbc + byte.val)) := finalByte.symm
      _ = initial.getByte (BitVec.ofNat 64 (0x23dbc + byte.val)) := frame _ low
      _ = _ := initialByte
  have bitEq := congrArg (fun value : BitVec 8 => value.getLsbD (bit % 8)) byteEq
  have offset : 8 * byte.val + bit % 8 = bit := by
    dsimp [byte]
    omega
  simpa only [BitVec.getLsbD_extractLsb', show bit % 8 < 8 by omega,
    decide_true, Bool.true_and, offset] using bitEq

theorem honest_first_upper_counter_word_after_frame
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (initial final : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire pk signature) = some initial)
    (frame : ∀ address, address.toNat < 0x40000 →
      final.getByte address = initial.getByte address) :
    final.getWord32 0x23dbc =
      BitVec.ofNat 32 (signature.layers topLayer).counter.toNat := by
  exact (first_upper_counter_word_after_frame initial final frame).trans
    (loaded_first_upper_counter_word publicKey message pk signature initial loaded)

theorem first_upper_handoff_low_frame (hash : Hash)
    (initial state : MachineState)
    (frame : ∀ address, address.toNat < 0x40000 →
      state.getByte address = initial.getByte address)
    (address : Word) (low : address.toNat < 0x40000) :
    (SphincsVerifierXmssTransitionMessage.handoffState (0 : Fin 5)
      (SphincsVerifierXmssPathControl.pathState hash
        (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5))
        (layerHeight (SphincsVerifierXmssTransition.previousLayer
          (0 : Fin 5))) state)).getByte address =
      initial.getByte address := by
  let previous := SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)
  let pathEnd := SphincsVerifierXmssPathControl.pathState hash previous
    (layerHeight previous) state
  have pathFrame : pathEnd.getByte address = state.getByte address := by
    apply SphincsVerifierWotsSemanticAllChains.lowByteFrame state pathEnd
      (fun read small =>
        SphincsVerifierXmssPathControl.path_low_mem hash previous
          (layerHeight previous) state read small) address low
  exact (upper_handoff_low_byte_frame (0 : Fin 5) pathEnd address low).trans
    (pathFrame.trans (frame address low))

theorem honest_first_upper_handoff_counter_word (hash : Hash)
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (initial state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire pk signature) = some initial)
    (frame : ∀ address, address.toNat < 0x40000 →
      state.getByte address = initial.getByte address) :
    (SphincsVerifierXmssTransitionMessage.handoffState (0 : Fin 5)
      (SphincsVerifierXmssPathControl.pathState hash
        (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5))
        (layerHeight (SphincsVerifierXmssTransition.previousLayer
          (0 : Fin 5))) state)).getWord32 0x23dbc =
      BitVec.ofNat 32 (signature.layers topLayer).counter.toNat := by
  exact honest_first_upper_counter_word_after_frame publicKey message pk
    signature initial _ loaded
    (first_upper_handoff_low_frame hash initial state frame)

theorem first_upper_honest_counter_small (counter : Counter) :
    BitVec.setWidth 64 (BitVec.ofNat 32 counter.toNat) >>> 20 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight]
  rw [BitVec.toNat_setWidth_of_le (by decide)]
  simp only [BitVec.toNat_ofNat]
  have below : counter.toNat < 2 ^ 20 := counter.isLt
  rw [Nat.mod_eq_of_lt (by omega : counter.toNat < 2 ^ 32)]
  exact Nat.shiftRight_eq_zero counter.toNat 20 below

theorem first_upper_encoding_query (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter)
    (pc : state.pc = 0x6d1c)
    (small : BitVec.setWidth 64 (state.getWord32 0x23dbc) >>> 20 = 0)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (positionZero : state.getMem 0x43010 = 0)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (witness : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (payload : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        message.extractLsb' (8*i) 8)
    (counterWord : state.getWord32 0x23dbc =
      BitVec.ofNat 32 counter.toNat) :
    hashInput (firstUpperPrehashState state) =
      toQuery (firstUpperEncodingInput pk lay tree leaf message counter) := by
  obtain ⟨_, _, source, bits, _, _⟩ := first_upper_prehash_block state pc small
  apply first_upper_encoding_query_of_parts
    (firstUpperPrehashState state) pk lay tree leaf message counter source bits
  · intro i hi
    exact first_upper_prehash_header state lay tree leaf
      layerCell positionZero treeCell leafCell i hi
  · intro i hi
    exact first_upper_prehash_parameter state pk witness i hi
  · intro i hi
    exact (first_upper_prehash_payload_byte state i hi).trans (payload i hi)
  · intro i hi
    exact first_upper_prehash_counter_bytes state counter counterWord i hi

theorem first_upper_encoding_query_after_frame
    (publicKey : SigGolf.PublicKey) (inputMessage : SigGolf.Message)
    (pk : SphincsSecurity.PublicKey)
    (signature : SphincsSecurity.Signature)
    (initial state : MachineState)
    (loaded : initialState SphincsSubmission.submission .verify
      (inputMessage, publicKey, SphincsWireEncoding.wire pk signature) = some initial)
    (frame : ∀ address, address.toNat < 0x40000 →
      state.getByte address = initial.getByte address)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest)
    (pc : state.pc = 0x6d1c)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (positionZero : state.getMem 0x43010 = 0)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (leafCell : state.getMem 0x43018 = BitVec.ofNat 64 leaf.val)
    (witness : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (payload : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        message.extractLsb' (8*i) 8) :
    hashInput (firstUpperPrehashState state) =
      toQuery (firstUpperEncodingInput pk lay tree leaf message
        (signature.layers topLayer).counter) := by
  have counterWord := honest_first_upper_counter_word_after_frame
    publicKey inputMessage pk signature initial state loaded frame
  have small : BitVec.setWidth 64 (state.getWord32 0x23dbc) >>> 20 = 0 := by
    rw [counterWord]
    exact first_upper_honest_counter_small _
  exact first_upper_encoding_query state pk lay tree leaf message
    (signature.layers topLayer).counter pc small layerCell positionZero
    treeCell leafCell witness payload counterWord

theorem first_upper_handoff_root_and_frame (hash : Hash)
    (initial state : MachineState) (pk : SphincsSecurity.PublicKey)
    (tree : TreeIndex) (leaf : LeafIndex)
    (signature : SphincsSecurity.Signature) (first : Digest)
    (pointer : Word)
    (frame : ∀ address, address.toNat < 0x40000 →
      state.getByte address = initial.getByte address)
    (pc : state.pc = SphincsVerifierXmssParity.nodePc
      (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)))
    (pointerValue : state.getMem 0x43028 = pointer)
    (pointerBound : pointer.toNat + 20 * layerHeight
      (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)) ≤ 0x40000)
    (pointerAligned : pointer.toNat % 4 = 0)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64
      (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)).val)
    (treeCell : state.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (levelCell : state.getMem 0x43048 = 1)
    (bitCell : state.getMem 0x43070 = BitVec.ofNat 64 leaf.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (current : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        first.extractLsb' (8 * i) 8)
    (siblings : SphincsVerifierXmssPathControl.PathWitness state signature
      (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)) pointer) :
    let previous := SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)
    let pathEnd := SphincsVerifierXmssPathControl.pathState hash previous
      (layerHeight previous) state
    let nextState := SphincsVerifierXmssTransitionMessage.handoffState
      (0 : Fin 5) pathEnd
    (∀ i, (hi : i < 20) →
      nextState.getByte (BitVec.ofNat 64 (0x40028 + i)) =
        (SphincsSecurity.Concrete.foldValue (adaptOracle hash) pk.parameter
          previous tree leaf
          (SphincsSecurity.Concrete.signaturePath signature previous) first
          (layerHeight previous)).extractLsb' (8*i) 8) ∧
    (∀ address, address.toNat < 0x40000 →
      nextState.getByte address = initial.getByte address) := by
  constructor
  · exact (SphincsVerifierXmssTransitionComplete.complete_path_handoff hash
      (0 : Fin 5) state pk tree leaf signature first pointer pc pointerValue
      pointerBound pointerAligned layerCell treeCell levelCell bitCell
      hprefix current siblings).2
  · intro address low
    exact first_upper_handoff_low_frame hash initial state frame address low

theorem first_upper_encoding_query_after_previous_path (hash : Hash)
    (publicKey : SigGolf.PublicKey) (inputMessage : SigGolf.Message)
    (initial state nextState : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (priorTree nextTree : TreeIndex) (priorLeaf nextLeaf : LeafIndex)
    (signature : SphincsSecurity.Signature) (first : Digest)
    (pointer : Word)
    (loaded : initialState SphincsSubmission.submission .verify
      (inputMessage, publicKey, SphincsWireEncoding.wire pk signature) = some initial)
    (frame : ∀ address, address.toNat < 0x40000 →
      state.getByte address = initial.getByte address)
    (pc : state.pc = SphincsVerifierXmssParity.nodePc
      (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)))
    (pointerValue : state.getMem 0x43028 = pointer)
    (pointerBound : pointer.toNat + 20 * layerHeight
      (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)) ≤ 0x40000)
    (pointerAligned : pointer.toNat % 4 = 0)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64
      (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)).val)
    (priorTreeCell : state.getMem 0x43008 = BitVec.ofNat 64 priorTree.val)
    (levelCell : state.getMem 0x43048 = 1)
    (bitCell : state.getMem 0x43070 = BitVec.ofNat 64 priorLeaf.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (current : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        first.extractLsb' (8 * i) 8)
    (siblings : SphincsVerifierXmssPathControl.PathWitness state signature
      (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)) pointer)
    (nextEq : nextState =
      SphincsVerifierXmssTransitionMessage.handoffState (0 : Fin 5)
        (SphincsVerifierXmssPathControl.pathState hash
          (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5))
          (layerHeight (SphincsVerifierXmssTransition.previousLayer
            (0 : Fin 5))) state))
    (nextTreeCell : nextState.getMem 0x43008 = BitVec.ofNat 64 nextTree.val)
    (nextLeafCell : nextState.getMem 0x43018 = BitVec.ofNat 64 nextLeaf.val) :
    hashInput (firstUpperPrehashState nextState) =
      toQuery (firstUpperEncodingInput pk topLayer nextTree nextLeaf
        (SphincsSecurity.Concrete.foldValue (adaptOracle hash) pk.parameter
          (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5))
          priorTree priorLeaf
          (SphincsSecurity.Concrete.signaturePath signature
            (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)))
          first (layerHeight (SphincsVerifierXmssTransition.previousLayer
            (0 : Fin 5))))
        (signature.layers topLayer).counter) := by
  subst nextState
  let previous := SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)
  let pathEnd := SphincsVerifierXmssPathControl.pathState hash previous
    (layerHeight previous) state
  obtain ⟨root, frameNext⟩ := first_upper_handoff_root_and_frame hash
    initial state pk priorTree priorLeaf signature first pointer frame pc
    pointerValue pointerBound pointerAligned layerCell priorTreeCell
    levelCell bitCell hprefix current siblings
  have pathPc := (SphincsVerifierXmssPathComplete.complete_path hash previous
    state pk priorTree priorLeaf signature first pointer pc pointerValue
    pointerBound pointerAligned layerCell priorTreeCell levelCell bitCell
    hprefix current siblings).1
  have transitionPc : pathEnd.pc =
      SphincsVerifierXmssTransition.transitionPc (0 : Fin 5) := by
    simpa [pathEnd, SphincsVerifierXmssTransition.transitionPc] using pathPc
  have nextPc : (SphincsVerifierXmssTransitionMessage.handoffState
      (0 : Fin 5) pathEnd).pc = 0x6d1c := by
    calc
      _ = SphincsVerifierXmssTransitionMessage.messagePc (0 : Fin 5) + 56 :=
        upper_handoff_prefix_pc (0 : Fin 5) pathEnd transitionPc
      _ = 0x6d1c := by decide
  have controls := upper_handoff_control_cells (0 : Fin 5) pathEnd
  have topCell : (SphincsVerifierXmssTransitionMessage.handoffState
      (0 : Fin 5) pathEnd).getMem 0x43000 =
      BitVec.ofNat 64 topLayer.val := by
    simpa [SphincsVerifierXmssTransition.targetLayer, topLayer] using controls.1
  have positionZero := upper_handoff_position_zero (0 : Fin 5) pathEnd
  have witness := loaded_upper_prefix_after_frame publicKey inputMessage pk
    signature initial _ loaded frameNext
  exact first_upper_encoding_query_after_frame publicKey inputMessage pk
    signature initial _ loaded frameNext topLayer nextTree nextLeaf _ nextPc
    topCell positionZero nextTreeCell nextLeafCell witness root

theorem upper_handoff_index_cells (target : Fin 5)
    (pathEnd : MachineState) (index : Index)
    (global : pathEnd.getMem 0x43078 = BitVec.ofNat 64 index.val) :
    let done := SphincsVerifierXmssTransitionMessage.handoffState target pathEnd
    let lay := SphincsVerifierXmssTransition.targetLayer target
    done.getMem 0x43008 =
      BitVec.ofNat 64 (SphincsSecurity.Concrete.treeIndexAt index lay).val ∧
    done.getMem 0x43018 =
      BitVec.ofNat 64 (SphincsSecurity.Concrete.leafIndexAt index lay).val := by
  have controls := upper_handoff_control_cells target pathEnd
  have tree := SphincsVerifierXmssTransitionIndex.transition_tree_index
    target pathEnd index global
  have leaf := SphincsVerifierXmssTransitionIndex.transition_leaf_index
    target pathEnd index global
  constructor
  · calc
      _ = pathEnd.getMem 0x43078 >>>
            (heightBelow (SphincsVerifierXmssTransition.targetLayer target) +
              layerHeight (SphincsVerifierXmssTransition.targetLayer target)) :=
          controls.2.1
      _ = (SphincsVerifierXmssTransition.transitionState target pathEnd).getMem
            0x43008 := (SphincsVerifierXmssTransition.transition_tree target pathEnd).symm
      _ = _ := tree
  · calc
      _ = (SphincsVerifierXmssTransitionMessage.handoffState target pathEnd).getMem
            0x43020 := controls.2.2.2
      _ = (pathEnd.getMem 0x43078 >>>
            heightBelow (SphincsVerifierXmssTransition.targetLayer target)) &&&
            BitVec.ofNat 64
              (2 ^ layerHeight (SphincsVerifierXmssTransition.targetLayer target) - 1) :=
          controls.2.2.1
      _ = (SphincsVerifierXmssTransition.transitionState target pathEnd).getMem
            0x43020 := (SphincsVerifierXmssTransition.transition_leaf target pathEnd).symm
      _ = _ := leaf

theorem upper_path_handoff_low_frame (target : Fin 5) (hash : Hash)
    (initial state : MachineState)
    (frame : ∀ address, address.toNat < 0x40000 →
      state.getByte address = initial.getByte address)
    (address : Word) (low : address.toNat < 0x40000) :
    (SphincsVerifierXmssTransitionMessage.handoffState target
      (SphincsVerifierXmssPathControl.pathState hash
        (SphincsVerifierXmssTransition.previousLayer target)
        (layerHeight (SphincsVerifierXmssTransition.previousLayer target))
        state)).getByte address = initial.getByte address := by
  let previous := SphincsVerifierXmssTransition.previousLayer target
  let pathEnd := SphincsVerifierXmssPathControl.pathState hash previous
    (layerHeight previous) state
  have pathFrame : pathEnd.getByte address = state.getByte address := by
    apply SphincsVerifierWotsSemanticAllChains.lowByteFrame state pathEnd
      (fun read small =>
        SphincsVerifierXmssPathControl.path_low_mem hash previous
          (layerHeight previous) state read small) address low
  exact (upper_handoff_low_byte_frame target pathEnd address low).trans
    (pathFrame.trans (frame address low))

theorem upper_path_handoff_global_index_cell (target : Fin 5)
    (hash : Hash) (state : MachineState) :
    (SphincsVerifierXmssTransitionMessage.handoffState target
      (SphincsVerifierXmssPathControl.pathState hash
        (SphincsVerifierXmssTransition.previousLayer target)
        (layerHeight (SphincsVerifierXmssTransition.previousLayer target))
        state)).getMem 0x43078 = state.getMem 0x43078 := by
  rw [upper_handoff_global_index_cell,
    path_global_index_cell]

theorem decoder_step_global_index_cell (i : Fin 52)
    (state : MachineState) :
    (SphincsVerifierWotsDecode.decoderState i state).getMem 0x43078 =
      state.getMem 0x43078 := by
  have separate : alignToDword (BitVec.ofNat 64 (0x44000 + i.val)) ≠
      (0x43078 : Word) := by
    fin_cases i <;> decide
  have storeAddress : (0x44000 : Word) +
      signExtend12 (BitVec.ofNat 12 i.val) + signExtend12 (0 : BitVec 12) =
      BitVec.ofNat 64 (0x44000 + i.val) := by
    fin_cases i <;> decide
  have distinct : (0x43078 : Word) ≠
      alignToDword ((0x44000 : Word) +
        signExtend12 (BitVec.ofNat 12 i.val) +
        signExtend12 (0 : BitVec 12)) := by
    intro equal
    exact separate ((congrArg alignToDword storeAddress).symm.trans equal.symm)
  simp [SphincsVerifierWotsDecode.decoderState,
    SphincsVerifierWotsDecode.decoderSuffixState,
    SphincsVerifierWotsDecode.decoderMiddleState,
    SphincsVerifierWotsDecode.decoderPrefixState,
    execInstrBr, MachineState.setByte,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  intro same
  exact (distinct same).elim

theorem decoder_run_global_index_cell (count : Nat)
    (state : MachineState) :
    (SphincsVerifierWotsDecodeData.decoderRun count state).getMem 0x43078 =
      state.getMem 0x43078 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (SphincsVerifierWotsDecode.decoderState
        ⟨count % 52, Nat.mod_lt _ (by decide)⟩
        (SphincsVerifierWotsDecodeData.decoderRun count state)).getMem
          0x43078 = _
      exact (decoder_step_global_index_cell _ _).trans ih

theorem upper_decoder_global_index_cell (target : Fin 5)
    (state : MachineState) :
    (SphincsVerifierDecoderRelocation.upperDecoderState target state).getMem
      0x43078 = state.getMem 0x43078 := by
  simp only [SphincsVerifierDecoderRelocation.upperDecoderState,
    SphincsMaskedSignOtsShift.shift_mem,
    decoder_run_global_index_cell]

theorem upper_setup_global_index_cell (target : Fin 5)
    (state : MachineState) :
    (SphincsVerifierDecoderRelocation.setupState target
      (SphincsVerifierDecoderRelocation.upperDecoderState target state)).getMem
        0x43078 = state.getMem 0x43078 := by
  rw [SphincsVerifierDecoderRelocation.setup_mem_other target _ 0x43078
      (by decide) (by decide),
    upper_decoder_global_index_cell]

theorem upper_handoff_global_index_from_input (target : Fin 5)
    (state ready nextState : MachineState)
    (readyEq : ready =
      SphincsVerifierDecoderRelocation.setupState target
        (SphincsVerifierDecoderRelocation.upperDecoderState target state))
    (handoffIndex : nextState.getMem 0x43078 = ready.getMem 0x43078) :
    nextState.getMem 0x43078 = state.getMem 0x43078 := by
  exact handoffIndex.trans (by
    rw [readyEq]
    exact upper_setup_global_index_cell target state)

theorem first_upper_encoding_query_with_index (hash : Hash)
    (publicKey : SigGolf.PublicKey) (inputMessage : SigGolf.Message)
    (initial state nextState : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (priorTree : TreeIndex) (priorLeaf : LeafIndex) (index : Index)
    (signature : SphincsSecurity.Signature) (first : Digest)
    (pointer : Word)
    (loaded : initialState SphincsSubmission.submission .verify
      (inputMessage, publicKey, SphincsWireEncoding.wire pk signature) = some initial)
    (frame : ∀ address, address.toNat < 0x40000 →
      state.getByte address = initial.getByte address)
    (pc : state.pc = SphincsVerifierXmssParity.nodePc
      (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)))
    (pointerValue : state.getMem 0x43028 = pointer)
    (pointerBound : pointer.toNat + 20 * layerHeight
      (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)) ≤ 0x40000)
    (pointerAligned : pointer.toNat % 4 = 0)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64
      (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)).val)
    (priorTreeCell : state.getMem 0x43008 = BitVec.ofNat 64 priorTree.val)
    (levelCell : state.getMem 0x43048 = 1)
    (bitCell : state.getMem 0x43070 = BitVec.ofNat 64 priorLeaf.val)
    (global : state.getMem 0x43078 = BitVec.ofNat 64 index.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (current : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        first.extractLsb' (8 * i) 8)
    (siblings : SphincsVerifierXmssPathControl.PathWitness state signature
      (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)) pointer)
    (nextEq : nextState =
      SphincsVerifierXmssTransitionMessage.handoffState (0 : Fin 5)
        (SphincsVerifierXmssPathControl.pathState hash
          (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5))
          (layerHeight (SphincsVerifierXmssTransition.previousLayer
            (0 : Fin 5))) state)) :
    hashInput (firstUpperPrehashState nextState) =
      toQuery (firstUpperEncodingInput pk topLayer
        (SphincsSecurity.Concrete.treeIndexAt index topLayer)
        (SphincsSecurity.Concrete.leafIndexAt index topLayer)
        (SphincsSecurity.Concrete.foldValue (adaptOracle hash) pk.parameter
          (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5))
          priorTree priorLeaf
          (SphincsSecurity.Concrete.signaturePath signature
            (SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)))
          first (layerHeight (SphincsVerifierXmssTransition.previousLayer
            (0 : Fin 5))))
        (signature.layers topLayer).counter) := by
  let previous := SphincsVerifierXmssTransition.previousLayer (0 : Fin 5)
  let pathEnd := SphincsVerifierXmssPathControl.pathState hash previous
    (layerHeight previous) state
  have pathGlobal : pathEnd.getMem 0x43078 = BitVec.ofNat 64 index.val :=
    (path_global_index_cell hash previous (layerHeight previous) state).trans
      global
  have controls := upper_handoff_index_cells (0 : Fin 5) pathEnd index
    pathGlobal
  have treeCell : nextState.getMem 0x43008 = BitVec.ofNat 64
      (SphincsSecurity.Concrete.treeIndexAt index topLayer).val := by
    rw [nextEq]
    simpa [SphincsVerifierXmssTransition.targetLayer, topLayer] using
      controls.1
  have leafCell : nextState.getMem 0x43018 = BitVec.ofNat 64
      (SphincsSecurity.Concrete.leafIndexAt index topLayer).val := by
    rw [nextEq]
    simpa [SphincsVerifierXmssTransition.targetLayer, topLayer] using
      controls.2
  exact first_upper_encoding_query_after_previous_path hash publicKey
    inputMessage initial state nextState pk priorTree
    (SphincsSecurity.Concrete.treeIndexAt index topLayer) priorLeaf
    (SphincsSecurity.Concrete.leafIndexAt index topLayer) signature first
    pointer loaded frame pc pointerValue pointerBound pointerAligned layerCell
    priorTreeCell levelCell bitCell hprefix current siblings nextEq treeCell
    leafCell

theorem upper_encoding_query_after_previous_path (target : Fin 5)
    (hash : Hash)
    (publicKey : SigGolf.PublicKey) (inputMessage : SigGolf.Message)
    (initial state : MachineState) (pk : SphincsSecurity.PublicKey)
    (priorTree : TreeIndex) (priorLeaf : LeafIndex) (index : Index)
    (signature : SphincsSecurity.Signature) (first : Digest)
    (pointer : Word)
    (loaded : initialState SphincsSubmission.submission .verify
      (inputMessage, publicKey, SphincsWireEncoding.wire pk signature) = some initial)
    (frame : ∀ address, address.toNat < 0x40000 →
      state.getByte address = initial.getByte address)
    (pc : state.pc = SphincsVerifierXmssParity.nodePc
      (SphincsVerifierXmssTransition.previousLayer target))
    (pointerValue : state.getMem 0x43028 = pointer)
    (pointerBound : pointer.toNat + 20 * layerHeight
      (SphincsVerifierXmssTransition.previousLayer target) ≤ 0x40000)
    (pointerAligned : pointer.toNat % 4 = 0)
    (layerCell : state.getMem 0x43000 = BitVec.ofNat 64
      (SphincsVerifierXmssTransition.previousLayer target).val)
    (priorTreeCell : state.getMem 0x43008 = BitVec.ofNat 64 priorTree.val)
    (levelCell : state.getMem 0x43048 = 1)
    (bitCell : state.getMem 0x43070 = BitVec.ofNat 64 priorLeaf.val)
    (global : state.getMem 0x43078 = BitVec.ofNat 64 index.val)
    (hprefix : SphincsVerifierHashBytes.WitnessPrefix state pk)
    (current : ∀ i, (hi : i < 20) →
      state.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        first.extractLsb' (8 * i) 8)
    (siblings : SphincsVerifierXmssPathControl.PathWitness state signature
      (SphincsVerifierXmssTransition.previousLayer target) pointer) :
    let previous := SphincsVerifierXmssTransition.previousLayer target
    let lay := SphincsVerifierXmssTransition.targetLayer target
    let pathEnd := SphincsVerifierXmssPathControl.pathState hash previous
      (layerHeight previous) state
    let nextState := SphincsVerifierXmssTransitionMessage.handoffState target pathEnd
    hashInput (upperPrehashState target nextState) =
      toQuery (firstUpperEncodingInput pk lay
        (SphincsSecurity.Concrete.treeIndexAt index lay)
        (SphincsSecurity.Concrete.leafIndexAt index lay)
        (SphincsSecurity.Concrete.foldValue (adaptOracle hash) pk.parameter
          previous priorTree priorLeaf
          (SphincsSecurity.Concrete.signaturePath signature previous)
          first (layerHeight previous))
        (signature.layers lay).counter) := by
  let previous := SphincsVerifierXmssTransition.previousLayer target
  let lay := SphincsVerifierXmssTransition.targetLayer target
  let pathEnd := SphincsVerifierXmssPathControl.pathState hash previous
    (layerHeight previous) state
  let nextState := SphincsVerifierXmssTransitionMessage.handoffState target pathEnd
  have root := (SphincsVerifierXmssTransitionComplete.complete_path_handoff
    hash target state pk priorTree priorLeaf signature first pointer pc
    pointerValue pointerBound pointerAligned layerCell priorTreeCell levelCell
    bitCell hprefix current siblings).2
  have frameNext : ∀ address, address.toNat < 0x40000 →
      nextState.getByte address = initial.getByte address := by
    intro address low
    exact upper_path_handoff_low_frame target hash initial state frame
      address low
  have pathPc := (SphincsVerifierXmssPathComplete.complete_path hash previous
    state pk priorTree priorLeaf signature first pointer pc pointerValue
    pointerBound pointerAligned layerCell priorTreeCell levelCell bitCell
    hprefix current siblings).1
  have transitionPc : pathEnd.pc =
      SphincsVerifierXmssTransition.transitionPc target := by
    simpa [pathEnd, previous,
      SphincsVerifierXmssTransition.transitionPc] using pathPc
  have nextPc : nextState.pc = upperPrefixPc target := by
    calc
      _ = SphincsVerifierXmssTransitionMessage.messagePc target + 56 :=
        upper_handoff_prefix_pc target pathEnd transitionPc
      _ = upperPrefixPc target := by fin_cases target <;> decide
  have controls := upper_handoff_control_cells target pathEnd
  have nextLayer : nextState.getMem 0x43000 = BitVec.ofNat 64 lay.val := by
    exact controls.1
  have positionZero := upper_handoff_position_zero target pathEnd
  have pathGlobal : pathEnd.getMem 0x43078 = BitVec.ofNat 64 index.val :=
    (path_global_index_cell hash previous (layerHeight previous) state).trans
      global
  have indexCells := upper_handoff_index_cells target pathEnd index pathGlobal
  have witness := loaded_upper_prefix_after_frame publicKey inputMessage pk
    signature initial nextState loaded frameNext
  exact upper_encoding_query_after_frame target publicKey inputMessage pk
    signature initial nextState loaded frameNext lay
    (SphincsSecurity.Concrete.treeIndexAt index lay)
    (SphincsSecurity.Concrete.leafIndexAt index lay) _ nextPc
    nextLayer positionZero indexCells.1 indexCells.2 witness root

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_path_handoff_low_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_path_handoff_low_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_encoding_query_after_previous_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_encoding_query_after_previous_path

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_encoding_query_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_encoding_query_of_parts


/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_handoff_control_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_handoff_control_cells

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_handoff_decoder_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_handoff_decoder_gap

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.loaded_next_upper_witness_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_next_upper_witness_inputs

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_decoder_path_handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_decoder_path_handoff

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_ready_low_byte_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_ready_low_byte_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.pathWitness_of_low_frame' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms pathWitness_of_low_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.loaded_upper_path_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_upper_path_witness

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.loaded_upper_chain_source_after_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_upper_chain_source_after_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.loaded_upper_prefix_after_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_upper_prefix_after_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.pathWitness_of_low_byte_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pathWitness_of_low_byte_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.loaded_upper_path_witness_after_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_upper_path_witness_after_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_handoff_low_byte_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_handoff_low_byte_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_handoff_path_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_handoff_path_witness

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_path_pointer_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_path_pointer_bound

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_path_pointer_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_path_pointer_aligned

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_path_node_pc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_path_node_pc

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_decoder_path_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_decoder_path_digest

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_ready_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_ready_source

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_chains_from_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_chains_from_ready

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_prepare_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_prepare_trace

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_decoder_chains_semantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_decoder_chains_semantics

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_rootCopy_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_rootCopy_payload

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.rootCopySetup_mem_other' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms rootCopySetup_mem_other

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.rootCopySetup_position_zero' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms rootCopySetup_position_zero

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.witnessPrefix_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms witnessPrefix_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.leaf_copy_dest_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms leaf_copy_dest_other

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.leaf_copy_context_of_frame' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms leaf_copy_context_of_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_leaf_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_leaf_query

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.xmssInit_current_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms xmssInit_current_byte

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.leaf_copy_path_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms leaf_copy_path_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.leafHashNext_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms leafHashNext_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.leaf_finish_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms leaf_finish_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.leaf_finish_bit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms leaf_finish_bit

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.leaf_finish_semantic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms leaf_finish_semantic

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.runSchedule_schedule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms runSchedule_schedule

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.leafHashReady_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms leafHashReady_shift

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_leaf_finish_semantic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_leaf_finish_semantic

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_leaf_from_endpoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_leaf_from_endpoints

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_decoder_leaf_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_decoder_leaf_digest

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_chains_semantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms upper_chains_semantics

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_prehash_counter_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_prehash_counter_word

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_parameter_copied_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_parameter_copied_bytes

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_prehash_parameter_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_prehash_parameter_byte

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_prehash_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_prehash_parameter

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_prehash_payload_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_prehash_payload_byte

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_prehash_counter_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_prehash_counter_bytes

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_header_tag_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_header_tag_word

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_header_position_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_header_position_word

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_header_tree_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_header_tree_word

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_header_index_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_header_index_word

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_prehash_header_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_prehash_header_byte

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_handoff_position_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_handoff_position_zero

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_header_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_header_bytes

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_prehash_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_prehash_header

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_encoding_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_encoding_query

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.loaded_first_upper_counter_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_first_upper_counter_word

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_counter_word_after_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_counter_word_after_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.honest_first_upper_counter_word_after_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_first_upper_counter_word_after_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_handoff_low_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_handoff_low_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.honest_first_upper_handoff_counter_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_first_upper_handoff_counter_word

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_honest_counter_small' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_honest_counter_small

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_encoding_query_after_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_encoding_query_after_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_handoff_root_and_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_handoff_root_and_frame

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_encoding_query_after_previous_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_encoding_query_after_previous_path

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_handoff_index_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_handoff_index_cells

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.round_global_index_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms round_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.path_global_index_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms path_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_handoff_global_index_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_handoff_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_path_handoff_global_index_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_path_handoff_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.decoder_step_global_index_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decoder_step_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.decoder_run_global_index_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decoder_run_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_decoder_global_index_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_decoder_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_setup_global_index_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_setup_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_handoff_global_index_from_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upper_handoff_global_index_from_input

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.chain_end_global_index_cell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chain_end_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.leaf_copy_global_index_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_copy_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.leafHashNext_global_index_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leafHashNext_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.xmssInit_global_index_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssInit_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.leaf_finish_global_index_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_finish_global_index_cell

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.first_upper_encoding_query_with_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_upper_encoding_query_with_index

end SigGolfCandidate.SphincsVerifierWotsSemanticRelocation
