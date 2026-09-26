import SigGolfCandidate.SphincsVerifierXmssTransition
import SigGolfCandidate.SphincsMaskedKeygenPadding

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
      (middleFrame address (Or.inl low))
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
    endPc, endCounter, endPointer, ?_, ?_, ?_,
    lowFrame, digitFrame, otherFrame, endpointByte,
    by omega, by omega, by omega, by omega, ?_⟩
  · rw [context 0x43000 (Or.inl rfl)]; exact middleLayer
  · rw [context 0x43008 (Or.inr (Or.inl rfl))]; exact middleTree
  · rw [context 0x43018 (Or.inr (Or.inr rfl))]; exact middleLeaf
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
      nextPointer, nextLayer, nextTree, nextLeaf, nextLow, nextDigit,
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
       layerCell, treeCell, leafCell,
       by intro address _; rfl,
       by intro address _; rfl,
       by intro chain impossible; omega⟩
  refine ⟨final, steps, cycles, calls, blocks, run,
    by simpa [Inv, History] using inv.pc,
    by simpa using inv.counter,
    by simpa using inv.pointer,
    inv.layerCell, inv.treeCell, inv.leafCell,
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
    sourcePointer, layerFinal, treeFinal, leafFinal, valuesDone, lowFrame,
    stepBound, cycleBound, callBound, blockBound, inside⟩ :=
    all_chains_inside_semantics hash state pk layer tree leaf digits values
      base baseBound baseAligned pc counter pointer layerCell treeCell
      leafCell hprefix decoded source
  refine ⟨shift (delta target) final, steps, cycles, calls, blocks,
    trace_shift target hash run inside, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    stepBound, cycleBound, callBound, blockBound⟩
  · simp [shift_pc, done]
  · simpa using count
  · simpa using sourcePointer
  · simpa using layerFinal
  · simpa using treeFinal
  · simpa using leafFinal
  · intro chain j hj
    simpa using valuesDone chain j hj
  · intro address low
    simpa using lowFrame address low

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
      final.getMem 0x43000 = BitVec.ofNat 64 layer.val ∧
      final.getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
      final.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
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
    _counter, _pointer, layerFinal, treeFinal, leafFinal, endpoints, _lowFrame,
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
  refine ⟨final, steps, cycles, calls, blocks, ?_, finalPc,
    layerFinal, treeFinal, leafFinal, endpoints,
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
      final.getMem 0x43000 = BitVec.ofNat 64 layer.val ∧
      final.getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
      final.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
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
    done, layerFinal, treeFinal, leafFinal, endpoints,
    stepBound, cycleBound, callBound, blockBound⟩ :=
    upper_chains_from_ready target hash ready pk layer tree leaf digits values
      (by simpa only [readyEq] using preparedPc)
      (by simpa only [readyEq] using preparedCounter)
      (by simpa only [readyEq] using preparedPointer)
      layerCell treeCell leafCell readyPrefix decoded readySource
  refine ⟨final, 507 + steps, 507 + cycles, calls, blocks,
    ?_, done, layerFinal, treeFinal, leafFinal, endpoints,
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

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_ready_low_byte_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms upper_ready_low_byte_frame

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

/-- info: 'SigGolfCandidate.SphincsVerifierWotsSemanticRelocation.upper_chains_semantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms upper_chains_semantics

end SigGolfCandidate.SphincsVerifierWotsSemanticRelocation
