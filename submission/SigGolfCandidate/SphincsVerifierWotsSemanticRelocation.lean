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
    lowFrame, digitFrame, otherFrame, endpointByte,
    by omega, by omega, by omega, by omega, ?_⟩
  · rw [context 0x43000 (Or.inl rfl)]; exact middleLayer
  · rw [context 0x43008 (Or.inr (Or.inl rfl))]; exact middleTree
  · rw [context 0x43018 (Or.inr (Or.inr (Or.inl rfl)))]; exact middleLeaf
  · rw [context 0x43020 (Or.inr (Or.inr (Or.inr rfl)))]
    exact middleFrame 0x43020
      (Or.inl (Or.inr ⟨by decide, by decide, by decide, by decide⟩))
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
      nextPointer, nextLayer, nextTree, nextLeaf, nextBit, nextLow, nextDigit,
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
       layerCell, treeCell, leafCell, rfl,
       by intro address _; rfl,
       by intro address _; rfl,
       by intro chain impossible; omega⟩
  refine ⟨final, steps, cycles, calls, blocks, run,
    by simpa [Inv, History] using inv.pc,
    by simpa using inv.counter,
    by simpa using inv.pointer,
    inv.layerCell, inv.treeCell, inv.leafCell, inv.bitCell,
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
    sourcePointer, layerFinal, treeFinal, leafFinal, bitFinal, valuesDone, lowFrame,
    stepBound, cycleBound, callBound, blockBound, inside⟩ :=
    all_chains_inside_semantics hash state pk layer tree leaf digits values
      base baseBound baseAligned pc counter pointer layerCell treeCell
      leafCell hprefix decoded source
  refine ⟨shift (delta target) final, steps, cycles, calls, blocks,
    trace_shift target hash run inside, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    stepBound, cycleBound, callBound, blockBound⟩
  · simp [shift_pc, done]
  · simpa using count
  · simpa using sourcePointer
  · simpa using layerFinal
  · simpa using treeFinal
  · simpa using leafFinal
  · simpa using bitFinal
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
    finalPrefix, lowFrame, endpoints,
    stepBound, cycleBound, callBound, blockBound⟩ :=
    upper_chains_from_ready target hash ready pk layer tree leaf digits values
      (by simpa only [readyEq] using preparedPc)
      (by simpa only [readyEq] using preparedCounter)
      (by simpa only [readyEq] using preparedPointer)
      layerCell treeCell leafCell readyPrefix decoded readySource
  refine ⟨final, 507 + steps, 507 + cycles, calls, blocks,
    ?_, done, pointerFinal, layerFinal, treeFinal, leafFinal, bitFinal,
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
  refine ⟨final, run, done, ?_, ?_, ?_, ?_, inside⟩
  · intro i hi
    rw [exact, xmssInit_current_byte _ i hi,
      SphincsVerifierWotsLeafResult.leafHashNext_byte_of_query
        hash state _ query i hi, abstract]
  · rw [exact]
    exact SphincsVerifierXmssInit.xmssInit_level _
  · rw [exact]
    exact leaf_finish_bit hash state
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
  obtain ⟨finish, run, done, digest, level, bit, frame, inside⟩ :=
    leaf_finish_semantic hash base pk layer tree leaf endpoints basePc baseQuery
  refine ⟨shift (delta target) finish, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [restored] using trace_shift target hash run inside
  · rw [shift_pc, done]
  · intro i hi
    simpa using digest i hi
  · simpa only [shift_mem] using level
  · simpa only [shift_mem, base] using bit
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
      (∀ read, LeafPathRetained read →
        final.getMem read = state.getMem read) := by
  obtain ⟨copied, copyRun, copiedPc, query,
    _layerFinal, _treeFinal, _leafFinal, _prefixFinal, copyFrame⟩ :=
    upper_leaf_query target hash state pk layer tree leaf endpoints
      pc layerCell treeCell leafCell hprefix values
  obtain ⟨final, finishRun, done, digest, level, bit, finishFrame⟩ :=
    upper_leaf_finish_semantic target hash copied pk layer tree leaf endpoints
      copiedPc query
  refine ⟨final, ?_, done, digest, level, ?_, ?_⟩
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
      SphincsVerifierHashBytes.WitnessPrefix final pk ∧
      (∀ address, address.toNat < 0x40000 →
        final.getMem address = ready.getMem address) ∧
      steps ≤ 507 + 728 * 52 + 856 ∧
      cycles ≤ 507 + 777 * 52 + 991 ∧
      calls ≤ 7 * 52 + 1 ∧ blocks ≤ 7 * 52 + 17 := by
  obtain ⟨chains, chainSteps, chainCycles, chainCalls, chainBlocks,
    chainRun, chainsPc, pointerFinal, layerFinal, treeFinal, leafFinal, bitFinal,
    prefixFinal, lowFrame, endpointBytes, stepBound, cycleBound,
    callBound, blockBound⟩ :=
    upper_decoder_chains_semantics target hash state ready pk layer tree leaf
      digits values readyEq pc checksum layerCell treeCell leafCell decoded
      hprefix source
  let recovered : ChainIndex → Digest := fun chain =>
    evalWithAnswerFn (adaptOracle hash)
      (Concrete.recoverChain pk.parameter layer tree leaf chain
        (digits chain) (values chain))
  obtain ⟨final, leafRun, done, digest, level, bitDone, leafFrame⟩ :=
    upper_leaf_from_endpoints target hash chains pk layer tree leaf recovered
      chainsPc layerFinal treeFinal leafFinal prefixFinal
      (by intro chain j hj; exact endpointBytes chain j hj)
  refine ⟨final, chainSteps + 856, chainCycles + 991,
    chainCalls + 1, chainBlocks + 17, ?_, done, ?_, ?_, ?_, digest, level,
    bitDone.trans bitFinal, ?_, ?_,
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
    layerFinal, treeFinal, current, level, bit, prefixFinal, lowFrame,
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
    path.1, path.2.1, path.2.2, endFrame⟩

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
    donePc, rootBytes, _pathCycleBound, pathFrame⟩ :=
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
    stepBound, cycleBound, callBound, blockBound, handoff, ?_, ?_, lowFrame, ?_⟩
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

end SigGolfCandidate.SphincsVerifierWotsSemanticRelocation
