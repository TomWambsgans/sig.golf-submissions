import SigGolfCandidate.SphincsVerifierWotsSemanticEntry
import SigGolfCandidate.SphincsVerifierWotsEndpointFrame

namespace SigGolfCandidate.SphincsVerifierWotsSemanticAllChains
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierWotsChainEnd
open SigGolfCandidate.SphincsVerifierWotsChainEntry
open SigGolfCandidate.SphincsVerifierWotsEndpointFrame
open SigGolfCandidate.SphincsVerifierWotsEndpointCopy
open SigGolfCandidate.SphincsVerifierWotsSemanticFrame
open SigGolfCandidate.SphincsVerifierWotsStepIteration
open SigGolfCandidate.SphincsVerifierWotsSemanticWalk
open SigGolfCandidate.SphincsVerifierWotsSemanticChain
open SigGolfCandidate.SphincsVerifierWotsSemanticEntry
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
open SigGolfCandidate.SphincsBridge
open OracleComp
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierWotsLoop
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- Copying a completed endpoint cannot change an input-witness byte. -/
theorem chainEnd_lowFrame (state : MachineState) (chain : Fin 52)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (address : Word) (low : address.toNat < 0x40000) :
    (chainEndState state).getMem address = state.getMem address := by
  let pointers := endpointSourceState (endpointPointersState state)
  have destination : pointers.getReg .x7 =
      BitVec.ofNat 64 (0x44300 + 20 * chain.val) := by
    simpa [pointers, endpointSourceState, execInstrBr,
      MachineState.getReg_setReg_ne] using
        endpointPointers_regs state chain counter
  have copyFrame := copyRoot_mem_frame pointers address (by
    intro offset
    rw [destination]
    apply safe_ne address (Or.inl low)
    right
    left
    fin_cases chain <;> fin_cases offset <;> decide)
  have pointerFrame : pointers.getMem address = state.getMem address := by
    simp [pointers, endpointSourceState, endpointPointersState, execInstrBr]
  have distinctPointer : address ≠ 0x43028 := by
    intro equal
    have := congrArg BitVec.toNat equal
    simp at this
    omega
  have distinctCounter : address ≠ 0x43050 := by
    intro equal
    have := congrArg BitVec.toNat equal
    simp at this
    omega
  have advanceFrame :
      (chainBranchState (chainAdvanceState
        (pointerAdvanceState (copyRootState pointers)))).getMem address =
          (copyRootState pointers).getMem address := by
    simp [chainBranchState, chainAdvanceState, pointerAdvanceState,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    split_ifs with equal1 equal2
    · exact (distinctCounter equal1).elim
    · exact (distinctPointer equal2).elim
    · rfl
  exact advanceFrame.trans (copyFrame.trans pointerFrame)

def ContextAddr (address : Word) : Prop :=
  address = 0x43000 ∨ address = 0x43008 ∨ address = 0x43018

theorem chainEnd_contextFrame (state : MachineState) (chain : Fin 52)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (address : Word) (context : ContextAddr address) :
    (chainEndState state).getMem address = state.getMem address := by
  let pointers := endpointSourceState (endpointPointersState state)
  have destination : pointers.getReg .x7 =
      BitVec.ofNat 64 (0x44300 + 20 * chain.val) := by
    simpa [pointers, endpointSourceState, execInstrBr,
      MachineState.getReg_setReg_ne] using
        endpointPointers_regs state chain counter
  have copyFrame := copyRoot_mem_frame pointers address (by
    intro offset
    rw [destination]
    rcases context with rfl | rfl | rfl <;>
      fin_cases chain <;> fin_cases offset <;> decide)
  have pointerFrame : pointers.getMem address = state.getMem address := by
    simp [pointers, endpointSourceState, endpointPointersState, execInstrBr]
  have distinctPointer : address ≠ 0x43028 := by
    rcases context with rfl | rfl | rfl <;> decide
  have distinctCounter : address ≠ 0x43050 := by
    rcases context with rfl | rfl | rfl <;> decide
  have advanceFrame :
      (chainBranchState (chainAdvanceState
        (pointerAdvanceState (copyRootState pointers)))).getMem address =
          (copyRootState pointers).getMem address := by
    simp [chainBranchState, chainAdvanceState, pointerAdvanceState,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    split_ifs with equal1 equal2
    · exact (distinctCounter equal1).elim
    · exact (distinctPointer equal2).elim
    · rfl
  exact advanceFrame.trans (copyFrame.trans pointerFrame)

def StableAddr (address : Word) : Prop :=
  address.toNat < 0x40000 ∨ ScratchAddr address

theorem stepRound_stableFrame (hash : Hash) (state : MachineState)
    (address : Word) (stable : StableAddr address) :
    (stepRound hash state).getMem address = state.getMem address := by
  rcases stable with low | scratch
  · rw [stepRound]
    exact (stepNext_safeFrame hash
      (SphincsVerifierWotsStepCheck.stepCheckState state) address
      (Or.inl low)).trans (stepCheck_mem state address)
  · exact stepRound_scratchFrame hash state address scratch

theorem chainEntry_stableFrame (state : MachineState)
    (address : Word) (stable : StableAddr address) :
    (chainEntryState state).getMem address = state.getMem address := by
  rcases stable with low | scratch
  · exact chainEntry_safeFrame state address (Or.inl low)
  · exact chainEntry_scratchFrame state address scratch

/-- The semantic WOTS loop also leaves all witness bytes and prior endpoints intact. -/
theorem walkInv_loop_stable (hash : Hash) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (start : Fin 8) (initial : Digest)
    (sourceBase : Nat)
    (state : MachineState)
    (initialInv : WalkInv hash pk layer tree leaf chain start initial sourceBase 0 state) :
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      WalkInv hash pk layer tree leaf chain start initial sourceBase
        (7 - start.val) final ∧
      (∀ address, StableAddr address →
        final.getMem address = state.getMem address) ∧
      steps ≤ 94 * (7 - start.val) ∧
      cycles ≤ 101 * (7 - start.val) ∧
      calls ≤ 7 - start.val ∧
      blocks ≤ 7 - start.val ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  let Inv : Nat → MachineState → Prop := fun i current =>
    WalkInv hash pk layer tree leaf chain start initial sourceBase i current ∧
    ∀ address, StableAddr address →
      current.getMem address = state.getMem address
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
        BitVec.ofNat 64 digit.val := inv.1.stepCell
    refine ⟨stepRound hash current, 94, 101, 1, 1,
      ⟨walkInv_step hash pk layer tree leaf chain start initial sourceBase i
          current small inv.1, ?_⟩,
      by decide, by decide, by decide, by decide, ?_⟩
    · intro address stable
      exact (stepRound_stableFrame hash current address stable).trans
        (inv.2 address stable)
    · intro tailSteps result tail
      exact stepRound_exec hash current digit inv.1.pc currentCell
        digitSmall tailSteps result tail
  obtain ⟨final, steps, cycles, calls, blocks, finalInv,
    stepBound, cycleBound, callBound, blockBound, run⟩ :=
    bounded_loop hash SphincsImages.verify Inv (7 - start.val)
      94 101 1 1 next 0 (7 - start.val) state
      (by omega) ⟨initialInv, by intro address _; rfl⟩
  refine ⟨final, steps, cycles, calls, blocks, ?_, finalInv.2,
    stepBound, cycleBound, ?_, ?_, run⟩
  · simpa only [Nat.zero_add] using finalInv.1
  · simpa only [one_mul] using callBound
  · simpa only [one_mul] using blockBound

/-- One complete WOTS chain writes its abstract endpoint and preserves every other chain slot. -/
theorem chainRound_recover (hash : Hash) (state : MachineState)
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
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc = (if chain.val + 1 = 52 then 0x298c else 0x2710) ∧
      final.getMem 0x43050 = BitVec.ofNat 64 (chain.val + 1) ∧
      final.getMem 0x43028 =
        BitVec.ofNat 64 (base + 20 * (chain.val + 1)) ∧
      final.getMem 0x43000 = BitVec.ofNat 64 layer.val ∧
      final.getMem 0x43008 = BitVec.ofNat 64 tree.val ∧
      final.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
      (∀ address, address.toNat < 0x40000 →
        final.getMem address = state.getMem address) ∧
      (∀ address, SphincsVerifierWotsDigitFrame.DigitAddr address →
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
      calls ≤ 7 - digit.val ∧
      blocks ≤ 7 - digit.val ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
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
  obtain ⟨seven, steps, cycles, calls, blocks, finalInv, stable,
    stepBound, cycleBound, callBound, blockBound, run⟩ :=
    walkInv_loop_stable hash pk layer tree leaf chain digit initial base
      (chainEntryState state) initialInv
  have cell : seven.getMem 0x43058 = 7 := by
    simpa [show digit.val + (7 - digit.val) = 7 by
      have := digit.isLt; omega] using finalInv.stepCell
  have checked := SphincsVerifierWotsStepCheck.stepCheck_block
    seven ⟨7, by decide⟩ finalInv.pc (by simpa using cell)
  let middle := SphincsVerifierWotsStepCheck.stepCheckState seven
  have middleFrame (address : Word) (inside : StableAddr address) :
      middle.getMem address = state.getMem address := by
    exact (stepCheck_mem seven address).trans
      ((stable address inside).trans
        (chainEntry_stableFrame state address inside))
  have middleCounter : middle.getMem 0x43050 =
      BitVec.ofNat 64 chain.val := by
    rw [stepCheck_mem]
    exact finalInv.chainCell
  have middlePointer : middle.getMem 0x43028 =
      BitVec.ofNat 64 (base + 20 * chain.val) := by
    rw [stepCheck_mem]
    exact finalInv.pointerCell
  have middleValue (i : Nat) (hi : i < 20) :
      middle.getByte (BitVec.ofNat 64 (0x44b00 + i)) =
        (evalWithAnswerFn (adaptOracle hash)
          (Concrete.recoverChain pk.parameter layer tree leaf chain digit initial)).extractLsb'
            (8 * i) 8 := by
    rw [stepCheck_byte]
    exact walkInv_recoverChain hash pk layer tree leaf chain digit
      initial base seven finalInv i hi
  obtain ⟨endTrace, endPc, endCounter⟩ :=
    chainEnd_block middle chain (by simpa [middle] using checked.2)
      middleCounter
  have endPointer := SphincsVerifierWotsChainEndGeneral.chainEnd_pointer_general
    middle chain base middleCounter middlePointer
  have context (address : Word) (inside : ContextAddr address) :
      (chainEndState middle).getMem address = middle.getMem address :=
    chainEnd_contextFrame middle chain middleCounter address inside
  have lowFrame (address : Word) (low : address.toNat < 0x40000) :
      (chainEndState middle).getMem address = state.getMem address :=
    (chainEnd_lowFrame middle chain middleCounter address low).trans
      (middleFrame address (Or.inl low))
  have digitFrame (address : Word)
      (inside : SphincsVerifierWotsDigitFrame.DigitAddr address) :
      (chainEndState middle).getMem address = state.getMem address := by
    have scratch : ScratchAddr address := by
      dsimp [ScratchAddr, SphincsVerifierWotsDigitFrame.DigitAddr] at *
      omega
    exact (SphincsVerifierWotsDigitFrame.chainEnd_digitFrame middle chain
      middleCounter address inside).trans (middleFrame address (Or.inr scratch))
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
  refine ⟨chainEndState middle, steps + 70, cycles + 70,
    calls, blocks, endPc, endCounter, endPointer, ?_, ?_, ?_,
    lowFrame, digitFrame, otherFrame, endpointByte,
    by omega, by omega, callBound, blockBound, ?_⟩
  · rw [context 0x43000 (Or.inl rfl), stepCheck_mem]
    exact finalInv.layerCell
  · rw [context 0x43008 (Or.inr (Or.inl rfl)), stepCheck_mem]
    exact finalInv.treeCell
  · rw [context 0x43018 (Or.inr (Or.inr rfl)), stepCheck_mem]
    exact finalInv.leafCell
  · intro tailSteps result tail
    have after := endTrace.then_executes tail
    have middleRun := checked.1.then_executes after
    have middleRun' : Executes hash SphincsImages.verify seven
        (tailSteps + 45) (result.charge 45 0 0) := by
      simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using middleRun
    have before := run (tailSteps + 45) (result.charge 45 0 0) middleRun'
    have full := entry.1.then_executes before
    simpa [Execution.charge, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using full

theorem lowByteFrame (initial current : MachineState)
    (frame : ∀ address, address.toNat < 0x40000 →
      current.getMem address = initial.getMem address)
    (address : Word) (small : address.toNat < 0x40000) :
    current.getByte address = initial.getByte address := by
  have aligned : (alignToDword address).toNat < 0x40000 := by
    have le : (alignToDword address).toNat ≤ address.toNat := by
      unfold alignToDword
      rw [BitVec.toNat_and]
      exact Nat.and_le_left
    omega
  simpa only [MachineState.getByte] using
    congrArg (fun value : Word => extractByte value (byteOffset address))
      (frame (alignToDword address) aligned)

theorem sourceByteSmall (base : Nat) (baseBound : base + 20 * 52 ≤ 0x40000)
    (chain : Fin 52) (i : Nat) (hi : i < 20) :
    (BitVec.ofNat 64 (base + 20 * chain.val + i)).toNat < 0x40000 := by
  have hc : chain.val < 52 := by exact chain.isLt
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem digitByteFrame (initial current : MachineState)
    (frame : ∀ address, SphincsVerifierWotsDigitFrame.DigitAddr address →
      current.getMem address = initial.getMem address)
    (chain : Fin 52) :
    current.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) =
      initial.getByte (BitVec.ofNat 64 (0x44000 + chain.val)) := by
  let address : Word := BitVec.ofNat 64 (0x44000 + chain.val)
  have inside : SphincsVerifierWotsDigitFrame.DigitAddr
      (alignToDword address) := by
    unfold SphincsVerifierWotsDigitFrame.DigitAddr
    fin_cases chain <;> decide
  simpa only [MachineState.getByte] using
    congrArg (fun value : Word => extractByte value (byteOffset address))
      (frame (alignToDword address) inside)

private structure History (hash : Hash)
    (initial : MachineState) (pk : SphincsSecurity.PublicKey)
    (layer : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (digits : ChainIndex → Fin 8) (values : ChainIndex → Digest)
    (base : Nat)
    (i : Nat) (current : MachineState) : Prop where
  pc : current.pc = (if i = 52 then 0x298c else 0x2710)
  counter : current.getMem 0x43050 = BitVec.ofNat 64 i
  pointer : current.getMem 0x43028 = BitVec.ofNat 64 (base + 20 * i)
  layerCell : current.getMem 0x43000 = BitVec.ofNat 64 layer.val
  treeCell : current.getMem 0x43008 = BitVec.ofNat 64 tree.val
  leafCell : current.getMem 0x43018 = BitVec.ofNat 64 leaf.val
  lowFrame : ∀ address, address.toNat < 0x40000 →
    current.getMem address = initial.getMem address
  digitFrame : ∀ address, SphincsVerifierWotsDigitFrame.DigitAddr address →
    current.getMem address = initial.getMem address
  endpoints : ∀ chain : ChainIndex, chain.val < i → ∀ j, (hj : j < 20) →
    current.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + j)) =
      (evalWithAnswerFn (adaptOracle hash)
        (Concrete.recoverChain pk.parameter layer tree leaf chain
          (digits chain) (values chain))).extractLsb' (8 * j) 8

/-- One bounded induction identifies all 52 stored WOTS endpoints with abstract recovery. -/
theorem allChains_recover (hash : Hash) (state : MachineState)
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
    ∃ (final : MachineState) (steps cycles calls blocks : Nat),
      final.pc = 0x298c ∧
      final.getMem 0x43050 = 52 ∧
      final.getMem 0x43028 = BitVec.ofNat 64 (base + 20 * 52) ∧
      (∀ (chain : ChainIndex) (j : Nat), (hj : j < 20) →
        final.getByte (BitVec.ofNat 64 (0x44300 + 20 * chain.val + j)) =
          (evalWithAnswerFn (adaptOracle hash)
            (Concrete.recoverChain pk.parameter layer tree leaf chain
              (digits chain) (values chain))).extractLsb' (8 * j) 8) ∧
      (∀ address, address.toNat < 0x40000 →
        final.getMem address = state.getMem address) ∧
      steps ≤ 728 * 52 ∧ cycles ≤ 777 * 52 ∧
      calls ≤ 7 * 52 ∧ blocks ≤ 7 * 52 ∧
      ∀ (tailSteps : Nat) (result : Execution),
        Executes hash SphincsImages.verify final tailSteps result →
        Executes hash SphincsImages.verify state (tailSteps + steps)
          (result.charge cycles calls blocks) := by
  let Inv := History hash state pk layer tree leaf digits values base
  have next (i : Nat) (current : MachineState)
      (small : i < 52) (inv : Inv i current) :
      ∃ (following : MachineState) (steps cycles calls blocks : Nat),
        Inv (i + 1) following ∧
        steps ≤ 728 ∧ cycles ≤ 777 ∧ calls ≤ 7 ∧ blocks ≤ 7 ∧
        ∀ (tailSteps : Nat) (result : Execution),
          Executes hash SphincsImages.verify following tailSteps result →
          Executes hash SphincsImages.verify current (tailSteps + steps)
            (result.charge cycles calls blocks) := by
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
    obtain ⟨following, a, b, c, d, nextPc, nextCounter, nextPointer,
      nextLayer, nextTree, nextLeaf, nextLow, nextDigit, otherSlots,
      newEndpoint, stepBound, cycleBound, callBound, blockBound, run⟩ :=
      chainRound_recover hash current pk layer tree leaf chain digit
        (values chain) base baseBound baseAligned
        currentPc currentPointer currentCounter currentDigit
        inv.layerCell inv.treeCell inv.leafCell currentPrefix currentValue
    refine ⟨following, a, b, c, d, ?_, by
      have hd := digit.isLt; omega, by
      have hd := digit.isLt; omega, by omega, by omega, run⟩
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
          (by
            have ho : other.val < 52 := by simpa [numChains] using other.isLt
            omega)
          (by
            have ho : other.val < 52 := by simpa [numChains] using other.isLt
            omega)
          (by simp [Nat.add_mod, Nat.mul_mod])
          (by simp [Nat.add_mod, Nat.mul_mod])
          (fun index => otherSlots other index (by
            intro eq
            exact same eq.symm)) j hj
        exact transferred.trans oldValue
  obtain ⟨final, steps, cycles, calls, blocks, inv,
    stepBound, cycleBound, callBound, blockBound, run⟩ :=
    bounded_loop hash SphincsImages.verify Inv 52
      728 777 7 7 next 0 52 state (by decide)
      ⟨by simpa [Inv, History] using pc,
       by simpa [Inv, History] using counter,
       by simpa [Inv, History] using pointer,
       layerCell, treeCell, leafCell,
       by intro address _; rfl,
       by intro address _; rfl,
       by intro chain impossible; omega⟩
  refine ⟨final, steps, cycles, calls, blocks,
    by simpa [Inv, History] using inv.pc,
    by simpa using inv.counter,
    by simpa using inv.pointer,
    ?_, inv.lowFrame, stepBound, cycleBound,
    callBound, blockBound, run⟩
  intro chain j hj
  exact inv.endpoints chain (by
    have h := chain.isLt
    simpa [numChains] using h) j hj

#print axioms allChains_recover

#print axioms chainEnd_lowFrame
#print axioms chainEnd_contextFrame
#print axioms walkInv_loop_stable
#print axioms chainRound_recover

end SigGolfCandidate.SphincsVerifierWotsSemanticAllChains
