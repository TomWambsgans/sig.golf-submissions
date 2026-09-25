import SigGolfCandidate.SphincsVerifierFtsFinishNextSetup

namespace SigGolfCandidate.SphincsVerifierFtsNextReadyControls
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsNextTreeSetup
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolfCandidate.SphincsVerifierFtsAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierFtsPathAddress
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem nextTreeHashState_controls (state : MachineState)
    (tree : FtsTree) (index : Index) (leaf : FtsLeaf)
    (statePc : state.pc = 0x173c)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (source : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x22cdc + 180 * tree.val))
    (indexCell : state.getMem 0x43078 = BitVec.ofNat 64 index.val)
    (selectorByte : state.getByte
      (BitVec.ofNat 64 (0x44800 + tree.val)) =
        BitVec.ofNat 8 leaf.val) :
    let ready := nextTreeHashState state
    ready.pc = 0x18c8 ∧
      ready.getReg .x10 = 0x40000 ∧
      ready.getReg .x11 = 480 ∧
      ready.getReg .x12 = 0x42000 ∧
      ready.getReg .x5 = 1 ∧
      ready.getMem 0x43040 = BitVec.ofNat 64 tree.val ∧
      ready.getMem 0x43000 = BitVec.ofNat 64 tree.val ∧
      ready.getMem 0x43008 = BitVec.ofNat 64 index.val ∧
      ready.getMem 0x43070 = BitVec.ofNat 64 leaf.val ∧
      ready.getMem 0x43028 =
        BitVec.ofNat 64 (pathAddress tree ⟨0, by decide⟩) := by
  let header := ftsTreeHeaderState state
  let selected := ftsSelectState header
  let pointers := ftsCopyPointers selected
  let copied := SphincsVerifierCopy.copyRootState pointers
  let advanced := ftsAdvanceState copied
  have pc : (nextTreeHashState state).pc = 0x18c8 := by
    exact nextTreeSetup_pc state statePc
  have regs := nextTreeSetup_hash_regs state
  have headerCounter : header.getMem 0x43040 = BitVec.ofNat 64 tree.val := by
    rw [ftsTreeHeader_mem_frame state 0x43040 (by decide) (by decide)]
    exact counter
  have selectedLeaf : selected.getMem 0x43070 = BitVec.ofNat 64 leaf.val := by
    rw [(ftsSelect_leaf header tree headerCounter).2]
    rw [ftsTreeHeader_selector_byte state tree, selectorByte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have h := leaf.isLt
    simp only [ftsTreeHeight] at h
    omega
  have headerCells := ftsTreeHeader_cells state
  have selectedTree : selected.getMem 0x43000 = BitVec.ofNat 64 tree.val := by
    rw [ftsSelect_mem_frame header 0x43000 (by decide) (by decide) (by decide),
      headerCells.1, counter]
  have selectedIndex : selected.getMem 0x43008 = BitVec.ofNat 64 index.val := by
    rw [ftsSelect_mem_frame header 0x43008 (by decide) (by decide) (by decide),
      headerCells.2, indexCell]
  have selectedSource : selected.getMem 0x43028 =
      BitVec.ofNat 64 (0x22cdc + 180 * tree.val) := by
    rw [ftsSelect_mem_frame header 0x43028 (by decide) (by decide) (by decide),
      ftsTreeHeader_mem_frame state 0x43028 (by decide) (by decide), source]
  have copiedFrame (address : Word)
      (outside : ∀ offset : Fin 5,
        address ≠ alignToDword
          (pointers.getReg .x7 + signExtend12
            (4#12 * BitVec.ofNat 12 offset.val))) :
      copied.getMem address = pointers.getMem address := by
    exact SphincsVerifierCopyMemory.copyRoot_mem_frame pointers address outside
  have beforeReady (address : Word)
      (notPointer : address ≠ 0x43028) (notIndex : address ≠ 0x43018)
      (outside : ∀ offset : Fin 5,
        address ≠ alignToDword
          (pointers.getReg .x7 + signExtend12
            (4#12 * BitVec.ofNat 12 offset.val))) :
      advanced.getMem address = selected.getMem address := by
    rw [ftsAdvance_mem_frame copied address notPointer notIndex,
      copiedFrame address outside, ftsCopyPointers_mem selected address]
  have fieldFrame (address : Word)
      (eligible : address = 0x43040 ∨ address = 0x43000 ∨
        address = 0x43008 ∨ address = 0x43070) :
      (nextTreeHashState state).getMem address = selected.getMem address := by
    rcases eligible with h | h | h | h <;> subst address
    all_goals change (SphincsVerifierFtsSetup.ftsHashReadyState advanced).getMem _ = selected.getMem _
    all_goals rw [hashReady_mem_frame advanced _ (by decide) (by decide)
      (by decide) (by decide) (by intro offset; fin_cases offset <;> decide)]
    all_goals exact beforeReady _ (by decide) (by decide) (by
      intro offset; rw [(ftsCopyPointers_regs selected).2]
      fin_cases offset <;> decide)
  refine ⟨pc, regs.1, regs.2.1, regs.2.2.1, regs.2.2.2,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [fieldFrame 0x43040 (Or.inl rfl)]
    rw [ftsSelect_mem_frame header 0x43040 (by decide) (by decide) (by decide)]
    exact headerCounter
  · rw [fieldFrame 0x43000 (Or.inr (Or.inl rfl))]
    exact selectedTree
  · rw [fieldFrame 0x43008 (Or.inr (Or.inr (Or.inl rfl)))]
    exact selectedIndex
  · rw [fieldFrame 0x43070 (Or.inr (Or.inr (Or.inr rfl)))]
    exact selectedLeaf
  · change (SphincsVerifierFtsSetup.ftsHashReadyState advanced).getMem
      0x43028 = _
    rw [hashReady_pointer_frame advanced]
    rw [(ftsAdvance_cells copied).1]
    rw [copiedFrame 0x43028 (by
      intro offset; rw [(ftsCopyPointers_regs selected).2]
      fin_cases offset <;> decide),
      ftsCopyPointers_mem selected 0x43028, selectedSource]
    have addressEq : 0x22cdc + 180 * tree.val + 20 =
        pathAddress tree ⟨0, by decide⟩ := by
      norm_num [pathAddress, SphincsWire.ftsOpeningBytes,
        SphincsWire.digestBytes, ftsTreeHeight]
      omega
    simpa [BitVec.ofNat_add] using
      congrArg (BitVec.ofNat 64) addressEq

/-- info: 'SigGolfCandidate.SphincsVerifierFtsNextReadyControls.nextTreeHashState_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nextTreeHashState_controls

end SigGolfCandidate.SphincsVerifierFtsNextReadyControls
