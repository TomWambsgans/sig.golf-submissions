import SigGolfCandidate.SphincsVerifierFtsPriorRoots
import SigGolfCandidate.SphincsVerifierFtsSetup
import SigGolfCandidate.SphincsVerifierFtsLeafCopy

namespace SigGolfCandidate.SphincsVerifierFtsNextTreeSetup
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolfCandidate.SphincsVerifierFtsLeafCopy
open SigGolfCandidate.SphincsVerifierFtsAdvance
open SigGolfCandidate.SphincsVerifierFtsSetup
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def nextTreeHashState (state : MachineState) : MachineState :=
  ftsHashReadyState (ftsAdvanceState
    (copyRootState (ftsCopyPointers
      (ftsSelectState (ftsTreeHeaderState state)))))

theorem nextTreeSetup_block (state : MachineState) (tree : FtsTree)
    (pc : state.pc = 0x173c)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (source : state.getMem 0x43028 =
      BitVec.ofNat 64 (0x22cdc + 180 * tree.val)) :
    OrdinarySteps SphincsImages.verify state 99
      (nextTreeHashState state) := by
  let header := ftsTreeHeaderState state
  let selected := ftsSelectState header
  let pointers := ftsCopyPointers selected
  let copied := copyRootState pointers
  let advanced := ftsAdvanceState copied
  have headerBlock := ftsTreeHeader_block state pc
  have headerPc := ftsTreeHeader_pc state pc
  have headerCounter : header.getMem 0x43040 =
      BitVec.ofNat 64 tree.val := by
    rw [ftsTreeHeader_mem_frame state 0x43040 (by decide) (by decide)]
    exact counter
  have selectedBlock := ftsSelect_block header tree headerPc headerCounter
  have selectedPc := ftsSelect_pc header headerPc
  have pointersBlock := ftsCopyPointers_block selected selectedPc
  have pointersPc := ftsCopyPointers_pc selected selectedPc
  have sourceReg : pointers.getReg .x6 =
      BitVec.ofNat 64 (0x22cdc + 180 * tree.val) := by
    rw [(ftsCopyPointers_regs selected).1,
      ftsSelect_mem_frame header 0x43028 (by decide) (by decide) (by decide),
      ftsTreeHeader_mem_frame state 0x43028 (by decide) (by decide)]
    exact source
  have destinationReg : pointers.getReg .x7 = 0x40028 :=
    (ftsCopyPointers_regs selected).2
  have copyBlock : OrdinarySteps SphincsImages.verify pointers 10 copied := by
    apply copy20_block_general SphincsImages.verify 497
      ftsLeafCopy_code pointers (0x22cdc + 180 * tree.val) 0x40028
      (by simpa using pointersPc) sourceReg destinationReg
    · omega
    · have h : tree.val < ftsTrees - 1 := tree.isLt
      dsimp [ftsTrees] at h
      dsimp [MEMORY_BYTES]
      omega
    · decide
    · decide
    · decide
  have copiedPc := ftsLeafCopy_pc pointers pointersPc
  have advanceBlock := ftsAdvance_block copied copiedPc
  have advancePc := ftsAdvance_pc copied copiedPc
  have readyBlock := ftsHashReady_block advanced advancePc
  change OrdinarySteps SphincsImages.verify state 99
    (ftsHashReadyState advanced)
  convert (((((headerBlock.append selectedBlock).append pointersBlock).append
    copyBlock).append advanceBlock).append readyBlock) using 1

theorem nextTreeSetup_pc (state : MachineState) (pc : state.pc = 0x173c) :
    (nextTreeHashState state).pc = 0x18c8 := by
  let header := ftsTreeHeaderState state
  let selected := ftsSelectState header
  let pointers := ftsCopyPointers selected
  let copied := copyRootState pointers
  let advanced := ftsAdvanceState copied
  have headerPc := ftsTreeHeader_pc state pc
  have selectedPc := ftsSelect_pc header headerPc
  have pointersPc := ftsCopyPointers_pc selected selectedPc
  have copiedPc := ftsLeafCopy_pc pointers pointersPc
  have advancePc := ftsAdvance_pc copied copiedPc
  exact ftsHashReady_pc advanced advancePc

theorem nextTreeSetup_hash_regs (state : MachineState) :
    (nextTreeHashState state).getReg .x10 = 0x40000 ∧
      (nextTreeHashState state).getReg .x11 = 480 ∧
      (nextTreeHashState state).getReg .x12 = 0x42000 ∧
      (nextTreeHashState state).getReg .x5 = 1 :=
  ftsHashReady_regs _

/-- info: 'SigGolfCandidate.SphincsVerifierFtsNextTreeSetup.nextTreeSetup_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nextTreeSetup_block

/-- info: 'SigGolfCandidate.SphincsVerifierFtsNextTreeSetup.nextTreeSetup_pc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nextTreeSetup_pc

/-- info: 'SigGolfCandidate.SphincsVerifierFtsNextTreeSetup.nextTreeSetup_hash_regs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nextTreeSetup_hash_regs

end SigGolfCandidate.SphincsVerifierFtsNextTreeSetup
