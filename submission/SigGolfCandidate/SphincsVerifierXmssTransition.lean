import SigGolfCandidate.SphincsVerifierXmssPathComplete
import SigGolfCandidate.SphincsVerifierCopy20DataGeneral
import SigGolfCandidate.SphincsVerifierSecondHashBytes
import SigGolfCandidate.SphincsMaskedSignOtsShift

namespace SigGolfCandidate.SphincsVerifierXmssTransition
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssNext
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsVerifierXmssNodeSite
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def targetLayer (target : Fin 5) : Layer := ⟨target.val, by
  exact lt_trans target.isLt (by decide)⟩

def previousLayer (target : Fin 5) : Layer := ⟨target.val + 1, by
  have := target.isLt
  simp only [numLayers]
  omega⟩

def transitionPc (target : Fin 5) : Word :=
  branchPc (previousLayer target) + 4

def transitionSchedule (target : Fin 5) : List (Word × Instr) :=
  let p := transitionPc target
  let lay := targetLayer target
  [
  (p, .ADDI .x6 .x0 (BitVec.ofNat 12 lay.val)),
  (p + 4, .LUI .x28 0x43),
  (p + 8, .ADDI .x28 .x28 0),
  (p + 12, .SD .x28 .x6 0),
  (p + 16, .LUI .x28 0x43),
  (p + 20, .ADDI .x28 .x28 120),
  (p + 24, .LD .x6 .x28 0),
  (p + 28, .SRLI .x6 .x6
    (BitVec.ofNat 6 (heightBelow lay + layerHeight lay))),
  (p + 32, .LUI .x28 0x43),
  (p + 36, .ADDI .x28 .x28 8),
  (p + 40, .SD .x28 .x6 0),
  (p + 44, .LUI .x28 0x43),
  (p + 48, .ADDI .x28 .x28 120),
  (p + 52, .LD .x6 .x28 0),
  (p + 56, .SRLI .x6 .x6 (BitVec.ofNat 6 (heightBelow lay))),
  (p + 60, .ANDI .x6 .x6 (BitVec.ofNat 12 (2 ^ layerHeight lay - 1))),
  (p + 64, .LUI .x28 0x43),
  (p + 68, .ADDI .x28 .x28 32),
  (p + 72, .SD .x28 .x6 0),
  (p + 76, .ADDI .x6 .x0 0),
  (p + 80, .LUI .x28 0x43),
  (p + 84, .ADDI .x28 .x28 16),
  (p + 88, .SD .x28 .x6 0),
  (p + 92, .LUI .x28 0x43),
  (p + 96, .ADDI .x28 .x28 32),
  (p + 100, .LD .x6 .x28 0),
  (p + 104, .LUI .x28 0x43),
  (p + 108, .ADDI .x28 .x28 24),
  (p + 112, .SD .x28 .x6 0)]

theorem transition_code (target : Fin 5) :
    ∀ entry ∈ transitionSchedule target,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by
  fin_cases target <;>
    decide

def transitionState (target : Fin 5) (s : MachineState) : MachineState :=
  runSchedule (transitionSchedule target) s

theorem transition_checked (target : Fin 5) (s : MachineState)
    (pc : s.pc = transitionPc target) :
    Checked (transitionSchedule target) s := by
  fin_cases target <;>
    simp [Checked, transitionSchedule, transitionPc, targetLayer,
      previousLayer, branchPc, checkPc, advancePc, nodeHashPc, nodePc,
      heightBelow, layerHeight, maxLayerHeight, execInstrBr,
      ordinaryStep, memoryArgumentsValid, accessValid, rangeValid,
      MEMORY_BYTES, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, pc] <;> bv_decide

theorem transition_block (target : Fin 5) (s : MachineState)
    (pc : s.pc = transitionPc target) :
    OrdinarySteps SphincsImages.verify s 29 (transitionState target s) := by
  simpa only [transitionState,
      show (transitionSchedule target).length = 29 by
        simp [transitionSchedule]] using
    checked_sound _ (transitionSchedule target) (transition_code target)
      s (transition_checked target s pc)

theorem transition_pc (target : Fin 5) (s : MachineState)
    (pc : s.pc = transitionPc target) :
    (transitionState target s).pc = transitionPc target + 116 := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, transitionPc, previousLayer, branchPc,
      checkPc, advancePc, nodeHashPc, pc] <;>
    bv_decide

theorem transition_layer (target : Fin 5) (s : MachineState) :
    (transitionState target s).getMem 0x43000 =
      BitVec.ofNat 64 target.val := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] <;>
    decide

theorem transition_tree (target : Fin 5) (s : MachineState) :
    (transitionState target s).getMem 0x43008 =
      s.getMem 0x43078 >>>
        (heightBelow (targetLayer target) + layerHeight (targetLayer target)) := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      targetLayer, heightBelow, layerHeight, maxLayerHeight] <;>
    congr 1 <;> decide

theorem transition_leaf (target : Fin 5) (s : MachineState) :
    (transitionState target s).getMem 0x43020 =
      (s.getMem 0x43078 >>> heightBelow (targetLayer target)) &&&
        BitVec.ofNat 64 (2 ^ layerHeight (targetLayer target) - 1) := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      targetLayer, heightBelow, layerHeight, maxLayerHeight] <;>
    congr 1 <;> decide

theorem transition_level (target : Fin 5) (s : MachineState) :
    (transitionState target s).getMem 0x43010 = 0 := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem transition_index (target : Fin 5) (s : MachineState) :
    (transitionState target s).getMem 0x43018 =
      (transitionState target s).getMem 0x43020 := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem transition_global_index (target : Fin 5) (s : MachineState) :
    (transitionState target s).getMem 0x43078 = s.getMem 0x43078 := by
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem transition_current_mem (target : Fin 5) (s : MachineState)
    (read : Word) (inside : 0x44a00 ≤ read.toNat ∧ read.toNat < 0x44a18) :
    (transitionState target s).getMem read = s.getMem read := by
  have ne (address : Word) (small : address.toNat < 0x44a00) :
      read ≠ address := by
    intro h
    have eqNat := congrArg BitVec.toNat h
    omega
  fin_cases target <;>
    simp [transitionState, transitionSchedule, runSchedule,
      execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne] <;>
    split_ifs <;> bv_omega

theorem transition_current_byte (target : Fin 5) (s : MachineState)
    (i : Nat) (hi : i < 20) :
    (transitionState target s).getByte
        (BitVec.ofNat 64 (0x44a00 + i)) =
      s.getByte (BitVec.ofNat 64 (0x44a00 + i)) := by
  simp only [MachineState.getByte]
  rw [transition_current_mem target s _ (by interval_cases i <;> decide)]

/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransition.transition_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transition_block
/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransition.transition_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transition_tree
/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransition.transition_current_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transition_current_byte

end SigGolfCandidate.SphincsVerifierXmssTransition

namespace SigGolfCandidate.SphincsVerifierXmssTransitionMessage
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierXmssTransition
open SigGolfCandidate.SphincsVerifierXmssNext
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsCopyAccess
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopy20DataGeneral
open SigGolfCandidate.SphincsVerifierXmssNodeSite
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def messagePc (target : Fin 5) : Word := transitionPc target + 116

def pointerSchedule (target : Fin 5) : List (Word × Instr) :=
  let p := messagePc target
  [(p, .LUI .x6 0x45),
   (p + 4, .ADDI .x6 .x6 (-1536)),
   (p + 8, .LUI .x7 0x40),
   (p + 12, .ADDI .x7 .x7 40)]

theorem pointer_code (target : Fin 5) :
    ∀ entry ∈ pointerSchedule target,
      SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
        some (.base entry.2) := by
  fin_cases target <;> decide

def pointerState (target : Fin 5) (s : MachineState) : MachineState :=
  runSchedule (pointerSchedule target) s

theorem pointer_checked (target : Fin 5) (s : MachineState)
    (pc : s.pc = messagePc target) :
    Checked (pointerSchedule target) s := by
  fin_cases target <;>
    simp [Checked, pointerSchedule, messagePc, transitionPc, previousLayer,
      branchPc, checkPc, advancePc, nodeHashPc, nodePc,
      execInstrBr, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, signExtend12, pc] <;> bv_decide

theorem pointer_block (target : Fin 5) (s : MachineState)
    (pc : s.pc = messagePc target) :
    OrdinarySteps SphincsImages.verify s 4 (pointerState target s) := by
  simpa only [pointerState, show (pointerSchedule target).length = 4 by
    simp [pointerSchedule]] using
      checked_sound _ (pointerSchedule target) (pointer_code target)
        s (pointer_checked target s pc)

theorem pointer_pc (target : Fin 5) (s : MachineState)
    (pc : s.pc = messagePc target) :
    (pointerState target s).pc = messagePc target + 16 := by
  fin_cases target <;>
    simp [pointerState, pointerSchedule, runSchedule, execInstrBr,
      messagePc, transitionPc, previousLayer, branchPc,
      checkPc, advancePc, nodeHashPc, nodePc, pc] <;> bv_decide

theorem pointer_source (target : Fin 5) (s : MachineState) :
    (pointerState target s).getReg .x6 = 0x44a00 := by
  simp [pointerState, pointerSchedule, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem pointer_destination (target : Fin 5) (s : MachineState) :
    (pointerState target s).getReg .x7 = 0x40028 := by
  simp [pointerState, pointerSchedule, runSchedule, execInstrBr,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem pointer_mem (target : Fin 5) (s : MachineState) (a : Word) :
    (pointerState target s).getMem a = s.getMem a := by
  simp [pointerState, pointerSchedule, runSchedule, execInstrBr]

def messageState (target : Fin 5) (s : MachineState) : MachineState :=
  copyRootState (pointerState target s)

theorem message_code (target : Fin 5) :
    Copy20Code SphincsImages.verify
      ((messagePc target + 16).toNat / 4 - 0x400) := by
  fin_cases target <;> constructor <;> intro offset <;>
    fin_cases offset <;> decide

theorem message_block (target : Fin 5) (s : MachineState)
    (pc : s.pc = messagePc target) :
    OrdinarySteps SphincsImages.verify s 14 (messageState target s) := by
  have first := pointer_block target s pc
  have second := copy20_block_general SphincsImages.verify
    ((messagePc target + 16).toNat / 4 - 0x400)
    (message_code target) (pointerState target s) 0x44a00 0x40028
    (by rw [pointer_pc target s pc]; fin_cases target <;>
      decide)
    (pointer_source target s) (pointer_destination target s)
    (by decide) (by decide) (by decide) (by decide)
    (by fin_cases target <;> decide)
  simpa [messageState] using first.append second

private theorem source_word_frame (written read : Fin 5)
    (state : MachineState) (destination : state.getReg .x7 = 0x40028) :
    (copyWordState written state).getWord32
        (BitVec.ofNat 64 (0x44a00 + 4 * read.val)) =
      state.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * read.val)) := by
  fin_cases written <;> fin_cases read <;>
    simp_all [copyWordState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_ne] <;>
    (rw [getWord32_setWord32_other _ _ _ _ (by decide)]; simp)

private def CopyInv (original : MachineState) (count : Nat)
    (state : MachineState) : Prop :=
  state.getReg .x6 = 0x44a00 ∧
  state.getReg .x7 = 0x40028 ∧
  (∀ index : Fin 5,
    state.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val))) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)))

private theorem copy_step (original state : MachineState) (slot : Fin 5)
    (inv : CopyInv original slot.val state) :
    CopyInv original (slot.val + 1) (copyWordState slot state) := by
  rcases inv with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ := copyWord_pointers slot state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination, ?_, ?_⟩
  · intro index
    rw [source_word_frame slot index state destination]
    exact sourceWords index
  · intro index earlier
    by_cases same : slot = index
    · subst index
      rw [copyWord_data_general slot state 0x44a00 0x40028 source destination]
      exact sourceWords slot
    · rw [copyWord_other_fts slot index same state destination]
      have smaller : index.val < slot.val := by
        have unequal : slot.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact copiedWords index smaller

theorem copied_root_word (original : MachineState)
    (source : original.getReg .x6 = 0x44a00)
    (destination : original.getReg .x7 = 0x40028)
    (index : Fin 5) :
    (copyRootState original).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      original.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  have initial : CopyInv original 0 original := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro _ impossible
    omega
  have s0 := copy_step original original 0 initial
  have s1 := copy_step original (copyWordState 0 original) 1 s0
  have s2 := copy_step original (copyWordState 1 (copyWordState 0 original)) 2 s1
  have s3 := copy_step original
    (copyWordState 2 (copyWordState 1 (copyWordState 0 original))) 3 s2
  have s4 := copy_step original
    (copyWordState 3 (copyWordState 2
      (copyWordState 1 (copyWordState 0 original)))) 4 s3
  exact s4.2.2.2 index (by have := index.isLt; omega)

theorem message_word (target : Fin 5) (s : MachineState)
    (index : Fin 5) :
    (messageState target s).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * index.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * index.val)) := by
  rw [messageState, copied_root_word _ (pointer_source target s)
    (pointer_destination target s) index]
  simp [MachineState.getWord32, pointer_mem]

private theorem field_byte (state : MachineState) (base : Nat)
    (supported : base = 0x40028 ∨ base = 0x44a00)
    (index : Fin 5) (byte : Fin 4) :
    state.getByte (BitVec.ofNat 64 (base + 4 * index.val + byte.val)) =
      (state.getWord32 (BitVec.ofNat 64 (base + 4 * index.val))).extractLsb'
        (8 * byte.val) 8 := by
  have split := SphincsVerifierSecondHashHeader.extractByte_from_word32
    (state.getMem (alignToDword
      (BitVec.ofNat 64 (base + 4 * index.val + byte.val))))
    ⟨(base + 4 * index.val + byte.val) % 8,
      Nat.mod_lt _ (by decide)⟩
  rcases supported with h | h <;> subst base <;>
    fin_cases index <;> fin_cases byte <;>
      simpa [MachineState.getByte, MachineState.getWord32,
        alignToDword, byteOffset] using split

theorem message_byte (target : Fin 5) (s : MachineState)
    (i : Nat) (hi : i < 20) :
    (messageState target s).getByte (BitVec.ofNat 64 (0x40028 + i)) =
      s.getByte (BitVec.ofNat 64 (0x44a00 + i)) := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, by omega⟩
  have split : i = 4 * index.val + byte.val := by
    simp [index, byte]
    omega
  rw [split]
  rw [show 0x40028 + (4 * index.val + byte.val) =
        0x40028 + 4 * index.val + byte.val by omega,
      show 0x44a00 + (4 * index.val + byte.val) =
        0x44a00 + 4 * index.val + byte.val by omega]
  rw [field_byte _ 0x40028 (Or.inl rfl) index byte,
    field_byte _ 0x44a00 (Or.inr rfl) index byte,
    message_word target s index]

def handoffState (target : Fin 5) (s : MachineState) : MachineState :=
  messageState target (transitionState target s)

theorem handoff_block (target : Fin 5) (s : MachineState)
    (pc : s.pc = transitionPc target) :
    OrdinarySteps SphincsImages.verify s 43 (handoffState target s) := by
  have first := transition_block target s pc
  have second := message_block target (transitionState target s)
    (by simpa [messagePc] using transition_pc target s pc)
  simpa [handoffState] using first.append second

theorem handoff_byte (target : Fin 5) (s : MachineState)
    (i : Nat) (hi : i < 20) :
    (handoffState target s).getByte (BitVec.ofNat 64 (0x40028 + i)) =
      s.getByte (BitVec.ofNat 64 (0x44a00 + i)) := by
  rw [handoffState, message_byte target (transitionState target s) i hi,
    transition_current_byte target s i hi]

/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransitionMessage.message_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms message_byte

/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransitionMessage.handoff_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms handoff_byte

end SigGolfCandidate.SphincsVerifierXmssTransitionMessage

namespace SigGolfCandidate.SphincsVerifierWotsRelocation
open SigGolfCandidate.SphincsVerifierXmssTransition
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def chainPc (target : Fin 5) : Nat := 0x2710 + 0xfcc * (5 - target.val)

/-- The entire WOTS chain-and-leaf block is identical in all six layers. -/
theorem chain_segment_identical (target : Fin 5) :
    (SphincsImages.verify.code.drop ((chainPc target - 0x1000) / 4)).take 241 =
      (SphincsImages.verify.code.drop ((0x2710 - 0x1000) / 4)).take 241 := by
  fin_cases target <;> decide

/-- info: 'SigGolfCandidate.SphincsVerifierWotsRelocation.chain_segment_identical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chain_segment_identical

end SigGolfCandidate.SphincsVerifierWotsRelocation

namespace SigGolfCandidate.SphincsVerifierXmssTransitionComplete
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssTransition
open SigGolfCandidate.SphincsVerifierXmssTransitionMessage
open SigGolfCandidate.SphincsVerifierXmssPathControl
open SigGolfCandidate.SphincsVerifierXmssPathSemantic
open SigGolfCandidate.SphincsVerifierXmssPathComplete
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsVerifierXmssNext
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsBridge
open SphincsSecurity.Concrete
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- The complete prior XMSS path is exactly the next WOTS message. -/
theorem complete_path_handoff (hash : Hash) (target : Fin 5)
    (s : MachineState) (pk : SphincsSecurity.PublicKey)
    (tree : TreeIndex) (leaf : LeafIndex)
    (signature : SphincsSecurity.Signature) (first : Digest)
    (pointer : Word)
    (pc : s.pc = nodePc (previousLayer target))
    (pointerValue : s.getMem 0x43028 = pointer)
    (pointerBound : pointer.toNat + 20 * layerHeight (previousLayer target) ≤ 0x40000)
    (pointerAligned : pointer.toNat % 4 = 0)
    (layerCell : s.getMem 0x43000 = BitVec.ofNat 64 (previousLayer target).val)
    (treeCell : s.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (levelCell : s.getMem 0x43048 = 1)
    (bitCell : s.getMem 0x43070 = BitVec.ofNat 64 leaf.val)
    (hprefix : WitnessPrefix s pk)
    (current : ∀ i, (hi : i < 20) →
      s.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        first.extractLsb' (8 * i) 8)
    (siblings : PathWitness s signature (previousLayer target) pointer) :
    let doneState := pathState hash (previousLayer target)
      (layerHeight (previousLayer target)) s
    let nextState := handoffState target doneState
    OrdinarySteps SphincsImages.verify doneState 43 nextState ∧
      ∀ i, (hi : i < 20) →
        nextState.getByte (BitVec.ofNat 64 (0x40028 + i)) =
          (foldValue (adaptOracle hash) pk.parameter
            (previousLayer target) tree leaf
            (signaturePath signature (previousLayer target)) first
            (layerHeight (previousLayer target))).extractLsb' (8 * i) 8 := by
  have finished := complete_path hash (previousLayer target) s pk tree leaf
    signature first pointer pc pointerValue pointerBound pointerAligned
    layerCell treeCell levelCell bitCell hprefix current siblings
  dsimp at finished ⊢
  constructor
  · exact handoff_block target _ finished.1
  · intro i hi
    rw [handoff_byte target _ i hi]
    exact finished.2.1 i hi

/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransitionComplete.complete_path_handoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms complete_path_handoff

end SigGolfCandidate.SphincsVerifierXmssTransitionComplete


namespace SigGolfCandidate.SphincsVerifierXmssTransitionIndex
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SphincsSecurity.Concrete
open SigGolfCandidate.SphincsVerifierXmssTransition
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem index_small (index : Index) : index.val < 2 ^ 64 := by
  exact lt_trans index.isLt (by decide)

theorem target_tree_exponent (target : Fin 5) :
    heightBelow (targetLayer target) + layerHeight (targetLayer target) =
      totalHeight - heightAbove (targetLayer target) := by
  fin_cases target <;> decide

theorem target_height_small (target : Fin 5) :
    2 ^ layerHeight (targetLayer target) - 1 < 2 ^ 64 := by
  fin_cases target <;> decide

theorem transition_tree_index (target : Fin 5) (s : MachineState)
    (index : Index)
    (global : s.getMem 0x43078 = BitVec.ofNat 64 index.val) :
    (transitionState target s).getMem 0x43008 =
      BitVec.ofNat 64 (treeIndexAt index (targetLayer target)).val := by
  rw [transition_tree, global]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (index_small index)]
  rw [target_tree_exponent]
  have small : (treeIndexAt index (targetLayer target)).val < 2 ^ 64 :=
    lt_trans (treeIndexAt index (targetLayer target)).isLt (by decide)
  rw [Nat.mod_eq_of_lt small]
  rfl

theorem transition_leaf_index (target : Fin 5) (s : MachineState)
    (index : Index)
    (global : s.getMem 0x43078 = BitVec.ofNat 64 index.val) :
    (transitionState target s).getMem 0x43020 =
      BitVec.ofNat 64 (leafIndexAt index (targetLayer target)).val := by
  rw [transition_leaf, global]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (index_small index),
    Nat.mod_eq_of_lt (target_height_small target)]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have small : (leafIndexAt index (targetLayer target)).val < 2 ^ 64 :=
    lt_trans (leafIndexAt index (targetLayer target)).isLt (by decide)
  rw [Nat.mod_eq_of_lt small]
  rfl

theorem transition_index_leaf (target : Fin 5) (s : MachineState)
    (index : Index)
    (global : s.getMem 0x43078 = BitVec.ofNat 64 index.val) :
    (transitionState target s).getMem 0x43018 =
      BitVec.ofNat 64 (leafIndexAt index (targetLayer target)).val := by
  rw [transition_index]
  exact transition_leaf_index target s index global

/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransitionIndex.transition_tree_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transition_tree_index
/-- info: 'SigGolfCandidate.SphincsVerifierXmssTransitionIndex.transition_leaf_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transition_leaf_index

end SigGolfCandidate.SphincsVerifierXmssTransitionIndex

namespace SigGolfCandidate.SphincsVerifierWotsRelocationTrace
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.SphincsVerifierWotsRelocation
open SigGolfCandidate.SphincsVerifierFtsRootCopy
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsMaskedSignOtsShift
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def delta (target : Fin 5) : Word := BitVec.ofNat 64 (0xfcc * (5 - target.val))
def wordOffset (target : Fin 5) : Nat := 1011 * (5 - target.val)

theorem delta_offset (target : Fin 5) :
    delta target = BitVec.ofNat 64 (4 * wordOffset target) := by
  fin_cases target <;> decide

theorem word_reloc (target : Fin 5) (i : Fin 241) :
    SphincsImages.verify.code[1476 + wordOffset target + i.val]? =
      SphincsImages.verify.code[1476 + i.val]? := by
  have eq := congrArg (fun words : List (BitVec 32) => words[i.val]?)
    (chain_segment_identical target)
  have start : ((chainPc target - 0x1000) / 4) =
      1476 + wordOffset target := by
    simp [chainPc, wordOffset]
    omega
  simpa only [start, List.getElem?_take_of_lt i.isLt,
    List.getElem?_drop] using eq

theorem instructionAt_index (image : Image) (i : Nat)
    (small : 0x1000 + 4 * i < 2 ^ 64) :
    instructionAt image (BitVec.ofNat 64 (0x1000 + 4 * i)) =
      image.code[i]?.bind decodeInstruction := by
  simpa [instructionAt] using fetch_index image
    ({ regs := fun _ => 0, mem := fun _ => 0,
       pc := BitVec.ofNat 64 (0x1000 + 4 * i) } : MachineState)
    i small rfl

theorem instruction_transfer (target : Fin 5) (pc : Word)
    (lower : 0x2710 ≤ pc.toNat) (upper : pc.toNat < 0x2ad4)
    (aligned : pc.toNat % 4 = 0) :
    instructionAt SphincsImages.verify (pc + delta target) =
      instructionAt SphincsImages.verify pc := by
  let i : Fin 241 := ⟨(pc.toNat - 0x2710) / 4, by omega⟩
  have original : pc = BitVec.ofNat 64 (0x1000 + 4 * (1476 + i.val)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [i]; omega)]
    dsimp [i]
    omega
  have translated : pc + delta target =
      BitVec.ofNat 64 (0x1000 + 4 * (1476 + wordOffset target + i.val)) := by
    rw [original, delta_offset, ← BitVec.ofNat_add]
    congr 1
    omega
  rw [translated, instructionAt_index _ _ (by
      fin_cases target <;> simp [wordOffset] <;> omega),
    original, instructionAt_index _ _ (by omega), word_reloc target i]


def VerifierSupported (i : Instr) : Prop :=
  Supported i ∨ ∃ offset, i = .JAL .x0 offset

instance (i : Instr) : Decidable (VerifierSupported i) := by
  unfold VerifierSupported
  cases i <;> infer_instance

theorem exec_shift_verifier (target : Fin 5) (s : MachineState)
    (i : Instr) (supported : VerifierSupported i) :
    execInstrBr (shift (delta target) s) i =
      shift (delta target) (execInstrBr s i) := by
  rcases supported with h | ⟨offset, rfl⟩
  · exact exec_shift _ _ _ h
  · simp [shift, execInstrBr, MachineState.setReg, MachineState.setPC,
      add_assoc, add_comm, add_left_comm]

theorem ordinary_shift_verifier (target : Fin 5) (s : MachineState)
    (i : Instr) (supported : VerifierSupported i)
    (step : ordinaryStep s (.base i) = some (execInstrBr s i)) :
    ordinaryStep (shift (delta target) s) (.base i) =
      some (shift (delta target) (execInstrBr s i)) := by
  rcases supported with h | ⟨offset, rfl⟩
  · rw [ordinary_shift _ _ _ h step, exec_shift _ _ _ h]
  · have valid : memoryArgumentsValid s (.JAL .x0 offset) = true := rfl
    simpa [ordinaryStep, memory_shift, valid] using
      congrArg some (exec_shift_verifier target s (.JAL .x0 offset)
        (Or.inr ⟨offset, rfl⟩))

def supportedWord (i : Nat) : Bool :=
  match SphincsImages.verify.code[1476 + i]?.bind decodeInstruction with
  | some (.base instruction) => decide (VerifierSupported instruction)
  | _ => false

theorem supportedWord_all : (List.range 241).all supportedWord = true := by
  decide

theorem segment_supported (i : Fin 241) :
    match SphincsImages.verify.code[1476 + i.val]?.bind decodeInstruction with
    | some (.base instruction) => VerifierSupported instruction
    | _ => False := by
  have h := List.all_eq_true.mp supportedWord_all i.val (List.mem_range.mpr i.isLt)
  unfold supportedWord at h
  cases hc : SphincsImages.verify.code[1476 + i.val]?.bind decodeInstruction with
  | none => simp [hc] at h ⊢
  | some result =>
      cases result with
      | base instruction =>
          simpa [hc] using (of_decide_eq_true (by simpa [hc] using h))
      | word op rd rs1 rs2 => simp [hc] at h ⊢
      | sraiw rd rs shamt => simp [hc] at h ⊢

theorem fetched_supported (s : MachineState) (instruction : Instruction)
    (lower : 0x2710 ≤ s.pc.toNat) (upper : s.pc.toNat < 0x2ad4)
    (aligned : s.pc.toNat % 4 = 0)
    (fetched : fetch SphincsImages.verify s = some instruction) :
    ∃ base, instruction = .base base ∧ VerifierSupported base := by
  let i : Fin 241 := ⟨(s.pc.toNat - 0x2710) / 4, by omega⟩
  have pc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (1476 + i.val)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [i]; omega)]
    dsimp [i]
    omega
  rw [fetch_index SphincsImages.verify s (1476 + i.val) (by omega) pc] at fetched
  have safe := segment_supported i
  cases h : SphincsImages.verify.code[1476 + i.val]?.bind decodeInstruction with
  | none => simp [h] at fetched
  | some result =>
      rw [h] at safe fetched
      cases result with
      | base base => exact ⟨base, by cases fetched; rfl, by simpa using safe⟩
      | word op rd rs1 rs2 => simp at safe
      | sraiw rd rs shamt => simp at safe

theorem ordinaryStep_result (s next : MachineState) (i : Instr)
    (step : ordinaryStep s (.base i) = some next) :
    next = execInstrBr s i := by
  cases i <;> simp_all [ordinaryStep]

def InSegment (s : MachineState) : Prop :=
  0x2710 ≤ s.pc.toNat ∧ s.pc.toNat < 0x2ad4 ∧ s.pc.toNat % 4 = 0

inductive SegmentInterior (hash : Hash) :
    {s : MachineState} → {steps cycles calls blocks : Nat} →
    {t : MachineState} →
    Trace hash SphincsImages.verify s steps cycles calls blocks t → Prop where
  | refl (s : MachineState) :
      SegmentInterior hash (Trace.refl s)
  | ordinary (s next final : MachineState) (instruction : Instruction)
      (steps cycles calls blocks : Nat)
      (hf : fetch SphincsImages.verify s = some instruction)
      (hs : ordinaryStep s instruction = some next)
      (tail : Trace hash SphincsImages.verify next steps cycles calls blocks final)
      (inside : InSegment s) (rest : SegmentInterior hash tail) :
      SegmentInterior hash (Trace.ordinary s next final instruction
        steps cycles calls blocks hf hs tail)
  | hash (s final : MachineState) (steps cycles calls blocks : Nat)
      (hf : fetch SphincsImages.verify s = some (.base .ECALL))
      (service : s.getReg .x5 = 1) (valid : hashArgumentsValid s = true)
      (tail : Trace hash SphincsImages.verify
        (writeHash s (hash (hashInput s))) steps cycles calls blocks final)
      (inside : InSegment s) (rest : SegmentInterior hash tail) :
      SegmentInterior hash (Trace.hash s final steps cycles calls blocks
        hf service valid tail)

theorem trace_shift (target : Fin 5) (hash : Hash)
    {s t : MachineState} {steps cycles calls blocks : Nat}
    (trace : Trace hash SphincsImages.verify s steps cycles calls blocks t)
    (inside : SegmentInterior hash trace) :
    Trace hash SphincsImages.verify (shift (delta target) s)
      steps cycles calls blocks (shift (delta target) t) := by
  induction inside with
  | refl s => exact Trace.refl _
  | ordinary s next final instruction steps cycles calls blocks
      hf hs tail range rest ih =>
      obtain ⟨base, rfl, supported⟩ := fetched_supported s instruction
        range.1 range.2.1 range.2.2 hf
      have fetchShift : fetch SphincsImages.verify (shift (delta target) s) =
          some (.base base) := by
        rw [fetch_at, shift_pc,
          instruction_transfer target s.pc range.1 range.2.1 range.2.2]
        simpa [fetch_at] using hf
      have eqNext := ordinaryStep_result s next base hs
      subst next
      have stepShift := ordinary_shift_verifier target s base supported hs
      exact Trace.ordinary _ _ _ _ _ _ _ _ fetchShift stepShift ih
  | hash s final steps cycles calls blocks hf service valid tail range rest ih =>
      have fetchShift : fetch SphincsImages.verify (shift (delta target) s) =
          some (.base .ECALL) := by
        rw [fetch_at, shift_pc,
          instruction_transfer target s.pc range.1 range.2.1 range.2.2]
        simpa [fetch_at] using hf
      have nextShift := writeHash_shift (delta target) s (hash (hashInput s))
      rw [←nextShift] at ih
      exact Trace.hash _ _ _ _ _ _ fetchShift
        (by simpa using service) (by simpa using valid) ih

/-- info: 'SigGolfCandidate.SphincsVerifierWotsRelocationTrace.trace_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms trace_shift

end SigGolfCandidate.SphincsVerifierWotsRelocationTrace
