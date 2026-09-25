import SigGolfCandidate.SphincsVerifierXmssPathSemantic

namespace SigGolfCandidate.SphincsVerifierXmssPathComplete
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssPathControl
open SigGolfCandidate.SphincsVerifierXmssPathSemantic
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsVerifierXmssNext
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsBridge
open SphincsSecurity.Concrete
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- A complete authentication path reaches the abstract XMSS root at the exit PC. -/
theorem complete_path (hash : Hash) (lay : Layer)
    (s : MachineState) (pk : SphincsSecurity.PublicKey)
    (tree : TreeIndex) (leaf : LeafIndex)
    (signature : SphincsSecurity.Signature) (first : Digest)
    (pointer : Word)
    (pc : s.pc = nodePc lay)
    (pointerValue : s.getMem 0x43028 = pointer)
    (pointerBound : pointer.toNat + 20 * layerHeight lay ≤ 0x40000)
    (pointerAligned : pointer.toNat % 4 = 0)
    (layerCell : s.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (treeCell : s.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (levelCell : s.getMem 0x43048 = 1)
    (bitCell : s.getMem 0x43070 = BitVec.ofNat 64 leaf.val)
    (hprefix : WitnessPrefix s pk)
    (current : ∀ i, (hi : i < 20) →
      s.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        first.extractLsb' (8 * i) 8)
    (siblings : PathWitness s signature lay pointer) :
    let doneState := pathState hash lay (layerHeight lay) s
    doneState.pc = branchPc lay + 4 ∧
      (∀ i, (hi : i < 20) →
        doneState.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (foldValue (adaptOracle hash) pk.parameter lay tree leaf
            (signaturePath signature lay) first (layerHeight lay)).extractLsb'
              (8 * i) 8) ∧
      pathCycles hash lay (layerHeight lay) s ≤ 141 * layerHeight lay := by
  dsimp
  have positive : 1 ≤ layerHeight lay := by
    fin_cases lay <;> decide
  refine ⟨?_, ?_, ?_⟩
  · exact path_pc_done hash lay (layerHeight lay) 1 s pointer
      (by omega) positive (by omega) pc levelCell pointerValue
      pointerBound pointerAligned
  · exact path_current_byte hash lay (layerHeight lay) s pk tree leaf
      signature first pointer (by omega) pointerValue pointerBound
      pointerAligned layerCell treeCell levelCell bitCell hprefix current siblings
  · exact pathCycles_le hash lay (layerHeight lay) s

/-- Prefix the exact machine trace to any continuation after the XMSS root. -/
theorem complete_path_executes (hash : Hash) (lay : Layer)
    (s : MachineState) (pointer : Word)
    (pc : s.pc = nodePc lay)
    (pointerValue : s.getMem 0x43028 = pointer)
    (pointerBound : pointer.toNat + 20 * layerHeight lay ≤ 0x40000)
    (pointerAligned : pointer.toNat % 4 = 0)
    (levelCell : s.getMem 0x43048 = 1)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (pathState hash lay (layerHeight lay) s) steps result) :
    Executes hash SphincsImages.verify s
      (steps + pathInstructions hash lay (layerHeight lay) s)
      (result.charge (pathCycles hash lay (layerHeight lay) s)
        (layerHeight lay) (2 * layerHeight lay)) := by
  exact path_executes hash lay (layerHeight lay) 1 s pointer steps result
    (by omega) (Or.inr pc) levelCell pointerValue pointerBound pointerAligned tail

/-- info: 'SigGolfCandidate.SphincsVerifierXmssPathComplete.complete_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms complete_path
/-- info: 'SigGolfCandidate.SphincsVerifierXmssPathComplete.complete_path_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms complete_path_executes

end SigGolfCandidate.SphincsVerifierXmssPathComplete


namespace SigGolfCandidate.SphincsVerifierXmssFinish
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def finishSchedule : List (Word × Instr) := [
  (0x7c3c, .LUI .x6 0x45),
  (0x7c40, .ADDI .x6 .x6 0xa00),
  (0x7c44, .LUI .x7 0x23),
  (0x7c48, .ADDI .x7 .x7 0xca0),
  (0x7c4c, .LWU .x10 .x6 0),
  (0x7c50, .LWU .x11 .x7 0),
  (0x7c54, .BEQ .x10 .x11 8),
  (0x7c5c, .LWU .x10 .x6 4),
  (0x7c60, .LWU .x11 .x7 4),
  (0x7c64, .BEQ .x10 .x11 8),
  (0x7c6c, .LWU .x10 .x6 8),
  (0x7c70, .LWU .x11 .x7 8),
  (0x7c74, .BEQ .x10 .x11 8),
  (0x7c7c, .LWU .x10 .x6 12),
  (0x7c80, .LWU .x11 .x7 12),
  (0x7c84, .BEQ .x10 .x11 8),
  (0x7c8c, .LWU .x10 .x6 16),
  (0x7c90, .LWU .x11 .x7 16),
  (0x7c94, .BEQ .x10 .x11 8)]

def afterComparison (s : MachineState) : MachineState :=
  runSchedule finishSchedule s

def finishState (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (afterComparison s) (.ADDI .x5 .x0 0))
    (.ADDI .x10 .x0 1)

private theorem widened_eq_iff (a b : BitVec 32) :
    (a.setWidth 64 = b.setWidth 64) ↔ a = b := by
  constructor
  · intro h
    have q := congrArg (fun x : BitVec 64 => x.setWidth 32) h
    simpa using q
  · intro h
    rw [h]

theorem finish_code : ∀ entry ∈ finishSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by decide

theorem finish_checked (s : MachineState) (pc : s.pc = 0x7c3c)
    (rootWords : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * i.val))) :
    Checked finishSchedule s := by
  have h0 := rootWords 0
  have h1 := rootWords 1
  have h2 := rootWords 2
  have h3 := rootWords 3
  have h4 := rootWords 4
  norm_num at h0 h1 h2 h3 h4
  simp [Checked, finishSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, signExtend13, widened_eq_iff,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc, h0, h1, h2, h3, h4]

theorem finish_block (s : MachineState) (pc : s.pc = 0x7c3c)
    (rootWords : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * i.val))) :
    OrdinarySteps SphincsImages.verify s 19 (afterComparison s) := by
  exact checked_sound _ finishSchedule finish_code s (finish_checked s pc rootWords)

theorem afterComparison_pc (s : MachineState) (pc : s.pc = 0x7c3c)
    (rootWords : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * i.val))) :
    (afterComparison s).pc = 0x7c9c := by
  have h0 := rootWords 0
  have h1 := rootWords 1
  have h2 := rootWords 2
  have h3 := rootWords 3
  have h4 := rootWords 4
  norm_num at h0 h1 h2 h3 h4
  simp [afterComparison, runSchedule, finishSchedule, execInstrBr,
    signExtend12, signExtend13, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc, h0, h1, h2, h3, h4]

theorem finish_registers (s : MachineState) (pc : s.pc = 0x7c3c)
    (rootWords : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * i.val))) :
    (finishState s).pc = 0x7ca4 ∧
    (finishState s).getReg .x5 = 0 ∧
    (finishState s).getReg .x10 = 1 := by
  have loc := afterComparison_pc s pc rootWords
  simp [finishState, execInstrBr, signExtend12, loc,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem finish_tail_block (s : MachineState) (pc : s.pc = 0x7c9c) :
    OrdinarySteps SphincsImages.verify s 2
      (execInstrBr (execInstrBr s (.ADDI .x5 .x0 0))
        (.ADDI .x10 .x0 1)) := by
  apply OrdinarySteps.step s (execInstrBr s (.ADDI .x5 .x0 0)) _
    (.base (.ADDI .x5 .x0 0)) 1
  · rw [SphincsVerifierFtsRootCopy.fetch_at, pc]
    decide
  · rfl
  apply OrdinarySteps.step _ _ _ (.base (.ADDI .x10 .x0 1)) 0
  · have nextPc : (execInstrBr s (.ADDI .x5 .x0 0)).pc = 0x7ca0 := by
      simp [execInstrBr, pc]
    rw [SphincsVerifierFtsRootCopy.fetch_at, nextPc]
    decide
  · rfl
  exact OrdinarySteps.refl _

theorem finish_executes (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x7c3c)
    (rootWords : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * i.val))) :
    Executes hash SphincsImages.verify s 22
      ⟨.success, finishState s, 22, 0, 0⟩ := by
  obtain ⟨loc, service, status⟩ := finish_registers s pc rootWords
  have fetch : fetch SphincsImages.verify (finishState s) =
      some (.base .ECALL) := by
    rw [SphincsVerifierFtsRootCopy.fetch_at, loc]
    decide
  have terminal := Executes.halt (hash := hash)
    (image := SphincsImages.verify) (finishState s) fetch service
  have whole := ((finish_block s pc rootWords).append
    (finish_tail_block (afterComparison s) (afterComparison_pc s pc rootWords))).then_executes terminal
  simpa [status, Execution.charge] using whole

/-- info: 'SigGolfCandidate.SphincsVerifierXmssFinish.finish_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finish_executes

end SigGolfCandidate.SphincsVerifierXmssFinish
