import SigGolfCandidate.SphincsVerifierXmssRoundFrame

namespace SigGolfCandidate.SphincsVerifierXmssRoundControl
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsVerifierXmssNodeSite
open SigGolfCandidate.SphincsVerifierXmssNodeReady
open SigGolfCandidate.SphincsVerifierXmssNext
open SigGolfCandidate.SphincsVerifierXmssRound
open SigGolfCandidate.SphincsVerifierXmssRoundFrame
open SigGolfCandidate.SphincsVerifierFtsParentLevel
open SigGolfCandidate.SphincsVerifierXmssAnswer
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem next_pc_repeat (lay : Layer) (s : MachineState) (k : Nat)
    (pc : s.pc = advancePc lay)
    (level : s.getMem 0x43048 = BitVec.ofNat 64 k)
    (small : k < layerHeight lay) :
    (nextState lay s).pc = nodePc lay := by
  let a := advanceLevelState s
  let c := checkState lay a
  have apc : a.pc = checkPc lay := by
    simp [a, advanceLevelState, execInstrBr, pc, checkPc]
    bv_decide
  have cpc : c.pc = branchPc lay := by
    simp [c, checkState, execInstrBr, apc, branchPc, checkPc]
    bv_decide
  have values := check_values lay a
  have aLevel : a.getMem 0x43048 = BitVec.ofNat 64 (k + 1) := by
    rw [advanceLevel_cell, level, BitVec.ofNat_add]
    rfl
  have different : c.getReg .x6 ≠ c.getReg .x7 := by
    rw [values.1, values.2, aLevel]
    fin_cases lay <;> simp [layerHeight, maxLayerHeight] at small ⊢
    all_goals interval_cases k <;> decide
  exact branch_pc_repeat lay c cpc different

theorem next_pc_done (lay : Layer) (s : MachineState)
    (pc : s.pc = advancePc lay)
    (level : s.getMem 0x43048 =
      BitVec.ofNat 64 (layerHeight lay)) :
    (nextState lay s).pc = branchPc lay + 4 := by
  let a := advanceLevelState s
  let c := checkState lay a
  have apc : a.pc = checkPc lay := by
    simp [a, advanceLevelState, execInstrBr, pc, checkPc]
    bv_decide
  have cpc : c.pc = branchPc lay := by
    simp [c, checkState, execInstrBr, apc, branchPc, checkPc]
    bv_decide
  have values := check_values lay a
  have aLevel : a.getMem 0x43048 =
      BitVec.ofNat 64 (layerHeight lay + 1) := by
    rw [advanceLevel_cell, level, BitVec.ofNat_add]
    rfl
  have same : c.getReg .x6 = c.getReg .x7 := by
    rw [values.1, values.2, aLevel]
  exact branch_pc_done lay c cpc same

theorem preNext_level_cell (hash : Hash) (lay : Layer) (s : MachineState) :
    (nodeHashNext hash (readyState s)).getMem 0x43048 =
      s.getMem 0x43048 := by
  have h := round_level_cell hash lay s
  change (nextState lay (nodeHashNext hash (readyState s))).getMem 0x43048 =
    s.getMem 0x43048 + 1 at h
  rw [SphincsVerifierXmssRoundInvariant.next_level_cell] at h
  exact add_right_cancel h

theorem preNext_pc (hash : Hash) (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay)
    (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0) :
    (nodeHashNext hash (readyState s)).pc = advancePc lay := by
  let r := readyState s
  let hashed := writeHash r (hash (hashInput r))
  have ready := ready_trace lay s pc pointer pointerValue small aligned
  have hashPc : hashed.pc = nodeHashPc lay + 4 := by
    have rpc : r.pc = nodeHashPc lay := ready.2.1
    simp [hashed, writeHash, r, ready.2.1]
  simpa [nodeHashNext, r, hashed, advancePc] using
    nodeAnswerCopy_pc lay hashed hashPc

theorem round_pc_repeat (hash : Hash) (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay)
    (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (pointerSmall : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0)
    (k : Nat)
    (level : s.getMem 0x43048 = BitVec.ofNat 64 k)
    (small : k < layerHeight lay) :
    (roundState hash lay s).pc = nodePc lay := by
  change (nextState lay (nodeHashNext hash (readyState s))).pc = nodePc lay
  apply next_pc_repeat lay (nodeHashNext hash (readyState s)) k
  · exact preNext_pc hash lay s pc pointer pointerValue pointerSmall aligned
  · rw [preNext_level_cell hash lay s]
    exact level
  · exact small

theorem round_pc_done (hash : Hash) (lay : Layer) (s : MachineState)
    (pc : s.pc = nodePc lay)
    (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (pointerSmall : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0)
    (level : s.getMem 0x43048 =
      BitVec.ofNat 64 (layerHeight lay)) :
    (roundState hash lay s).pc = branchPc lay + 4 := by
  change (nextState lay (nodeHashNext hash (readyState s))).pc = branchPc lay + 4
  apply next_pc_done lay (nodeHashNext hash (readyState s))
  · exact preNext_pc hash lay s pc pointer pointerValue pointerSmall aligned
  · rw [preNext_level_cell hash lay s]
    exact level

#print axioms next_pc_repeat
#print axioms next_pc_done
#print axioms preNext_level_cell
#print axioms preNext_pc
#print axioms round_pc_repeat
/-- info: 'SigGolfCandidate.SphincsVerifierXmssRoundControl.round_pc_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms round_pc_done

end SigGolfCandidate.SphincsVerifierXmssRoundControl
