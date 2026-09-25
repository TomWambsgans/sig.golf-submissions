import SigGolfCandidate.SphincsVerifierXmssNodeTransport

namespace SigGolfCandidate.SphincsVerifierXmssRoundInvariant
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssRound
open SigGolfCandidate.SphincsVerifierXmssNext
open SigGolfCandidate.SphincsVerifierXmssAnswer
open SigGolfCandidate.SphincsVerifierFtsParentLevel
open SigGolfCandidate.SphincsVerifierXmssNodeTransport
open SigGolfCandidate.SphincsVerifierXmssNodeHeader
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierHashBytes
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem next_mem_frame (lay : Layer) (s : MachineState) (read : Word)
    (outside : read ≠ 0x43048) :
    (nextState lay s).getMem read = s.getMem read := by
  simp [nextState, branchState, checkState, execInstrBr]
  exact advanceLevel_mem_frame s read outside

theorem next_level_cell (lay : Layer) (s : MachineState) :
    (nextState lay s).getMem 0x43048 = s.getMem 0x43048 + 1 := by
  simp [nextState, branchState, checkState, execInstrBr]
  exact advanceLevel_cell s

theorem round_current_byte (hash : Hash) (lay : Layer) (s : MachineState)
    (destination : (readyState s).getReg .x12 = 0x42000)
    (i : Nat) (hi : i < 20) :
    (roundState hash lay s).getByte (BitVec.ofNat 64 (0x44a00 + i)) =
      (hash (hashInput (readyState s))).extractLsb' (8 * i) 8 := by
  have outside : alignToDword (BitVec.ofNat 64 (0x44a00 + i)) ≠ 0x43048 := by
    interval_cases i <;> decide
  let addr := BitVec.ofNat 64 (0x44a00 + i)
  have preserved : (nextState lay (nodeHashNext hash (readyState s))).getByte addr =
      (nodeHashNext hash (readyState s)).getByte addr := by
    simp only [MachineState.getByte]
    rw [next_mem_frame lay _ (alignToDword addr) outside]
  exact preserved.trans (nodeHashNext_byte hash (readyState s)
    destination i hi)

theorem round_current_byte_abstract (hash : Hash) (lay : Layer) (s : MachineState)
    (pk : SphincsSecurity.PublicKey) (tree : TreeIndex)
    (level nodeIdx : Nat) (current sibling : Digest) (pointer : Word)
    (pointerValue : s.getMem 0x43028 = pointer)
    (small : pointer.toNat + 20 ≤ 0x40000)
    (aligned : pointer.toNat % 4 = 0)
    (layerCell : s.getMem 0x43000 = BitVec.ofNat 64 lay.val)
    (treeCell : s.getMem 0x43008 = BitVec.ofNat 64 tree.val)
    (levelCell : s.getMem 0x43048 = BitVec.ofNat 64 level)
    (indexCell : s.getMem 0x43070 >>> 1 = BitVec.ofNat 64 nodeIdx)
    (parameterEncoded : WitnessPrefix s pk)
    (currentEncoded : ∀ i, (hi : i < 20) →
      s.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        current.extractLsb' (8 * i) 8)
    (siblingEncoded : ∀ i, (hi : i < 20) →
      s.getByte (BitVec.ofNat 64 (pointer.toNat + i)) =
        sibling.extractLsb' (8 * i) 8)
    (destination : (readyState s).getReg .x12 = 0x42000)
    (i : Nat) (hi : i < 20) :
    (roundState hash lay s).getByte (BitVec.ofNat 64 (0x44a00 + i)) =
      (truncateHash (hash (toQuery (nodeInput pk lay tree level nodeIdx
        (if s.getMem 0x43070 &&& 1 = 0 then current else sibling)
        (if s.getMem 0x43070 &&& 1 = 0 then sibling else current))))).extractLsb'
          (8 * i) 8 := by
  rw [round_current_byte hash lay s destination i hi,
    ready_hashInput_from_pair s pk lay tree level nodeIdx current sibling pointer
      pointerValue small aligned layerCell treeCell levelCell indexCell
      parameterEncoded currentEncoded siblingEncoded]
  exact
    (BitVec.extractLsb'_extractLsb'_of_le
      (x := hash (toQuery (nodeInput pk lay tree level nodeIdx
        (if s.getMem 0x43070 &&& 1 = 0 then current else sibling)
        (if s.getMem 0x43070 &&& 1 = 0 then sibling else current))))
      (start := 8 * i) (len := 8) (len' := digestBits)
      (by unfold digestBits; omega)).symm

#print axioms next_mem_frame
#print axioms next_level_cell
#print axioms round_current_byte
/-- info: 'SigGolfCandidate.SphincsVerifierXmssRoundInvariant.round_current_byte_abstract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms round_current_byte_abstract

end SigGolfCandidate.SphincsVerifierXmssRoundInvariant
