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
