import SigGolfCandidate.SphincsVerifierXmssPathControl
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.Extract

namespace SigGolfCandidate.SphincsVerifierXmssPathSemantic
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssPathControl
open SigGolfCandidate.SphincsVerifierXmssRound
open SigGolfCandidate.SphincsVerifierXmssRoundFrame
open SigGolfCandidate.SphincsVerifierXmssRoundInvariant
open SigGolfCandidate.SphincsVerifierXmssNodeHeader
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsBridge
open SphincsSecurity.Concrete
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem path_bit_toNat (hash : Hash) (lay : Layer) (n : Nat)
    (s : MachineState) :
    ((pathState hash lay n s).getMem 0x43070).toNat =
      (s.getMem 0x43070).toNat / 2 ^ n := by
  induction n generalizing s with
  | zero => simp [pathState]
  | succ n ih =>
      rw [pathState_succ, ih, round_bit_cell, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]
      congr 1
      omega

theorem path_bit_leaf (hash : Hash) (lay : Layer) (n : Nat)
    (s : MachineState) (leaf : LeafIndex)
    (initial : s.getMem 0x43070 = BitVec.ofNat 64 leaf.val) :
    (pathState hash lay n s).getMem 0x43070 =
      BitVec.ofNat 64 (leaf.val / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [path_bit_toNat, initial]
  have small : leaf.val < 2 ^ 64 := by
    exact lt_trans leaf.isLt (by decide)
  have small' : leaf.val / 2 ^ n < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) small
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt small']

theorem path_node_index (hash : Hash) (lay : Layer) (n : Nat)
    (s : MachineState) (leaf : LeafIndex)
    (initial : s.getMem 0x43070 = BitVec.ofNat 64 leaf.val) :
    (pathState hash lay n s).getMem 0x43070 >>> 1 =
      BitVec.ofNat 64 (leaf.val / 2 ^ (n + 1)) := by
  rw [path_bit_leaf hash lay n s leaf initial]
  apply BitVec.eq_of_toNat_eq
  have small : leaf.val / 2 ^ (n + 1) < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans leaf.isLt (by decide))
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  have smaller : leaf.val / 2 ^ n < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans leaf.isLt (by decide))
  rw [Nat.mod_eq_of_lt smaller, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt small, Nat.pow_succ, Nat.div_div_eq_div_mul]
  congr 1

theorem path_level (hash : Hash) (lay : Layer) (n : Nat)
    (s : MachineState)
    (initial : s.getMem 0x43048 = 1) :
    (pathState hash lay n s).getMem 0x43048 = BitVec.ofNat 64 (n + 1) := by
  rw [path_level_cell, initial, BitVec.ofNat_add]
  bv_omega

theorem path_parity (hash : Hash) (lay : Layer) (n : Nat)
    (s : MachineState) (leaf : LeafIndex)
    (initial : s.getMem 0x43070 = BitVec.ofNat 64 leaf.val) :
    ((pathState hash lay n s).getMem 0x43070 &&& 1 = 0) =
      (leaf.val.testBit n = false) := by
  rw [path_bit_leaf hash lay n s leaf initial]
  have small : leaf.val / 2 ^ n < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans leaf.isLt (by decide))
  apply propext
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt small,
      show (1 : Word).toNat = 1 by decide,
      show (0 : Word).toNat = 0 by decide] at hn
    rw [Nat.and_one_is_mod] at hn
    by_cases ht : leaf.val.testBit n = true
    · have : leaf.val / 2 ^ n % 2 = 1 :=
        (SphincsSecurity.testBit_iff_div_mod _ _).mp ht
      omega
    · cases b : leaf.val.testBit n <;> simp_all
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt small,
      show (1 : Word).toNat = 1 by decide,
      show (0 : Word).toNat = 0 by decide]
    rw [Nat.and_one_is_mod]
    have notTrue : leaf.val.testBit n ≠ true := by simp [h]
    exact Nat.mod_two_ne_one.mp (by
      intro one
      exact notTrue ((SphincsSecurity.testBit_iff_div_mod _ _).mpr one))

theorem pathState_succ_right (hash : Hash) (lay : Layer) (n : Nat)
    (s : MachineState) :
    pathState hash lay (n + 1) s =
      roundState hash lay (pathState hash lay n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [pathState_succ, ih, pathState_succ]

theorem ready_destination (s : MachineState) :
    (readyState s).getReg .x12 = 0x42000 := by
  have regs := SphincsVerifierFtsParentSetup.hashRegisters_ready
    (SphincsVerifierCopy.copyRootState
      (SphincsVerifierFtsParentParameter.parameterPointers
        (SphincsVerifierXmssNodeReady.nodeHeaderState
          (SphincsVerifierXmssNodeReady.nodeTagState
            (SphincsVerifierXmssPrefix.nodePrefixState (pairState s))))))
  exact regs.2.2.1

theorem foldStep_vm (hash : Hash) (lay : Layer)
    (s : MachineState) (pk : SphincsSecurity.PublicKey)
    (tree : TreeIndex) (leaf : LeafIndex)
    (signature : SphincsSecurity.Signature) (first : Digest) (n : Nat)
    (bit : (pathState hash lay n s).getMem 0x43070 =
      BitVec.ofNat 64 (leaf.val / 2 ^ n)) :
    foldValue (adaptOracle hash) pk.parameter lay tree leaf
        (signaturePath signature lay) first (n + 1) =
      truncateHash (hash (toQuery (nodeInput pk lay tree (n + 1)
        (leaf.val / 2 ^ (n + 1))
        (if (pathState hash lay n s).getMem 0x43070 &&& 1 = 0 then
          foldValue (adaptOracle hash) pk.parameter lay tree leaf
            (signaturePath signature lay) first n
        else signaturePath signature lay n)
        (if (pathState hash lay n s).getMem 0x43070 &&& 1 = 0 then
          signaturePath signature lay n
        else foldValue (adaptOracle hash) pk.parameter lay tree leaf
          (signaturePath signature lay) first n)))) := by
  rw [foldValue_succ]
  have parity :
      ((pathState hash lay n s).getMem 0x43070 &&& 1 = 0) =
        (leaf.val.testBit n = false) := by
    rw [bit]
    have small : leaf.val / 2 ^ n < 2 ^ 64 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans leaf.isLt (by decide))
    apply propext
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt small,
        show (1 : Word).toNat = 1 by decide,
        show (0 : Word).toNat = 0 by decide, Nat.and_one_is_mod] at hn
      by_cases ht : leaf.val.testBit n = true
      · have : leaf.val / 2 ^ n % 2 = 1 :=
          (SphincsSecurity.testBit_iff_div_mod _ _).mp ht
        omega
      · cases b : leaf.val.testBit n <;> simp_all
    · intro h
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt small,
        show (1 : Word).toNat = 1 by decide,
        show (0 : Word).toNat = 0 by decide, Nat.and_one_is_mod]
      have notTrue : leaf.val.testBit n ≠ true := by simp [h]
      exact Nat.mod_two_ne_one.mp (by
        intro one
        exact notTrue ((SphincsSecurity.testBit_iff_div_mod _ _).mpr one))
  have inputEq :
      tweakableHashInput pk.parameter
          (.node lay tree (n + 1) (leaf.val / 2 ^ (n + 1)))
          (foldPayload (adaptOracle hash) pk.parameter lay tree leaf
            (signaturePath signature lay) first n) =
        nodeInput pk lay tree (n + 1) (leaf.val / 2 ^ (n + 1))
          (if (pathState hash lay n s).getMem 0x43070 &&& 1 = 0 then
            foldValue (adaptOracle hash) pk.parameter lay tree leaf
              (signaturePath signature lay) first n
          else signaturePath signature lay n)
          (if (pathState hash lay n s).getMem 0x43070 &&& 1 = 0 then
            signaturePath signature lay n
          else foldValue (adaptOracle hash) pk.parameter lay tree leaf
            (signaturePath signature lay) first n) := by
    simp only [nodeInput, parity]
    cases h : leaf.val.testBit n <;>
      simp [foldPayload, orderedPayload, h]
  change truncateHash (adaptOracle hash
      (tweakableHashInput pk.parameter
        (.node lay tree (n + 1) (leaf.val / 2 ^ (n + 1)))
        (foldPayload (adaptOracle hash) pk.parameter lay tree leaf
          (signaturePath signature lay) first n))) =
    truncateHash (adaptOracle hash
      (nodeInput pk lay tree (n + 1) (leaf.val / 2 ^ (n + 1))
        (if (pathState hash lay n s).getMem 0x43070 &&& 1 = 0 then
          foldValue (adaptOracle hash) pk.parameter lay tree leaf
            (signaturePath signature lay) first n
        else signaturePath signature lay n)
        (if (pathState hash lay n s).getMem 0x43070 &&& 1 = 0 then
          signaturePath signature lay n
        else foldValue (adaptOracle hash) pk.parameter lay tree leaf
          (signaturePath signature lay) first n)))
  exact congrArg (fun input => truncateHash (adaptOracle hash input)) inputEq

theorem path_current_byte (hash : Hash) (lay : Layer) (n : Nat)
    (s : MachineState) (pk : SphincsSecurity.PublicKey)
    (tree : TreeIndex) (leaf : LeafIndex)
    (signature : SphincsSecurity.Signature) (first : Digest)
    (pointer : Word)
    (height : n ≤ layerHeight lay)
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
    ∀ i, (hi : i < 20) →
      (pathState hash lay n s).getByte (BitVec.ofNat 64 (0x44a00 + i)) =
        (foldValue (adaptOracle hash) pk.parameter lay tree leaf
          (signaturePath signature lay) first n).extractLsb' (8 * i) 8 := by
  induction n with
  | zero =>
      intro i hi
      simpa [pathState, foldValue, treeFold, evalWithAnswerFn_pure] using
        current i hi
  | succ n ih =>
      intro i hi
      let state := pathState hash lay n s
      let currentValue := foldValue (adaptOracle hash) pk.parameter lay tree leaf
        (signaturePath signature lay) first n
      let siblingValue := signaturePath signature lay n
      let ptr := state.getMem 0x43028
      have nSmall : n < layerHeight lay := by omega
      have ptrNat : ptr.toNat = pointer.toNat + 20 * n := by
        exact path_pointer_nat hash lay n s pointer pointerValue (by omega)
      have ptrBound : ptr.toNat + 20 ≤ 0x40000 := by omega
      have ptrAligned : ptr.toNat % 4 = 0 := by
        rw [ptrNat]
        omega
      have layerState : state.getMem 0x43000 = BitVec.ofNat 64 lay.val := by
        rw [path_layer_cell, layerCell]
      have treeState : state.getMem 0x43008 = BitVec.ofNat 64 tree.val := by
        rw [path_tree_cell, treeCell]
      have levelState : state.getMem 0x43048 = BitVec.ofNat 64 (n + 1) :=
        path_level hash lay n s levelCell
      have indexState : state.getMem 0x43070 >>> 1 =
          BitVec.ofNat 64 (leaf.val / 2 ^ (n + 1)) :=
        path_node_index hash lay n s leaf bitCell
      have prefixState : WitnessPrefix state pk :=
        path_prefix hash lay n s pk hprefix
      have currentState : ∀ j, (hj : j < 20) →
          state.getByte (BitVec.ofNat 64 (0x44a00 + j)) =
            currentValue.extractLsb' (8 * j) 8 := by
        intro j hj
        exact ih (by omega) j hj
      have siblingState : ∀ j, (hj : j < 20) →
          state.getByte (BitVec.ofNat 64 (ptr.toNat + j)) =
            siblingValue.extractLsb' (8 * j) 8 := by
        intro j hj
        exact path_signature_sibling_byte hash lay n s pointer signature
          pointerValue (by omega) nSmall siblings j hj
      have digestStep := round_current_byte_abstract hash lay state pk tree
        (n + 1) (leaf.val / 2 ^ (n + 1)) currentValue siblingValue
        ptr rfl ptrBound ptrAligned layerState treeState levelState indexState
        prefixState currentState siblingState (ready_destination state) i hi
      have abstractStep := foldStep_vm hash lay s pk tree leaf signature first n
        (path_bit_leaf hash lay n s leaf bitCell)
      rw [pathState_succ_right]
      exact digestStep.trans (congrArg (fun value : Digest =>
        value.extractLsb' (8 * i) 8) abstractStep.symm)

/-- info: 'SigGolfCandidate.SphincsVerifierXmssPathSemantic.path_current_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms path_current_byte

end SigGolfCandidate.SphincsVerifierXmssPathSemantic
