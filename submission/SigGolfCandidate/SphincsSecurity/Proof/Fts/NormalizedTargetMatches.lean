import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeFresh
import SigGolfCandidate.SphincsSecurity.Proof.Fts.SubsetTargetExpectation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_uniformHashOutput_admissible_weight (weight : FewTimeView → ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0)) =
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ *
        ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight target := by
  have hexpand (output : HashOutput) :
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0) =
        ∑' target, if Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = target then weight target else 0 := by
    by_cases h : Admissible (truncateMessageDigest output) <;> simp only [h, true_and, false_and, if_true, if_false, tsum_zero]
    simp
  simp_rw [hexpand, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro target
  calc
    _ = Pr[fun output => Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = target |
        ($ᵗ HashOutput : ProbComp HashOutput)] * weight target := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro output
      split_ifs <;> simp
    _ = _ := by
      simp only [← signAttemptResultOfOutput_ne_none_iff]
      rw [probEvent_uniformHashOutput_admissible_view (fun view => view = target),
        probEvent_eq_eq_probOutput, mul_assoc]

end SphincsSecurity.Concrete


/-! ## TargetCacheProductQuery -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sourceSubsetMatch_prod {m : Nat} (target source : FewTimeView) (groups : Fin m → Finset FtsTree) (selected : Finset (Fin m)) :
    (∏ slot ∈ selected, sourceSubsetMatch target source (groups slot)) =
      sourceSubsetMatch target source (selected.biUnion groups) := by
  induction selected using Finset.induction_on with
  | empty => simp [sourceSubsetMatch]
  | @insert slot selected hnot ih =>
      rw [Finset.prod_insert hnot, Finset.biUnion_insert, ih, sourceSubsetMatch_mul]

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def normalizedSourceSubsetMatch (target source : FewTimeView) (required : Finset FtsTree) : ENNReal :=
  (Fintype.card FtsLeaf ^ required.card : Nat) * (sourceSubsetMatch target source required : ENNReal)

theorem normalizedSourceSubsetMatch_prod {m : Nat} (target source : FewTimeView) (groups : Fin m → Finset FtsTree)
    (selected : Finset (Fin m)) (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) =
      normalizedSourceSubsetMatch target source (selected.biUnion groups) := by
  simp only [normalizedSourceSubsetMatch, Finset.prod_mul_distrib, ← Nat.cast_prod,
    Finset.prod_pow_eq_pow_sum, sourceSubsetMatch_prod, Finset.card_biUnion hdisjoint]

theorem expected_normalizedSourceSubsetMatch (target : FewTimeView) (required : Finset FtsTree) (hne : required.Nonempty) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * normalizedSourceSubsetMatch target source required) =
      (Fintype.card Index : ENNReal)⁻¹ := by
  simp only [normalizedSourceSubsetMatch, mul_left_comm (Pr[= _ | ($ᵗ FewTimeView : ProbComp FewTimeView)]), ENNReal.tsum_mul_left]
  exact normalized_expected_sourceSubsetMatch target required hne

theorem expected_normalizedSourceSubsetMatch_prod {m : Nat} (target : FewTimeView) (groups : Fin m → Finset FtsTree)
    (selected : Finset (Fin m)) (hselected : selected.Nonempty) (hgroups : ∀ slot ∈ selected, (groups slot).Nonempty)
    (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      ∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) = (Fintype.card Index : ENNReal)⁻¹ := by
  simp only [normalizedSourceSubsetMatch_prod target _ groups selected hdisjoint]
  obtain ⟨slot, hslot⟩ := hselected
  obtain ⟨tree, htree⟩ := hgroups slot hslot
  exact expected_normalizedSourceSubsetMatch target _ ⟨tree, Finset.mem_biUnion.mpr ⟨slot, hslot, htree⟩⟩

theorem expected_hash_normalizedSourceSubsetMatch_prod {m : Nat} (target : FewTimeView) (groups : Fin m → Finset FtsTree)
    (selected : Finset (Fin m)) (hselected : selected.Nonempty) (hgroups : ∀ slot ∈ selected, (groups slot).Nonempty)
    (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        ∏ slot ∈ selected, normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) else 0)) =
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹ := by
  rw [expected_uniformHashOutput_admissible_weight
    (fun source => ∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)),
    expected_normalizedSourceSubsetMatch_prod target groups selected hselected hgroups hdisjoint]

end SphincsSecurity.Concrete
