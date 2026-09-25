import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Replay
/-!
# Finite witnesses for the few-time leak

A leak chooses one successful signing entry for each of the twenty opened trees. Keeping the
range of that choice as a finset exposes the number of distinct signatures used by the opening.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

abbrev SigningEntry := (request : Message) × SigningSpec.Range request
theorem indexGroup_eq_ftsIndexOf_or_last (tree : IndexGroup) :
    (∃ ftsTree : FtsTree, tree = ftsIndexOf ftsTree) ∨ tree = lastIndexGroup := by
  by_cases htree : tree.val < ftsTrees - 1
  · left
    let ftsTree : FtsTree := ⟨tree.val, htree⟩
    refine ⟨ftsTree, Fin.ext ?_⟩
    rfl
  · right
    apply Fin.ext
    change tree.val = 24
    change ¬ tree.val < 24 at htree
    have hlt := tree.isLt
    change tree.val < 25 at hlt
    omega

end SphincsSecurity.Concrete

/-!
# Probability of a fixed few-time coverage pattern

The relevant part of an admissible digest is its 34-bit index and its twenty opened 8-bit leaf
coordinates.  For a fixed assignment of trees to distinct signing results, the successful tuples
are in bijection with one free index and one free leaf vector per signing result.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

abbrev FewTimeView := Index × (FtsTree → FtsLeaf)

theorem fewTimeView_card : Fintype.card FewTimeView =
    2 ^ (totalHeight + ftsTreeHeight * (ftsTrees - 1)) := by
  simp only [FewTimeView, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Index, FtsTree, FtsLeaf]
  rw [← pow_mul, ← pow_add]

noncomputable local instance instSampleableTypeOfFintypeOfNonempty_sphincsSecurity {R : Type} [Fintype R] [Nonempty R] : SampleableType R :=
  SampleableType.ofFintype R

end SphincsSecurity.Concrete
