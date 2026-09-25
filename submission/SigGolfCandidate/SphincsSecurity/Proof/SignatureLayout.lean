import SigGolfCandidate.SphincsSecurity.Scheme
import Mathlib.Tactic.IrreducibleDef
import SigGolfCandidate.SphincsSecurity.Proof.Ots.Code
import SigGolfCandidate.SphincsSecurity.Proof.Fts.Parameters

/-!
# Hypertree hash costs

The oracle calls an honest computation of the hypertree makes, as formulas in the parameters of `Scheme.lean`. They are sealed, so the accounting carries them symbolically and never evaluates them.
-/

namespace SphincsSecurity.Concrete

/-- A one-time public key: every chain walked to its end. -/
irreducible_def oneTimeKeyHashCost : Nat := numChains * (chainLength - 1)

/-- A node at `level` of a layer tree, the leaves being level `0`: each leaf is a one-time public key and its leaf hash. -/
irreducible_def treeNodeHashCost (level : Nat) : Nat := (oneTimeKeyHashCost + 2) * 2 ^ level - 1

/-- Key generation: the root of the top layer's tree. -/
irreducible_def keygenHashCost : Nat := treeNodeHashCost (layerHeight topLayer)

theorem treeNodeHashCost_zero : treeNodeHashCost 0 = oneTimeKeyHashCost + 1 := by
  rw [treeNodeHashCost_def, pow_zero, mul_one]
  omega

theorem treeNodeHashCost_succ (level : Nat) :
    treeNodeHashCost (level + 1) = treeNodeHashCost level + (treeNodeHashCost level + 1) := by
  simp only [treeNodeHashCost_def, pow_succ, ← mul_assoc]
  have hpos : 0 < (oneTimeKeyHashCost + 2) * 2 ^ level := by positivity
  generalize (oneTimeKeyHashCost + 2) * 2 ^ level = nodes at hpos ⊢
  omega

end SphincsSecurity.Concrete


/-!
# Where the two budget routes meet

`budgetSplit` is the budget at which the proof switches from the forced few-time games to the retained residual monitor. `primitiveCoefficient` bounds, per query below it, the one-time primitive events and the message work of the full certificate. Both are sealed; their values enter only `primitive_rates_small` and the closing arithmetic.
-/

namespace SphincsSecurity.Concrete

open ENNReal

irreducible_def budgetSplit : Nat := 3 * 2 ^ 114

noncomputable irreducible_def primitiveCoefficient : ENNReal := 7 / 4

theorem budgetSplit_le : budgetSplit ≤ 2 ^ 127 := by
  rw [budgetSplit_def]
  norm_num

end SphincsSecurity.Concrete


namespace SphincsSecurity

theorem layerHeight_le (lay : Layer) : layerHeight lay ≤ maxLayerHeight := by
  unfold layerHeight maxLayerHeight
  split_ifs <;> omega

abbrev Signature.counter (signature : Signature) (lay : Layer) : Counter :=
  (signature.layers lay).counter

abbrev Signature.chainValue (signature : Signature) (lay : Layer) : ChainIndex → Digest :=
  (signature.layers lay).chainValues

abbrev PaddedLayer := Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest)

/-- Restrict an intermediate proof's padded path to the layer's actual height. -/
abbrev LayerSignature.ofPadded (lay : Layer) (part : PaddedLayer) : LayerSignature lay :=
  ⟨part.1, part.2.1, fun level => part.2.2 (level.castLE (layerHeight_le lay))⟩

@[ext]
theorem LayerSignature.ext {lay : Layer} {left right : LayerSignature lay}
    (hcounter : left.counter = right.counter) (hvalues : left.chainValues = right.chainValues)
    (hpath : left.path = right.path) : left = right := by
  cases left
  cases right
  simp_all

end SphincsSecurity
