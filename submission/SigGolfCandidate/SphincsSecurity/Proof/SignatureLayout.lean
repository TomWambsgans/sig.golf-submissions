import SigGolfCandidate.SphincsSecurity.Scheme
import Mathlib.Tactic.IrreducibleDef
import SigGolfCandidate.SphincsSecurity.Proof.Ots.Code
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.Parameters
import SigGolfCandidate.SphincsSecurity.Proof.Fts.Parameters

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
