import SphincsSecurity.Proof.Event.Transfer
import SphincsSecurity.Proof.Residual.RetainedResidualEventLarge
/-!
# Assembly of the event form

The ideal (independent) scheme's event-form bound splits at `budgetSplit`: above it the large-budget
chain (`RetainedResidualEventLarge`), below it the small-budget chain.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security

theorem independentEventStatement_of_small
    (hsmall : ∀ q, 1 ≤ q → q ≤ Concrete.budgetSplit → ∀ adversary : SphincsSecurity.Adversary,
      Concrete.forgeEventAdvantage Concrete.scheme adversary q ≤ (q : ENNReal) / 2 ^ 127) :
    IndependentEventStatement := by
  intro q hq adversary
  have hcast : ((2 ^ 127 : Nat) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 127 := by norm_num
  rw [hcast]
  by_cases h : q ≤ Concrete.budgetSplit
  · exact hsmall q hq h adversary
  · exact Concrete.security127_event_of_large_budget q (by omega) adversary

end SphincsSecurity.Security
