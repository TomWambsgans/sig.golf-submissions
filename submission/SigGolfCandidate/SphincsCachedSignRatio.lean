import SigGolfCandidate.SphincsCachedSignAdaptiveTrace

namespace SigGolfCandidate.CachedSignerTrace
open OracleComp SphincsSecurity SphincsSecurity.Concrete
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- A pointwise cost ratio between two coupled signing oracles lifts through any adaptive strategy. -/
theorem adaptive_signer_ratio
    (hash : QueryImpl HashSpec Id) (secretKey : Seeded.SecretKey)
    (world : QueryImpl OracleWorld Id)
    (single : ∀ message : Message,
      (rawSigner hash secretKey message).1 = (cachedSigner hash secretKey message).1 ∧
      (rawSigner hash secretKey message).2 ≤ 48 * (cachedSigner hash secretKey message).2)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    let raw := runInteraction world (rawSigner hash secretKey) computation
    let cached := runInteraction world (cachedSigner hash secretKey) computation
    raw.value = cached.value ∧
      raw.signingRequests = cached.signingRequests ∧
      raw.hashCalls ≤ 48 * cached.hashCalls := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [runInteraction_pure]
  | query_bind input next ih =>
    cases input with
    | inl input =>
      simp only [runInteraction_query_bind]
      have htail := ih (world input)
      dsimp only at htail ⊢
      constructor
      · exact htail.1
      constructor
      · exact htail.2.1
      · omega
    | inr message =>
      simp only [runInteraction_query_bind]
      have hsingle := single message
      rw [hsingle.1]
      have htail := ih (cachedSigner hash secretKey message).1
      dsimp only at htail ⊢
      constructor
      · exact htail.1
      constructor
      · exact congrArg Nat.succ htail.2.1
      · omega

/-- External hash calls and setup work also fit the same ratio. -/
theorem adaptive_raw_budget_ratio
    (hash : QueryImpl HashSpec Id) (secretKey : Seeded.SecretKey)
    (world : QueryImpl OracleWorld Id)
    (single : ∀ message : Message,
      (rawSigner hash secretKey message).1 = (cachedSigner hash secretKey message).1 ∧
      (rawSigner hash secretKey message).2 ≤ 48 * (cachedSigner hash secretKey message).2)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (outsideCalls q : Nat)
    (hcost : outsideCalls +
      (runInteraction world (cachedSigner hash secretKey) computation).hashCalls ≤ q) :
    outsideCalls +
      (runInteraction world (rawSigner hash secretKey) computation).hashCalls ≤ 48 * q := by
  have hratio := adaptive_signer_ratio hash secretKey world single computation
  dsimp only at hratio
  omega

end SigGolfCandidate.CachedSignerTrace

/-- info: 'SigGolfCandidate.CachedSignerTrace.adaptive_signer_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SigGolfCandidate.CachedSignerTrace.adaptive_signer_ratio
