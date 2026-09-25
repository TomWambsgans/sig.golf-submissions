import SigGolfCandidate.SphincsCachedSignTraceSign

/-! Pathwise accounting for any sequence of signing requests. The message
sequence may be chosen adaptively; this theorem does not assume a distribution
or independence. The game-level coupling must additionally establish that the
two executions expose the same signature replies and therefore have the same
request sequence. -/

namespace SigGolfCandidate.CachedSignerTrace

open SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCachedSignValue

noncomputable def rawSigningCalls (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message) : Nat :=
  (runCount hash
    (Seeded.sign secretKey message : OracleComp HashSpec (Option Signature))).2

noncomputable def cachedSigningCalls (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message) : Nat :=
  (runCount hash
    (signWithCache secretKey message (canonicalTopCache hash secretKey))).2

theorem signingRequests_calls_le (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (messages : List Message) :
    (messages.map (rawSigningCalls hash secretKey)).sum ≤
      (messages.map (cachedSigningCalls hash secretKey)).sum +
        messages.length * 1711698 := by
  induction messages with
  | nil => simp
  | cons message rest ih =>
    have hsingle := (runCount_sign_related hash secretKey message).2
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    dsimp [rawSigningCalls, cachedSigningCalls] at hsingle ⊢
    omega

theorem signingRequests_calls_le_lifetime (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (messages : List Message)
    (hrequests : messages.length ≤ signatureLimit) :
    (messages.map (rawSigningCalls hash secretKey)).sum ≤
      (messages.map (cachedSigningCalls hash secretKey)).sum +
        signatureLimit * 1711698 := by
  have h := signingRequests_calls_le hash secretKey messages
  have hmul := Nat.mul_le_mul_right 1711698 hrequests
  exact h.trans (Nat.add_le_add_left hmul _)

theorem lifetime_extra_calls_lt : signatureLimit * 1711698 < 2 ^ 53 := by
  norm_num [signatureLimit]

/-- info: 'SigGolfCandidate.CachedSignerTrace.signingRequests_calls_le_lifetime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms signingRequests_calls_le_lifetime

end SigGolfCandidate.CachedSignerTrace
