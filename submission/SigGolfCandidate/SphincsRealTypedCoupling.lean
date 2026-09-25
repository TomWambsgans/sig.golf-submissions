import SigGolfCandidate.SphincsTypedInteractionPlan

/-! Pointwise coupling of actual masked-cache signing requests to the typed
all-failure interaction, up to the first altered-ciphertext MAC success. -/

namespace SigGolfCandidate.SphincsRealTypedCoupling
open SigGolf OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsTypedInteractionPlan
open SigGolfCandidate.SphincsCacheMacTypedGame
open SigGolfCandidate.SphincsCacheMacFiniteDomain
open SigGolfCandidate.SphincsCacheRequestSplit
open SigGolfCandidate.SphincsAlignedQuery
open SigGolfCandidate.SphincsCacheBlindMacGuess
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem altered_test_hit_iff_tag_pass
    (hash : SigGolf.Hash) (secretKey : SigGolf.SecretKey)
    (canonical cache : SigGolf.Cache)
    (hprefix : authPrefix cache ≠ authPrefix canonical) :
    truncateHash (hash (SigGolfCandidate.SphincsBridge.toQuery
      (alteredInput (SphincsMaskedKeygenRefinement.parameter hash secretKey)
        secretKey (ciphertext canonical)
        ⟨ciphertext cache,
          ciphertext_ne_of_auth_prefix_ne cache canonical hprefix⟩))) =
      macTag cache ↔ TagPass hash secretKey cache := by
  unfold TagPass alteredInput
  rw [cacheCiphertext_eq_ofFn]
  exact eq_comm

def macAnswer (hash : SigGolf.Hash) (secretKey : SigGolf.SecretKey)
    (canonical : SigGolf.Cache)
    (test : Altered (ciphertext canonical)) : Digest :=
  truncateHash (hash (SigGolfCandidate.SphincsBridge.toQuery
    (alteredInput (SphincsMaskedKeygenRefinement.parameter hash secretKey)
      secretKey (ciphertext canonical) test)))

noncomputable def realTrace
    (adversary : SigGolf.Adversary SphincsSubmission.submission.sizes)
    (hash : SigGolf.Hash) (secretKey : SigGolf.SecretKey)
    (canonical : SigGolf.Cache)
    (nonalignedAnswer : NonalignedQuery → BitVec 256)
    (world : QueryImpl SphincsCacheMacThreeService.OuterWorld Id)
    (Q : Nat) : Nat → adversary.State → Nat →
      List (Altered (ciphertext canonical) × Digest)
  | 0, _, _ => []
  | rounds + 1, state, count =>
      match adversary.step state with
      | .submit _ => []
      | .hash input resume =>
          if h : input.1 % 8 = 0 then
            realTrace adversary hash secretKey canonical nonalignedAnswer world Q rounds
              (resume (world (.inl (.inr (alignedInput input h))))) count
          else
            realTrace adversary hash secretKey canonical nonalignedAnswer world Q rounds
              (resume (nonalignedAnswer ⟨input, h⟩)) count
      | .sample n resume =>
          realTrace adversary hash secretKey canonical nonalignedAnswer world Q rounds
            (resume (world (.inl (.inl n)))) count
      | .step next =>
          realTrace adversary hash secretKey canonical nonalignedAnswer world Q rounds
            next count
      | .sign request resume =>
          if count < Q ∧ count < SigGolf.LIFETIME then
            let response := (SphincsSubmission.submission.runWith hash .sign
              (secretKey, request.cache, request.message)).value
            let tail := realTrace adversary hash secretKey canonical nonalignedAnswer
              world Q rounds (resume response) (count + 1)
            if hprefix : authPrefix request.cache = authPrefix canonical then tail
            else
              (⟨ciphertext request.cache,
                ciphertext_ne_of_auth_prefix_ne request.cache canonical hprefix⟩,
                macTag request.cache) :: tail
          else []

theorem realTrace_eq_typedFailureTrace_no_hit
    (adversary : SigGolf.Adversary SphincsSubmission.submission.sizes)
    (hash : SigGolf.Hash) (secretKey : SigGolf.SecretKey)
    (canonical : SigGolf.Cache)
    (sem : SphincsMaskedKeygenRefinement.CacheSemantics hash secretKey canonical)
    (nonalignedAnswer : NonalignedQuery → BitVec 256)
    (wire : SphincsSecurity.Signature →
      SigGolf.Bytes SphincsSubmission.submission.sizes.signature)
    (world : QueryImpl SphincsCacheMacThreeService.OuterWorld Id)
    (hcanonical : ∀ message : SigGolf.Message,
      (world (.inr message)).map wire =
        (SphincsSubmission.submission.runWith hash .sign
          (secretKey, canonical, message)).value)
    (Q rounds : Nat) (state : adversary.State) (count : Nat)
    (hmiss : ¬Hit
      (typedFailureTrace world
        (plan adversary canonical nonalignedAnswer wire Q rounds state count))
      (macAnswer hash secretKey canonical)) :
    realTrace adversary hash secretKey canonical nonalignedAnswer world Q rounds
      state count =
    typedFailureTrace world
      (plan adversary canonical nonalignedAnswer wire Q rounds state count) := by
  induction rounds generalizing state count with
  | zero => simp [realTrace, plan, typedFailureTrace]
  | succ rounds ih =>
      cases haction : adversary.step state with
      | submit candidate => simp [realTrace, plan, haction, typedFailureTrace]
      | hash input resume =>
          by_cases halign : input.1 % 8 = 0
          · simp [realTrace, plan, haction, halign, typedFailureTrace] at hmiss ⊢
            exact ih (resume (world (.inl (.inr (alignedInput input halign)))))
              count hmiss
          · have hmiss' : ¬Hit
                (typedFailureTrace world (plan adversary canonical
                  nonalignedAnswer wire Q rounds
                  (resume (nonalignedAnswer ⟨input, halign⟩)) count))
                (macAnswer hash secretKey canonical) := by
              simpa [plan, haction, halign] using hmiss
            simpa [realTrace, plan, haction, halign] using
              ih (resume (nonalignedAnswer ⟨input, halign⟩)) count hmiss'
      | sample n resume =>
          simp [realTrace, plan, haction, typedFailureTrace] at hmiss ⊢
          exact ih (resume (world (.inl (.inl n)))) count hmiss
      | step next =>
          have hmiss' : ¬Hit
              (typedFailureTrace world (plan adversary canonical
                nonalignedAnswer wire Q rounds next count))
              (macAnswer hash secretKey canonical) := by
            simpa [plan, haction] using hmiss
          simpa [realTrace, plan, haction] using ih next count hmiss'
      | sign request resume =>
          by_cases hcap : count < Q ∧ count < SigGolf.LIFETIME
          · by_cases hprefix : authPrefix request.cache = authPrefix canonical
            · by_cases htag : macTag request.cache = macTag canonical
              · have hcache := cache_eq_of_prefix_tag request.cache canonical
                  hprefix htag
                have hvalue := hcanonical request.message
                simp [realTrace, plan, haction, hcap,
                  typedFailureTrace, hcache, hvalue] at hmiss ⊢
                change ¬Hit
                  (typedFailureTrace world
                    (plan adversary canonical nonalignedAnswer wire Q rounds
                      (resume (SphincsSubmission.submission.runWith hash .sign
                        (secretKey, canonical, request.message)).value) (count + 1)))
                  (macAnswer hash secretKey canonical) at hmiss
                change realTrace adversary hash secretKey canonical
                  nonalignedAnswer world Q rounds
                    (resume (SphincsSubmission.submission.runWith hash .sign
                      (secretKey, canonical, request.message)).value) (count + 1) =
                  typedFailureTrace world
                    (plan adversary canonical nonalignedAnswer wire Q rounds
                      (resume (SphincsSubmission.submission.runWith hash .sign
                        (secretKey, canonical, request.message)).value) (count + 1))
                exact ih _ _ hmiss
              · have hvalue := (same_prefix_wrong_tag_rejects hash secretKey
                  canonical request.cache request.message sem hprefix htag).1
                simp [realTrace, plan, haction, hcap, hprefix, htag,
                  typedFailureTrace, hvalue] at hmiss ⊢
                exact ih (resume none) (count + 1) hmiss
            · let test : Altered (ciphertext canonical) × Digest :=
                (⟨ciphertext request.cache,
                    ciphertext_ne_of_auth_prefix_ne request.cache canonical hprefix⟩,
                  macTag request.cache)
              let tail := typedFailureTrace world
                (plan adversary canonical nonalignedAnswer wire Q rounds
                  (resume none) (count + 1))
              have hsplit : macAnswer hash secretKey canonical test.1 ≠ test.2 ∧
                  ¬Hit tail (macAnswer hash secretKey canonical) := by
                simp only [plan, haction, hcap, hprefix,
                  typedFailureTrace] at hmiss
                simp only [and_self, ↓reduceIte] at hmiss
                change ¬Hit (test :: tail) (macAnswer hash secretKey canonical) at hmiss
                rw [hit_cons] at hmiss
                exact not_or.mp hmiss
              have htagmiss : ¬TagPass hash secretKey request.cache := by
                intro htagpass
                apply hsplit.1
                exact (altered_test_hit_iff_tag_pass hash secretKey canonical
                  request.cache hprefix).2 htagpass
              have hvalue := (altered_prefix_no_mac_hit_rejects hash secretKey
                canonical request.cache request.message hprefix htagmiss).1
              simp [realTrace, plan, haction, hcap, hprefix,
                typedFailureTrace, hvalue] at hmiss ⊢
              change realTrace adversary hash secretKey canonical
                nonalignedAnswer world Q rounds (resume none) (count + 1) =
                typedFailureTrace world
                  (plan adversary canonical nonalignedAnswer wire Q rounds
                    (resume none) (count + 1))
              exact ih (resume none) (count + 1) hsplit.2
          · simp [realTrace, plan, haction, hcap, typedFailureTrace]

end SigGolfCandidate.SphincsRealTypedCoupling

/-- info: 'SigGolfCandidate.SphincsRealTypedCoupling.altered_test_hit_iff_tag_pass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsRealTypedCoupling.altered_test_hit_iff_tag_pass

/-- info: 'SigGolfCandidate.SphincsRealTypedCoupling.realTrace_eq_typedFailureTrace_no_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsRealTypedCoupling.realTrace_eq_typedFailureTrace_no_hit
