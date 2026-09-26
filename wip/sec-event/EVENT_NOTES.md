# Event-form security (branch `eventform`)

Goal: `security127_event : ∀ q ≥ 1, ∀ A, Pr[won ∧ calls ≤ q | experiment A] ≤ q / 2^127`,
no query-bound hypothesis; old `HasClassicalSecurityBits 127` derived from it.

## Why no black-box reduction
The adversary cannot see the cost of a signing call (digest trials are hidden: the
randomizer of failed trials never leaves the signer), so no wrapper can enforce the
total cap; pointwise overshoot is unbounded (hidden trials of every call accumulate).
So the event has to be threaded through the proof.

## Map (from reading)
- Outer layers (Adversary/, Deterministic/, Seeded/): generic in the computation; the
  count is part of `countHashQueries`. Seed-guessing needs a pointwise bound -> apply it
  to the `QueryCap.run`-capped computation.
- Concrete: the count is recorded from the first step (`boundaryGameCore`,
  `SigningBoundaryTrace.hashCalls`, later `memory.external.hashCalls`).
- Large chain (Residual/): leaves = primitive potential, creation mass, cache payment,
  monitor-stop classification.
- Small chain (Reference/, Ots/, Chains/, Fts/, Forced/): leaves = joint budget,
  Chains caps (`hreal`), certificate creation mass, forced near-guess.

## Slack
- small range (q ≤ 3·2^114): closing inequality has ≥ 0.147·x slack (x = q/2^128); the
  event is empty for q < keygenHashCost, so additive losses up to ~2^-111 are absorbable.
- large range: slack ≥ x(x - 11/65536) ≥ 2^-28 absolute.

## Log
- Large-budget Concrete chain done: `Concrete.security127_event_of_large_budget` (Residual/RetainedResidualEventLarge.lean).
  New pieces: Event/Boundary (event on boundary game), Residual/RetainedResidualEventTransfer (counted coupling
  to the source game), Fts/CertificateCreationBudget + Residual/RetainedResidualCreationBudget (creation mass ≤ budget
  structurally, via the monitor's activity rule), Residual/RetainedResidualEventPotential (primitive potential on
  the monitored run, paying hazards while hc ≤ q and the monitor's creation mass; a live overshooting signing
  request is paid from remaining ≥ 2^ftsTreeHeight), Event/TruncatedCharge + Residual/RetainedResidualEventCache
  (cache exception counted per hash call within the budget), Residual/RetainedResidualEventCoverage.
  Same closing bound as before: no arithmetic change.
- Merged branch `scheme` (7 layers etc.); only fix needed: an attribute line in EventTransfer.
- Outer layers done (Event/Erasure, Event/Deterministic, Event/Transfer):
  `Security.security127_event_of_independent : IndependentEventStatement → ∀ q ≥ 1, ∀ A, Pr[won ∧ calls ≤ q] ≤ q/2^127`
  where `IndependentEventStatement` is the event form for `Concrete.scheme`. Pieces: counted erasure
  (`Erases.probEvent_counted_le`, keygen saves one query), capped-computation seed guessing
  (`probEvent_random_cache_change_event`, via `QueryCap.run`), counted memoization, counted table→reference.
  Same loss as before: `(q-1)/2^256` absorbed by `seed_loss_absorbed`.
- `hasClassicalSecurityBits_of_event`: the old statement follows from the event form.

## Remaining: the small-budget Concrete chain (q ≤ 3·2^114) -- plan (A_vis)
Constants: K = keygenHashCost = 9503, G = ftsOpenHashCost = 28659 (every signing makes ≥ G calls,
`boundaryHashAtLeast_sign`), V_max ≈ 2263 = syntactic bound on verify's hash calls (need V_max + 1 ≤ K),
G_max = syntactic bound on one signing (≈ 8.5e6), b = q + 1.
A_vis(A, b): runs A.main pk, charging 1 per own hash query and G per signing request; stops (dummy forgery
with an out-of-range counter, verify makes no call) before the charge would exceed b - K - 1; at the end
makes one marker query: a message-class input with odd payload length 2m+1, m = number of its own
nonmessage hash queries. Syntactic: own + G·#sign ≤ b - K (weighted IsQueryBound).
1. Coupling: Pr[win ∧ hc ≤ q | A] ≤ Pr[win ∧ hc ≤ q+1 | A_vis(q+1)] (on the event the cap never fires,
   since real cost ≥ charge; the marker adds 1; the marker input is never queried by verify).
   After this the event is dropped: bound Pr[win | A_vis].
2. Crude cap: HasHashQueryBound A_vis q' with q' = b + (b/G)·G_max + V_max (≈ 300·b): used by B (full
   certificate, unchanged, excess term q'·11/2^144 ≈ 0.05x) and by the D monitor (hwork at q').
3. Probes (C pair, D slots): probes = adversary world queries + verify queries ≤ (b - K) + V_max ≤ b + V_max
   pointwise (syntactic; signing makes no probes).  C = pairRate(b + V_max); D slots over range(b+V_max).
4. D per slot: monitor budget q'; creation mass ≤ own + V + 2^10·#sign ≤ b (syntactic, 2^10 ≤ G) replaces
   hwork in `near_alive_le`; stopped case pays q'·cacheRate (negligible).
5. A-part (Ots/Chains): the Chains glue takes cost := const b; hcharge = syntactic prefix-query bound
   (prefix queries only from own hash queries (≤ b - K) and verify (≤ V_max); signing makes none), hreal trivial.
   Rates at b.  Joint budget in expectation: E[recorded nonmessage + messageCalls | refRecorded] ≤ b:
   recorded nonmessage ≤ m(trace) + V_max (marker decodes m), then trace-law transport to the real game,
   where m + messageCalls = own + 1 + Σ attempts + V_msg ≤ b - K - G·#sign + Σ attempts + 1 and
   E[attempts per signing | cache] ≤ 2^11 ≤ G (lazy ROM, fresh randomizer, cache ≤ q' ≤ 2^127).
6. Closing: same shape at b = q + 1 (plus q'·excess and pair/near at b + V_max); slack absorbs.
