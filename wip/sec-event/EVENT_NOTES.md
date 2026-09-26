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

## Remaining: the small-budget Concrete chain (q ≤ 3·2^114)
Plan (A_vis): cap the adversary by its visible cost (own hash queries + G_min per signing request);
on the event the cap is never hit. A-part (Ots/Chains) uses syntactic query bounds of A_vis; the joint
budget needs E[signing digest attempts] ≤ G_min per signing (lazy ROM), transported to the reference
game; B/C/D carry the event per result.
