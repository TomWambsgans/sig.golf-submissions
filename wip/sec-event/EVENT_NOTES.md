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
