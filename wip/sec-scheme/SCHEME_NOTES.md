# SPHINCS-golf scheme port: status notes

Branch `scheme`. Target: the scheme of `work/design/SPEC.md` / `work/py/ref.py`.

## Status: DONE
`lake build SphincsSecurity` succeeds (3916 jobs). The root module proves
`sphincs_has_127_bits_of_classical_security`, `sphincs_is_correct`, `sphincs_is_complete` and the new
`sphincs_is_complete_for_every_seed`. Each is pinned by `#guard_msgs` to [propext, Classical.choice, Quot.sound].
There are no `sorry`, `native_decide` or `bv_decide` anywhere.

## Scheme (`Scheme.lean`)
- Parameters: 7 layers, heights (5,5,5,5,5,5,4), h = 34, T = 170, q_s = 2^32, A_max = C_max = 2^20.
- The tweak tree field is 40 bits; byte 3 holds bits 32..39.
- P = 0. There is no parameter derivation (`KeygenDomain.parameter` is removed). `PublicKey` keeps its
  `parameter` field, which is always 0.
- The digest payload is `rho || 0^16 || m`. The root argument is kept but ignored.
- `verify` checks `CountersInRange` first, with no query, then runs `verifyCore`.
- The signer builds each tree once: `buildLevel(s)`, `buildChain`, `buildLeaf`, `buildLayerTree`,
  `buildFtsTree`, `buildForest`, `encodingSearch`, `signLayers` and `signFrom`. `signFrom` is shared by
  the seeded signer and the table signer.
- `difftest/` holds a harness that runs the definitions against `ref.py`.
  - keygen (10815 queries), sign (118677) and verify (1072) match query for query.
  - The root and the 7756-byte signature are byte-identical.
  - A counter of 2^20 or more is rejected with 0 queries.

## Proof changes
- **Specification functions.** The recursive functions `treeNode`, `treePath`, `ftsNode`, `ftsOpen`,
  `ftsKey`, `otsSign`, `signLayer` and `layerMessage` are kept in `IdealStatement.lean` as specifications.
- **Builders against the specification.** `Scheme/BuildEval.lean` shows the builders compute the
  specification: `eval_signFrom` and `signatureValue`.
- **Exact costs.** `BoundaryHashEvaluation` and `FrontierSigningEvaluation` give them:
  - a layer tree costs `treeNodeHashCost h`;
  - the forest costs `ftsOpenHashCost` (redefined as the forest cost, 28659);
  - a signature costs the forest plus, per layer, the counter search and the tree;
  - `boundaryHashAtLeast_sign` bounds the signature cost below by `ftsOpenHashCost`.
- **Seven layers.** The fixed three-layer arguments are replaced by recursions over the layers:
  `hypertree_walk`, `layers_link`, the generic `layerMessagePosition` and `sequenceLayersHashCost`.
- **Counter check.**
  - `counters_of_verify` gives `CountersInRange` from an accepting verifier.
  - The certificate outcomes (`ReferenceFtsCoverage.Outcome` and `NearGuess`) now carry `CountersInRange`.
  - `canonicalEncodingInputs` ranges over all 2^32 counters.
- **P = 0 in the ideal game.** `sampleParameter := pure 0`. The few Forced lemmas that needed a sampled
  parameter now take `hparameter : parameter ∈ support sampleParameter`.
- **Seeded and Deterministic coupling.**
  - Build-once erasure goes through getter congruence lemmas.
  - The `q - 1` slack now comes from the erased first secret derivation.
  - The final assembly takes the ideal bound as a hypothesis, in the `Transfer.lean` files.
- **Numerics.**
  - Arrival rate 2^-44 and cached-index threshold 2^72.
  - r_cache ≤ 2^-153.
  - fixedProposalLength = 6455033869; proposal prefix slack 2^23; Chernoff base 1025/1024.
  - Unchanged: 1537/1024, 19/50, 557, δ = 11/65536, 7/4 and q0 = 3·2^114.
- **Completeness.**
  - `2^119 ≤ codeCount 170`.
  - The counter search fails with probability ≤ 2^-2048 and the digest search with ≤ 2^-1023 (room 1/1025).
  - `complete_seeded` holds for every seed, and `complete` follows from it.

## Statement changes
- `Statement.lean` is unchanged.
- `Completeness.lean` only gains `seededGameCore`, `seededExperiment` and `SphincsSeededCompletenessStatement`.
  The existing statements are unchanged.
