# SPHINCS-golf scheme port: status notes

Branch `scheme`. Target: the scheme of `work/design/SPEC.md` / `work/py/ref.py`.

## Done
- `Scheme.lean`: parameters (7 layers, heights 5,5,5,5,5,5,4, h = 34, T = 170, q_s = 2^32,
  A_max = C_max = 2^20), 40-bit tree tweak field (byte 3 = bits 32..39), no parameter derivation
  (P = 0, `KeygenDomain.parameter` removed), rootless digest payload, `verify` = counter range
  check then `verifyCore`, build-once signer (`buildLevel(s)`, `buildChain`, `buildLeaf`,
  `buildLayerTree`, `buildFtsTree`, `buildForest`, `encodingSearch`, `signLayers`, `signFrom`).
- `IdealStatement.lean`: `sampleParameter := pure 0`, `keygenRoot`, `signAfterDigest := signFrom`
  with table secrets, `randomizedSign` mirrors `Seeded.sign`. Recursive `treeNode`/`treePath`/
  `ftsNode`/`ftsOpen`/`ftsKey`/`otsSign`/`signLayer`/`layerMessage` kept as specifications.
- `Proof/Scheme/BuildEval.lean`: builders equal the specification under every answer function
  (`eval_buildLayerTree`, `eval_buildForest`, `eval_signLayers`, `eval_signFrom`,
  `eval_signAfterDigest`, `signatureValue`).
- `Proof/Reference/BoundaryHashEvaluation.lean`: exact costs (`boundaryEval_buildLayerTree_pure` =
  `treeNodeHashCost h`, `boundaryEval_buildForest_pure` = `ftsOpenHashCost`, now the forest cost
  14·2047+1), generic `sequenceLayersHashCost`; `FrontierSigningEvaluation`: `boundaryEval_signAfterDigest`.
- Seven-layer generalizations: StatementLemmas (`layers_link`, `heightAbove_succ`), Descent
  (`hypertree_walk`, `counters_of_verify`), ForgeryClassify, SignSupport, EncodingTarget,
  ReferenceHypertreeWitness, RetainedResidualVerify; NoMessage for builders.
- Differential test vs ref.py: helper was interrupted; to be redone.

## In progress (helpers, WIP commits)
- Completeness/* (+ per-seed completeness).
- Seeded/*, Deterministic/*, Adversary/* coupling (budget slack now from the erased first
  secret derivation instead of the parameter query).
- Few-time numeric closers (Option B: T_idx 2^72, arrival 2^-44, etc.).

## Remaining (coordinator)
- Frontier/public signer cost plumbing (FrontierSignerErasure, PublicGraphSigner, consumers),
  and everything downstream.
