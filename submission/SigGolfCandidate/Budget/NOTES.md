# Budget: sign compression bound (notes)

Goal: E[2^(K/2^17)] <= 2 for the sign phase (K = countBlocks of signRef under the lazy RO after
keygen), plus keygen (K = 11135 <= 2^20) and expand (K = 0), and `Submission.CompressionBounds`
modulo refinement hypotheses.

Plan / status
* `Basic.lean` (done): `V z oa c` = E[z^compressions] under the lazy RO from cache `c`;
  `V_bind_le` (multiplicative), `V_query`, fresh/cached RO step; `Spec P Post k oa`
  (queries in `P`, results in `Post`, cost <= k) with `Spec.V_le`, `Spec.support` (cache invariants).
* `Bytes.lean` (done): `qbyte`, `qbyte_pad64`, `pad64_inj`, tweak tag/layer bytes, `le32_inj`.
* `Loops.lean` (WIP): Spec for trees/FORS/searches. Costs: chain 8, leaf 347, tree h:
  347*2^h + 2^h - 1 (11135 / 5567), FORS tree 3071, FORS 14*3071 = 42994, roots 4.
  K_det = 42998 + 6*11135 + 5567 = 115375.
* TODO: counting (admissible 2^-10 exactly; counter decode C/2^128 with
  C = 693523430046796437145478038506044352), search bounds, numerics, top level.

Sign image change 8b8dff9: staging/packing only; Ref (signRef) unchanged, so no effect here.
