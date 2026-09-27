# Budget: compression bounds (notes)

Status: **done** for keygen, sign and expand, modulo the sign and expand bytecode refinements
(keygen's refinement `Keygen.keygen_run_counts` is used directly). No `sorry`, `native_decide`,
`bv_decide`; axioms: propext, Classical.choice, Quot.sound (`Axioms.lean`).

## Final statements

```lean
-- Main.lean (any submission)
def KeygenRefines sub := ∀ sk, ∃ G, (fun r => (r.value, r.hashCompressions)) <$> sub.run .keygen sk =
    (fun p => (G p.1, p.2)) <$> countBlocks (keygenRef sk)
def SignRefines sub := ∀ sk cache m, (fun r => r.hashCompressions) <$> sub.run .sign (sk, cache, m) =
    Prod.snd <$> countBlocks (signRef sk m)
def ExpandNoHash sub := ∀ input, (fun r => r.hashCompressions) <$> sub.run .expand input = pure 0
theorem compressionBounds_of_refinement (hK : KeygenRefines sub) (hS : SignRefines sub)
    (hE : ExpandNoHash sub) : sub.CompressionBounds
theorem keygen_bound / sign_bound / expand_bound   -- per phase and per message

-- Bridge.lean (the refinement form of Sign.Sim.run_eq: F <$> Sign.countBoth oa)
def RefinesCounts sub phase input oa := ∃ F, (fun r => (r.value, r.hashCalls, r.hashCompressions))
    <$> sub.run phase input = (fun p => (F p.1, p.2.1, p.2.2)) <$> Sign.countBoth oa
theorem submission_keygenRefines : KeygenRefines submission          -- from Keygen.keygen_run_counts
theorem submission_compressionBounds_of_counts
    (hS : ∀ sk cache m, RefinesCounts submission .sign (sk, cache, m) (signRef sk m))
    (hE : ∀ input, ∃ (α : Type) (a : α), RefinesCounts submission .expand input (pure a)) :
    submission.CompressionBounds

-- Numeric.lean (the math, from any cache without tweak types 4/7/12)
theorem V_signRef_le_two (sk m) (cache) (hinv : CacheInv Inv0 cache) :
    V (zOf (2 ^ 17)) (signRef sk m) cache ≤ 2
theorem V_keygenRef_le_two (sk) (cache) : V (zOf (2 ^ 20)) (keygenRef sk) cache ≤ 2
```
`V z oa c` = E[z^(countBlocks count)] under the lazy RO from cache `c`; `zOf B = 2^(1/B)`, and
`2^(K/B) = zOf B ^ K` (`costFun_eq`).

## Proof structure (files)

* `Basic.lean`: `V`, `V_bind_le` (multiplicative along binds, bound from every reachable state),
  `V_query`, RO fresh/cached steps; `Spec P Post k oa` (queries in `P`, results in `Post`,
  cost ≤ k) with `Spec.V_le` (V ≤ z^k) and `Spec.support` (cache invariants of reachable states).
* `Bytes.lean`: `qbyte`, `qbyte_pad64`, `pad64_inj`, tweak type/layer bytes, `le32_inj`.
* `Loops.lean`: Spec for chains (8), leaves (347), trees (347·2^h + 2^h − 1: 11135 / 5567),
  FORS trees (3071), FORS (14·3071), roots (4), keygen (11135), counter search (tag 4, layer lay,
  1 block/trial), digest search (tags 7/12, 4 blocks/trial).
* `Counting.lean`: Pr[fresh digest admissible] = 2^246/2^256 exactly; Pr[randomizer ∈ R] ≤ |R|/2^128;
  Pr[fresh encoding decodes] = 2^128·codeCount/2^256 with
  codeCount = 693523430046796437145478038506044352 (generating function `(1+X+..+X^7)^42` at
  X = 2^128, digit 170, kernel `decide`).
  Gotcha: instantiating counting lemmas with concrete huge ranges (e.g. `range (2^82)`) blew up
  memory in elaboration; keep the big factor abstract (`count_admissible_gen`, `count_Dok (W T)`).
* `Search.lean`: `V_searchCounter`, `V_searchDigest` (induction on fuel; digest carries the set R
  of drawn randomizers, per-trial failure ≤ rhoD + 2^20/2^128). Condition `w(ρ b + 1 − ρ) ≤ b`.
* `Sign.lean`: `V_signRef ≤ bD · z^42998 · bC^7 · z^72377` from `CacheInv Inv0`
  (K_det = 42998 + 72377 = 115375). Cache invariants: `InvL n` (cached counter queries have
  layer ≥ n) threaded through the layers.
* `Numeric.lean`: bD = 1.023, bC = 1.0027, z ≤ 1/(1 − 0.6931471808/2^17);
  2^(115375/2^17)·bD·bC^7 ≤ 2 via 2^(15697/2^17) ≥ 1 + 0.6931471803·15697/2^17. (≈ 1.919)
* `Main.lean`: splits `honest` after each phase (`honest_eq`, rfl), support lemmas for the costs
  recorded by later phases, keygen cache invariant from `KeygenRefines`.
* `Bridge.lean`: `countBoth` form → hypotheses; keygen discharged.

Sign image change 8b8dff9 (staging/packing only): Ref (signRef) unchanged, no effect here.
