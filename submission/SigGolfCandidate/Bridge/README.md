# Security bridge: organizer game → abstract SUF-CMA game

Namespace `SigGolfCandidate.Bridge`. Entry point `SigGolfCandidate/Bridge/All.lean`.
It uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), checked by
`#guard_msgs` / `#print axioms` in `All.lean`. There is no `sorry`, `native_decide` or
`bv_decide`.

```lean
theorem Assumptions.secure {sub : SigGolf.Submission} (B : Assumptions sub) : sub.Secure
theorem ZeroPadAssumptions.secure {sub : SigGolf.Submission} (Z : ZeroPadAssumptions sub) : sub.Secure
```

The bridge depends only on the *statement-level* API of `SphincsSecurity`:
`Security.experiment`, `Security.Adversary`, `Forgery`, `SigningSpec`, `SigningTranscript`,
`signatureLimit`, `sampleMasterSeed`, `Seeded.keygenFromSeed`, `Seeded.sign`, `Concrete.verify`,
and the types `Message`, `Signature`, `PublicKey`, `MasterSeed`, `Seeded.SecretKey`.
It needs two definitional facts: the hash output is `BitVec 256`, and
`HashInput = List UInt8`.

## Assumptions (`Setup.lean`, structure `Assumptions sub`)

| field | meaning |
|---|---|
| `security : EventSecurity` | (A) `∀ q ≥ 1, ∀ adv, Pr[r.1 = true ∧ r.2 ≤ q ∣ Security.experiment adv] ≤ q / 2^127` |
| `lifetime_le : LIFETIME ≤ signatureLimit` | **currently false** (`2^32` vs `2^24`); see below |
| `seedOf`, `seedOf_dist` | organizer key ↦ master seed, pushing `sampleSecretKey` to `sampleMasterSeed` (`seedOf_id_dist` proves this for `seedOf = id`) |
| `msgOf`, `msgOf_injective` | messages (take `id`) |
| `sigCodec : Bytes sizes.signature ≃ Signature` | (B) signature codec |
| `expandFn`, `witDec`, `witDec_expandFn : witDec (expandFn b) = sigCodec b` | (B) witness form, e.g. `expandFn = perm`, `witDec = sigCodec ∘ perm⁻¹` |
| `pkEnc : PublicKey → Bytes 16`, `cacheOf : PublicKey → Cache` | (B) published key bytes and the published cache, both functions of the abstract `pk` |
| `pad`, `unpad`, `Honest`, `pad_unpad : pad (unpad y) = y`, `unpad_pad : Honest x → unpad (pad x) = x` | (C) oracle relabelling |
| `keygen_eq`, `sign_eq`, `expand_eq`, `verify_eq` | (D) implementation equations, below |
| `keygen_honest`, `sign_honest`, `verify_honest` | every query made by the abstract algorithms is `Honest` (`AllQ Honest …`) |

(D) is stated on the `(value, hashCalls)` projection of `submission.run`.
`countCalls : OracleComp spec α → OracleComp spec (α × ℕ)` is `simulateQ` into `StateT ℕ`, where each query adds 1.
`relabel f` renames query inputs.
`aKeygen`, `aSign` and `aVerify` are the abstract algorithms typed over `AHash := List UInt8 →ₒ BitVec 256`.

```lean
keygen_eq : ∀ sk, (fun r => (r.value, r.hashCalls)) <$> run .keygen sk =
  (fun p => (some (pkEnc p.1.1, cacheOf p.1.1), p.2)) <$> countCalls (relabel pad (aKeygen (seedOf sk)))
sign_eq : ∀ sk pk sk', (pk, sk') ∈ support (aKeygen (seedOf sk)) → ∀ cache m,
  (fun r => (r.value, r.hashCalls)) <$> run .sign (sk, cache, m) =
  (fun p => (p.1.map sigCodec.symm, p.2)) <$> countCalls (relabel pad (aSign sk' (msgOf m)))
expand_eq : ∀ m pk σ, (fun r => (r.value, r.hashCalls)) <$> run .expand (m, pk, σ) = pure (some (expandFn σ), 0)
verify_eq : ∀ seed pk sk', (pk, sk') ∈ support (aKeygen seed) → ∀ m w,
  (fun r => (r.value, r.hashCalls)) <$> run .verify (m, pkEnc pk, w) =
  (fun p => (if p.1 then some () else none, p.2)) <$> countCalls (relabel pad (aVerify pk (msgOf m) (witDec w)))
```

These are free-monad equalities in `OracleComp SigGolf.HashSpec`. They have the shape the
RISC-V refinement proofs deliver: `g <$> countCalls spec`, with `spec = relabel pad abstractAlg`.
Signing ignores the cache. It may use any abstract secret key that key generation can output.

`ZeroPadAssumptions` (`Convenience.lean`) states (C) the way the task specifies it:
- `pad` (zero padding) is `Set.InjOn` on `Honest`;
- every honest input starts with byte `1`;
- `qEnc : Query → List UInt8` is injective. `defaultQEnc` is one such map.

An adversary query `y` outside `pad '' Honest` becomes the abstract query `0 :: qEnc y`.
`toAssumptions` builds the inverse pair `zpPad`/`zpUnpad`. It also rewrites (D) from `pad` to
`zpPad`, using `relabel_congr_of_allQ`.

## The `lifetime_le` blocker

The organizer allows `LIFETIME = 2^32` signing requests. The abstract game only counts a
forgery as valid when the log has at most `signatureLimit = 2^24` entries. An adversary that makes
more than `2^24` requests can never win the abstract game, and it has no cheap reduction.
So the scheme's `signatureLimit` must be raised to at least `2^32` (and (A) proved for that
limit), or the organizer's `LIFETIME` must change. The bridge takes this as the hypothesis
`lifetime_le`.

## Proof structure

1. **Generic tools** (`Basic.lean`):
   - `relabel`/`relabelW` rename query inputs.
   - `countFrom`/`countCalls` count queries.
   - `AllQ` says every query on every path satisfies a predicate.
   - `Ext`/`Rel` is a synchronized coupling of two free-monad programs, where the first program may stop early. `Rel.probEvent_le` turns a `Rel` into a probability inequality under any `StateT σ ProbComp` handler.
2. **Lazy random oracle relabelling** (`run'_relabelW`). For an injective `enc`, running `P` against the lazy random oracle on `ι'` gives *exactly the same* `ProbComp` as running `relabelW enc P` against the lazy random oracle on `ι`, starting from related caches. This is a literal equality, proved by induction with the cache invariant `cO x = cA (enc x)`.
3. **Writer-cost bridge** (`withAddCost_run_eq_countFrom`, `probEvent_countFrom_eq`). The `AddWriterT` cost instrumentation (`countedOracle`) equals explicit `StateT ℕ` counting in the program. This covers every call, including cache hits.
4. **Organizer side** (`Org.lean`). `securityExperiment_eq` rewrites the organizer experiment as `orgGame` run against the lazy random oracle on `List UInt8`, with enc = `unpad`. `(D)` and `unpad ∘ pad = id` on honest queries turn every program run into the counted abstract algorithm. The unfolding lemmas `orgK_*` follow each adversary action.
5. **Reduction** (`Abs.lean`). `reduction B A rounds : Security.Adversary` replays the organizer adversary:
   - hash `y` ↦ abstract query `unpad y`;
   - sign ↦ `SigningSpec` query `msgOf m`, and the answer is re-encoded by `sigCodec.symm`;
   - it keeps the signing-request counter, so the `LIFETIME` check and the `rounds` fuel are mirrored exactly;
   - both forgery forms become `⟨msgOf m, witDec w⟩` or `⟨msgOf m, sigCodec σ⟩`;
   - running out of fuel or lifetime returns a dummy forgery.

   `experiment_eq` (by `rfl`) retypes `Security.experiment` over `AW`. `abs_top` and `absK_*` unfold it.
6. **Coupling** (`Main.lean`, `rel_main`). By induction on the fuel, `Rel (orgK …) (absK …) RFin`, where `RFin`: an organizer win implies an abstract win with the same call count. The invariant `Inv` says:
   - the counters are equal;
   - `signingRequests = log length ≤ LIFETIME`;
   - every successful log entry `(msgOf mo, some σ)` has `(mo, sigCodec.symm σ)` in the organizer transcript.

   Fresh message implies no log entry for the message. Fresh (message, signature) implies no identical log entry (strong freshness). Failed signing requests use a slot and are logged, matching `record`. Early stops (fuel 0, lifetime exhausted) are organizer losses; the abstract side's extra verification calls are discarded by `Ext`.
7. **Final step** (`probEvent_le`, `Assumptions.secure`). Averaging over the key moves `sampleSecretKey` to `sampleMasterSeed` (`seed_swap`). Then (A) is applied at `q = Q`.
