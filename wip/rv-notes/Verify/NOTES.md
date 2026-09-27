# Verify refinement proof (SigGolfCandidate/Verify)

## Main results (`Main.lean`, axioms: propext, Classical.choice, Quot.sound — see `Axioms.lean`)

```lean
theorem verify_refines (m : Message) (pk : PublicKey) (w : Bytes 7756) :
    (fun r => (r.value, r.hashCalls)) <$> submission.run .verify (m, pk, w) =
      (fun p => (if p.1 then some () else none, p.2)) <$> countCalls (verifyRef m pk w)

theorem verify_terminates (hash : Hash) (input : SigGolf.Input submission.sizes .verify) :
    (submission.runWith hash .verify input).finished = true ∧
      (submission.runWith hash .verify input).cycles ≤ 18357 ∧
      (submission.runWith hash .verify input).cycles < CYCLE_LIMIT

theorem verify_accept_cycles (hash : Hash) (input : SigGolf.Input submission.sizes .verify)
    (_h : (submission.runWith hash .verify input).value = some ()) :
    (submission.runWith hash .verify input).cycles ≤ 18357
```
The cycle bound 18357 holds for *every* run (rejecting runs are shorter), so the scored
constant is C = 18357 + ceil(7756/256) = 18388. The images and the generator were not changed.

## Method

* `Exec`: path-guided symbolic executor `pathAux` (follows jumps; a symbolic branch takes the
  direction from `dirs` and records a `Br` obligation; stops at ECALL or at a stop pc), started
  from `σK known` (known registers are constants, so every verify address is a constant).
  Soundness: `pathAux_sound`/`pathRun_sound`. `Code`: chunked instruction lookup `vlook`.
* `Judg`: `Good s N C X` := for all fuel ≥ N, `(exit = success, hashCalls) <$> execute = X`, and
  for every fixed oracle the run finishes within C cycles. Laws for blocks (`Good.steps'`),
  HASH (`Good.hash`, `Good.hashH`), HALT (`Good.halt`/`Good.reject`); `cc oa K` runs the spec
  `oa` under `countCalls` and continues with `K` (CPS; `cc_bind`, `cc_pure`, `cc_hash16`).
* Families of runs (chain blocks: 294 chains x (8 digit dispatches + 6 steps + end); 174 fold
  levels x 2 slot positions; layer/FORS blocks) are compared by the kernel (`decide +kernel`)
  with generic expected results (`*Runs.lean`, `ChainCheck*`, `FoldCheck*`). The semantics
  is then proven once, generically (`ChainSem`, `FoldSem`, `LayerSem`, `LeafSem`, `ForsSem`,
  `Start`, `Compare`).
* Invariants: `Glob` (constant registers, witness, pk, zero P slots), `HeadInv/StepInv/EndInv`
  (chains), `FoldInv/FoldEnd` (folds, with a frame relative to the fold start), `LayerIn`,
  `EncOut`, `LeafDone`, `ForsIn/ForsCarry/LeafDoneF`, `DigestOut`, `InitOK`.
* Arithmetic: `Words` (hash input words of every format), `Arith*` (sub-word merges, route,
  u_k, idx, admissibility, counters), `Swar` (the SWAR digit sum = digit sum, via Horner lanes).
* Composition: `Chains` (42 chains, cost 1911 when the digits sum to 170), `LayerGood`
  (one layer), `Compare` (`layers_good`: 7 layers + comparison), `ForsGood` (trees, roots),
  `Top` (`main_good : Good s0 40100 18357 (cc (verifyList ..) Kb)`), `Main`.

## Build

Clean build of all Verify modules: 2.5 min wall on this (shared) machine, ~15 min summed CPU;
peak RSS per Lean process ~5.9 GB (baseline import ~3.4 GB). The kernel checks are split into
one declaration per chain/tree/layer and 14 + 2 files (memory grows ~80 MB per checked chain
within a file).

Note: `lake build SigGolfCandidate` currently reports "some modules have bad imports", apparently
because the lakefile uses `.andSubmodules` for directories without a root module file
(`SigGolfCandidate/Verify.lean` etc. do not exist); `.submodules` would avoid this. Build the
verify results with `lake build SigGolfCandidate.Verify.Axioms` (or `.Main`).
