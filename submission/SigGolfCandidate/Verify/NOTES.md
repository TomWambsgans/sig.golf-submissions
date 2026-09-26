# Verify refinement proof: progress notes

Approach
- `Exec.lean`: path-guided symbolic executor `pathAux` (follows jumps; takes symbolic branches in
  the direction given by `dirs`, recording `Br` obligations; stops at ECALL or a stop pc), started
  from `σK known` (known registers as constants, so all verify addresses become constants).
  Soundness `pathAux_sound` / `pathRun_sound`. Structural Bool equality `PRes.beq`/`optBeq` for
  kernel-checked families of runs (`decide +kernel` over parameter ranges).
- `Code.lean`: `vlook` = chunked (256) instruction lookup in the verify image, `vlook_ok`.

Plan
- Judgment `Good s N C X`: ∀ fuel ≥ N, `(exit = success, hashCalls) <$> execute = X` and for every
  fixed oracle the run finishes with cycles ≤ C. Laws for ordinary steps, HASH, HALT; CPS
  combinator `cc oa K` over `countCalls`.
- Segments: start/counters, digest, FORS leaf/fold levels, roots, layer enc + check, chain
  dispatch (8 digit cases), chain steps, chain end, leaf, folds, compare. Families checked by the
  kernel against generic expected results; semantics proven once generically.

Status (files in dependency order)
- Exec, Code: executor + lookup. Judg: `Good`, `cc`, laws. Words: byte/word formats of all hash
  inputs. Mem: `Glob` invariant. Post: generic run consequences. Arith/Arith2/Swar: bit arithmetic
  (SWAR digit sum proven via Horner lanes; `omega` alone is too slow on 42 digit atoms).
- ChainRuns/ChainCheck0..6: expected results of all chain blocks, kernel-checked per layer
  (~30 s wall in parallel). ChainSem/ChainGood/Chains: chain semantics, 42 chains of a layer,
  cost 1911 when the digits sum to 170.
- FoldRuns/FoldCheck/FoldSem: Merkle fold levels (FORS + layers).
- LayerRuns/LayerSem/LeafSem/LayerGood/Layers: one layer, all layers. Compare: final compare and
  `layers_good` (all 7 layers + comparison).
- TODO: FORS trees + roots, start/digest, initial state, top-level theorems.
