# SigGolfCandidate.Sign — notes (sign refinement; shared tree_build infrastructure)

## Code changes (work/py/gen.py, sign only; keygen/verify/expand images unchanged)
* Layer captures go to an 8-aligned **staging area** `STG = 0x900`, layer `lay` at
  `STG + 760 lay`: counter dword at +0, chain value i at +8+16i, path node l at +680+16l.
  (The symbolic executor needs 8-aligned bases for sub-dword accesses; signature layers are
  4-aligned only.) After the layer loop a straight-line **pack** (`pack_<g>` labels, constant
  addresses only) copies the staging into `SIG + 2480 ..`.
* Digits are stored as dwords at `DIG8 = 0x780` (+8i) and loaded with `ld X, 1920(I<<3)`.
* EB counter written with `sd CNT, EB+48` (no `sw x0, EB+52`).
* Query sequence unchanged (test.py passes; same compressions).

## Files
* `Sim.lean` — generic, reusable by every phase:
  - `countBoth oa : OracleComp HashSpec (α × Nat × Nat)` (calls, compressions), with
    `countBoth_pure/_bind/_query/_H`, `countBoth_calls` (→ `countCalls`), `countBoth_blocks`
    (→ `countBlocks`), `fst_countBoth`.
  - `Sim image s W oa Q`: the machine from `s` refines the spec `oa` query for query, ending in
    a state `t` with `Q a t`, at most `W` cycles. Combinators: `Sim.pure`, `Sim.pure_steps`,
    `Sim.steps` (prefix `Steps`), `Sim.query`, `Sim.query_bind`, `Sim.hash16_bind`, `Sim.hash16`,
    `Sim.bind`, `Sim.mono`, `Sim.of_eq`, `Sim.foldlM_range`, `Sim.foldlM_range'`.
  - Whole phase: `Sim.run_eq` (value/calls/compressions of `submission.run` = `F <$> countBoth oa`
    when every final state is at a HALT ecall) and `Sim.runWith` (finished, cycles ≤ W+1).
* `Words.lean` — `wordsOf` (byte list → LE dwords), `valOfWords`, `answerBytes_16`,
  `pad64_eq_query`, `hashInput_eq_pad64` (HASH input = `pad64 x` from `readWords`), `hashArgs_of`,
  `twWords` (tweak dwords), per-format dword lists `words_prfInput/_ftsPrfInput/_th16/_th32/
  _thVals/_encInput/_rndInput/_digestInput`, `readWords_ofNat_*`, `readWords_slots`,
  `writeHash_getMem_ofNat/_frame/_readWords_val`.
* `Base.lean` — `kernel_theorem` (kernel-only `Eq.refl`, lets the executor run at a **variable
  pc**: relocatable block lemmas usable in several images), `addN`, `pcOf`, `retarget`,
  `ofNat_*` (BitVec.ofNat 64 arithmetic → Nat), `lo32/hi32` + `replaceWord32` half lemmas,
  `word_of_halves`.
* `TreeBuildNode.lean` — **shared node loop** (`node_hash` + `addi a6; bne a6,a7`, identical
  words in sign FORS, sign tree_build and keygen tree_build): `nodeSegA/B`, relocatable
  `nodeA_spec`/`nodeB_spec` (any image/pc with `CodeAt`), `node_hashInput`, and
  `nodeLoop_sim : Sim image s (m*25) (buildLevel (nodeFmt tt lay tau) lam lvl) (NodeInv …)`
  (`nodeInput_eq`, `ftsNodeInput_eq` identify the Ref formats). Keygen: instantiate with
  `L :=` index of `tb_node_loop`, `c.B := TA`.
