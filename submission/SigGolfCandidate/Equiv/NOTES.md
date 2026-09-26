# `SigGolfCandidate.Equiv`: reference spec = abstract scheme

Status: **done**. `lake build SigGolfCandidate.Equiv.All` succeeds. `All.lean` pins every main
theorem with `#guard_msgs` to the axioms `[propext, Classical.choice, Quot.sound]`. There is no
`sorry`, `native_decide` or `bv_decide`. The only `decide`s are small kernel checks: the
layer-height tables, and the 7756 length.

Dependencies:
- `SphincsSecurity.Scheme`: only definitions, no lemmas.
- `SigGolfCandidate.Ref`.
- `SigGolfCandidate.Bridge.Basic`: `relabel`, `AllQ`, `countCalls`.
- `Bridge.All` and `Submission`, used only in `Main.lean`.

## Conventions

- **Relabelling.** `toB : List UInt8 → List Byte := map UInt8.toBitVec`, and
  `padQ x := Ref.pad64 (toB x)`. `relabel` is the Bridge's `relabel`: `simulateQ`, each query
  `x ↦ query (padQ x)`.
- **Abstract computations.** `AComp := OracleComp SphincsSecurity.HashSpec`, instantiated at
  `m := AComp`.
- **Values.** `dv (d : Digest) : Val := Ref.toList (n := 16) d` gives the 16 LE bytes.
- **Key and message.** The seed is `sk` itself (`seedOf = id`) and the message is `m` itself. The
  byte orders agree: `Ref.toList (bytes LE) = toB ∘ bytesLE`.
- **Every relation has the form `refProg = f <$> relabel padQ absProg`,** where `f` encodes the
  abstract result as reference bytes.
- **Local reducibility.** Each file sets
  `set_option allowUnsafeReducibility true in attribute [local reducible] hashOutputBits digestBits …`.
  This lets `rw` see `BitVec hashOutputBits` as `BitVec 256`. It only affects the elaborator;
  kernel checking and axioms are unchanged. `Main.lean` also makes `submission` locally reducible.

## Files

| file | content |
|---|---|
| `Basic.lean` | `toB`, `padQ`, `dv`; `toB_bytesLE`, `toB_tweakFields` (tweak bytes = `Ref.tweak`), `answerBytes_eq`, `hash16_tweakable` (`Ref.hash16 y = dv <$> relabel padQ (tweakableHash 0 dom payload)` when `toB input = y`); loops: `relabel_sequenceFin`, `foldlM_range_seq` (fold over `range n` with pure update vs `sequenceFin`), `map_fst_foldlM`, pure folds (`foldl_finRange_append/capture`, `foldl_prod`) |
| `Tree.lean` | per-hash inputs (`hash16_prf/chain/leaf/node`); `chainWalk_foldlM`, `chainFold_eq`, `buildChain_split`, `buildChain_eq`; `buildLeaf_eq`; independence of the captured digits (`fst_buildChain`, `fst_buildLeaf`, `buildLeaves_canon`); `buildLeaves_eq`; generic `buildLevels_steps`/`buildLevels_eq` (any node format); `buildTree_eq`; `keygenList_eq`, **`keygenRef_eq`** |
| `Digits.lean` | **`decodeDigits_dv`** (reference decoder = `TargetSum.decodeDigest`, digits as numbers); `truncateMessageDigest_toNat`, `idxOf_eq`, `uOf_eq` (`uFun`: groups, 0 past 14), `admissible_eq` |
| `Sign.lean` | FORS: `buildFtsLeaves_eq`, `buildFtsTree_eq`, `signForsU_eq`; `searchCounter_eq`; `route_eq`/`height_eq`; `signLayers_eq`; `searchDigest_eq` (via projections `projN`/`projA`); `serialize_eq`; `signCont_eq`; `signList_eq`; **`signRef_eq`** |
| `Codec.lean` | slices; `sigToList`/`sigOfList` with both round trips; **`sigCodec : Bytes 7756 ≃ Signature`**; witness decoder `witDec` (`sigOfWit`, fields at the witness offsets), `witDec_eq : witDec w = sigCodec (unexpandRef w)`, `witDec_expandRef` |
| `Verify.lean` | generic `foldPath_eq` (TreeFold/FtsFold); witness field lemmas, `countersOk_eq`; `verifyFors_eq`, `verifyLeaf_eq`, `verifyLayers_eq`; **`verifyRef_eq`**, `verifyRef_eq'`, `verifySigRef_eq` |
| `Honest.lean` | `tagLen`, `Honest`; **`padQ_injOn`**, `honest_head`; `HQ` (= `AllQ Honest`) for every routine; **`hq_keygen`, `hq_sign`, `hq_verify`** |
| `Main.lean` | `countCalls_eq` (`Ref.countCalls = Bridge.countCalls`, rfl), `countCalls_map`, `keygen_support`; `Refinements` (the 4 bytecode theorems as hypotheses); **`zeroPadAssumptions`**; **`submission_secure`** |
| `All.lean` | axiom audit |

## Final statements

```lean
-- relabelling (Basic)
def toB (x : List UInt8) : List Byte := x.map UInt8.toBitVec
def padQ (x : List UInt8) : Query := Ref.pad64 (toB x)

-- (1) codec (Codec)
def sigCodec : Bytes 7756 ≃ SphincsSecurity.Signature
  -- toFun b := sigOfList (Ref.toList b), invFun σ := Ref.ofList 7756 (sigToList σ)
  -- sigToList σ = dv rho ++ (s_k ++ path_k)_{k<14} ++ (toList c ++ vals ++ path)_{lay<7}
def witDec (w : Bytes 7756) : Signature              -- fields read at the witness offsets
theorem witDec_eq (w) : witDec w = sigCodec (Ref.unexpandRef w)
theorem witDec_expandRef (b) : witDec (Ref.expandRef b) = sigCodec b
def pkEnc (pk : PublicKey) : SigGolf.PublicKey := pk.root                    -- (Main)

-- (2) keygen (Tree)
theorem keygenRef_eq (sk : Bytes 32) :
    Ref.keygenRef sk = (fun kp => (kp.1.root : Bytes 16)) <$>
      relabel padQ (SphincsSecurity.Seeded.keygenFromSeed sk)

-- (3) sign (Sign): any secret key with seed `sk.seed` and parameter 0 (the root is ignored)
theorem signRef_eq (sk : Seeded.SecretKey) (hP : sk.parameter = 0) (m : Bytes 32) :
    Ref.signRef sk.seed m =
      Option.map sigCodec.symm <$> relabel padQ (Seeded.sign (m := AComp) sk m)

-- (4) verify (Verify)
theorem verifyRef_eq (m : Bytes 32) (pk : Bytes 16) (w : Bytes 7756) :
    Ref.verifyRef m pk w = relabel padQ (Concrete.verify (m := AComp) ⟨pk, 0⟩ m (witDec w))
theorem verifyRef_eq' (m pk w) :
    Ref.verifyRef m pk w =
      relabel padQ (Concrete.verify (m := AComp) ⟨pk, 0⟩ m (sigCodec (Ref.unexpandRef w)))
theorem verifySigRef_eq (m pk σ) :          -- verifySigRef m pk σ = verifyRef m pk (expandRef σ)
    Ref.verifySigRef m pk σ = relabel padQ (Concrete.verify (m := AComp) ⟨pk, 0⟩ m (sigCodec σ))

-- (5) honest queries (Honest)
def Honest (x : List UInt8) : Prop := x.head? = some 1 ∧ x.length = tagLen (x.getD 1 0).toNat
theorem padQ_injOn : Set.InjOn padQ Honest
theorem honest_head (x) (h : Honest x) : x.head? = some 1
theorem hq_keygen (seed) : AllQ Honest (Seeded.keygenFromSeed seed)
theorem hq_sign (sk m) : AllQ Honest (Seeded.sign (m := AComp) sk m)           -- every sk
theorem hq_verify (pk m σ) : AllQ Honest (Concrete.verify (m := AComp) pk m σ) -- every pk, σ

-- combined (Main)
structure Refinements : Prop where
  keygen : ∀ sk, (fun r => (r.value, r.hashCalls)) <$> submission.run .keygen sk =
    (fun p => (some (p.1, (0 : Cache)), p.2)) <$> Ref.countCalls (Ref.keygenRef sk)
  sign : ∀ sk cache m, (fun r => (r.value, r.hashCalls)) <$> submission.run .sign (sk, cache, m) =
    (fun p => (p.1, p.2)) <$> Ref.countCalls (Ref.signRef sk m)
  expand : ∀ m pk σ, (fun r => (r.value, r.hashCalls)) <$> submission.run .expand (m, pk, σ) =
    pure (some (Ref.expandRef σ), 0)
  verify : ∀ m pk w, (fun r => (r.value, r.hashCalls)) <$> submission.run .verify (m, pk, w) =
    (fun p => (if p.1 then some () else none, p.2)) <$> Ref.countCalls (Ref.verifyRef m pk w)
noncomputable def zeroPadAssumptions (security : Bridge.EventSecurity)
    (lifetime_le : LIFETIME ≤ signatureLimit) (R : Refinements) :
    Bridge.ZeroPadAssumptions submission
  -- seedOf = id, msgOf = id, sigCodec, expandFn = expandRef, witDec, pkEnc, cacheOf = 0,
  -- pad = padQ, Honest, qEnc = defaultQEnc; (D) keygen/sign/expand/verify_eq from R
theorem submission_secure (security) (lifetime_le) (R : Refinements) : submission.Secure
```

### How the refinement hypotheses match the RISC-V proofs

- **keygen.** `Keygen/Main.lean` proves `keygen_run : submission.run .keygen sk = (fun pk => ⟨some (pk, 0), true, …, 10815, …⟩) <$> keygenRef sk` and `keygenRef_counts`. Together these give `Refinements.keygen`: map the constant call count through `countCalls`.
- **expand.** `Expand/Main.lean` `expand_run` gives `Refinements.expand` directly.
- **sign and verify.** `Sim.run_eq` (`Sign/Sim.lean`) has the shape `(value, calls, compressions) <$> run = (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth oa`. Project it to `(value, calls)` with `(fun p => (p.1, p.2.1)) <$> countBoth oa = countCalls oa`, which is proved in `Sign/Sim.lean`.
- `Ref.countCalls` and `Bridge.countCalls` are definitionally equal (`countCalls_eq`, `rfl`).

## Proof notes

- **Loops.** `foldlM_range_seq` turns every `List.range` fold with a pure state update (append, pair append, capture `if j = cap`) into `sequenceFin`. The pure fold is then computed by `foldl_prod`, `foldl_finRange_append` and `foldl_finRange_capture`.
- **Recursions.** `chainWalk`, `treeFold`, `ftsFold`, `buildLevels`, the searches and the layer loops are handled by induction on the step count.
- **Captured digits.** `Ref.buildLeaves` passes the digits `x` to *every* leaf; the abstract passes `zeroEncoding` to non-captured leaves. `fst_buildLeaf` shows the leaf value is independent of the digits (`map_fst_foldlM`), and `buildLeaves_canon` rewrites the reference to pass `[]` to non-captured leaves.
- **Digest search.**
  - The reference keeps `N`, the abstract keeps `(index, leaves)`.
  - The continuation only reads `idxOf N` and `uOf N`, and `uOf N k = 0` for `k ≥ 15` since `N < 2^184`. So the relation is stated on the projections `projN`/`projA`, and `signList_eq_cont` factors the reference signer through `projN`.
- **Counter search.** It is stated with `c + fuel ≤ 2^32` so that `(ofNat 32 c).toNat = c`; this is used with `c = 0`, `fuel = 2^20`.
- **Verifier.**
  - It reads the *witness* offsets.
  - `witDec` decodes at those offsets.
  - `sigOfWit_eq` relates it to `sigOfList ∘ fromWitness` bytewise, through `signatureSrc`; `signatureSrc_layer` isolates the div/mod arithmetic.
- **Honest.**
  - The tag (byte 1) fixes the length: 0,3,8,10 → 64; 1,9 → 48; 2 → 704; 4 → 52; 7,12 → 96; 11 → 256.
  - Injectivity: equal padded queries have equal byte 1, so equal lengths, so equal prefixes.
  - `HQ` holds for every parameter `P`, so `hq_verify` needs no hypothesis on `pk`.
