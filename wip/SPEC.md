# sig.golf SPHINCS+ variant ("SPHINCS-golf") — working specification

Derived from `~/leanVM/doc/sphincs/main.tex` (WOTS+C / FORS+C / hypertree). Only the
differences are listed in full; everything not mentioned is exactly as in that document and in
`~/leanVM/formal/sphincs/SphincsSecurity/Scheme.lean`.

## Parameters

| Symbol | Value | leanVM value |
|---|---|---|
| n | 128 bits | same |
| w, v | 3, 42 | same |
| T (target sum) | **170** | 191 |
| d (layers) | **7** | 3 |
| heights h_0..h_6 (layer 0 = top) | **(5,5,5,5,5,5,4)** | (12,7,7) |
| h (total) | **34** | 26 |
| a, k | 10, 15 (14 trees + pinned group) | same |
| q_s (signing lifetime) | **2^32** | 2^24 |
| A_max (digest trials) | **2^20** | 2^32 |
| C_max (encoding counters) | **2^20** | 2^32 |

## Keys

* Secret key = master seed S (32 bytes). No public parameter derivation: **P = 0^128** (constant).
* Public key = root (16 bytes) = TreeRoot(P, 0, 0).
* sig.golf cache: unused. keygen leaves it zero; sign ignores it.

## Tweaks (16 bytes)

`enc(t, lay, tau, p, j) = LE8(1) || LE8(t) || LE8(lay) || LE8(tau >> 32) || LE32(p) || LE32(tau mod 2^32) || LE32(j)`

i.e. the formerly-zero byte 3 carries bits 32..39 of the tree field (tree field is 40 bits).
Needed because FORS tweaks put the 34-bit index `idx` in the tree field. Hypertree tree
indices are < 2^30. Tags as in leanVM (type 5 = parameter derivation is no longer used).

## Hash inputs

Abstract inputs are exactly the leanVM byte strings (`tweak || P || payload`, keygen
`tweak || P || S`, randomizer `tweak(7,0,0,a,0) || P || S || m`), with one change:

* Message digest payload: `rho || 0^16 || m` (the root slot is zero; the signer does not need
  the root). `Digest = Truncate_{184}(H(tw_msg || P || rho || 0^16 || m))`.

The sig.golf oracle takes 64k-byte inputs. The RISC-V programs query `pad64(x)` = x followed
by zero bytes up to the next multiple of 64 (lengths: chain/ftsLeaf 48->64, enc 52->64,
node/ftsNode/keygen 64, leaf 704, ftsRoots 256, message 96->128, randomizer 96->128).
The security bridge relabels oracle inputs (injective on honest formats; every honest-format
list starts with byte 1, adversary lists y not of the form pad64(x) are sent to `0 :: y`).

## Index split

`N` = 184-bit digest (LE). `idx = N mod 2^34`; `u_kappa = floor(N / 2^(34+10 kappa)) mod 2^10`,
kappa < 15; admissible iff `u_14 = 0`.
`e_lay` = bits of idx: e_0 = bits 29..33, e_1 = 24..28, ..., e_5 = 4..8, e_6 = bits 0..3.
`tau_lay = idx >> (sum_{j >= lay} h_j)`; tau_0 = 0.

## Signing (abstract signer = exactly what the bytecode does, query for query)

1. Digest loop a = 0..A_max-1: rho_a = Th(P, tw_rnd(a), S||m); D = Digest(rho_a); stop at first
   admissible. Fail if none.
2. FORS: for kappa = 0..13 build tree kappa of instance idx once (leaves in order j = 0..1023:
   secret s = Th(P, tw_ftsprf(idx,kappa,j), S), leaf = Th(P, tw_ftsleaf, s); then levels
   1..10 left to right). Record s_{u_kappa}, the path, the root. Then FtsKey.
3. For lay = 6, 5, ..., 0 (M_6 = FtsKey): counter search c = 0..C_max-1 on Enc(M_lay, c)
   (fail if none), then build tree (lay, tau_lay) once: leaves e = 0..2^h-1 in order (per leaf:
   for i = 0..41: secret, then 7 chain steps; then leaf hash), then levels bottom-up left to
   right. Capture C_{i,x_i} of leaf e_lay, the path of e_lay, the root = M_{lay-1}.
   (Exact interleaving to be fixed with the bytecode; the Lean abstract signer must match it.)
4. Signature = rho || FORS openings (kappa increasing: s, 10 siblings) || layers lay = 0..6
   (LE32 counter, 42 chain values, path) — 7756 bytes.

## Verification

As leanVM `Concrete.verify` plus: reject if any layer counter >= C_max (2^20).
Honest verification cost is constant (target sum + fixed paths).

## Budgets (compressions, sign)

Deterministic ~115.4k (FORS 42,998; trees 208 leaves x 347 + 201 nodes) + grind (4 per trial,
geometric p = 2^-10) + 7 encoding searches (1 each, geometric p ~ 2^-8.94).
E[2^(K/2^17)] ~ 1.92 <= 2.
