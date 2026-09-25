# Compact SPHINCS candidate — work in progress

This branch holds the proposed submission in `submission/`. It is not ready for a PR: `SigGolf.Challenge.certificate` is missing, and the numbers in `claim.json` are targets, not certified results.

The candidate has 11,324-byte signatures and witnesses, a 16-byte public-key commitment, and a proposed 171,399-cycle verification bound. Its target score is 1,940,922,276.

## Proved so far

- The inherited abstract SPHINCS security and completeness theorems build with only standard Lean axioms. They describe a different signing interface, so they are not yet a certificate for this submission.
- The exact expansion image and verifier prefix have compiled proofs. Parameterized RISC-V theorems compose all 24 FORS trees, preserve earlier roots, and account for their instructions and HASH calls. The loader invariant now identifies every final FORS root with its abstract scheme fold; the post-FORS verifier tail remains open.
- For a fixed oracle, canonical cached signing gives the same signature as the abstract signer. An exact six-layer theorem identifies the extra 855,635 hash calls when its top layer succeeds. A pointwise theorem preserves signatures and bounds raw hash calls by 48 times cached calls; a second theorem lifts this bound through adaptive signing requests. The accepted altered-cache split reduces the two signer checks to the honest case, a 160-bit top-node collision, or a 128-bit commitment collision.
- The inherited security reduction now compiles through 2^128 abstract queries while retaining its Q/2^127 final claim. A separate conditional bound fits query inflation, a 128-bit public-key commitment event, and a 160-bit cache-path collision event within that final claim. The abstract signer's two redundant top-tree computations cost at most 1,711,698 calls per signing request, less than 2^53 over the full lifetime. This establishes the 2^128 cap but not the stronger r ≤ 48Q inflation premise for cheap rejected cache requests.

## Required before submission

- Compose the 24-tree FORS loop and the remaining WOTS/XMSS verifier layers, then prove exact-image keygen, sign, and verify refinement, termination, compression bounds, and the claimed verification-cycle bound.
- Prove security for the actual interface: the attacker sees the public top-tree cache, may replace it on each signing request, and may submit either a witness or a compact signature. The inherited theorem neither reveals this cache nor models the cached signer. The missing bridge must connect the canonical-cache coupling to the randomized game, charge both collision events, and handle adversary-modified caches and cheap rejected requests; the 48× theorem currently covers canonical cached signing only. Exact sign-bytecode checks and keygen/verifier refinements are also open.
- Assemble `SigGolf.Challenge.certificate`, build it with the standard-axiom guard, run the independent verifier, then push and open a normal PR from the fork.

The source package currently passes the verifier's file and byte admission checks. The 1,000-entry limit remains a constraint. Seventy-two single-use abstract proof modules were merged into their parents; the abstract security entry point rebuilt with only standard Lean axioms. The package currently has 824 admitted files.
