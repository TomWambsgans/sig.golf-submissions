# Compact SPHINCS candidate — work in progress

This branch holds the proposed submission in `submission/`. It is not ready for a PR: `SigGolf.Challenge.certificate` is missing, and the numbers in `claim.json` are targets, not certified results.

The candidate has 11,324-byte signatures and witnesses, a 16-byte public-key commitment, and a proposed 171,399-cycle verification bound. Its target score is 1,940,922,276.

## Proved so far

- The inherited abstract SPHINCS security and completeness theorems build with only standard Lean axioms. They describe a different signing interface, so they are not yet a certificate for this submission.
- The exact expansion image and verifier prefix have compiled proofs. A parameterized RISC-V theorem covers one complete FORS tree: eight parent rounds, the byte-level abstract root, root storage, counter advance, next-tree or exit branch, and its execution cost.
- For a fixed oracle, canonical cached signing produces the same signature value as the abstract signer. The actual top-cache fold now has a Lean collision extractor: an accepted altered path with the honest leaf and root is canonical or yields distinct oracle inputs with the same truncated output.
- The inherited security reduction now compiles through 2^128 abstract queries while retaining its Q/2^127 final claim. A separate conditional bound fits query inflation, a 128-bit public-key commitment event, and a 160-bit cache-path collision event within that final claim. The abstract signer's two redundant top-tree computations cost at most 1,711,698 calls per signing request, less than 2^53 over the full lifetime.

## Required before submission

- Compose the 24-tree FORS loop and the remaining WOTS/XMSS verifier layers, then prove exact-image keygen, sign, and verify refinement, termination, compression bounds, and the claimed verification-cycle bound.
- Prove security for the actual interface: the attacker sees the public top-tree cache, may replace it on each signing request, and may submit either a witness or a compact signature. The inherited theorem neither reveals this cache nor models the cached signer. The missing bridge must preserve adaptive-game behavior and account for every extra virtual hash call; fixed-oracle value equality and the numerical bounds do not establish that bridge.
- Assemble `SigGolf.Challenge.certificate`, build it with the standard-axiom guard, run the independent verifier, then push and open a normal PR from the fork.

The source package currently passes the verifier's file and byte admission checks. Its 1,000-entry limit is a constraint: an isolated pilot showed that single-use abstract proof modules can be merged safely in small, compiled batches to free room for the remaining proof.
