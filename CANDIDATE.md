# Compact SPHINCS candidate — work in progress

This branch holds the proposed submission in `submission/`. It is not ready for a PR: `SigGolf.Challenge.certificate` is missing, and the numbers in `claim.json` are targets, not certified results.

The candidate has 11,324-byte signatures and witnesses, a 16-byte public-key commitment, and a proposed 171,399-cycle verification bound. Its target score is 1,940,922,276.

## Proved so far

- The inherited abstract SPHINCS security and completeness theorems build with only standard Lean axioms. They describe a different signing interface, so they are not yet a certificate for this submission.
- The exact expansion image and the verifier prefix through the first FORS tree have compiled proofs. The first tree's eight parent rounds compute the abstract root with an exact cost bound. A parameterized theorem now covers the same leaf-and-path computation for any of the 24 FORS tree indices.
- The root-copy block writes the computed digest into the selected tree slot, and the following 12 instructions advance the tree counter and branch correctly.
- Under a fixed oracle, removing the abstract signer's unused final top-tree recomputation leaves its signature value unchanged. A separate generic theorem extracts a hash collision from two distinct authentication paths with the same leaf and root.

## Required before submission

- Compose the 24-tree FORS loop and the remaining WOTS/XMSS verifier layers, then prove exact-image keygen, sign, and verify refinement, termination, compression bounds, and the claimed verification-cycle bound.
- Prove security for the actual interface: the attacker sees the public top-tree cache, may replace it on each signing request, and may submit either a witness or a compact signature. The inherited theorem neither reveals this cache nor models the cached signer, and it charges 856,063 redundant top-tree hash calls per successful signing. Fixed-oracle value equality alone does not settle the query-budget reduction.
- Assemble `SigGolf.Challenge.certificate`, build it with the standard-axiom guard, run the independent verifier, then push and open a normal PR from the fork.

The source package currently passes the verifier's file and byte admission checks. Its 1,000-entry limit is a constraint: an isolated pilot showed that single-use abstract proof modules can be merged safely in small, compiled batches to free room for the remaining proof.
