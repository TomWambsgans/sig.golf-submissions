# Compact SPHINCS candidate — work in progress

This branch contains a proposed submission in `submission/`. It is **not ready for a PR**: `SigGolf.Challenge.certificate` has not been proved. The values in `claim.json` are targets, not certified results: S = W = 11,324 bytes, C = 171,399 cycles, and S × C = 1,940,922,276.

## Proved

- The exact keygen image returns the intended 16-byte public key and masked, authenticated cache for every secret key and random oracle. Its full trace, output bytes, 92,369,576-cycle termination, and keygen compression moment are proved.
- The exact expand image copies every signature byte into the witness. It terminates in 8,500 cycles, makes no hash calls, and meets its compression moment.
- The sign image loads and checks the masked cache. Its nonce and 24-tree FORS block has an exact trace and byte-for-byte agreement with the abstract scheme. The five lower WOTS layers have proved 52-chain endpoints, exact abstract leaf values in every tree cache, and an exact path initializer and sibling copier; copied siblings are linked to the inherited abstract tree path. The path loop and full output refinement remain open.
- The verify image has exact FORS and WOTS traces and byte semantics. The XMSS node round, full path digest/root, and next-layer transition have exact traces and byte semantics, with path cost at most 141 cycles per node. Six-layer composition and the claimed total cycle bound remain open. Commitment mismatches are proved to reject and terminate below the universal cycle limit.
- The inherited abstract SPHINCS security and completeness proofs build with only standard Lean axioms. A concrete altered-cache MAC first-hit bound and a finite lazy-oracle model for the full adaptive interaction are proved. The exact keygen cache has a joint law with a fresh dynamic MAC answer, and this law extends through the sampled secret key and entire organizer interaction while preserving the attacker result and hash-call count. Coupling concrete signing and verification to the inherited SUF game remains open.

The submission passes the independent source-admission check. Lean axiom guards on completed modules report only `propext`, `Classical.choice`, and `Quot.sound`.

## Still required

- Complete the signer’s authentication-path loop, root/path serialization, full output refinement, and cost distribution.
- Compose the verifier’s XMSS layers and final comparison, prove full result refinement, and establish the 171,399-cycle bound.
- Prove universal sign/verify termination below the competition limit, end-to-end completeness, and security for the actual public, replaceable cache and both submission paths. In particular, connect the finite-table setup law and exact cache bytes to the full attacker game, refine the concrete sign image, and charge bad events to the game’s hash-call budget.
- Assemble and build `SigGolf.Challenge.certificate`, run the independent verifier, then open a normal PR from the fork.
