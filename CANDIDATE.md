# Compact SPHINCS candidate — work in progress

This branch contains a proposed submission in `submission/`. It is **not ready for a PR**: `SigGolf.Challenge.certificate` has not been proved. The values in `claim.json` are targets, not certified results: S = W = 11,324 bytes, C = 171,399 cycles, and S × C = 1,940,922,276.

## Proved

- The exact keygen image returns the intended 16-byte public key and masked, authenticated cache for every secret key and random oracle. Its full trace, output bytes, 92,369,576-cycle termination, and keygen compression moment are proved.
- The exact expand image copies every signature byte into the witness. It terminates in 8,500 cycles, makes no hash calls, and meets its compression moment.
- The sign image loads and checks the masked cache. Its nonce and 24-tree FORS block has an exact trace and byte-for-byte agreement with the abstract scheme. The five lower WOTS layers have proved 52-chain endpoints and abstract leaf values. The full lower-layer authentication path, from the parent subtree exit through the path initializer, is emitted byte-for-byte as the abstract `treePath`; WOTS signature-chain and full output refinement remain open.
- The verify image has exact FORS and lower-layer WOTS traces and byte semantics. The XMSS node round and full path digest/root have exact traces, with path cost at most 141 cycles per node. Each completed root becomes the next layer's WOTS message byte-for-byte, and the repeated instruction blocks match. Dynamic WOTS-loop relocation, six-layer composition, and the claimed total cycle bound remain open. Commitment mismatches are proved to reject and terminate below the universal cycle limit.
- The inherited abstract SPHINCS security and completeness proofs build with only standard Lean axioms. A concrete altered-cache MAC first-hit bound and a finite lazy-oracle model for the full adaptive interaction are proved. The exact keygen cache has a joint law with a fresh dynamic MAC answer, and this law extends through the sampled secret key and organizer interaction. The numerical 128-to-127-bit margin for cache and seed bad events is proved. Coupling the full concrete attacker result to the inherited SUF game remains open.

The submission passes the independent source-admission check. Lean axiom guards on completed modules report only `propext`, `Classical.choice`, and `Quot.sound`.

## Still required

- Prove the signer's WOTS signature-chain serialization, then full output refinement and cost distribution.
- Relocate the verifier's dynamic WOTS loop across layers, compose all layers and final comparison, prove full result refinement, and establish the 171,399-cycle bound.
- Prove universal sign/verify termination below the competition limit, end-to-end completeness, and security for the actual public, replaceable cache and both submission paths. In particular, connect the finite-table setup law and exact cache bytes to the full attacker game, refine the concrete sign image, and charge bad events to the game’s hash-call budget.
- Assemble and build `SigGolf.Challenge.certificate`, run the independent verifier, then open a normal PR from the fork.
