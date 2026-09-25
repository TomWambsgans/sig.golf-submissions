# Compact SPHINCS candidate — work in progress

This branch contains a proposed submission in `submission/`. It is **not ready for a PR**: `SigGolf.Challenge.certificate` has not been proved. The values in `claim.json` are targets, not certified results: S = W = 11,324 bytes, C = 171,399 cycles, and S × C = 1,940,922,276.

## Proved

- The exact keygen image returns the intended 16-byte public key and masked, authenticated cache for every secret key and random oracle. Its full trace, output bytes, 92,369,576-cycle termination, and keygen compression moment are proved.
- The exact expand image copies every signature byte into the witness. It terminates in 8,500 cycles, makes no hash calls, and meets its compression moment.
- The sign image loads and checks the masked cache. Its nonce and 24-tree FORS block has an exact trace and byte-for-byte agreement with the abstract scheme. The five lower WOTS layers have a proved 52-chain endpoint loop and live-layer leaf HASH semantics.
- The verify image has exact FORS and WOTS traces and byte semantics. The XMSS node round, including branch-dependent cycle cost, is proved; the full six-layer path and claimed cycle bound remain open.
- The inherited abstract SPHINCS security and completeness proofs build with only standard Lean axioms. A concrete altered-cache MAC first-hit bound, lazy-oracle finite-table model, and joint distribution of plaintext setup, ciphertext cache words, and dynamic MAC answer are proved. These are ingredients for the actual bytecode security bridge, not the bridge itself.

The submission passes the independent source-admission check. Lean axiom guards on completed modules report only `propext`, `Classical.choice`, and `Quot.sound`.

## Still required

- Complete the signer’s WOTS/tree loops and exact output refinement, including its cost distribution.
- Complete the verifier’s XMSS path, full result refinement, and the 171,399-cycle bound.
- Prove universal sign/verify termination below the competition limit, end-to-end completeness, and security for the actual public, replaceable cache and both submission paths. In particular, connect the finite-table cache game to the concrete keygen/sign images and charge bad events to the game’s hash-call budget.
- Assemble and build `SigGolf.Challenge.certificate`, run the independent verifier, then open a normal PR from the fork.
