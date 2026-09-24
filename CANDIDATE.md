# Compact SPHINCS candidate — work in progress

This branch holds the proposed submission in `submission/`, based on the fork’s `beta` branch. It is not ready for a PR: `SigGolf.Challenge.certificate` is still missing. The published `claim.json` numbers are targets, not certified results.

The scheme uses 11,324-byte signatures and witnesses, a 16-byte public-key commitment, and a proposed 171,399-cycle verification bound. The abstract Lean security proof and the exact expand-image proof build. The verifier proof covers its first commitment hash and comparison, proves that the next hash input contains the submitted message word for word, and proves that the two subsequent 20-byte copy blocks preserve their source words. Those source words still need to be connected to the loaded witness. Full keygen/sign/verify correspondence, resource bounds, and the reduction for the committed public key and adversarial cache remain open.

The branch contains only the import closure needed by the current candidate, under the verifier’s file and source-size ceilings. Once the certificate builds and the verifier accepts it, this branch can be opened as an ordinary PR against `leanEthereum/sig.golf-submissions:beta`.
