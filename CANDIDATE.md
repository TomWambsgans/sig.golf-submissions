# Compact SPHINCS candidate — work in progress

This branch holds the proposed submission in `submission/`. It is not ready for a PR: `SigGolf.Challenge.certificate` is missing, and the numbers in `claim.json` are targets, not certified results.

The candidate has 11,324-byte signatures and witnesses, a 16-byte public-key commitment, and a proposed 171,399-cycle verification bound. Its target score is 1,940,922,276.

## Proved so far

- The inherited abstract SPHINCS security and completeness theorems build with only standard Lean axioms. They describe a different signing interface, so they are not yet a certificate for this submission.
- The exact expansion image is proved to copy the compact signature to the witness without oracle calls; its security-game signature-submission branch now simplifies to direct verification. Parameterized RISC-V theorems compose all 24 FORS trees, preserve earlier roots, and account for their instructions and HASH calls. The loader invariant identifies every final FORS root with its abstract scheme fold. The WOTS verifier trace now reaches one chain-step HASH and its loop return, but the 52-chain induction and XMSS tail remain open. The masked keygen proof covers its first HASH, all 52 seven-step chains for one leaf, and all 1,040 endpoint bytes; the 2,048-leaf and parent-tree loops remain open.
- For a fixed oracle, legacy plaintext-cache signing gives the same signature as the abstract signer. A pointwise theorem bounds raw hash calls by 48 times cached calls and lifts this through adaptive signing requests. These lemmas help the security reduction, but they do not establish the corrected masked signer's behavior.
- The inherited security reduction compiles through 2^128 abstract queries while retaining its Q/2^127 final claim. Separate arithmetic allows query inflation plus public-key and MAC bad events within that target. The active signer's game-level coupling remains open.
- The active keygen and sign images mask the public top-tree cache and authenticate it with a secret-keyed MAC. Guarded Lean lemmas prove uniform masking, domain separation, freshness of altered MAC inputs, and a blind-guess bound over adaptive attempts. These are components of a security proof, not yet a game-level reduction.

## Required before submission

- Compose the 24-tree FORS loop and the remaining WOTS/XMSS verifier layers, then prove exact-image keygen, sign, and verify refinement, termination, compression bounds, and the claimed verification-cycle bound.
- Prove security for the actual interface: the attacker sees the public masked cache, may replace it on each signing request, and may submit either a witness or a compact signature. The active sign image checks the MAC before signing. The bridge must establish the real/simulated cache distribution, first-success coupling for adaptive MAC attempts, and reduction to inherited SUF. The old plaintext-cache image remains as a proof scaffold only; it cannot be the submission because the beta loader does not supply a public-key input to `sign`.
- A differential run of the masked images matched the reference keygen and signature with 1,007,616 keygen and 106,413 sign compressions. The last-attempt retry stress path extrapolates to 4,113,369,039 sign cycles, below the 2^32 limit by 181,598,257, but this is not a universal Lean bound. The proposed honest sign compression-moment proof uses `K ≤ 97,128 + 4D + Σ E_i` and conditional search tails; the rational upper bound is below 1.854, leaving room under the required value 2. The exact-image cost refinement and moment proof remain open.
- Assemble `SigGolf.Challenge.certificate`, build it with the standard-axiom guard, run the independent verifier, then push and open a normal PR from the fork.

The source package passes the verifier's file and byte admission checks. The 1,000-entry limit remains a constraint. Seventy-two single-use abstract proof modules were merged into their parents; the abstract security entry point rebuilt with only standard Lean axioms. The source checker is rerun as proof modules are added.
