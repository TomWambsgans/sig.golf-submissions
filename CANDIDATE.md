# 152-level hypertree port — work in progress

This branch ports [Holindauer's certified PR #12](https://github.com/leanEthereum/sig.golf-submissions/pull/12) to the current beta interface. Its recorded score is 113,616 signature bytes × 1,690,289 verification cycles = 192,043,875,024. The source under `submission/` is the exact archived PR source at this checkpoint; it does **not yet** prove the current contract, which no longer supplies the public key to `sign` and requires a declared memory layout. Do not open a verification PR from this checkpoint.

The port will preserve attribution, prove the exact current images and all current statements, pass the independent verifier, and only then be submitted as a normal PR. Any further cycle improvement will be claimed only after a new Lean certificate checks.
