# Masked-cache prototype

This branch preserves an experimental replacement for the current candidate's `keygen` and `sign` images. It leaves `submission/` unchanged. Keygen masks each of the 4,095 top-tree nodes with a domain-separated secret-keyed random-oracle pad and appends a secret-keyed MAC of the public cache. Sign checks the MAC before grinding or constructing a signature, decrypts the root and selected top authentication path, and otherwise produces the same compact signature. The verifier and proposed score are unchanged.

From the repository root, run `PYTHONPATH=. python3 -m examples.sphincs.check_mask` for one keygen/signature differential test and an altered-cache rejection test. Run `PYTHONPATH=. python3 -m examples.sphincs.check_worst_cycles` for the all-retries-last execution measurement and linear extrapolation. `PYTHONPATH=. python3 -m examples.sphincs.build_images` writes image literals to `prototype-images/` without replacing the submitted images.

The tested keygen uses 1,007,616 compressions and its image is 3,584 bytes. The tested sign uses 106,414 compressions and its image is 44,140 bytes. The last-attempt retry path extrapolates to 4,113,369,127 cycles, below the universal 2³² limit by 181,598,169 cycles. This is an executable prototype, not a Lean certificate or a proof of the universal cycle bound, compression moments, completeness, or security.
