# Reproduce the beta64 images

Run `python3 tools/beta64/build.py` from the submissions repository. The script reads the **legacy** image literals in `submission/SigGolfCandidate/SphincsMaskedImages.lean` and `SphincsImages.lean`, translates their HASH/HALT services to the sig.golf-dev beta contract at `dbbbfe5e206dc501dbd15c920ff2892e453ec30f`, and writes `tools/beta64/output/SphincsBeta64Images.lean`. It checks all four legacy and translated code hashes, 64-byte HASH alignment, and the exact generated image-section hash. No source generator or network access is needed.

The generated image section is the exact prefix of `submission/SigGolfCandidate/SphincsBeta64Images.lean`; the rest of that Lean file contains the handwritten submission and admission theorem. The script checks this prefix equality. The per-site JSON report and four `.hex` files are diagnostic outputs.
