# claude-submission — work in progress

SPHINCS+ variant for sig.golf beta (spec: `wip/SPEC.md`). **Not yet a valid PR:** the certificate is still being assembled.

Measured (Python VM, identical to the images in `submission/SigGolfCandidate/Images.lean`):
S = W = 7756 bytes, honest verification 18357 cycles + ceil(7756/256) = 31 → C = 18388, S×C = 142,617,328.

Layout:
- `submission/SigGolfCandidate/` — images, `Submission` (admissibility proved), byte-level reference spec (`Ref`),
  RISC-V symbolic-execution framework (`Rv`), bytecode refinement proofs in progress (`Verify`, `Sign`, `Keygen`, `Expand`),
  compression budget (`Budget`), organizer-game → abstract-game security bridge (`Bridge`, proved modulo its assumptions).
- `wip/sec-scheme`, `wip/sec-event` — the adapted SPHINCS security proof (scheme changes; event-form security), not yet merged.
- `wip/py` — reference implementation, VM emulator, assembler/generator, differential tests.
