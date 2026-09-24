# sig.golf submissions · beta

Build a stateless hash-based signature scheme, prove it against the [beta rules](https://github.com/leanEthereum/sig.golf-dev/blob/beta/README.md), and minimize signature bytes × RISC-V verification cycles.

Open a pull request **against this repository's `beta` branch**. Put the entire candidate under `submission/`:

```text
submission/
  claim.json
  Solution.lean
  SigGolfCandidate/
    ... your Lean helper modules ...
```

`claim.json` declares signature bytes `S`, witness bytes `W`, verification cycles `C`, and one layout shared by all four programs. For example: `{"S":119632,"W":119632,"C":5883520,"layout":{"message":0,"secret_key":32,"public_key":64,"cache":96,"signature":131168,"witness":250800}}`. Every offset is a nonnegative decimal byte address, aligned to 8 bytes; the six buffers must be disjoint and fit below the embedded-data region of each program. The verifier checks the layout automatically. The score is `S × C`. The proof must tie the sizes, layout, and four exact RISC-V images together. Name its exported declarations `SigGolf.Challenge.submission`, `SigGolf.Challenge.signature_bytes`, `SigGolf.Challenge.witness_bytes`, `SigGolf.Challenge.layout_offsets`, and `SigGolf.Challenge.certificate`; the [challenge template](https://github.com/leanEthereum/sig.golf-dev/blob/beta/verifier/Challenge.lean.in) gives their types.

Submission code may import the protected `SigGolf` modules, `Mathlib`, `ToMathlib`, `VCVio`, `RiscvZkvm`, `Batteries`, `Lean`, `Init`, and `Std`, plus its own `SigGolfCandidate` modules. The root has at most 1000 entries, 8 MiB per file, and 16 MiB total. Only `.lean` files, `Solution.lean`, and `claim.json` are admitted. Library source belongs in imports, not in the PR.

The verifier freezes the PR head, applies the source policy, and independently checks the claimed statements and permitted axioms. A passing PR receives a bot verdict. If it sets a new best score, the bot publishes the record on this repository's `beta` branch automatically after verification. The server's local files are disposable; GitHub holds the PR, the published `records.json`, and a copy of each verified source under `verified/<PR-head-SHA>/`.

License: [Apache 2.0](LICENSE).
