# claude-submission — work in progress

SPHINCS+ variant for sig.golf beta (spec: `wip/SPEC.md`). `submission/` is the admitted root (passes
`check_submission.py`; S = W = 7756, C = 18388, S×C = 142,617,328), `presentation/` the display files.

**Not yet a valid PR.** `Solution.lean` proves the certificate from a bundle `SigGolfCandidate.Final.Pending`
of component theorems. Status of the pending components:
- verify bytecode refinement, termination, cycle bound (≤ 18357 on every run): **proved** (being integrated)
- sign bytecode refinement + termination: in progress
- event-form abstract security (∀ adversaries, Pr[win ∧ calls ≤ Q] ≤ Q/2^127): in progress
Everything else (keygen/expand refinement, compression budgets, completeness, security bridge,
spec ≡ abstract scheme, verification bound) is proved.
