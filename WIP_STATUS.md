# claude-submission-tooling

Development material behind branch `claude-submission` (the PR branch, which contains only
`submission/` and `presentation/`):
- `wip/SPEC.md` — scheme specification; `wip/py/` — reference implementation, sig.golf VM emulator,
  assembler/generator of the four images, differential tests, Lean export.
- `wip/package.py` — assembles the admitted root (import closure of Solution.lean, SphincsSecurity moved
  under SigGolfCandidate); `wip/verify_local.py` — organizer verify.py without the namespace-isolation
  properties this host's AppArmor forbids (same project assembly, comparator command and resource limits).
- notes of each proof component (`wip/sec-*`, `wip/rv-notes`).
