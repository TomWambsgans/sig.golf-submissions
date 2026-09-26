# claude-submission — status

SPHINCS+ variant for sig.golf beta (spec: `wip/SPEC.md`). `submission/` is the admitted root (passes
`check_submission.py`; S = W = 7756, C = 18388, S×C = 142,617,328), `presentation/` the display files.

`SigGolf.Challenge.certificate : SigGolf.Certificate submission 18388` is fully proved
(axioms: propext, Classical.choice, Quot.sound). Remaining before opening the PR:
memory reduction of a few sign-proof modules (the verifier builds under a 24 GB cgroup) and a local run
of the organizer's verifier (comparator) on this exact tree.
