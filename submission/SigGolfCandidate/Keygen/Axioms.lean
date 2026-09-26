import SigGolfCandidate.Keygen.Main

/-! Axiom audit for `keygen`. -/

/--
info: 'SigGolfCandidate.Keygen.keygen_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms SigGolfCandidate.Keygen.keygen_run

/--
info: 'SigGolfCandidate.Keygen.keygen_run_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms SigGolfCandidate.Keygen.keygen_run_counts

/--
info: 'SigGolfCandidate.Keygen.keygen_runWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms SigGolfCandidate.Keygen.keygen_runWith
