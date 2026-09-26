import SigGolfCandidate.Expand.Main

/-! Axiom audit for `expand`. -/

/--
info: 'SigGolfCandidate.Expand.expand_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms SigGolfCandidate.Expand.expand_run

/--
info: 'SigGolfCandidate.Expand.expand_runWith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms SigGolfCandidate.Expand.expand_runWith
