import SigGolfCandidate.Budget.Bridge

/-! Axiom audit of the budget results. -/

/--
info: 'SigGolfCandidate.Budget.submission_compressionBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.Budget.submission_compressionBounds

/--
info: 'SigGolfCandidate.Budget.V_signRef_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.Budget.V_signRef_le_two

/--
info: 'SigGolfCandidate.Budget.submission_compressionBounds_of_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.Budget.submission_compressionBounds_of_counts
