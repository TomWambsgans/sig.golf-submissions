import SigGolfCandidate.Ref
import SigGolfCandidate.Submission

/-! Axiom audit of the reference-spec lemmas and the admissibility proof. -/

open SigGolfCandidate SigGolfCandidate.Ref

/-- info: 'SigGolfCandidate.submission_admissible' depends on axioms: [propext] -/
#guard_msgs in #print axioms submission_admissible
/-- info: 'SigGolfCandidate.Ref.unexpandRef_expandRef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unexpandRef_expandRef
/-- info: 'SigGolfCandidate.Ref.expandRef_unexpandRef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expandRef_unexpandRef
/-- info: 'SigGolfCandidate.Ref.countWith_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms countWith_bind
/-- info: 'SigGolfCandidate.Ref.fst_countWith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fst_countWith
/-- info: 'SigGolfCandidate.Ref.pad64_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pad64_eq
