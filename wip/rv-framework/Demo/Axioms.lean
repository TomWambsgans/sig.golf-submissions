import SigGolfCandidate.Rv.Demo.Block40
import SigGolfCandidate.Rv.Demo.CopyLoop
import SigGolfCandidate.Rv.Demo.HashStep
import SigGolfCandidate.Rv.Scale.Blocks7

/-! Axiom audit: only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no
`Lean.ofReduceBool`). `#guard_msgs` makes the build fail if this changes. -/

open SigGolfCandidate.Rv

/-- info: 'SigGolfCandidate.Rv.symRun_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms symRun_sound
/-- info: 'SigGolfCandidate.Rv.symRun_ecall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms symRun_ecall
/-- info: 'SigGolfCandidate.Rv.Steps.execute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Steps.execute
/-- info: 'SigGolfCandidate.Rv.execute_hash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms execute_hash
/-- info: 'SigGolfCandidate.Rv.hashInput_eq_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hashInput_eq_words
/-- info: 'SigGolfCandidate.Rv.runWith_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runWith_eq
/-- info: 'SigGolfCandidate.Rv.Demo1.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Demo1.spec
/-- info: 'SigGolfCandidate.Rv.CopyLoop.copy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CopyLoop.copy_spec
/-- info: 'SigGolfCandidate.Rv.HashStep.hash_execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HashStep.hash_execute
/-- info: 'SigGolfCandidate.Rv.Scale.spec399' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Scale.spec399
