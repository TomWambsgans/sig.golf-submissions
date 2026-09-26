import SigGolfCandidate.Equiv.Main

/-! # Reference spec = abstract scheme: entry point and axiom audit -/

open SigGolfCandidate.Equiv

/-- info: 'SigGolfCandidate.Equiv.keygenRef_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keygenRef_eq
/-- info: 'SigGolfCandidate.Equiv.signRef_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signRef_eq
/-- info: 'SigGolfCandidate.Equiv.verifyRef_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyRef_eq
/-- info: 'SigGolfCandidate.Equiv.verifySigRef_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifySigRef_eq
/-- info: 'SigGolfCandidate.Equiv.padQ_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padQ_injOn
/-- info: 'SigGolfCandidate.Equiv.hq_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hq_keygen
/-- info: 'SigGolfCandidate.Equiv.hq_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hq_sign
/-- info: 'SigGolfCandidate.Equiv.hq_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hq_verify
/-- info: 'SigGolfCandidate.Equiv.zeroPadAssumptions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zeroPadAssumptions
/-- info: 'SigGolfCandidate.Equiv.submission_secure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms submission_secure
