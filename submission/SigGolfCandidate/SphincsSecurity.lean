import SigGolfCandidate.SphincsSecurity.Proof.Adversary.Embedding
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.Security
import SigGolfCandidate.SphincsSecurity.Statement
import SigGolfCandidate.SphincsSecurity.Completeness
import SigGolfCandidate.SphincsSecurity.Completeness.Assembly

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity.Security

set_option backward.isDefEq.respectTransparency false

/-- The embedding preserves both the winning event and the complete hash-query budget. -/
theorem security127 : HasClassicalSecurityBits 127 := by
  intro q hq adversary hbound
  rw [← advantage_embed]
  apply Seeded.scheme_has_127_bits_of_classical_security q hq
  change ∀ result ∈ support ((simulateQ countedRomImpl
    (SphincsSecurity.gameCore Seeded.scheme (embed adversary))).run.run' ∅), result.2 ≤ q
  rw [experiment_embed]
  exact hbound

end SphincsSecurity.Security


namespace SphincsSecurity

/-- The SPHINCS scheme has 127 bits of classical security (SUF-CMA in the ROM). -/
theorem sphincs_has_127_bits_of_classical_security : SphincsSecurityStatement :=
  Security.security127

/-- A signature the SPHINCS signer produces verifies, under every hash function. -/
theorem sphincs_is_correct : SphincsCorrectnessStatement :=
  Completeness.correct

/-- One SPHINCS key signs every message successfully except with probability at most `2⁻²⁵⁶`. -/
theorem sphincs_is_complete : SphincsCompletenessStatement :=
  Completeness.complete

/-! The build fails if the axiom footprint ever grows beyond Lean's three standard axioms, so a `sorry` or `native_decide` anywhere in the proof cannot go unnoticed. -/

/-- info: 'SphincsSecurity.sphincs_has_127_bits_of_classical_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphincs_has_127_bits_of_classical_security

/-- info: 'SphincsSecurity.sphincs_is_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphincs_is_correct

/-- info: 'SphincsSecurity.sphincs_is_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphincs_is_complete

end SphincsSecurity
