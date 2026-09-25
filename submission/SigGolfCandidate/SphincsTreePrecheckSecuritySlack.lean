import SigGolfCandidate.SphincsRawSecurityBound

namespace SphincsSecurity.Concrete
open ENNReal

set_option exponentiation.threshold 1024

/-- Conservative union bound over all 2,047 canonical parent positions still
fits the competition's 127-bit target after the 48× raw-signer simulation. -/
theorem inflated_security_with_full_tree_precheck (q r : Nat)
    (hr : 1 ≤ r) (hcap : r ≤ 2 ^ 128) (hinflate : r ≤ 48 * q)
    (adversary : Adversary) (hbound : HasHashQueryBound scheme adversary r) :
    forgeAdvantage scheme adversary + (q : ENNReal) / 2 ^ 128 +
      (q : ENNReal) * 2047 / 2 ^ 160 ≤ (q : ENNReal) / 2 ^ 127 := by
  calc
    _ ≤ (r : ENNReal) / 2 ^ 140 + (q : ENNReal) / 2 ^ 128 +
          (q : ENNReal) * 2047 / 2 ^ 160 := by
      exact add_le_add
        (add_le_add
          ((RetainedResidual.forgeAdvantage_le_native_bound fixedReferenceDummy
            (fun _ _ _ => fixedReferenceDummyWord_valid) adversary r hbound hcap).trans
            (raw_native_bound_le_140 r hr hcap)) le_rfl) le_rfl
    _ ≤ (q : ENNReal) / 2 ^ 127 := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div,
        ENNReal.toReal_mul, ENNReal.toReal_natCast]
      have hreal : (r : ℝ) ≤ 48 * q := by exact_mod_cast hinflate
      norm_num
      linarith

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.inflated_security_with_full_tree_precheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.inflated_security_with_full_tree_precheck
