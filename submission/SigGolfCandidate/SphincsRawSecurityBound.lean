import SigGolfCandidate.SphincsSecurity.Proof.Residual.Security127LargeBudget
import SigGolfCandidate.SphincsSecurity.Proof.Security127Completion

namespace SphincsSecurity.Concrete

open ENNReal

set_option exponentiation.threshold 1024

private theorem rawRate_le_140 (r : Nat) (hr : 1 ≤ r) :
    (r : ENNReal) * 2 / 2 ^ 160 +
      (r : ENNReal) * ((2 ^ 144 : ENNReal)⁻¹ + 11 / 2 ^ 144) +
      ((r : ENNReal) * (2 ^ 155 : ENNReal)⁻¹ + (2 ^ 700 : ENNReal)⁻¹) ≤
      (r : ENNReal) / 2 ^ 140 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  norm_num
  linarith

theorem raw_native_bound_le_140 (r : Nat) (hr : 1 ≤ r) (hsmall : r ≤ 2 ^ 128) :
    ENNReal.ofReal (2 * ((r : ℝ) / 2 ^ digestBits) - ((r : ℝ) / 2 ^ digestBits) ^ 2) +
      (r : ENNReal) * fullCertificateTotalRate +
      ((r : ENNReal) * certificateCacheExceptionRate + proposalPrefixExceptionBound) ≤
      (r : ENNReal) / 2 ^ 140 := by
  have hfirst : ENNReal.ofReal
      (2 * ((r : ℝ) / 2 ^ digestBits) - ((r : ℝ) / 2 ^ digestBits) ^ 2) ≤
      (r : ENNReal) * 2 / 2 ^ 160 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    have hrR : (0 : ℝ) ≤ r := by positivity
    have hupper : (r : ℝ) ≤ 2 ^ 128 := by exact_mod_cast hsmall
    have hy : (r : ℝ) / 2 ^ digestBits ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      dsimp [digestBits]
      norm_num at hupper ⊢
      linarith
    have hp : 0 ≤ 2 * ((r : ℝ) / 2 ^ digestBits) - ((r : ℝ) / 2 ^ digestBits) ^ 2 := by
      have hnonneg : 0 ≤ (r : ℝ) / 2 ^ digestBits := by positivity
      nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hy)]
    rw [ENNReal.toReal_ofReal hp]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat]
    dsimp [digestBits]
    norm_num
    nlinarith [sq_nonneg ((r : ℝ) / 2 ^ 160)]
  rw [fullCertificateTotalRate_def, fullCertificateExcessRate_def,
    proposalPrefixExceptionBound_def]
  calc
    _ ≤ (r : ENNReal) * 2 / 2 ^ 160 +
          (r : ENNReal) * ((2 ^ 144 : ENNReal)⁻¹ + 11 / 2 ^ 144) +
          ((r : ENNReal) * (2 ^ 155 : ENNReal)⁻¹ + (2 ^ 700 : ENNReal)⁻¹) := by
            gcongr
            exact certificateCacheExceptionRate_le
    _ ≤ (r : ENNReal) / 2 ^ 140 := rawRate_le_140 r hr

/-- The unrounded scheme bound leaves room for at most 48 times as many
abstract hash queries plus one 128-bit commitment guess per concrete query. -/
theorem inflated_security_with_commitment (q r : Nat)
    (hr : 1 ≤ r) (hcap : r ≤ 2 ^ 128) (hinflate : r ≤ 48 * q)
    (adversary : Adversary) (hbound : HasHashQueryBound scheme adversary r) :
    forgeAdvantage scheme adversary + (q : ENNReal) / 2 ^ 128 ≤
      (q : ENNReal) / 2 ^ 127 := by
  calc
    _ ≤ (r : ENNReal) / 2 ^ 140 + (q : ENNReal) / 2 ^ 128 := by
      exact add_le_add
        ((RetainedResidual.forgeAdvantage_le_native_bound fixedReferenceDummy
          (fun _ _ _ => fixedReferenceDummyWord_valid) adversary r hbound hcap).trans
          (raw_native_bound_le_140 r hr hcap)) le_rfl
    _ ≤ (q : ENNReal) / 2 ^ 127 := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div,
        ENNReal.toReal_natCast]
      have hreal : (r : ℝ) ≤ 48 * q := by exact_mod_cast hinflate
      norm_num
      linarith

/-- The same accounting includes a further 160-bit collision event from an
attacker-modified public cache. -/
theorem inflated_security_with_commitment_and_cache (q r : Nat)
    (hr : 1 ≤ r) (hcap : r ≤ 2 ^ 128) (hinflate : r ≤ 48 * q)
    (adversary : Adversary) (hbound : HasHashQueryBound scheme adversary r) :
    forgeAdvantage scheme adversary + (q : ENNReal) / 2 ^ 128 +
      (q : ENNReal) / 2 ^ 160 ≤ (q : ENNReal) / 2 ^ 127 := by
  calc
    _ ≤ (r : ENNReal) / 2 ^ 140 + (q : ENNReal) / 2 ^ 128 +
          (q : ENNReal) / 2 ^ 160 := by
      exact add_le_add
        (add_le_add
          ((RetainedResidual.forgeAdvantage_le_native_bound fixedReferenceDummy
            (fun _ _ _ => fixedReferenceDummyWord_valid) adversary r hbound hcap).trans
            (raw_native_bound_le_140 r hr hcap)) le_rfl) le_rfl
    _ ≤ (q : ENNReal) / 2 ^ 127 := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div,
        ENNReal.toReal_natCast]
      have hreal : (r : ℝ) ≤ 48 * q := by exact_mod_cast hinflate
      norm_num
      linarith

/-- info: 'SphincsSecurity.Concrete.inflated_security_with_commitment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inflated_security_with_commitment

/-- info: 'SphincsSecurity.Concrete.inflated_security_with_commitment_and_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms inflated_security_with_commitment_and_cache

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

/-- Hash calls in the seed signer's final, unused top-tree recomputation: each
leaf derives 52 chain seeds, walks seven links per chain, and hashes the leaf;
the remaining nodes each hash once. -/
def seededTreeNodeCalls (level : Nat) : Nat :=
  (numChains * chainLength + 2) * 2 ^ level - 1

def seededFinalTreeCalls : Nat :=
  seededTreeNodeCalls (layerHeight topLayer)

theorem seededFinalTreeCalls_eq : seededFinalTreeCalls = 856063 := by
  norm_num [seededFinalTreeCalls, seededTreeNodeCalls, numChains, chainLength, winternitzBits,
    layerHeight, topLayer, maxLayerHeight]

def seededTopPathCalls : Nat :=
  ∑ level ∈ Finset.range (layerHeight topLayer), seededTreeNodeCalls level

theorem seededTopPathCalls_eq : seededTopPathCalls = 855635 := by
  decide

/-- A request can perform the top path even if a later step fails. The final
tree runs only after all layers succeed. Charging both for every request
therefore covers successful and failed requests alike. -/
def cachedSignerOverheadCalls : Nat := seededTopPathCalls + seededFinalTreeCalls

theorem cachedSignerOverheadCalls_eq : cachedSignerOverheadCalls = 1711698 := by
  norm_num [cachedSignerOverheadCalls, seededTopPathCalls_eq, seededFinalTreeCalls_eq]

theorem lifetime_cachedSignerOverheadCalls_lt :
    signatureLimit * cachedSignerOverheadCalls < 2 ^ 53 := by
  norm_num [cachedSignerOverheadCalls_eq, signatureLimit]

/-- The arithmetic boundary needed by the 128-cap residual theorem. The
premise `hinflation` must still be proved from an exact trace equivalence. -/
theorem virtual_query_budget_below_128 (q r requests : Nat)
    (hq : q < 2 ^ 127) (hrequests : requests ≤ signatureLimit)
    (hinflation : r ≤ q + requests * cachedSignerOverheadCalls) :
    r ≤ 2 ^ 128 := by
  have hscaled : requests * cachedSignerOverheadCalls ≤
      signatureLimit * cachedSignerOverheadCalls :=
    Nat.mul_le_mul_right cachedSignerOverheadCalls hrequests
  have hmax := lifetime_cachedSignerOverheadCalls_lt
  omega

/-- info: 'SphincsSecurity.Concrete.virtual_query_budget_below_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms virtual_query_budget_below_128

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.security127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphincsSecurity.Concrete.security127
