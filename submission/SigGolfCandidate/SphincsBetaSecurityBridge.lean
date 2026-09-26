import SigGolfCandidate.SphincsAlignedQuery
import SigGolfCandidate.SphincsSecurity.Proof.Residual.Security127LargeBudget

namespace SigGolfCandidate.BetaQuery
open SigGolf SphincsSecurity OracleComp OracleSpec ENNReal

noncomputable def abstractReference (adversary : SphincsSecurity.Adversary) :
    SPMF SigGolf.AttackResult :=
  (fun result : Bool × Nat => ⟨result.1, result.2⟩) <$>
    𝒮[(simulateQ abstractWorldOnBeta
      (countHashQueries (gameCore SphincsSecurity.Concrete.scheme adversary))).run' ∅]

theorem abstractReference_budget_rate (adversary : SphincsSecurity.Adversary)
    (q : Nat) (hq : 1 ≤ q) (hsmall : q ≤ 2 ^ 127) :
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ q |
      abstractReference adversary] ≤ (q : ENNReal) / 2 ^ 128 := by
  have hraw :
      Pr[fun result => result.1 = true ∧ result.2 ≤ q |
        (simulateQ abstractWorldOnBeta
          (countHashQueries (gameCore SphincsSecurity.Concrete.scheme adversary))).run' ∅] ≤
        (q : ENNReal) / 2 ^ 128 := by
    rw [betaWorld_reindex]
    exact SphincsSecurity.Concrete.originalGame_actual_budget_le_security128 adversary q hq hsmall
  simp only [abstractReference, probEvent_map, probEvent_evalSPMF]
  exact hraw

theorem joint_budget_event_le
    (actual reference : SPMF SigGolf.AttackResult)
    (joint : SPMF (SigGolf.AttackResult × SigGolf.AttackResult × Bool × Bool))
    (q : Nat)
    (hactual : (fun z => z.1) <$> joint = actual)
    (hreference : (fun z => z.2.1) <$> joint = reference)
    (hwin : ∀ z ∈ support joint,
      z.2.2.1 = false → z.2.2.2 = false →
      z.1.won = true → z.2.1.won = true)
    (hcost : ∀ z ∈ support joint,
      z.2.2.1 = false → z.2.2.2 = false →
      z.2.1.hashCalls ≤ z.1.hashCalls) :
    Pr[fun r => r.won = true ∧ r.hashCalls ≤ q | actual] ≤
      Pr[fun r => r.won = true ∧ r.hashCalls ≤ q | reference] +
      Pr[fun z => z.1.hashCalls ≤ q ∧ z.2.2.1 = true | joint] +
      Pr[fun z => z.1.hashCalls ≤ q ∧ z.2.2.2 = true | joint] := by
  have hstep :
      Pr[fun z => z.1.won = true ∧ z.1.hashCalls ≤ q | joint] ≤
      Pr[fun z =>
        (z.2.1.won = true ∧ z.2.1.hashCalls ≤ q) ∨
        (z.1.hashCalls ≤ q ∧ z.2.2.1 = true) ∨
        (z.1.hashCalls ≤ q ∧ z.2.2.2 = true) | joint] := by
    apply probEvent_mono
    intro z hz hevent
    rcases hevent with ⟨hwon, hbudget⟩
    cases hm : z.2.2.1 with
    | true => exact Or.inr (Or.inl ⟨hbudget, rfl⟩)
    | false =>
        cases hs : z.2.2.2 with
        | true => exact Or.inr (Or.inr ⟨hbudget, rfl⟩)
        | false => exact Or.inl ⟨hwin z hz hm hs hwon,
            (hcost z hz hm hs).trans hbudget⟩
  calc
    Pr[fun r => r.won = true ∧ r.hashCalls ≤ q | actual] =
        Pr[fun z => z.1.won = true ∧ z.1.hashCalls ≤ q | joint] := by
      rw [← hactual, probEvent_map]
      rfl
    _ ≤ _ := hstep
    _ ≤ Pr[fun z => z.2.1.won = true ∧ z.2.1.hashCalls ≤ q | joint] +
        Pr[fun z => (z.1.hashCalls ≤ q ∧ z.2.2.1 = true) ∨
          (z.1.hashCalls ≤ q ∧ z.2.2.2 = true) | joint] :=
      probEvent_or_le _ _ _
    _ ≤ Pr[fun z => z.2.1.won = true ∧ z.2.1.hashCalls ≤ q | joint] +
        (Pr[fun z => z.1.hashCalls ≤ q ∧ z.2.2.1 = true | joint] +
          Pr[fun z => z.1.hashCalls ≤ q ∧ z.2.2.2 = true | joint]) :=
      add_le_add le_rfl (probEvent_or_le _ _ _)
    _ = _ := by rw [← hreference, probEvent_map, add_assoc]; rfl

theorem joint_budget_security127
    (adversary : SphincsSecurity.Adversary)
    (actual : SPMF SigGolf.AttackResult)
    (joint : SPMF (SigGolf.AttackResult × SigGolf.AttackResult × Bool × Bool))
    (q : Nat) (hq : 1 ≤ q) (hsmall : q ≤ 2 ^ 127)
    (hactual : (fun z => z.1) <$> joint = actual)
    (hreference : (fun z => z.2.1) <$> joint = abstractReference adversary)
    (hwin : ∀ z ∈ support joint,
      z.2.2.1 = false → z.2.2.2 = false →
      z.1.won = true → z.2.1.won = true)
    (hcost : ∀ z ∈ support joint,
      z.2.2.1 = false → z.2.2.2 = false →
      z.2.1.hashCalls ≤ z.1.hashCalls)
    (hmac : Pr[fun z => z.1.hashCalls ≤ q ∧ z.2.2.1 = true | joint] ≤
      (q : ENNReal) / 2 ^ 160)
    (hseed : Pr[fun z => z.1.hashCalls ≤ q ∧ z.2.2.2 = true | joint] ≤
      (q : ENNReal) / 2 ^ 256) :
    Pr[fun r => r.won = true ∧ r.hashCalls ≤ q | actual] ≤
      (q : ENNReal) / 2 ^ 127 := by
  have hrate : (q : ENNReal) / 2 ^ 128 +
      (q : ENNReal) / 2 ^ 160 +
      (q : ENNReal) / 2 ^ 256 ≤
        (q : ENNReal) / 2 ^ 127 := by
    simp only [div_eq_mul_inv]
    rw [← mul_add, ← mul_add]
    gcongr
    have hnn : ((2 ^ 128 : NNReal)⁻¹ +
      (2 ^ 160 : NNReal)⁻¹ + (2 ^ 256 : NNReal)⁻¹) ≤
      (2 ^ 127 : NNReal)⁻¹ := by
      apply NNReal.coe_le_coe.mpr
      norm_num [div_le_div_iff₀]
    have henn := ENNReal.coe_le_coe.mpr hnn
    have hcast (n : Nat) : (↑((2 ^ n : NNReal)⁻¹) : ENNReal) =
        (2 ^ n : ENNReal)⁻¹ := by
      rw [ENNReal.coe_inv (by positivity), ENNReal.coe_pow]
      norm_num
    simpa only [ENNReal.coe_add, hcast] using henn
  exact (joint_budget_event_le actual (abstractReference adversary) joint q
    hactual hreference hwin hcost).trans
    ((add_le_add (add_le_add
      (abstractReference_budget_rate adversary q hq hsmall) hmac) hseed).trans hrate)

/-- The missing concrete interface: one adaptive coupling for the exact beta
images, preserving the charged HASH count on good traces. The two flags cover
the public-cache MAC and secret-key exception events. -/
def HasCandidate64SecurityCoupling : Prop :=
  ∀ (attacker : SigGolf.Adversary Candidate64.submission.sizes)
    (rounds q : Nat), 1 ≤ q → q ≤ 2 ^ 127 →
    ∃ (abstractAttacker : SphincsSecurity.Adversary)
      (joint : SPMF (SigGolf.AttackResult × SigGolf.AttackResult × Bool × Bool)),
      (fun z => z.1) <$> joint =
        𝒮[Candidate64.submission.securityExperiment attacker rounds] ∧
      (fun z => z.2.1) <$> joint = abstractReference abstractAttacker ∧
      (∀ z ∈ support joint,
        z.2.2.1 = false → z.2.2.2 = false →
        z.1.won = true → z.2.1.won = true) ∧
      (∀ z ∈ support joint,
        z.2.2.1 = false → z.2.2.2 = false →
        z.2.1.hashCalls ≤ z.1.hashCalls) ∧
      Pr[fun z => z.1.hashCalls ≤ q ∧ z.2.2.1 = true | joint] ≤
        (q : ENNReal) / 2 ^ 160 ∧
      Pr[fun z => z.1.hashCalls ≤ q ∧ z.2.2.2 = true | joint] ≤
        (q : ENNReal) / 2 ^ 256

theorem candidate64_secure_of_coupling
    (hmodel : HasCandidate64SecurityCoupling) :
    Candidate64.submission.Secure := by
  intro attacker rounds q hq
  by_cases hsmall : q ≤ 2 ^ 127
  · obtain ⟨abstractAttacker, joint, hactual, hreference, hwin,
        hcost, hmac, hseed⟩ := hmodel attacker rounds q hq hsmall
    rw [← probEvent_evalSPMF]
    exact joint_budget_security127 abstractAttacker
      𝒮[Candidate64.submission.securityExperiment attacker rounds]
      joint q hq hsmall hactual hreference hwin hcost hmac hseed
  · have hlarge : 2 ^ 127 ≤ q := by omega
    calc
      _ ≤ 1 := probEvent_le_one
      _ = ((2 ^ 127 : Nat) : ENNReal) / 2 ^ 127 := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          (ENNReal.div_self (by norm_num : (2 ^ 127 : ENNReal) ≠ 0)
            (by norm_num : (2 ^ 127 : ENNReal) ≠ ⊤)).symm
      _ ≤ _ := by
        apply ENNReal.div_le_div_right
        exact_mod_cast hlarge

end SigGolfCandidate.BetaQuery

/-- info: 'SigGolfCandidate.BetaQuery.abstractReference_budget_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.BetaQuery.abstractReference_budget_rate

/-- info: 'SigGolfCandidate.BetaQuery.joint_budget_security127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.BetaQuery.joint_budget_security127

/-- info: 'SigGolfCandidate.BetaQuery.candidate64_secure_of_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.BetaQuery.candidate64_secure_of_coupling
