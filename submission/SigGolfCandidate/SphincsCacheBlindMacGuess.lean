import SigGolfCandidate.SphincsSecurity.Scheme
import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude

/-! A blind verifier leaks only an equality bit for each guessed tag.
The list represents the attacker's all-failure path; private randomness and
other oracle replies may choose the list, but it is independent of the hidden
MAC table. Repeated guesses at one ciphertext are counted separately. -/

namespace SigGolfCandidate.SphincsCacheBlindMacGuess
open SphincsSecurity OracleComp ENNReal

variable {Key : Type}

def Hit (attempts : List (Key × Digest)) (table : Key → Digest) : Prop :=
  ∃ attempt ∈ attempts, table attempt.1 = attempt.2

theorem hit_cons (attempt : Key × Digest)
    (attempts : List (Key × Digest)) (table : Key → Digest) :
    Hit (attempt :: attempts) table ↔
      table attempt.1 = attempt.2 ∨ Hit attempts table := by
  simp [Hit]

/-- Union bound along a fixed all-failure path, including repeated guesses
against an answer cached at the same oracle input. No independence among
different MAC targets is needed; uniform marginals suffice. -/
theorem fixed_plan_bound (targets : PMF (Key → Digest))
    (hmarginal : ∀ key guess,
      Pr[fun table => table key = guess | targets] ≤
        (Fintype.card Digest : ENNReal)⁻¹)
    (attempts : List (Key × Digest)) :
    Pr[Hit attempts | targets] ≤
      attempts.length * (Fintype.card Digest : ENNReal)⁻¹ := by
  classical
  induction attempts with
  | nil =>
    have hempty : Hit ([] : List (Key × Digest)) = fun _ => False := by
      funext table
      simp [Hit]
    rw [hempty]
    simp
  | cons attempt attempts ih =>
    have hevent : Hit (attempt :: attempts) =
        fun table => table attempt.1 = attempt.2 ∨ Hit attempts table := by
      funext table
      exact propext (hit_cons attempt attempts table)
    rw [hevent]
    calc
      _ ≤ Pr[fun table => table attempt.1 = attempt.2 | targets] +
          Pr[Hit attempts | targets] := probEvent_or_le targets _ _
      _ ≤ (Fintype.card Digest : ENNReal)⁻¹ +
          attempts.length * (Fintype.card Digest : ENNReal)⁻¹ :=
        add_le_add (hmarginal attempt.1 attempt.2) ih
      _ = (attempt :: attempts).length * (Fintype.card Digest : ENNReal)⁻¹ := by
        simp [List.length_cons, Nat.cast_add, add_mul, add_comm]

/-- An arbitrary independent environment chooses the all-failure plan. Its
choices can encode private coins, public cache bytes, honest signatures and
unrelated RO answers. A repeated equality test consumes another attempt. -/
theorem adaptive_blind_bound {Env : Type} (environment : PMF Env)
    (targets : PMF (Key → Digest)) (plan : Env → List (Key × Digest))
    (hmarginal : ∀ key guess,
      Pr[fun table => table key = guess | targets] ≤
        (Fintype.card Digest : ENNReal)⁻¹)
    (q : Nat) (hbudget : ∀ env, (plan env).length ≤ q) :
    Pr[fun result => Hit (plan result.1) result.2 |
      (do
        let env ← (liftM environment : SPMF Env)
        let table ← (liftM targets : SPMF (Key → Digest))
        pure (env, table))] ≤
      q * (Fintype.card Digest : ENNReal)⁻¹ := by
  classical
  apply probEvent_bind_le_of_forall_le
  intro env _
  simp only [bind_pure_comp, probEvent_map, Function.comp_def,
    SPMF.probEvent_liftM]
  refine (fixed_plan_bound targets hmarginal (plan env)).trans ?_
  gcongr
  exact_mod_cast hbudget env

end SigGolfCandidate.SphincsCacheBlindMacGuess

/-- info: 'SigGolfCandidate.SphincsCacheBlindMacGuess.adaptive_blind_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheBlindMacGuess.adaptive_blind_bound
