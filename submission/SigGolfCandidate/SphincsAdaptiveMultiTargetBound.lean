import SigGolfCandidate.SphincsAdaptiveTargetBound

/-! A fresh random-oracle answer hitting any of a bounded number of public targets. -/

namespace SigGolfCandidate.SphincsAdaptiveMultiTargetBound
open OracleComp OracleSpec
open SigGolfCandidate.SphincsAdaptiveTargetBound
open SigGolfCandidate.Hypertree.SecurityUniform

set_option maxRecDepth 4096

private theorem passive_or_le {α : Type} (draw : ProbComp α)
    (flag : α → Bool) (next : α → ProbComp Bool) :
    Pr[fun hit => hit = true |
      (do let value ← draw
          let later ← next value
          pure (flag value || later))] ≤
      Pr[fun value => flag value = true | draw] +
        Pr[fun hit => hit = true | draw >>= next] := by
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' value, Pr[= value | draw] *
        ((if flag value = true then 1 else 0) +
          Pr[fun hit => hit = true | next value]) := by
      apply ENNReal.tsum_le_tsum
      intro value
      apply mul_le_mul' le_rfl
      cases same : flag value with
      | false => simp
      | true =>
          simp only [Bool.true_or, ↓reduceIte]
          exact probEvent_le_one.trans (le_add_right le_rfl)
    _ = _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, probEvent_bind_eq_tsum,
        probEvent_eq_tsum_ite]
      congr 1
      apply tsum_congr
      intro value
      split_ifs <;> simp

noncomputable def play {input : Type} [DecidableEq input] {high low : Nat}
    (targets : input → Finset (BitVec low)) :
    Cache input high low → Strategy input high low → Nat → ProbComp Bool
  | _, .done, _ => pure false
  | _, .query _ _, 0 => pure false
  | cache, .query address next, budget + 1 =>
      match cache address with
      | some answer => play targets cache (next answer) budget
      | none => do
          let answer ← $ᵗ BitVec (high + low)
          let later ← play targets (Function.update cache address (some answer))
            (next answer) budget
          return decide (answer.extractLsb' 0 low ∈ targets address) || later
  | cache, .bits next, budget => do
      let value ← $ᵗ BitVec 256
      play targets cache (next value) budget
  | cache, .coin n next, budget => do
      let value ← $ᵗ Fin (n + 1)
      play targets cache (next value) budget

/-- Counts hits by fresh queries after the initial cache. Collisions already present
    in that cache require a separate setup bound. -/
theorem adaptive_targets_le {input : Type} [DecidableEq input]
    (high low maxTargets : Nat) (targets : input → Finset (BitVec low))
    (hcard : ∀ address, (targets address).card ≤ maxTargets)
    (strategy : Strategy input high low) (cache : Cache input high low)
    (budget : Nat) :
    Pr[fun hit => hit = true | play targets cache strategy budget] ≤
      (budget : ENNReal) * maxTargets / 2 ^ low := by
  induction strategy generalizing cache budget with
  | done => simp [play]
  | query address next ih =>
      cases budget with
      | zero => simp [play]
      | succ budget =>
          cases present : cache address with
          | some answer =>
              simp only [play, present]
              exact (ih answer cache budget).trans (by
                apply ENNReal.div_le_div_right
                exact_mod_cast Nat.mul_le_mul_right maxTargets (Nat.le_succ budget))
          | none =>
              simp only [play, present]
              have one := passive_or_le ($ᵗ BitVec (high + low))
                (fun answer => decide (answer.extractLsb' 0 low ∈ targets address))
                (fun answer => play targets
                  (Function.update cache address (some answer))
                  (next answer) budget)
              have first :
                  Pr[fun answer : BitVec (high + low) =>
                    decide (answer.extractLsb' 0 low ∈ targets address) = true |
                    ($ᵗ BitVec (high + low))] ≤
                    (maxTargets : ENNReal) / 2 ^ low := by
                have hcard' : ((targets address).card : ENNReal) ≤ maxTargets := by
                  exact_mod_cast hcard address
                simpa only [decide_eq_true_eq] using
                  (prob_extract_mem high low (targets address)).le.trans
                    (ENNReal.div_le_div_right hcard' (2 ^ low))
              have later :
                  Pr[fun hit => hit = true |
                    (do let answer ← $ᵗ BitVec (high + low)
                        play targets (Function.update cache address (some answer))
                          (next answer) budget)] ≤
                    (budget : ENNReal) * maxTargets / 2 ^ low := by
                exact probEvent_bind_le_of_forall_le (fun answer _ =>
                  ih answer (Function.update cache address (some answer)) budget)
              calc
                _ ≤ _ := one
                _ ≤ (maxTargets : ENNReal) / 2 ^ low +
                      (budget : ENNReal) * maxTargets / 2 ^ low :=
                  add_le_add first later
                _ = _ := by
                  simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
                  ring
  | bits next ih =>
      simp only [play]
      exact probEvent_bind_le_of_forall_le (fun value _ => ih value cache budget)
  | coin n next ih =>
      simp only [play]
      exact probEvent_bind_le_of_forall_le (fun value _ => ih value cache budget)

end SigGolfCandidate.SphincsAdaptiveMultiTargetBound

/-- info: 'SigGolfCandidate.SphincsAdaptiveMultiTargetBound.adaptive_targets_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAdaptiveMultiTargetBound.adaptive_targets_le
