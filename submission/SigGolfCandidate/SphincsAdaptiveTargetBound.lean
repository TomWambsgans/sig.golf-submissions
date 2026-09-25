import SigGolfCandidate.Hypertree.SecurityUniform

/-!
A reusable adaptive random-oracle target bound. An initial cache and a fixed,
input-indexed target may be public. Each fresh query has a uniform answer;
the strategy may adapt to every answer, but cannot inspect the monitor's flag.
Repeated queries consume budget too and cannot create a fresh-target hit.
-/

namespace SigGolfCandidate.SphincsAdaptiveTargetBound
open OracleComp OracleSpec SigGolfCandidate.Hypertree.SecurityUniform

set_option maxRecDepth 4096

inductive Strategy (input : Type) (high low : Nat) where
  | done
  | query (address : input) (next : BitVec (high + low) → Strategy input high low)
  | bits (next : BitVec 256 → Strategy input high low)
  | coin (n : Nat) (next : Fin (n + 1) → Strategy input high low)

abbrev Cache (input : Type) (high low : Nat) := input → Option (BitVec (high + low))

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
    (target : input → Option (BitVec low)) :
    Cache input high low → Strategy input high low → Nat → ProbComp Bool
  | _, .done, _ => pure false
  | _, .query _ _, 0 => pure false
  | cache, .query address next, budget + 1 =>
      match cache address with
      | some answer => play target cache (next answer) budget
      | none => do
          let answer ← $ᵗ BitVec (high + low)
          let later ← play target (Function.update cache address (some answer))
            (next answer) budget
          return decide (∃ expected, target address = some expected ∧
            answer.extractLsb' 0 low = expected) || later
  | cache, .bits next, budget => do
      let value ← $ᵗ BitVec 256
      play target cache (next value) budget
  | cache, .coin n next, budget => do
      let value ← $ᵗ Fin (n + 1)
      play target cache (next value) budget

theorem fresh_target_hit_le (high low : Nat) (target : Option (BitVec low)) :
    Pr[fun answer : BitVec (high + low) =>
      ∃ expected, target = some expected ∧ answer.extractLsb' 0 low = expected |
      ($ᵗ BitVec (high + low))] ≤ 1 / 2 ^ low := by
  cases target with
  | none => simp
  | some expected =>
      simpa [eq_comm] using
        (prob_extract_mem high low ({expected} : Finset (BitVec low))).le

theorem adaptive_target_le {input : Type} [DecidableEq input]
    (high low : Nat) (target : input → Option (BitVec low))
    (strategy : Strategy input high low) (cache : Cache input high low)
    (budget : Nat) :
    Pr[fun hit => hit = true | play target cache strategy budget] ≤
      (budget : ENNReal) / 2 ^ low := by
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
                exact_mod_cast Nat.le_succ budget)
          | none =>
              simp only [play, present]
              have one := passive_or_le ($ᵗ BitVec (high + low))
                (fun answer => decide (∃ expected,
                  target address = some expected ∧ answer.extractLsb' 0 low = expected))
                (fun answer => play target (Function.update cache address (some answer))
                  (next answer) budget)
              have first :
                  Pr[fun answer : BitVec (high + low) =>
                    decide (∃ expected, target address = some expected ∧
                      answer.extractLsb' 0 low = expected) = true |
                    ($ᵗ BitVec (high + low))] ≤ 1 / 2 ^ low := by
                simpa only [decide_eq_true_eq] using
                  fresh_target_hit_le high low (target address)
              have later :
                  Pr[fun hit => hit = true |
                    (do let answer ← $ᵗ BitVec (high + low)
                        play target (Function.update cache address (some answer))
                          (next answer) budget)] ≤
                    (budget : ENNReal) / 2 ^ low := by
                exact probEvent_bind_le_of_forall_le (fun answer _ =>
                  ih answer (Function.update cache address (some answer)) budget)
              calc
                _ ≤ _ := one
                _ ≤ 1 / 2 ^ low + (budget : ENNReal) / 2 ^ low :=
                  add_le_add first later
                _ = _ := by simp only [Nat.cast_add, Nat.cast_one,
                  div_eq_mul_inv]; ring
  | bits next ih =>
      simp only [play]
      exact probEvent_bind_le_of_forall_le (fun value _ => ih value cache budget)
  | coin n next ih =>
      simp only [play]
      exact probEvent_bind_le_of_forall_le (fun value _ => ih value cache budget)

/-- info: 'SigGolfCandidate.SphincsAdaptiveTargetBound.adaptive_target_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms adaptive_target_le

end SigGolfCandidate.SphincsAdaptiveTargetBound
