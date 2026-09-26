import SigGolfCandidate.Verify.Arith2
import SigGolfCandidate.Verify.ForsRuns

/-! # Digest-word arithmetic: idx, u_k, admissibility, FORS tweak words -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem land1023 (n : Nat) : n &&& 1023 = n % 1024 := Nat.and_two_pow_sub_one_eq_mod n 10
theorem land63 (n : Nat) : n &&& 63 = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6

theorem or16 (x y : Nat) (hx : x < 64) (hy : y < 16) :
    x * 16 % 18446744073709551616 ||| y = x * 16 + y := by
  rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm, show (16 : Nat) = 2 ^ 4 from rfl,
    ← Nat.two_pow_add_eq_or_of_lt hy]

theorem uExprW_eval (w : Nat → Rv.E) (A : Nat) (s : MachineState)
    (hw : ∀ i, i < 3 → (w i).eval s = BitVec.ofNat 64 (A / 2 ^ (64 * i) % 2 ^ 64)) (k : Nat) (hk : k < 14) :
    (uExprW w k).eval s = BitVec.ofNat 64 (A / 2 ^ (34 + 10 * k) % 1024) := by
  have h0 := hw 0 (by decide); have h1 := hw 1 (by decide); have h2 := hw 2 (by decide)
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one] at h0 h1 h2
  apply BitVec.eq_of_toNat_eq
  interval_cases k <;> simp only [uExprW] <;> norm_num <;>
    simp only [Rv.E.eval, BinOp.eval, cw, h0, h1, h2, BitVec.toNat_and, BitVec.toNat_or,
      BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq] <;> norm_num <;> (try simp only [land1023, land63]) <;>
    first
    | omega
    | (rw [or16 _ _ (Nat.mod_lt _ (by decide)) (by omega)]; omega)

end SigGolfCandidate.Verify
