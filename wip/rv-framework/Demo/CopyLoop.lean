import SigGolfCandidate.Rv

/-!
# Demo 2: a loop (copy `n` doublewords), proven with a loop invariant

```
0x1000: ld   x13, 0(x10)
0x1004: sd   x13, 0(x11)
0x1008: addi x10, x10, 8
0x100c: addi x11, x11, 8
0x1010: addi x12, x12, -1
0x1014: bne  x12, x0, 0x1000
0x1018: ecall
```
The loop body is one symbolic block (`body`, 6 instructions, ends at the branch).
`copy_spec` is proven with `Steps.iterate` and the block lemma `body_spec`.
-/

namespace SigGolfCandidate.Rv.CopyLoop
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def code : List (BitVec 32) :=
  [0x00053683#32, 0x00d5b023#32, 0x00850513#32, 0x00858593#32, 0xfff60613#32, 0xfe0616e3#32]

def image : Image := ⟨code ++ [0x00000073#32], []⟩

theorem codeAt : CodeAt image 0x1000 code :=
  CodeAt.of_append (pre := []) (post := [0x00000073#32]) rfl _ (by decide) (by decide)

sym_block body := symRun {} code 0x1000 10

/-- Block lemma for one iteration, in readable concrete form. -/
theorem body_spec (t : MachineState) (hpc : t.pc = 0x1000)
    (hv10 : accessValid (t.getReg .x10) 8 = true) (hv11 : accessValid (t.getReg .x11) 8 = true) :
    ∃ u, Steps image t 6 6 u ∧
      u.getReg .x10 = t.getReg .x10 + 8 ∧ u.getReg .x11 = t.getReg .x11 + 8 ∧
      u.getReg .x12 = t.getReg .x12 - 1 ∧
      u.pc = (if t.getReg .x12 - 1 ≠ 0 then 0x1000 else 0x1018) ∧
      ∀ a, u.getMem a = if a = t.getReg .x11 then t.getMem (t.getReg .x10) else t.getMem a := by
  have hobl : body.res.obligs t := by simp only [body.res, rv_simp]; exact ⟨hv11, hv10⟩
  refine ⟨_, symRun_sound body codeAt t hpc hobl, ?_⟩
  simp only [body.res, rv_simp, bne_iff_ne, ne_eq]
  simp

/-- The same block lemma packaged as a `BlockSpec` (obligations deduplicated by `Oblig.dedup`,
computed by the kernel via `sym_eval`). -/
theorem body_blockSpec :
    BlockSpec image 0x1000 6 6
      (fun t => accessValid (t.getReg .x10) 8 = true ∧ accessValid (t.getReg .x11) 8 = true)
      (fun t u => u.getReg .x12 = t.getReg .x12 - 1) :=
  BlockSpec.of_symRun body codeAt
    (fun t ⟨h10, h11⟩ => body.res.obligs_of_dedup t (by sym_eval)
      (by simp only [rv_simp]; exact ⟨h11, h10⟩))
    (fun t _ => by simp only [body.res, rv_simp])

/-! ## The loop -/

theorem ofNat_add8 (x : Nat) : BitVec.ofNat 64 x + 8 = BitVec.ofNat 64 (x + 8) := by
  apply BitVec.eq_of_toNat_eq; simp

/-- Loop invariant with `i` iterations remaining. -/
def Inv (s : MachineState) (src dst n : Nat) (i : Nat) (t : MachineState) : Prop :=
  i ≤ n ∧
  t.getReg .x10 = BitVec.ofNat 64 (src + 8 * (n - i)) ∧
  t.getReg .x11 = BitVec.ofNat 64 (dst + 8 * (n - i)) ∧
  t.getReg .x12 = BitVec.ofNat 64 i ∧
  t.pc = (if i = 0 then 0x1018 else 0x1000) ∧
  (∀ j < n - i, t.getMem (BitVec.ofNat 64 (dst + 8 * j)) = s.getMem (BitVec.ofNat 64 (src + 8 * j))) ∧
  (∀ a, (∀ j < n - i, a ≠ BitVec.ofNat 64 (dst + 8 * j)) → t.getMem a = s.getMem a)

theorem ofNat_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x = y := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  · rintro rfl; rfl

/-- **Loop correctness**: the loop copies `n ≥ 1` doublewords from `src` to `dst`
in exactly `6 n` steps / cycles and halts at the `ecall` (`pc = 0x1018`). -/
theorem copy_spec (s : MachineState) (src dst n : Nat) (hpc : s.pc = 0x1000)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (hn : 0 < n)
    (hsa : src % 8 = 0) (hda : dst % 8 = 0)
    (hsb : src + 8 * n ≤ MEMORY_BYTES) (hdb : dst + 8 * n ≤ MEMORY_BYTES)
    (hdisj : src + 8 * n ≤ dst ∨ dst + 8 * n ≤ src) :
    ∃ t, Steps image s (n * 6) (n * 6) t ∧ t.pc = 0x1018 ∧
      (∀ j < n, t.getMem (BitVec.ofNat 64 (dst + 8 * j)) = s.getMem (BitVec.ofNat 64 (src + 8 * j))) ∧
      (∀ a, (∀ j < n, a ≠ BitVec.ofNat 64 (dst + 8 * j)) → t.getMem a = s.getMem a) := by
  have hM : MEMORY_BYTES = 2 ^ 24 := rfl
  have body_step : ∀ i t, Inv s src dst n (i + 1) t →
      ∃ u, Steps image t 6 6 u ∧ Inv s src dst n i u := by
    intro i t ⟨hi, t10, t11, t12, tpc, tmem, tframe⟩
    have hpc' : t.pc = 0x1000 := by simpa using tpc
    have hv : ∀ b, b % 8 = 0 → b + 8 * n ≤ MEMORY_BYTES →
        accessValid (BitVec.ofNat 64 (b + 8 * (n - (i + 1)))) 8 = true := by
      intro b hb hbb
      rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    obtain ⟨u, hst, u10, u11, u12, upc, umem⟩ :=
      body_spec t hpc' (t10 ▸ hv src hsa hsb) (t11 ▸ hv dst hda hdb)
    refine ⟨u, hst, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u10, t10, ofNat_add8]; congr 1; omega
    · rw [u11, t11, ofNat_add8]; congr 1; omega
    · rw [u12, t12]; apply BitVec.eq_of_toNat_eq; simp; omega
    · rw [upc, t12]
      by_cases h0 : i = 0
      · subst h0; simp
      · have : BitVec.ofNat 64 (i + 1) - 1 ≠ 0 := by
          intro h; have := congrArg BitVec.toNat h; simp at this; omega
        simp [h0]; exact this
    · intro j hj
      rw [umem, t11, t10]
      by_cases hjk : j = n - (i + 1)
      · subst hjk
        rw [if_pos rfl]
        apply tframe
        intro j' hj' heq
        rw [ofNat_inj (x := src + 8 * (n - (i + 1))) (y := dst + 8 * j') (by omega) (by omega)] at heq
        omega
      · rw [if_neg, tmem j (by omega)]
        rw [ofNat_inj (x := dst + 8 * j) (y := dst + 8 * (n - (i + 1))) (by omega) (by omega)]
        omega
    · intro a ha
      rw [umem, t11, if_neg (ha _ (by omega))]
      exact tframe a (fun j hj => ha j (by omega))
  have hinit : Inv s src dst n n s := by
    refine ⟨le_refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [h10]
    · simp [h11]
    · exact h12
    · simp [hpc]; omega
    · intro j hj; omega
    · intro a _; rfl
  obtain ⟨t, hst, _, _, _, _, tpc, tmem, tframe⟩ := Steps.iterate _ body_step n s hinit
  refine ⟨t, hst, by simpa using tpc, ?_, ?_⟩
  · intro j hj; exact tmem j (by omega)
  · intro a ha; exact tframe a (fun j hj => ha j (by omega))

/-- End-to-end: the loop followed by the HALT `ecall` (`t0 = 1`, `a0 = 0`) succeeds. -/
theorem copy_execute (s : MachineState) (src dst n : Nat) (hpc : s.pc = 0x1000)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (hn : 0 < n)
    (hsa : src % 8 = 0) (hda : dst % 8 = 0)
    (hsb : src + 8 * n ≤ MEMORY_BYTES) (hdb : dst + 8 * n ≤ MEMORY_BYTES)
    (hdisj : src + 8 * n ≤ dst ∨ dst + 8 * n ≤ src) (fuel : Nat) :
    ∃ t, (∀ j < n, t.getMem (BitVec.ofNat 64 (dst + 8 * j)) =
        s.getMem (BitVec.ofNat 64 (src + 8 * j))) ∧
      Riscv.execute (fuel + n * 6) image s =
        (fun e => e.charge (n * 6) 0 0) <$> Riscv.execute fuel image t ∧ t.pc = 0x1018 := by
  obtain ⟨t, hst, tpc, tmem, -⟩ := copy_spec s src dst n hpc h10 h11 h12 hn hsa hda hsb hdb hdisj
  exact ⟨t, tmem, hst.execute fuel, tpc⟩

end SigGolfCandidate.Rv.CopyLoop
