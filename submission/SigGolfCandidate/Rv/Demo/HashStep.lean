import SigGolfCandidate.Rv

/-!
# Demo 3: build a 64-byte buffer, then HASH

```
addi x6, x0, 0x60                 ; buffer (constant address)
addi x7, x10, i ; sd x7, 8i(x6)   ; for i = 0..7: buf[i] := a0 + i
addi a0, x6, 0 ; addi a1, x0, 64 ; addi a2, x0, 0x100 ; addi t0, x0, 0
ecall                             ; HASH(buf, 64 bytes) -> 0x100
```
`hash_execute` derives: `execute` = one oracle query of the expected `hashInput`
(the little-endian concatenation of the 8 stored doublewords), followed by `writeHash`.
-/

namespace SigGolfCandidate.Rv.HashStep
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp

def code : List (BitVec 32) :=
  [0x06000313#32, 0x00050393#32, 0x00733023#32, 0x00150393#32, 0x00733423#32, 0x00250393#32,
  0x00733823#32, 0x00350393#32, 0x00733c23#32, 0x00450393#32, 0x02733023#32, 0x00550393#32,
  0x02733423#32, 0x00650393#32, 0x02733823#32, 0x00750393#32, 0x02733c23#32, 0x00030513#32,
  0x04000593#32, 0x10000613#32, 0x00000293#32, 0x00000073#32]

def image : Image := ⟨code, []⟩

theorem codeAt : CodeAt image 0x1000 code :=
  CodeAt.of_append (pre := []) (post := []) (by simp [image]) _ (by decide) (by decide)

sym_block run := symRun {} code 0x1000 100

example : run.res.stop = .ecall ∧ run.res.steps = 21 ∧ run.res.cycles = 21 ∧ run.res.st.obl = [] := by
  decide

/-- The eight doublewords of the buffer. -/
def bufWords (s : MachineState) : List Word := (List.range 8).map fun i => s.getReg .x10 + BitVec.ofNat 64 i

/-- The HASH input of the state reached at the `ecall`. -/
theorem hashInput_final (s : MachineState) :
    hashInput (run.res.toState s) = queryOfWords 0 (bufWords s) := by
  rw [run.res.hashInput_toState s (cfg := {}) (k := ⟨none, 0x60⟩) (n := 0)
    (by simp only [run.res, rv_simp]) (by simp only [run.res, rv_simp]) (by decide)
    (by simp only [rv_simp]; decide) (by sym_eval) (by simp only [rv_simp])]
  simp only [List.map, rv_simp, bufWords, List.range, List.range.loop]

theorem hashArgs_final (s : MachineState) : hashArgumentsValid (run.res.toState s) = true := by
  simp only [hashArgumentsValid, run.res, rv_simp]; decide

/-- **HASH step**: 21 ordinary steps, then one oracle query of `queryOfWords 0 (bufWords s)`,
whose answer is written by `writeHash`. -/
theorem hash_execute (s : MachineState) (hpc : s.pc = 0x1000) (fuel : Nat) :
    Riscv.execute (fuel + 1 + 21) image s =
      (fun e => e.charge 21 0 0) <$> (do
        let a ← HashSpec.query (queryOfWords 0 (bufWords s))
        (fun r => r.charge 8 1 1) <$> Riscv.execute fuel image (writeHash (run.res.toState s) a)) := by
  have hobl : run.res.obligs s := by simp only [run.res, rv_simp]
  have hsteps := symRun_sound run codeAt s hpc hobl
  rw [show (21 : Nat) = run.res.steps by rfl, hsteps.execute (fuel + 1)]
  rw [execute_hash fuel (symRun_ecall run codeAt s hobl rfl)
    (by simp only [run.res, rv_simp]) (hashArgs_final s), hashInput_final]
  rfl

/-- Fixed-oracle version. -/
theorem hash_evalWith (hash : Hash) (s : MachineState) (hpc : s.pc = 0x1000) (fuel : Nat) :
    evalWithAnswerFn hash (Riscv.execute (fuel + 1 + 21) image s) =
      ((evalWithAnswerFn hash (Riscv.execute fuel image
        (writeHash (run.res.toState s) (hash (queryOfWords 0 (bufWords s)))))).charge 8 1 1).charge
          21 0 0 := by
  have hobl : run.res.obligs s := by simp only [run.res, rv_simp]
  have hsteps := symRun_sound run codeAt s hpc hobl
  rw [show (21 : Nat) = run.res.steps by rfl, hsteps.evalWith hash (fuel + 1),
    evalWith_hash hash fuel (symRun_ecall run codeAt s hobl rfl)
      (by simp only [run.res, rv_simp]) (hashArgs_final s), hashInput_final]
  rfl

end SigGolfCandidate.Rv.HashStep
