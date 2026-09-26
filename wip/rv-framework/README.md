# `SigGolfCandidate.Rv` — verified symbolic execution of RV64IM bytecode (sig.golf semantics)

This library proves facts about **concrete RV64IM bytecode** executed by the organizer
interpreter `SigGolf.Riscv.execute` (`/root/siggolf/dev/SigGolf/Riscv.lean`) on RiscvZkvm's
`MachineState`. You get:

1. **Generic execution lemmas** (`Steps.lean`): a relation `Steps image s k c t` for `k` ordinary
   (non-`ECALL`) steps costing `c` cycles, its composition law with `execute`, the HASH / HALT
   `ECALL` laws, fixed-oracle (`evalWithAnswerFn`) versions, and `Submission.run`/`runWith` in
   terms of `execute` from `initialState`.
2. **A verified symbolic executor** (`Expr.lean`, `Micro.lean`, `Exec.lean`, `Sound.lean`) that is
   run *inside the kernel* (proof by reflection): one kernel check certifies a whole straight-line
   block, producing its exact final state (registers, pc, memory as a write list, frame), its
   exact cycle count and a list of side conditions.
3. **Ergonomics** (`Tactic.lean`, `Api.lean`, `Hash.lean`): the `sym_block` command and `sym_eval` /
   `kernel_rfl` tactics, the `rv_simp` simp set (readable concrete forms), `rv_obligs`,
   `BlockSpec`, a loop lemma, a segment-layout table for 20k-instruction images, reflective
   memory reads, and the HASH-input-of-a-buffer lemma.

Trust: everything reduces to the organizer definitions. Only `propext`, `Classical.choice`,
`Quot.sound` are used (checked by `Demo/Axioms.lean` with `#guard_msgs`). No `sorry`,
`native_decide`, `bv_decide`, `Lean.ofReduceBool`. The tactics *compute* the result with compiled
code (untrusted) and then have **the kernel** check `symRun … = some <literal>` by `Eq.refl`
(exactly like `decide +kernel`); a wrong result is rejected by the kernel.

Project: `/root/siggolf/work/rv` (Lean v4.33.1, `lake build` builds library + demos + scale
test). Everything lives in `SigGolfCandidate/Rv/`; `import SigGolfCandidate.Rv` imports the API.

---------------------------------------------------------------------------------------------

## 1. Execution lemmas (`Steps.lean`)

```lean
inductive Steps (image : Image) : MachineState → Nat → Nat → MachineState → Prop
  | refl s : Steps image s 0 0 s
  | step (hf : fetch image s = some i) (hs : ordinaryStep s i = some t)
         (tail : Steps image t k c u) : Steps image s (k+1) (instructionCycles i + c) u

Steps.trans   : Steps image s k₁ c₁ t → Steps image t k₂ c₂ u → Steps image s (k₁+k₂) (c₁+c₂) u
Steps.of_eq   : Steps image s k c t → k = k' → c = c' → Steps image s k' c' t
Steps.execute : Steps image s k c t →
  execute (fuel + k) image s = (fun r => r.charge c 0 0) <$> execute fuel image t
Steps.execute_le : Steps image s k c t → k ≤ fuel →
  execute fuel image s = (fun r => r.charge c 0 0) <$> execute (fuel - k) image t
Steps.evalWith : Steps image s k c t → ∀ hash fuel,
  evalWithAnswerFn hash (execute (fuel + k) image s) =
    (evalWithAnswerFn hash (execute fuel image t)).charge c 0 0

execute_ordinary (hf : fetch image s = some i) (hs : ordinaryStep s i = some t) :
  execute (fuel+1) image s = (fun r => r.charge (instructionCycles i) 0 0) <$> execute fuel image t
execute_hash (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) :
  execute (fuel+1) image s = do
    let a ← HashSpec.query (hashInput s)
    (fun r => r.charge (8 * (hashInput s).blocks) 1 (hashInput s).blocks) <$>
      execute fuel image (writeHash s a)
execute_halt (hf : …ECALL) (ht0 : s.getReg .x5 = 1) :
  execute (fuel+1) image s = pure ⟨if s.getReg .x10 = 0 then .success else .failure, s, 1, 0, 0⟩
execute_ecall_fail, execute_fetch_none                    -- the failure branches
evalWith_hash hash fuel hf ht0 hv :
  evalWithAnswerFn hash (execute (fuel+1) image s) =
    (evalWithAnswerFn hash (execute fuel image (writeHash s (hash (hashInput s))))).charge
      (8 * (hashInput s).blocks) 1 (hashInput s).blocks
evalWith_halt                                               -- fixed-oracle HALT
Execution.charge_charge, charge_zero, charge_cycles, …      -- @[simp]

toRunResult submission phase (e : Execution) : RunResult _   -- what `run` builds from `e`
run_eq     (hinit : initialState submission phase input = some s) :
  submission.run phase input = toRunResult submission phase <$> execute CYCLE_LIMIT (submission.image phase) s
runWith_eq (hinit : …) : submission.runWith hash phase input =
  toRunResult submission phase (evalWithAnswerFn hash (execute CYCLE_LIMIT (submission.image phase) s))
initialState_pc (hinit : …) : s.pc = 0x1000
```

Typical end-to-end shape: `runWith_eq` → `Steps.execute_le`/`Steps.evalWith` for each block
(`CYCLE_LIMIT = 2^32` is split as `fuel + k`) → `evalWith_hash` at every HASH →
`evalWith_halt` at the end → `simp [toRunResult]`.

## 2. The symbolic executor

### Values (`Expr.lean`)

```lean
inductive E | c (v : Word) | reg (r : Reg) | ld (a : E) | un (op : UnOp) (a : E)
            | bin (op : BinOp) (a b : E) | ite (op : CmpOp) (x y a b : E)
E.eval (s : MachineState) : E → Word
```
Atoms are relative to the **initial state `s`** of the block: `E.reg r` = `s.getReg r`,
`E.ld a` = `s.getMem (a.eval s)` (an initial-memory word). `BinOp` covers all RV64IM ALU ops
(`add sub and or xor sll srl sra slt sltu mul mulh mulhsu mulhu div divu rem remu`), the
organizer's 32-bit word ops `w (op : WordOp)` (= `(wordResult op (x.truncate 32) (y.truncate 32)).signExtend 64`),
and sub-doubleword store merges `st k bo`; `UnOp.ld k bo` is sub-doubleword load extraction;
`CmpOp` = `eq ne lt ge ltu geu` (branch conditions, `SLT`-style results use `BinOp.slt/sltu`).
Smart constructors fold constants and normalize `a + const`, so addresses have the form
`base + off`.

Addresses: `structure Addr where base : Option E; off : Word` (`none` = constant `off`),
`Addr.eval s a = base.eval s + off`. `norm : E → Addr` splits `b + c`.

### Memory and aliasing

The symbolic memory is `SymMem := List (Addr × E)` (doubleword writes, newest first; a store
removes older writes with the *same* key). Meaning: `memEval s mem a` (`if a = k.eval s then v.eval s else …`,
ending in `s.getMem a`). A read at key `k` walks the write list with `Addr.alias`:

* `same` (same base (syntactically, `E.beq`) and same offset, or two equal constants) → the written value;
* `diff` (same base and different offsets — `b + o₁ ≠ b + o₂` since `+` is injective — or two
  different constants) → skip;
* `unknown` (different bases, or constant vs. base) → **fail** (`none`), unless
  `Config.noAlias := true`, in which case the side condition `Oblig.ne k k'` (`k.eval s ≠ k'.eval s`)
  is emitted and the write is skipped.

Reaching the end yields the initial-memory atom `E.ld k.toE`.

LD/SD use the exact address as key (organizer `getMem addr`). LW/LWU/LH/LHU/LB/LBU/SW/SH/SB
access the containing doubleword `alignToDword addr` at `byteOffset addr`: for a constant address
both are computed; for `base + off` the executor emits `Oblig.align8 base`
(`(base.eval s).toNat % 8 = 0`) and uses key `base + alignToDword off`, byte offset
`byteOffset off`.

### Side conditions

```lean
inductive Oblig | valid (a : Addr) (w : Nat) | align8 (b : E) | ne (a b : Addr)
Oblig.holds s : valid a w ↦ accessValid (a.eval s) w = true
                align8 b  ↦ (b.eval s).toNat % 8 = 0
                ne a b    ↦ a.eval s ≠ b.eval s
Oblig.all s : List Oblig → Prop        -- right-nested conjunction
Result.obligs r s := Oblig.all s r.st.obl
```
Memory validity (`memoryArgumentsValid`/`accessValid`: bounds `< MEMORY_BYTES = 2^24` and
alignment) is **checked by computation for constant addresses** (the executor fails if it is
false) and **emitted as `Oblig.valid`** otherwise. `valid`/`align8` are deduplicated during
execution; `ne` conditions are not (use `Result.obligs_of_dedup` + `Oblig.dedup` if you want a
deduplicated list).

### Running

```lean
structure Config where noAlias : Bool := false
symRun (cfg : Config) (code : List (BitVec 32)) (pc : Word) (fuel : Nat) : Option Result
structure Result where
  st : SymState        -- regs : RegFile (x1..x31 as E), mem : SymMem, obl : List Oblig
  pc : E               -- final pc (E.ite … for a branch)
  stop : Stop          -- fuel | endOfCode | branch | jump | ecall
  steps cycles : Nat   -- exact number of ordinary steps and their cycle count
Result.toState r s : MachineState   -- the explicit final concrete state
```
`code` is a *segment* whose first word is at `pc`; fetch/decoding use the organizer's
`decodeInstruction` on the segment words only (no walk over the whole image). The block ends
**after** a branch (`BEQ…BGEU`: pc = `E.ite cond (c taken) (c fallthrough)`), `JAL` (constant
target) or `JALR` (`(rs + off) &&& ~~~1`); **before** an `ECALL` (`Stop.ecall`, so you apply the
HASH/HALT law); or when `fuel` / the segment is exhausted.

Supported instructions: everything `classify` maps (`Micro.lean`): ADD SUB SLL SRL SRA AND OR XOR
SLT SLTU, ADDI ANDI ORI XORI SLTI SLTIU SLLI SRLI SRAI, LUI AUIPC, LD LW LWU LH LHU LB LBU,
SD SW SH SB, BEQ BNE BLT BGE BLTU BGEU, JAL JALR, ADDIW SLLIW SRLIW SRAIW (organizer `sraiw`),
ADDW SUBW SLLW SRLW SRAW MULW DIVW DIVUW REMW REMUW (organizer `Instruction.word`), MUL MULH
MULHSU MULHU DIV DIVU REM REMU (4 cycles), FENCE (no-op). `EBREAK`/`CSRS`/undecodable words make
the executor fail. (`classify_sound : classify i = some m → ordinaryStep s i = m.exec s`.)

### Soundness (`Sound.lean`)

```lean
def CodeAt (image : Image) (pc : Word) (code : List (BitVec 32)) : Prop :=
  0x1000 ≤ pc.toNat ∧ pc.toNat % 4 = 0 ∧ pc.toNat + 4 * code.length < 2^64 ∧
  code <+: image.code.drop ((pc.toNat - 0x1000) / 4)

theorem symRun_sound (hrun : symRun cfg code pc fuel = some r) (hcode : CodeAt image pc code)
    (s : MachineState) (hpc : s.pc = pc) (hobl : r.obligs s) :
    Steps image s r.steps r.cycles (r.toState s)

theorem symRun_ecall (hrun) (hcode) (s) (hobl) (hstop : r.stop = .ecall) :
    fetch image (r.toState s) = some (.base .ECALL)
```
`r.toState s` = `{ s with regs := (r.st.regs.get ·).eval s (x0 kept), mem := memEval s r.st.mem, pc := r.pc.eval s }`,
with simp lemmas `Result.toState_getReg/_getMem/_pc/_code`. Frame properties:
```lean
Result.toState_getMem_frame r s a (h : ∀ p ∈ r.st.mem, a ≠ p.1.eval s) : (r.toState s).getMem a = s.getMem a
memEval_frame                                                  -- same, for any SymMem
Result.toState_getMem_of_read r s (h : readMem cfg k r.st.mem = some (e, os)) (hos : Oblig.all s os) :
  (r.toState s).getMem (k.eval s) = e.eval s                   -- reflective read of the final memory
Result.readWords_toState r s (h : readWordsSym cfg r.st.mem k n = some (es, os)) (hos) :
  (r.toState s).readWords (k.eval s) n = es.map (E.eval s)
```

## 3. Usage patterns

### Place code

* Small images: `CodeAt.of_append (h : image.code = pre ++ code ++ post) pc (hpc : pc.toNat = 0x1000 + 4*pre.length) (hrange)`.
* Large images: build the image from a layout table `L : Layout := [(0, seg0), (50, seg1), …]`,
  `image.code := layoutCode L`, prove `layoutOk 0 L = true` **once** (`by decide +kernel`),
  then per segment
  `codeAt_layout rfl layout_ok (i := k) (by kernel_rfl) (by decide) : CodeAt image (BitVec.ofNat 64 (0x1000 + 4*o)) segk`.
  Use the same pc term (`BitVec.ofNat 64 (0x1000 + 4 * o)`) in `symRun` so the types match.

### Run a block

```lean
sym_block blk := symRun { noAlias := true } seg (BitVec.ofNat 64 (0x1000 + 4 * 850)) 50
-- defines  blk.res : Result  (a literal)  and  theorem blk : symRun … = some blk.res  (kernel-checked)
example : blk.res.steps = 50 ∧ blk.res.stop = .fuel := by decide
```
Inside proofs, `sym_eval` closes `lhs = ?rhs` for any closed computable `lhs` with a `ToExpr`
type (e.g. `readMem …`, `readWordsSym …`, `Oblig.dedup …`), assigning `?rhs`; `kernel_rfl` closes
closed `a = b` by a kernel-only `Eq.refl`.

### Discharge side conditions

`have hobl : blk.res.obligs s := by rv_obligs [blk.res, hx10]` — unfolds with `rv_simp`,
rewrites with your hypotheses (e.g. `hx10 : s.getReg .x10 = BitVec.ofNat 64 p`), turns
`accessValid`, `≠`, `=` into `toNat` arithmetic and closes each conjunct with `omega`.
Manually: `simp only [blk.res, rv_simp]` shows the conjunction, e.g.
`accessValid (s.getReg .x10 + 8#64) 8 = true ∧ (s.getReg .x10).toNat % 8 = 0 ∧ …`.

### Read the result

```lean
obtain hsteps := symRun_sound blk codeAt s hpc hobl     -- Steps image s k c (blk.res.toState s)
simp only [blk.res, rv_simp]    -- (blk.res.toState s).getReg .x10  ~>  s.getReg .x10 + 48#64
```
`rv_simp` includes the `E.eval`/`BinOp.eval`/`RegFile.get`/`memEval` equations and a simproc
turning `x + 18446744073709551552#64` into `x - 64#64`. Memory: use
`Result.toState_getMem_of_read … (by sym_eval) (by rv_obligs […])` then `simp only [rv_simp] at h`,
or `simp only [rv_simp]` on `memEval` (an `if`-chain) and discharge the address disequalities.

### Compose

* sequential blocks: `Steps.trans`, or `Steps.execute` repeatedly (`execute (fuel + k)`);
  the next block's initial state is `r.toState s` whose registers are readable expressions in `s`;
* branches: the final pc is `if cond then taken else fall` after `rv_simp`; `split`/`by_cases`;
* `BlockSpec image entry k c P Q := ∀ s, s.pc = entry → P s → ∃ t, Steps image s k c t ∧ Q s t`,
  `BlockSpec.of_symRun`, `.execute`, `.evalWith`, `.mono`;
* loops: `Steps.iterate Inv (body : ∀ i s, Inv (i+1) s → ∃ t, Steps image s k c t ∧ Inv i t) :
  ∀ n s, Inv n s → ∃ t, Steps image s (n*k) (n*c) t ∧ Inv 0 t` (see `Demo/CopyLoop.lean`).

### HASH

After a block with `stop = .ecall`: `symRun_ecall` gives the `ECALL` fetch; `t0`/argument
validity come from `rv_simp` + `decide`; the input:
```lean
hashInput_eq_words t n (h11 : t.getReg .x11 = BitVec.ofNat 64 (64*(n+1))) (hn) (h10 : (t.getReg .x10).toNat % 8 = 0) :
  hashInput t = queryOfWords n (t.readWords (t.getReg .x10) (8*(n+1)))
queryOfWords n ws = ⟨n, BitVec.ofNat _ (wordsToNat ws)⟩     -- little-endian word concatenation
Result.hashInput_toState r s (h10 : (r.st.regs.get .x10).eval s = k.eval s) (h11 …) (hn) (hal)
  (h : readWordsSym cfg r.st.mem k (8*(n+1)) = some (es, os)) (hos : Oblig.all s os) :
  hashInput (r.toState s) = queryOfWords n (es.map (E.eval s))
```
See `Demo/HashStep.lean` (`hash_execute`, `hash_evalWith`).

## 4. Demos (all in `SigGolfCandidate/Rv/Demo/`, built by `lake build`)

* `Block40.lean` — 40-instruction block with LD/SD/LW/LWU/SW/LBU/SB at constant addresses
  (`0x20060…`) and relative to `x10`, shifts, SLT(U), ADDIW/SRAIW/ADDW, MUL. `spec` states the
  final pc, registers (`t.getReg .x15 = s.getMem (s.getReg .x10 + 8)`…), memory
  (`t.getMem 0x20060 = s.getMem (s.getReg .x10) + s.getMem (s.getReg .x10 + 8)`…) and a frame
  property, under `x10 = p`, `p % 8 = 0`, `p + 48 ≤ 0x20000` (uses `noAlias`, 13 side conditions).
* `CopyLoop.lean` — `copy_spec`: the 6-instruction loop copies `n ≥ 1` doublewords
  (`src`/`dst` aligned, in bounds, disjoint) in exactly `6n` steps / cycles and reaches the
  `ecall`; plus frame. Proven with `Steps.iterate` and the block lemma `body_spec`.
* `HashStep.lean` — builds a 64-byte buffer (8 SDs) and does HASH: `hash_execute` shows
  `execute (fuel+1+21) image s = charge 21 <$> (do let a ← query (queryOfWords 0 (bufWords s)); charge 8 1 1 <$> execute fuel image (writeHash … a))`.
* `Scale/` — 20,000-instruction synthetic straight-line image (`tools/gen_scale.py`: random
  ALU/W/shift/LUI/AUIPC/MUL and LD/SD/LW/SW/LBU/SB relative to `x2`, `x10` and constants), 400
  segments of 50, one `sym_block` + `spec<k> : Steps image s … (run<k>.res.toState s)` each.
* `Axioms.lean` — axiom audit.

## 5. Performance (this machine, shared with other jobs; numbers are noisy)

* 40-instruction demo block: kernel check ≈ 75 ms. 6-instruction loop body ≈ 20 ms. HASH demo block ≈ 30 ms.
* Scale test, 400 × 50 instructions: kernel check per segment median ≈ 110 ms (range 75–300 ms);
  per file of 50 segments ≈ 9 s wall (≈ 5.7 s kernel + 2.3 s import); peak RSS ≈ 3.85 GB
  per Lean process, of which ≈ 3.48 GB is the baseline of importing Mathlib/VCVio/SigGolf.
  All 20,000 instructions: ≈ 14 s wall with `lake build` running the 8 block files in parallel
  (≈ 75 s summed sequential, ≈ 45 s of it kernel). A clean build of the whole library, demos
  and scale test takes ≈ 51 s wall. The image/layout file itself (400 segment literals + one
  `layoutOk` check over 20k words by `decide +kernel`, ≈ 0.7 s) takes ≈ 9–13 s, 4.2 GB.
* Cost drivers: obligation deduplication (quadratic; `ne` conditions are therefore not
  deduplicated), long write lists with `noAlias` (one `ne` per unknown write per read), size
  of the symbolic values. Literals are built with sharing (`resultToExprShared`), so values with
  repeated sub-terms stay linear (a 45-fold self-doubling chain checks instantly).

## 6. Limitations / notes

* One block = straight-line code; branches/jumps end a block (compose by hand, or use
  `BlockSpec`). Loops need an invariant (`Steps.iterate`).
* Aliasing is syntactic: pointers with different base expressions (or pointer vs. constant) either
  fail (`noAlias := false`) or produce `ne` side conditions. No region/range reasoning inside the
  executor; the address arithmetic is only `base + const` normalization (no `x + y` reassociation
  beyond `(a + b) + c`, no multiplication-by-constant normal form).
* Sub-doubleword accesses through a non-constant base need `align8 base`.
* No algebraic simplification of values (e.g. `(a + b) - a` stays as is — prove with
  `BitVec` lemmas after `rv_simp`).
* The executor starts from the identity symbolic state; to use facts about the entry state,
  rewrite after `rv_simp` (e.g. `rw [hx10]`) — there are no free variables other than the initial
  registers and initial memory.
* `sym_block`/`sym_eval` need closed terms (no local hypotheses/variables in the executor call).
* Pretty-printing `blk.res` of a block with heavily shared values can be large (it is a DAG).
* `rv_obligs` is a thin `simp; omega` wrapper; obligations mentioning non-linear terms must be
  proven by hand.
