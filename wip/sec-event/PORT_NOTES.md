# Port notes: Lean v4.31.0 / VCVio cbd4144 -> Lean v4.33.1 / VCVio 25f26bf

Result: `lake build SphincsSecurity` succeeds (3911 jobs). No theorem statements were changed,
and `SphincsSecurity.lean` is byte-identical to the original, so its `#guard_msgs` axiom checks
still pass. No `sorry`, `native_decide` or new axioms. 180 modules were edited and one helper
module was added (`SphincsSecurity/Compat.lean`).

## Kinds of fixes

1. **`evalDist` is now measure-valued.** In the new VCVio, `evalDist` / `𝒟[·]` return a Mathlib
   `Measure` and need `MeasurableSpace`. The old `SPMF`-valued `evalDist` is now called `evalSPMF`,
   with notation `𝒮[·]`. Both are defined as `liftM mx : SPMF α`. So every `𝒟[` became `𝒮[`, and
   every bare `evalDist` became `evalSPMF`. The VCVio lemmas were renamed the same way
   (`evalDist_bind` -> `evalSPMF_bind`, and likewise `_map`, `_pure`, `_ext`, `_ext_iff`,
   `_bind_congr`, `_bind_congr'`, `_bind_congr_left`, `_bind_comm`, `_bind_bind_swap`,
   `_map_bijective_uniform_cross`, `_uniformSample_bind_update`, `_query`, `_eq`, `_def`,
   `mem_support_iff_of_evalDist_eq`, and so on). The project's own lemmas named `evalDist_*` keep
   their names. Statements mean exactly what they meant before.
2. **`QueryCache` is now `@[reducible]`.** As a result, `c₁ ≤ c₂` on `QueryCache HashSpec` (whose
   range is `BitVec`) elaborated to the pointwise order `Pi.hasLe` / `Option` instead of VCVio's
   cache-extension `PartialOrder`. This silently changed what statements meant. `Compat.lean` adds a
   high-priority `LE (QueryCache spec)` instance equal to the `PartialOrder` one, which restores the
   original meaning. `Scheme.lean` and `Proof/Base/Prelude.lean` import it.
3. **Side effect of the same change: `DecidableEq (QueryCache HashSpec)` instance search now times
   out.** It chases `Fintype (List UInt8)` and never finishes. Where `simp` hit this, a local
   `haveI : DecidableEq (QueryCache HashSpec) := Classical.decEq _` was added
   (`Seeded/HashTrace`, `Reference/BoundaryMessageCost`).
4. **`autoImplicit`.** The original lakefile left `autoImplicit` at its default (on); the port
   lakefile turns it off. Every module that relied on auto-bound names (`α`, `alpha`, `m`, `count`,
   and one unused `variable ... CertificateStopRule`) got `set_option autoImplicit true`, which is
   the original behaviour.
5. **Mathlib renames.** `mul_le_mul_left'` became `mul_le_mul_right`. The root-level
   `card_bitVec` (from VCVio `ToMathlib`) became `Fintype.card_bitVec`.
6. **`simp [bytesLE_length]` no longer fires.** It fails when the argument's type is
   `BitVec publicParameterBits` rather than `BitVec (8*16)`. Fixed by stating the lengths
   explicitly: `(bytesLE_length 16 _).trans (bytesLE_length 16 _).symm`, `bytesLE_length 16 p`,
   `digestBytes_length`.
7. **Kernel timeouts or deep recursion.** The elaborator accepts these unifications but the kernel
   then unfolds too much.
   - Card computations (`rw [...card_fun..., ← pow_mul, ← pow_add]; rfl`): the `rw` was replaced by
     `simp only [...]` (`FewTimeProbability`, `FewTimeUniform`).
   - An `apply` that needed a `let` / definition to be unfolded: `simp only [lets, def]` and
     `unfold otsSign` were added first (`FrontierSignerErasure`).
   - `rw [evalSPMF_map]` across a Functor-instance mismatch: replaced by `simp only [evalSPMF_map]`
     (`ReferenceFamilyGame`).
8. **The Functor instance on `OracleComp` / `FreeM` is now separate** (`FreeM.instFunctor`).
   - `f <$> x` is no longer definitionally equal to `x >>= pure ∘ f` for `change`, so
     `rw [bind_pure_comp] at h` was added (`RetainedResidualCoverageStep`).
   - `convert` now leaves an extra instance goal, so `rfl` became `all_goals rfl`
     (`AlgorithmErasure`).
9. **Small tactic changes.**
   - `Option.some.injEq` no longer fires in `simp only`: `injection h with h` was added before
     `subst` (`Completeness/Recovery`).
   - `if_pos h` / `if_neg h` don't rewrite in `simpa only`: replaced by `[h, if_true]` /
     `[h, if_false]` (`FewTimeLoop`).
   - `synthInstance.maxSize 512` was needed for a large product `Fintype`
     (`CanonicalCoordinateSampling`).
