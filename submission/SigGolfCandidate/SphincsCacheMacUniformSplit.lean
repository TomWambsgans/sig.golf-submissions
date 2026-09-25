import SigGolfCandidate.SphincsCacheBlindMacGuess
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.FreshTable
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-! A publicly revealed genuine MAC value leaves every distinct tag-15 oracle
answer uniformly random. The finite table is for the finitely many targets
an execution can touch; index zero is the genuine ciphertext. -/

namespace SigGolfCandidate.SphincsCacheMacUniformSplit
open OracleComp OracleComp.DeferredSampling SphincsSecurity SphincsSecurity.Seeded
open SigGolfCandidate.SphincsCacheBlindMacGuess

theorem uniform_tail_marginal (n : Nat) (i : Fin n) (guess : Digest) :
    Pr[fun table : Fin n → Digest => table i = guess |
      ($ᵗ (Fin n → Digest) : ProbComp _)] =
    (Fintype.card Digest : ENNReal)⁻¹ := by
  have h := OracleComp.evalSPMF_uniformSample_bind_update_map
    (D := Fin n) (R := Digest) i (fun table : Fin n → Digest => table i)
  have hsimple :
      evalSPMF (do
        let u ← ($ᵗ Digest : ProbComp Digest)
        let g ← ($ᵗ (Fin n → Digest) : ProbComp _)
        pure ((Function.update g i u) i)) =
      evalSPMF ($ᵗ Digest : ProbComp Digest) := by
    simp only [Function.update_self]
    calc
      _ = evalSPMF (($ᵗ Digest : ProbComp Digest) >>= fun u => pure u) := by
        apply evalSPMF_bind_congr_left
        intro u
        simpa only [bind_pure_comp] using
          evalSPMF_bind_const_neverFails
            ($ᵗ (Fin n → Digest) : ProbComp _)
            (probFailure_uniformSample (α := Fin n → Digest)) (pure u)
      _ = _ := by simp
  have hdist :
      evalSPMF ((fun table : Fin n → Digest => table i) <$>
        ($ᵗ (Fin n → Digest) : ProbComp _)) =
      evalSPMF ($ᵗ Digest : ProbComp Digest) := by
    calc
      _ = evalSPMF (do
          let g ← ($ᵗ (Fin n → Digest) : ProbComp _)
          pure (g i)) := by simp only [evalSPMF_map, bind_pure_comp]
      _ = _ := h.symm.trans hsimple
  rw [show (fun table : Fin n → Digest => table i = guess) =
    (fun digest => digest = guess) ∘ (fun table => table i) from rfl,
    ← probEvent_map]
  rw [probEvent_eq_eq_probOutput, probOutput_def, hdist]
  rw [← probOutput_def]
  exact probOutput_uniformSample Digest guess

theorem uniform_tail_marginal_pmf (n : Nat) (i : Fin n) (guess : Digest) :
    Pr[fun table : Fin n → Digest => table i = guess |
      PMF.uniformOfFintype (Fin n → Digest)] =
    (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [probEvent_def, evalSPMF_uniformSample,
    SPMF.probEvent_liftM] using uniform_tail_marginal n i guess

/-- The authentic public tag can be revealed before an adaptive all-failure
plan is chosen. Each distinct altered ciphertext still has a uniform tag. -/
theorem public_genuine_tag_blind_bound {Env : Type} (n : Nat)
    (environment : PMF Env)
    (plan : Env → Digest → List (Fin n × Digest))
    (q : Nat)
    (hbudget : ∀ env tag, (plan env tag).length ≤ q) :
    Pr[fun result => Hit (plan result.1.1 result.1.2) result.2 |
      (do
        let env ← (liftM (do
          let e ← environment
          let tag ← PMF.uniformOfFintype Digest
          pure (e, tag)) : SPMF (Env × Digest))
        let table ← (liftM (PMF.uniformOfFintype (Fin n → Digest)) :
          SPMF (Fin n → Digest))
        pure (env, table))] ≤
      q * (Fintype.card Digest : ENNReal)⁻¹ := by
  exact adaptive_blind_bound
    (do
      let e ← environment
      let tag ← PMF.uniformOfFintype Digest
      pure (e, tag))
    (PMF.uniformOfFintype (Fin n → Digest))
    (fun pair => plan pair.1 pair.2)
    (fun i guess => (uniform_tail_marginal_pmf n i guess).le)
    q (fun pair => hbudget pair.1 pair.2)

theorem uniform_table_head_tail (n : Nat) :
    evalSPMF (do
      let table ← ($ᵗ (Fin (n + 1) → Digest) : ProbComp _)
      pure (table 0, fun i : Fin n => table i.succ)) =
    evalSPMF (do
      let head ← ($ᵗ Digest : ProbComp Digest)
      let tail ← ($ᵗ (Fin n → Digest) : ProbComp _)
      pure (head, tail)) := by
  have hequiv := evalSPMF_map_bijective_uniform_cross
    (α := Fin (n + 1) → Digest) (β := Digest × (Fin n → Digest))
    (finHeadTailEquiv Digest n).symm (finHeadTailEquiv Digest n).symm.bijective
  calc
    _ = evalSPMF ((finHeadTailEquiv Digest n).symm <$>
        ($ᵗ (Fin (n + 1) → Digest) : ProbComp _)) := by
          simp [finHeadTailEquiv, bind_pure_comp]
    _ = evalSPMF ($ᵗ (Digest × (Fin n → Digest))) := hequiv
    _ = _ := evalSPMF_independent_uniform_pair.symm

end SigGolfCandidate.SphincsCacheMacUniformSplit

/-- info: 'SigGolfCandidate.SphincsCacheMacUniformSplit.uniform_table_head_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacUniformSplit.uniform_table_head_tail

/-- info: 'SigGolfCandidate.SphincsCacheMacUniformSplit.public_genuine_tag_blind_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacUniformSplit.public_genuine_tag_blind_bound
