import SigGolfCandidate.SphincsSecurity.Proof.Seeded.Presampling
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.FreshTable

/-! Pre-sample finitely many distinct fresh lazy-RO answers before an adaptive
computation. This is the sampling half of the altered-cache MAC coupling. -/

namespace SigGolfCandidate.SphincsCacheMacFinitePresampling
open OracleComp OracleSpec SphincsSecurity SphincsSecurity.Seeded

theorem presampleFin {α : Type} {n : Nat}
    (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec)
    (inputs : Fin n → HashInput)
    (hinj : Function.Injective inputs)
    (hfresh : ∀ i, cache (inputs i) = none) :
    evalSPMF ((simulateQ romImpl computation).run' cache) =
    evalSPMF (do
      let outputs ← Concrete.sequenceFin fun _ : Fin n =>
        ($ᵗ HashOutput : ProbComp HashOutput)
      (simulateQ romImpl computation).run'
        (cacheFin cache inputs outputs)) := by
  induction n generalizing cache with
  | zero =>
      simp [Concrete.sequenceFin, cacheFin]
  | succ n ih =>
      rw [evalSPMF_presample_fresh computation cache (inputs 0) (hfresh 0)]
      simp only [Concrete.sequenceFin, cacheFin, bind_assoc]
      apply evalSPMF_bind_congr'
      intro head
      have hfreshTail : ∀ i : Fin n,
          (cache.cacheQuery (inputs 0) head) (inputs i.succ) = none := by
        intro i
        rw [QueryCache.cacheQuery_of_ne]
        · exact hfresh i.succ
        · intro heq
          exact Fin.succ_ne_zero i (hinj heq)
      exact ih (cache.cacheQuery (inputs 0) head)
        (fun i => inputs i.succ)
        (fun i j heq => Fin.succ_injective _ (hinj heq)) hfreshTail

end SigGolfCandidate.SphincsCacheMacFinitePresampling

/-- info: 'SigGolfCandidate.SphincsCacheMacFinitePresampling.presampleFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacFinitePresampling.presampleFin
