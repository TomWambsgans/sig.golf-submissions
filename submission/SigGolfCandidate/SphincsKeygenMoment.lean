import SigGolfCandidate.SphincsKeygenCost
import VCVio.EvalDist.Expectation

namespace SigGolfCandidate.SphincsKeygenMoment
open SigGolf OracleComp OracleSpec OracleComp.EvalDist

set_option maxRecDepth 4096

theorem fixed_hash_of_support {α : Type} (program : OracleComp HashSpec α)
    (value : α) (mem : value ∈ support (withRandomOracle program)) :
    ∃ hash : Hash, evalWithAnswerFn hash program = value := by
  rw [withRandomOracle, StateT.run'_eq] at mem
  obtain ⟨result, hresult, eq⟩ := mem_support_map_peel Prod.fst _ mem
  obtain ⟨hash, _, heval⟩ :=
    (exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support program ∅ value).mpr
      ⟨result.2, by simpa only [eq] using hresult⟩
  exact ⟨hash, heval⟩

theorem support_cost (secretKey : SecretKey) (result : HonestResult)
    (mem : result ∈ support (SphincsSubmission.submission.honestWorkload secretKey)) :
    result.costs .keygen = 1007616 := by
  unfold Submission.honestWorkload at mem
  rw [mem_support_bind_iff] at mem
  obtain ⟨message, _, hresult⟩ := mem
  obtain ⟨hash, heval⟩ := fixed_hash_of_support
    (SphincsSubmission.submission.honest secretKey message) result hresult
  rw [← heval]
  exact SphincsKeygenCost.honest_cost hash secretKey message

theorem compression_bound (secretKey : SecretKey) :
    OracleComp.EvalDist.expectedValue
      (SphincsSubmission.submission.honestWorkload secretKey)
      (fun result => ENNReal.ofReal (Real.rpow 2
        ((result.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ)))) ≤ 2 := by
  apply expectedValue_le_of_support
  intro result mem
  rw [support_cost secretKey result mem]
  exact SphincsKeygenCost.exponential_cost_le_two

/-- info: 'SigGolfCandidate.SphincsKeygenMoment.support_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_cost

/-- info: 'SigGolfCandidate.SphincsKeygenMoment.compression_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compression_bound

end SigGolfCandidate.SphincsKeygenMoment
