import SigGolfCandidate.Verify.ChainCheck0
import SigGolfCandidate.Verify.ChainCheck1
import SigGolfCandidate.Verify.ChainCheck2
import SigGolfCandidate.Verify.ChainCheck3
import SigGolfCandidate.Verify.ChainCheck4
import SigGolfCandidate.Verify.ChainCheck5
import SigGolfCandidate.Verify.ChainCheck6

namespace SigGolfCandidate.Verify

theorem chainCheck_at (lay i : Nat) (hlay : lay < 7) (hi : i < 42) : chainCheck lay i = true := by
  have key : ∀ l, ((List.range 42).all fun i => chainCheck l i) = true → chainCheck l i = true := by
    intro l h
    simp only [List.all_eq_true, List.mem_range] at h
    exact h i hi
  interval_cases lay
  · exact key 0 chainCheck_0
  · exact key 1 chainCheck_1
  · exact key 2 chainCheck_2
  · exact key 3 chainCheck_3
  · exact key 4 chainCheck_4
  · exact key 5 chainCheck_5
  · exact key 6 chainCheck_6

end SigGolfCandidate.Verify
