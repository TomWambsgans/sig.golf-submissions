import SigGolfCandidate.Verify.ChainRuns

/-! Kernel check of all chain blocks of layer 2. -/

namespace SigGolfCandidate.Verify

set_option maxRecDepth 100000 in
theorem chainCheck_2 : ((List.range 42).all fun i => chainCheck 2 i) = true := by decide +kernel

end SigGolfCandidate.Verify
