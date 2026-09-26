import SigGolfCandidate.Verify.ChainRuns

/-! Kernel check of all chain blocks of layer 4. -/

namespace SigGolfCandidate.Verify

set_option maxRecDepth 100000 in
theorem chainCheck_4 : ((List.range 42).all fun i => chainCheck 4 i) = true := by decide +kernel

end SigGolfCandidate.Verify
