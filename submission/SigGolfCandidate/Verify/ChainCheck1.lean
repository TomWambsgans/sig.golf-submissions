import SigGolfCandidate.Verify.ChainRuns

/-! Kernel check of all chain blocks of layer 1. -/

namespace SigGolfCandidate.Verify

set_option maxRecDepth 100000 in
theorem chainCheck_1 : ((List.range 42).all fun i => chainCheck 1 i) = true := by decide +kernel

end SigGolfCandidate.Verify
