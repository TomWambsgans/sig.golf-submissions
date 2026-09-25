import SigGolfCandidate.SphincsMaskedSignPrefix

/-! A certified HASH prefix charges its calls even when the rest of the
interpreter run later rejects or exhausts observation fuel. -/

namespace SigGolfCandidate.SphincsSignCallFloor
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem trace_calls_le_execute {hash : Hash} {image : Image}
    {first last : MachineState} {steps cycles calls blocks : Nat}
    (pre : Trace hash image first steps cycles calls blocks last)
    (fuel : Nat) (enough : steps ≤ fuel) :
    calls ≤ (evalWithAnswerFn hash (execute fuel image first)).hashCalls := by
  induction pre generalizing fuel with
  | refl state =>
      omega
  | ordinary state next final instruction steps cycles calls blocks hf hs tail ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have htail : steps ≤ fuel := by omega
          have hne : instruction ≠ .base .ECALL := by
            intro h
            simp [h, ordinaryStep] at hs
          cases instruction with
          | base instruction =>
              cases instruction <;> simp_all [execute, Execution.charge]
          | word op rd rs1 rs2 =>
              simpa [execute, hf, hs, Execution.charge] using ih fuel htail
          | sraiw rd rs shift =>
              simpa [execute, hf, hs, Execution.charge] using ih fuel htail
  | hash state final steps cycles calls blocks hf hs hv tail ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have htail : steps ≤ fuel := by omega
          have answer : evalWithAnswerFn hash
              (liftM (HashSpec.query (hashInput state))) = hash (hashInput state) := by
            simp [evalWithAnswerFn]
          have hresult := ih fuel htail
          simp [execute, hf, hs, hv, answer, Execution.charge]
          omega

/-- Every signer call starts with a valid HASH instruction, regardless of
the supplied public cache or whether the call later rejects. -/
theorem sign_runWith_one_call (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    1 ≤ (SphincsSubmission.submission.runWith hash .sign
      (secretKey, cache, message)).hashCalls := by
  have pre := SphincsMaskedSignPrefix.loaded_firstHash_trace
    hash secretKey cache message
  have hfloor := trace_calls_le_execute pre CYCLE_LIMIT (by
    norm_num [CYCLE_LIMIT])
  have himage : SphincsSubmission.submission.image .sign =
      SphincsMaskedImages.sign := rfl
  simpa only [Submission.runWith, Submission.run,
    SphincsMaskedSignPrefix.entry_loaded,
    himage,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    RunResult.hashCalls] using hfloor

end SigGolfCandidate.SphincsSignCallFloor

/-- info: 'SigGolfCandidate.SphincsSignCallFloor.trace_calls_le_execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSignCallFloor.trace_calls_le_execute

/-- info: 'SigGolfCandidate.SphincsSignCallFloor.sign_runWith_one_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSignCallFloor.sign_runWith_one_call
