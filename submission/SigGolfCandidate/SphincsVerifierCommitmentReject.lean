import SigGolfCandidate.SphincsVerifierCommitmentCheck
import SigGolfCandidate.SphincsMaskedKeygenPrefix
import SigGolfCandidate.SphincsVerifierXmssPathComplete

/-! The verifier's two public-key commitment mismatches reach the shared rejection block. -/

namespace SigGolfCandidate.SphincsVerifierCommitmentReject
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix
open SigGolfCandidate.SphincsVerifierCommitmentCheck

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def witnessInner (witness : Bytes SphincsWire.signatureBytes) :
    SphincsSecurity.PublicKey :=
  ⟨witness.extractLsb' 0 SphincsSecurity.digestBits,
    witness.extractLsb' SphincsSecurity.digestBits SphincsSecurity.digestBits⟩

theorem witnessInner_encoded (witness : Bytes SphincsWire.signatureBytes) :
    SphincsVerifierLoader.EncodedWitness witness (witnessInner witness) := by
  constructor
  · intro i hi
    change witness.extractLsb' (8 * i) 8 =
      (witness.extractLsb' 0 SphincsSecurity.digestBits).extractLsb' (8 * i) 8
    rw [BitVec.extractLsb'_extractLsb'_of_le (by
      dsimp [SphincsSecurity.digestBits]
      omega)]
  · intro i hi
    change witness.extractLsb' (8 * (20 + i)) 8 =
      (witness.extractLsb' SphincsSecurity.digestBits SphincsSecurity.digestBits).extractLsb' (8 * i) 8
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hinner : 8 * i + j < SphincsSecurity.digestBits := by
      dsimp [SphincsSecurity.digestBits]
      omega
    simp only [BitVec.getLsbD_extractLsb', decide_eq_true hj,
      decide_eq_true hinner, Bool.true_and]
    congr 1
    dsimp [SphincsSecurity.digestBits]
    omega

def lowSchedule : List (Word × Instr) := [
  (0x1134, .LUI .x6 0x42),
  (0x1138, .ADDI .x6 .x6 0),
  (0x113c, .ADDI .x7 .x0 64),
  (0x1140, .LD .x10 .x6 0),
  (0x1144, .LD .x11 .x7 0),
  (0x1148, .BEQ .x10 .x11 8),
  (0x114c, .JAL .x0 (-328))]

def highSchedule : List (Word × Instr) := [
  (0x1134, .LUI .x6 0x42),
  (0x1138, .ADDI .x6 .x6 0),
  (0x113c, .ADDI .x7 .x0 64),
  (0x1140, .LD .x10 .x6 0),
  (0x1144, .LD .x11 .x7 0),
  (0x1148, .BEQ .x10 .x11 8),
  (0x1150, .LD .x10 .x6 8),
  (0x1154, .LD .x11 .x7 8),
  (0x1158, .BEQ .x10 .x11 8),
  (0x115c, .JAL .x0 (-344))]

def failureSchedule : List (Word × Instr) := [
  (0x1004, .ADDI .x5 .x0 0),
  (0x1008, .ADDI .x10 .x0 0)]

theorem lowSchedule_code : ∀ entry ∈ lowSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by decide

theorem highSchedule_code : ∀ entry ∈ highSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by decide

theorem failureSchedule_code : ∀ entry ∈ failureSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by decide

theorem low_checked (s : MachineState) (pc : s.pc = 0x1134)
    (different : s.getMem 0x42000 ≠ s.getMem 0x40) :
    Checked lowSchedule s := by
  have d : s.getMem (270336#64) ≠ s.getMem (64#64) := by
    have ha : (270336#64 : Word) = (0x42000 : Word) := by decide
    have hb : (64#64 : Word) = (0x40 : Word) := by decide
    simpa only [ha, hb] using different
  simp [Checked, lowSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, signExtend13, signExtend21,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc, d]

theorem high_checked (s : MachineState) (pc : s.pc = 0x1134)
    (low : s.getMem 0x42000 = s.getMem 0x40)
    (different : s.getMem 0x42008 ≠ s.getMem 0x48) :
    Checked highSchedule s := by
  have e : s.getMem (270336#64) = s.getMem (64#64) := by
    have ha : (270336#64 : Word) = (0x42000 : Word) := by decide
    have hb : (64#64 : Word) = (0x40 : Word) := by decide
    simpa only [ha, hb] using low
  have d : s.getMem (270344#64) ≠ s.getMem (72#64) := by
    have ha : (270344#64 : Word) = (0x42008 : Word) := by decide
    have hb : (72#64 : Word) = (0x48 : Word) := by decide
    simpa only [ha, hb] using different
  simp [Checked, highSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, signExtend13, signExtend21,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    pc, e, d]

theorem low_reject_pc (s : MachineState) (pc : s.pc = 0x1134)
    (different : s.getMem 0x42000 ≠ s.getMem 0x40) :
    (runSchedule lowSchedule s).pc = 0x1004 := by
  have d : s.getMem (270336#64) ≠ s.getMem (64#64) := by
    have ha : (270336#64 : Word) = (0x42000 : Word) := by decide
    have hb : (64#64 : Word) = (0x40 : Word) := by decide
    simpa only [ha, hb] using different
  simp [runSchedule, lowSchedule, execInstrBr, signExtend12,
    signExtend13, signExtend21, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc, d]

theorem high_reject_pc (s : MachineState) (pc : s.pc = 0x1134)
    (low : s.getMem 0x42000 = s.getMem 0x40)
    (different : s.getMem 0x42008 ≠ s.getMem 0x48) :
    (runSchedule highSchedule s).pc = 0x1004 := by
  have e : s.getMem (270336#64) = s.getMem (64#64) := by
    have ha : (270336#64 : Word) = (0x42000 : Word) := by decide
    have hb : (64#64 : Word) = (0x40 : Word) := by decide
    simpa only [ha, hb] using low
  have d : s.getMem (270344#64) ≠ s.getMem (72#64) := by
    have ha : (270344#64 : Word) = (0x42008 : Word) := by decide
    have hb : (72#64 : Word) = (0x48 : Word) := by decide
    simpa only [ha, hb] using different
  simp [runSchedule, highSchedule, execInstrBr, signExtend12,
    signExtend13, signExtend21, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, pc, e, d]

theorem failure_checked (s : MachineState) (pc : s.pc = 0x1004) :
    Checked failureSchedule s := by
  simp [Checked, failureSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, pc]

theorem failure_registers (s : MachineState) (pc : s.pc = 0x1004) :
    (runSchedule failureSchedule s).pc = 0x100c ∧
    (runSchedule failureSchedule s).getReg .x5 = 0 ∧
    (runSchedule failureSchedule s).getReg .x10 = 0 := by
  simp [runSchedule, failureSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, pc]

theorem failure_executes (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1004) :
    Executes hash SphincsImages.verify s 3
      ⟨.failure, runSchedule failureSchedule s, 3, 0, 0⟩ := by
  obtain ⟨finalPc, service, status⟩ := failure_registers s pc
  have hf : fetch SphincsImages.verify (runSchedule failureSchedule s) =
      some (.base .ECALL) := by
    rw [SphincsVerifierFtsRootCopy.fetch_at, finalPc]
    decide
  have terminal := Executes.halt (hash := hash)
    (image := SphincsImages.verify) (runSchedule failureSchedule s) hf service
  have pre := checked_sound _ failureSchedule failureSchedule_code s
    (failure_checked s pc)
  have whole := pre.then_executes terminal
  rw [status] at whole
  simpa [failureSchedule, Execution.charge] using whole

theorem low_mismatch_executes (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1134)
    (different : s.getMem 0x42000 ≠ s.getMem 0x40) :
    Executes hash SphincsImages.verify s 10
      ⟨.failure, runSchedule failureSchedule (runSchedule lowSchedule s),
        10, 0, 0⟩ := by
  have path := checked_sound _ lowSchedule lowSchedule_code s
    (low_checked s pc different)
  have suffix := failure_executes hash (runSchedule lowSchedule s)
    (low_reject_pc s pc different)
  have whole := path.then_executes suffix
  simpa [lowSchedule, Execution.charge] using whole

theorem high_mismatch_executes (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1134)
    (low : s.getMem 0x42000 = s.getMem 0x40)
    (different : s.getMem 0x42008 ≠ s.getMem 0x48) :
    Executes hash SphincsImages.verify s 13
      ⟨.failure, runSchedule failureSchedule (runSchedule highSchedule s),
        13, 0, 0⟩ := by
  have path := checked_sound _ highSchedule highSchedule_code s
    (high_checked s pc low different)
  have suffix := failure_executes hash (runSchedule highSchedule s)
    (high_reject_pc s pc low different)
  have whole := path.then_executes suffix
  simpa [highSchedule, Execution.charge] using whole

theorem loaded_low_mismatch_terminates (hash : Hash)
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (witness : Bytes SphincsWire.signatureBytes)
    (bad : (hash (SphincsBridge.toQuery
      (SphincsWire.commitmentInput (witnessInner witness)))).extractLsb' 0 64 ≠
      publicKey.extractLsb' 0 64) :
    let result := SphincsSubmission.submission.runWith hash .verify
      (message, publicKey, witness)
    result.finished = true ∧ result.cycles < CYCLE_LIMIT := by
  obtain ⟨state, loaded, pc⟩ := initialState_exists
    SphincsSubmission.submission SphincsSubmission.admissible .verify
      (message, publicKey, witness)
  let inner := witnessInner witness
  let answer := hash (SphincsBridge.toQuery (SphincsWire.commitmentInput inner))
  let prepared := SphincsVerifierHashSetup.firstHashState state
  let afterHash := writeHash prepared answer
  have hpc : afterHash.pc = 0x1134 := by
    simp [afterHash, writeHash, prepared,
      SphincsVerifierHashSetup.firstHash_pc state pc]
  have hreg := SphincsVerifierHashSetup.firstHash_registers state
  have hlow : afterHash.getMem 0x42000 = answer.extractLsb' 0 64 :=
    writeHash_low prepared answer hreg.2.2.1
  have hkey : afterHash.getMem 0x40 = publicKey.extractLsb' 0 64 := by
    rw [show afterHash.getMem 0x40 = prepared.getMem 0x40 from
      writeHash_publicKey_frame prepared answer hreg.2.2.1 0]
    exact SphincsVerifierLoader.firstHash_publicKey_word
      publicKey message witness state loaded 0
  have hdiff : afterHash.getMem 0x42000 ≠ afterHash.getMem 0x40 := by
    rw [hlow, hkey]
    exact bad
  have tail := low_mismatch_executes hash afterHash hpc hdiff
  have execution := SphincsVerifierLoader.loaded_firstHash_executes
    hash publicKey message witness inner state loaded
    (witnessInner_encoded witness) 10 _ tail
  have himage : SphincsSubmission.submission.image .verify = SphincsImages.verify := rfl
  rw [← himage] at execution
  have hrun := runWith_of_executes SphincsSubmission.submission hash .verify
    (message, publicKey, witness) state _ _ loaded execution (by decide)
  simp [hrun, Execution.charge]
  norm_num [CYCLE_LIMIT]

theorem loaded_high_mismatch_terminates (hash : Hash)
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (witness : Bytes SphincsWire.signatureBytes)
    (low : (hash (SphincsBridge.toQuery
      (SphincsWire.commitmentInput (witnessInner witness)))).extractLsb' 0 64 =
      publicKey.extractLsb' 0 64)
    (bad : (hash (SphincsBridge.toQuery
      (SphincsWire.commitmentInput (witnessInner witness)))).extractLsb' 64 64 ≠
      publicKey.extractLsb' 64 64) :
    let result := SphincsSubmission.submission.runWith hash .verify
      (message, publicKey, witness)
    result.finished = true ∧ result.cycles < CYCLE_LIMIT := by
  obtain ⟨state, loaded, pc⟩ := initialState_exists
    SphincsSubmission.submission SphincsSubmission.admissible .verify
      (message, publicKey, witness)
  let inner := witnessInner witness
  let answer := hash (SphincsBridge.toQuery (SphincsWire.commitmentInput inner))
  let prepared := SphincsVerifierHashSetup.firstHashState state
  let afterHash := writeHash prepared answer
  have hpc : afterHash.pc = 0x1134 := by
    simp [afterHash, writeHash, prepared,
      SphincsVerifierHashSetup.firstHash_pc state pc]
  have hreg := SphincsVerifierHashSetup.firstHash_registers state
  have hlow : afterHash.getMem 0x42000 = answer.extractLsb' 0 64 :=
    writeHash_low prepared answer hreg.2.2.1
  have hhigh : afterHash.getMem 0x42008 = answer.extractLsb' 64 64 :=
    writeHash_high prepared answer hreg.2.2.1
  have hkeyLow : afterHash.getMem 0x40 = publicKey.extractLsb' 0 64 := by
    rw [show afterHash.getMem 0x40 = prepared.getMem 0x40 from
      writeHash_publicKey_frame prepared answer hreg.2.2.1 0]
    exact SphincsVerifierLoader.firstHash_publicKey_word
      publicKey message witness state loaded 0
  have hkeyHigh : afterHash.getMem 0x48 = publicKey.extractLsb' 64 64 := by
    rw [show afterHash.getMem 0x48 = prepared.getMem 0x48 from
      writeHash_publicKey_frame prepared answer hreg.2.2.1 1]
    exact SphincsVerifierLoader.firstHash_publicKey_word
      publicKey message witness state loaded 1
  have hequal : afterHash.getMem 0x42000 = afterHash.getMem 0x40 := by
    rw [hlow, hkeyLow]
    exact low
  have hdiff : afterHash.getMem 0x42008 ≠ afterHash.getMem 0x48 := by
    rw [hhigh, hkeyHigh]
    exact bad
  have tail := high_mismatch_executes hash afterHash hpc hequal hdiff
  have execution := SphincsVerifierLoader.loaded_firstHash_executes
    hash publicKey message witness inner state loaded
    (witnessInner_encoded witness) 13 _ tail
  have himage : SphincsSubmission.submission.image .verify = SphincsImages.verify := rfl
  rw [← himage] at execution
  have hrun := runWith_of_executes SphincsSubmission.submission hash .verify
    (message, publicKey, witness) state _ _ loaded execution (by decide)
  simp [hrun, Execution.charge]
  norm_num [CYCLE_LIMIT]

/-- info: 'SigGolfCandidate.SphincsVerifierCommitmentReject.low_mismatch_executes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_mismatch_executes

/-- info: 'SigGolfCandidate.SphincsVerifierCommitmentReject.high_mismatch_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms high_mismatch_executes

/-- info: 'SigGolfCandidate.SphincsVerifierCommitmentReject.loaded_low_mismatch_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_low_mismatch_terminates

/-- info: 'SigGolfCandidate.SphincsVerifierCommitmentReject.loaded_high_mismatch_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_high_mismatch_terminates

end SigGolfCandidate.SphincsVerifierCommitmentReject

namespace SigGolfCandidate.SphincsVerifierRootReject
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix
open SigGolfCandidate.SphincsVerifierCommitmentReject
open SigGolfCandidate.SphincsVerifierXmssFinish
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def rejectSchedule (i : Fin 5) : List (Word × Instr) :=
  finishSchedule.take (7 + 3 * i.val) ++
    [(BitVec.ofNat 64 (0x7c58 + 16 * i.val),
      .JAL .x0 (-(27732 + 16 * i.val)))]

def afterReject (i : Fin 5) (s : MachineState) : MachineState :=
  runSchedule (rejectSchedule i) s

theorem rejectSchedule_code (i : Fin 5) : ∀ entry ∈ rejectSchedule i,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by
  fin_cases i <;> decide

private theorem widened_eq_iff (a b : BitVec 32) :
    (a.setWidth 64 = b.setWidth 64) ↔ a = b := by
  constructor
  · intro h
    have q := congrArg (fun x : BitVec 64 => x.setWidth 32) h
    simpa using q
  · intro h
    rw [h]

theorem reject_checked (i : Fin 5) (s : MachineState)
    (pc : s.pc = 0x7c3c)
    (prior : ∀ j : Fin 5, j.val < i.val →
      s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * j.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * j.val)))
    (different : s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * i.val)) ≠
      s.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * i.val))) :
    Checked (rejectSchedule i) s := by
  fin_cases i
  · norm_num at different
    simp [Checked, rejectSchedule, finishSchedule, execInstrBr, ordinaryStep,
      memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
      signExtend12, signExtend13, signExtend21, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      pc, different]
  · have h0 := prior 0 (by decide)
    norm_num at h0 different
    simp [Checked, rejectSchedule, finishSchedule, execInstrBr, ordinaryStep,
      memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
      signExtend12, signExtend13, signExtend21, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      pc, h0, different]
  · have h0 := prior 0 (by decide)
    have h1 := prior 1 (by decide)
    norm_num at h0 h1 different
    simp [Checked, rejectSchedule, finishSchedule, execInstrBr, ordinaryStep,
      memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
      signExtend12, signExtend13, signExtend21, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      pc, h0, h1, different]
  · have h0 := prior 0 (by decide)
    have h1 := prior 1 (by decide)
    have h2 := prior 2 (by decide)
    norm_num at h0 h1 h2 different
    simp [Checked, rejectSchedule, finishSchedule, execInstrBr, ordinaryStep,
      memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
      signExtend12, signExtend13, signExtend21, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      pc, h0, h1, h2, different]
  · have h0 := prior 0 (by decide)
    have h1 := prior 1 (by decide)
    have h2 := prior 2 (by decide)
    have h3 := prior 3 (by decide)
    norm_num at h0 h1 h2 h3 different
    simp [Checked, rejectSchedule, finishSchedule, execInstrBr, ordinaryStep,
      memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
      signExtend12, signExtend13, signExtend21, widened_eq_iff,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      pc, h0, h1, h2, h3, different]

private theorem checked_last_jump_pc (pre : List (Word × Instr))
    (last : Word × Instr) (s : MachineState)
    (checked : Checked (pre ++ [last]) s)
    (jump : ∀ t : MachineState, t.pc = last.1 →
      (execInstrBr t last.2).pc = 0x1004) :
    (runSchedule (pre ++ [last]) s).pc = 0x1004 := by
  induction pre generalizing s with
  | nil =>
    obtain ⟨atPc, _, _⟩ := checked
    simpa [runSchedule] using jump s atPc
  | cons entry rest ih =>
    obtain ⟨_, _, tail⟩ := checked
    simpa [runSchedule] using ih (execInstrBr s entry.2) tail

theorem reject_pc (i : Fin 5) (s : MachineState)
    (pc : s.pc = 0x7c3c)
    (prior : ∀ j : Fin 5, j.val < i.val →
      s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * j.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * j.val)))
    (different : s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * i.val)) ≠
      s.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * i.val))) :
    (afterReject i s).pc = 0x1004 := by
  have checked := reject_checked i s pc prior different
  apply checked_last_jump_pc
    (finishSchedule.take (7 + 3 * i.val))
    (BitVec.ofNat 64 (0x7c58 + 16 * i.val),
      .JAL .x0 (-(27732 + 16 * i.val))) s
  · exact checked
  · intro t tpc
    fin_cases i <;> simp [execInstrBr, signExtend21, tpc]

theorem mismatch_executes (hash : Hash) (i : Fin 5) (s : MachineState)
    (pc : s.pc = 0x7c3c)
    (prior : ∀ j : Fin 5, j.val < i.val →
      s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * j.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * j.val)))
    (different : s.getWord32 (BitVec.ofNat 64 (0x44a00 + 4 * i.val)) ≠
      s.getWord32 (BitVec.ofNat 64 (0x22ca0 + 4 * i.val))) :
    Executes hash SphincsImages.verify s (11 + 3 * i.val)
      ⟨.failure, runSchedule failureSchedule (afterReject i s),
        11 + 3 * i.val, 0, 0⟩ := by
  have path := checked_sound _ (rejectSchedule i) (rejectSchedule_code i) s
    (reject_checked i s pc prior different)
  have length : (rejectSchedule i).length = 8 + 3 * i.val := by
    fin_cases i <;> decide
  rw [length] at path
  have suffix := failure_executes hash (afterReject i s)
    (reject_pc i s pc prior different)
  have whole := path.then_executes suffix
  convert whole using 1
  · omega
  · simp [Execution.charge]
    omega

/-- info: 'SigGolfCandidate.SphincsVerifierRootReject.mismatch_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mismatch_executes

end SigGolfCandidate.SphincsVerifierRootReject
