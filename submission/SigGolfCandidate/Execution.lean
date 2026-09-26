import SigGolfCandidate.Memory

namespace SigGolfCandidate
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- A finite execution derivation for the organizer's exact raw-bytecode interpreter. -/
inductive Executes (hash : Hash) (image : Image) : MachineState → Nat → Execution → Prop where
  | halt (state : MachineState) (hf : fetch image state = some (.base .ECALL))
      (hs : state.getReg .x5 = 0) :
      Executes hash image state 1
        ⟨if state.getReg .x10 = 1 then .success else .failure, state, 1, 0, 0⟩
  | ordinary (state next : MachineState) (instruction : Instruction) (steps : Nat) (result : Execution)
      (hf : fetch image state = some instruction) (he : instruction ≠ .base .ECALL)
      (hs : ordinaryStep state instruction = some next)
      (tail : Executes hash image next steps result) :
      Executes hash image state (steps + 1) (result.charge 1 0 0)
  | hash (state : MachineState) (steps : Nat) (result : Execution)
      (hf : fetch image state = some (.base .ECALL))
      (hs : state.getReg .x5 = 1) (hv : hashArgumentsValid state = true)
      (tail : Executes hash image (writeHash state (hash (hashInput state))) steps result) :
      Executes hash image state (steps + 1)
        (result.charge (8 * compressions (hashInput state).1) 1 (compressions (hashInput state).1))

/-- More observation fuel does not change a certified finite execution. -/
theorem Executes.sound {hash : Hash} {image : Image} {state : MachineState} {steps : Nat}
    {result : Execution} (derivation : Executes hash image state steps result) :
    ∀ fuel, steps ≤ fuel → evalWithAnswerFn hash (execute fuel image state) = result := by
  induction derivation with
  | halt state hf hs =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel => simp [execute, hf, hs]
  | ordinary state next instruction steps result hf he hs tail ih =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hstep : steps ≤ fuel := by omega
      cases instruction with
      | base instruction =>
        cases instruction <;> simp_all [execute]
      | word op rd rs1 rs2 => simp [execute, hf, hs, ih fuel hstep]
      | sraiw rd rs shift => simp [execute, hf, hs, ih fuel hstep]
  | hash state steps result hf hs hv tail ih =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hstep : steps ≤ fuel := by omega
      have answer : evalWithAnswerFn hash (liftM (HashSpec.query (hashInput state))) =
          hash (hashInput state) := by simp [evalWithAnswerFn]
      simp [execute, hf, hs, hv, answer, ih fuel hstep]

/-- A block of ordinary instructions, with each fetch and memory check certified. -/
inductive OrdinarySteps (image : Image) : MachineState → Nat → MachineState → Prop where
  | refl (state : MachineState) : OrdinarySteps image state 0 state
  | step (state next final : MachineState) (instruction : Instruction) (steps : Nat)
      (hf : fetch image state = some instruction)
      (hs : ordinaryStep state instruction = some next)
      (tail : OrdinarySteps image next steps final) :
      OrdinarySteps image state (steps + 1) final

theorem OrdinarySteps.append {image : Image} {first middle final : MachineState}
    {before after : Nat} (left : OrdinarySteps image first before middle)
    (right : OrdinarySteps image middle after final) :
    OrdinarySteps image first (before + after) final := by
  induction left with
  | refl => simpa using right
  | step state next middle instruction steps hf hs tail ih =>
      simpa [Nat.succ_add, Nat.add_assoc] using
        OrdinarySteps.step state next final instruction (steps + after) hf hs (ih right)

theorem OrdinarySteps.then_executes {hash : Hash} {image : Image} {state next : MachineState}
    {count steps : Nat} {result : Execution} (block : OrdinarySteps image state count next)
    (tail : Executes hash image next steps result) :
    Executes hash image state (steps + count) (result.charge count 0 0) := by
  induction block with
  | refl => simpa [Execution.charge] using tail
  | step state next final instruction count hf hs block ih =>
    have he : instruction ≠ .base .ECALL := by
      intro h
      simp [h, ordinaryStep] at hs
    have trace := Executes.ordinary state next instruction _ _ hf he hs (ih tail)
    simpa [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trace

private theorem load_buffers_pc (buffers : List (Nat × List Byte)) (state : MachineState) :
    (buffers.foldl (fun state buffer => state.writeBytesAsWords (BitVec.ofNat 64 buffer.1) buffer.2) state).pc = state.pc := by
  induction buffers generalizing state with
  | nil => rfl
  | cons head tail ih => simp only [List.foldl_cons, ih, MachineState.pc_writeBytesAsWords]

/-- Every admitted input starts at the entry point, independently of its contents. -/
theorem initialState_exists (submission : Submission) (admitted : submission.Admissible)
    (phase : Phase) (input : Input submission.sizes phase) :
    ∃ state, initialState submission phase input = some state ∧ state.pc = 0x1000 := by
  unfold initialState
  rw [if_pos (admitted.2 phase)]
  refine ⟨_, rfl, ?_⟩
  simp only [MachineState.pc_setReg, load_buffers_pc, MachineState.pc_writeBytesAsWords]

/-- info: 'SigGolfCandidate.Executes.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Executes.sound

end SigGolfCandidate

namespace SigGolfCandidate.BetaExpand
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
deriving instance DecidableEq for SigGolf.Riscv.Instruction

def translated : Image where
  code := [
    0x00020337, 0x06030313, 0x000233b7, 0xca038393,
    0x58700513, 0x00033583, 0x00b3b023, 0x00830313,
    0x00838393, 0xfff50513, 0xfe0516e3, 0x00036583,
    0x00b3a023, 0x00000293, 0x00100513, 0x0040006f,
    0x00100293, 0x00154513, 0x00000073]
  data := []

def oldExpand : Image where
  code := [
    0x00020337, 0x06030313, 0x000233b7, 0xca038393,
    0x58700513, 0x00033583, 0x00b3b023, 0x00830313,
    0x00838393, 0xfff50513, 0xfe0516e3, 0x00036583,
    0x00b3a023, 0x00000293, 0x00100513, 0x00000073]
  data := []

private theorem old_code_relation (i : Nat) (instruction : Instruction)
    (h : (oldExpand.code[i]?).bind decodeInstruction = some instruction)
    (ne : instruction ≠ .base .ECALL) :
    (translated.code[i]?).bind decodeInstruction = some instruction := by
  have bound : i < 16 := by
    by_contra hn
    have none : oldExpand.code[i]? = none := by
      apply List.getElem?_eq_none
      simp [oldExpand]
      omega
    simp [none] at h
  interval_cases i <;> simp [oldExpand, translated] at h ⊢
  all_goals try exact h
  have he : instruction = .base .ECALL := by
    simpa only [show decodeInstruction (115#32) = some (.base .ECALL) from rfl, Option.some.injEq] using h.symm
  exact False.elim (ne he)

private theorem old_code_cost (i : Nat) (instruction : Instruction)
    (h : (oldExpand.code[i]?).bind decodeInstruction = some instruction)
    (ne : instruction ≠ .base .ECALL) :
    instructionCycles instruction = 1 := by
  have bound : i < 16 := by
    by_contra hn
    have none : oldExpand.code[i]? = none := by
      apply List.getElem?_eq_none
      simp [oldExpand]
      omega
    simp [none] at h
  interval_cases i <;> simp [oldExpand] at h
  all_goals try (cases h; rfl)

private theorem ordinary_cost_old (state : MachineState) (instruction : Instruction)
    (hf : fetch oldExpand state = some instruction)
    (ne : instruction ≠ .base .ECALL) :
    instructionCycles instruction = 1 := by
  unfold fetch at hf
  split_ifs at hf
  exact old_code_cost _ instruction hf ne

private theorem old_ecall_index (i : Nat)
    (h : (oldExpand.code[i]?).bind decodeInstruction = some (.base .ECALL)) :
    i = 15 := by
  have bound : i < 16 := by
    by_contra hn
    have none : oldExpand.code[i]? = none := by
      apply List.getElem?_eq_none
      simp [oldExpand]
      omega
    simp [none] at h
  interval_cases i <;> simp [oldExpand] at h ⊢
  all_goals try (revert h; decide)

private theorem halt_pc_old (state : MachineState)
    (hf : fetch oldExpand state = some (.base .ECALL)) :
    state.pc = 0x103c := by
  unfold fetch at hf
  split_ifs at hf with hvalid
  have idx := old_ecall_index _ hf
  have low : 0x1000 ≤ state.pc.toNat := by
    simp at hvalid
    omega
  have align : state.pc.toNat % 4 = 0 := by
    simp at hvalid
    omega
  apply BitVec.eq_of_toNat_eq
  change state.pc.toNat = 4156
  omega

private theorem ordinary_fetch_old (state : MachineState) (instruction : Instruction)
    (hf : fetch oldExpand state = some instruction)
    (ne : instruction ≠ .base .ECALL) :
    fetch translated state = some instruction := by
  unfold fetch at hf ⊢
  split_ifs at hf ⊢; try contradiction
  exact old_code_relation _ instruction hf ne

private theorem decode_jal :
    decodeInstruction (0x0040006f : BitVec 32) = some (.base (.JAL .x0 4)) := by rfl
private theorem decode_addi :
    decodeInstruction (0x00100293 : BitVec 32) = some (.base (.ADDI .x5 .x0 1)) := by rfl
private theorem decode_xori :
    decodeInstruction (0x00154513 : BitVec 32) = some (.base (.XORI .x10 .x10 1)) := by rfl
private theorem decode_ecall :
    decodeInstruction (0x00000073 : BitVec 32) = some (.base .ECALL) := by rfl

private theorem fetch_site (s : MachineState) (pc : s.pc = 0x103c) :
    fetch translated s = some (.base (.JAL .x0 4)) := by
  simp [fetch, translated, pc]
  exact decode_jal

private theorem fetch_ecall (s : MachineState) (pc : s.pc = 0x1048) :
    fetch translated s = some (.base .ECALL) := by
  simp [fetch, translated, pc]
  exact decode_ecall

private def jumpState (s : MachineState) : MachineState := execInstrBr s (.JAL .x0 4)
private def selectorState (s : MachineState) : MachineState :=
  execInstrBr (jumpState s) (.ADDI .x5 .x0 1)
private def verdictState (s : MachineState) : MachineState :=
  execInstrBr (selectorState s) (.XORI .x10 .x10 1)

private theorem jump_pc (s : MachineState) (pc : s.pc = 0x103c) :
    (jumpState s).pc = 0x1040 := by simp [jumpState, execInstrBr, pc, MachineState.setPC, signExtend21]
private theorem selector_pc (s : MachineState) (pc : s.pc = 0x103c) :
    (selectorState s).pc = 0x1044 := by simp [selectorState, execInstrBr, jump_pc s pc, MachineState.setPC]
private theorem verdict_pc (s : MachineState) (pc : s.pc = 0x103c) :
    (verdictState s).pc = 0x1048 := by simp [verdictState, execInstrBr, selector_pc s pc, MachineState.setPC]

private theorem fetch_addi (s : MachineState) (pc : s.pc = 0x1040) :
    fetch translated s = some (.base (.ADDI .x5 .x0 1)) := by
  simp [fetch, translated, pc]
  exact decode_addi
private theorem fetch_xori (s : MachineState) (pc : s.pc = 0x1044) :
    fetch translated s = some (.base (.XORI .x10 .x10 1)) := by
  simp [fetch, translated, pc]
  exact decode_xori

private theorem halt_terminal (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1048) (selector : s.getReg .x5 = 1) :
    let result := evalWithAnswerFn hash (SigGolf.Riscv.execute 1 translated s)
    result.exit = (if s.getReg .x10 = 0 then .success else .failure) ∧
      result.cycles = 1 ∧ result.hashCalls = 0 ∧ result.hashCompressions = 0 ∧
      (∀ address, result.state.getMem address = s.getMem address) := by
  simp [SigGolf.Riscv.execute, fetch_ecall s pc, selector]

private theorem first_step (s : MachineState) (pc : s.pc = 0x103c) :
    SigGolf.Riscv.execute 4 translated s =
      (fun result => result.charge 1 0 0) <$> SigGolf.Riscv.execute 3 translated (jumpState s) := by
  rw [SigGolf.Riscv.execute]
  simp [fetch_site s pc, ordinaryStep, jumpState, memoryArgumentsValid, instructionCycles]

private theorem second_step (s : MachineState) (pc : s.pc = 0x1040) :
    SigGolf.Riscv.execute 3 translated s =
      (fun result => result.charge 1 0 0) <$> SigGolf.Riscv.execute 2 translated
        (execInstrBr s (.ADDI .x5 .x0 1)) := by
  rw [SigGolf.Riscv.execute]
  simp [fetch_addi s pc, ordinaryStep, memoryArgumentsValid, instructionCycles]

private theorem third_step (s : MachineState) (pc : s.pc = 0x1044) :
    SigGolf.Riscv.execute 2 translated s =
      (fun result => result.charge 1 0 0) <$> SigGolf.Riscv.execute 1 translated
        (execInstrBr s (.XORI .x10 .x10 1)) := by
  rw [SigGolf.Riscv.execute]
  simp [fetch_xori s pc, ordinaryStep, memoryArgumentsValid, instructionCycles]

private theorem selector_reg (s : MachineState) :
    (selectorState s).getReg .x5 = 1 := by
  simp [selectorState, execInstrBr, MachineState.getReg, MachineState.setPC,
    MachineState.setReg, signExtend12]
private theorem selector_x10 (s : MachineState) :
    (selectorState s).getReg .x10 = s.getReg .x10 := by
  simp [selectorState, jumpState, execInstrBr, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
private theorem verdict_selector (s : MachineState) :
    (verdictState s).getReg .x5 = 1 := by
  simp [verdictState, execInstrBr, MachineState.getReg_setReg_ne,
    MachineState.getReg_setPC, selector_reg]
private theorem verdict_register (s : MachineState) :
    (verdictState s).getReg .x10 = s.getReg .x10 ^^^ 1 := by
  simp [verdictState, execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setPC, selector_x10, signExtend12]

private theorem verdict_mem (s : MachineState) (address : Word) :
    (verdictState s).getMem address = s.getMem address := by
  simp [verdictState, selectorState, jumpState, execInstrBr,
    MachineState.getMem_setReg, MachineState.getMem_setPC]

private theorem four_result (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x103c) :
    evalWithAnswerFn hash (SigGolf.Riscv.execute 4 translated s) =
      (evalWithAnswerFn hash (SigGolf.Riscv.execute 1 translated (verdictState s))).charge 3 0 0 := by
  rw [first_step s pc, second_step (jumpState s) (jump_pc s pc)]
  rw [show execInstrBr (jumpState s) (.ADDI .x5 .x0 1) = selectorState s from rfl]
  rw [third_step (selectorState s) (selector_pc s pc)]
  rw [show execInstrBr (selectorState s) (.XORI .x10 .x10 1) = verdictState s from rfl]
  simp [verdictState, evalWithAnswerFn_map, Execution.charge]
  omega

private theorem xor_one_zero_iff (value : BitVec 64) :
    value ^^^ 1 = 0 ↔ value = 1 := by bv_decide

private theorem halt_stub (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x103c) :
    let result := evalWithAnswerFn hash (SigGolf.Riscv.execute 4 translated s)
    result.exit = (if s.getReg .x10 = 1 then .success else .failure) ∧
      result.cycles = 4 ∧ result.hashCalls = 0 ∧ result.hashCompressions = 0 ∧
      (∀ address, result.state.getMem address = s.getMem address) := by
  rw [four_result hash s pc]
  have terminal := halt_terminal hash (verdictState s) (verdict_pc s pc) (verdict_selector s)
  dsimp only at terminal ⊢
  rcases terminal with ⟨hexit, hcycles, hcalls, hblocks, hmem⟩
  simp only [Execution.charge, verdict_register] at hexit hcycles ⊢
  simp [hexit, hcycles, hcalls, hblocks, hmem, verdict_mem]

private theorem terminal_fuel (fuel : Nat) (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1048) (selector : s.getReg .x5 = 1) :
    let result := evalWithAnswerFn hash (SigGolf.Riscv.execute (fuel + 1) translated s)
    result.exit = (if s.getReg .x10 = 0 then .success else .failure) ∧
      result.cycles = 1 ∧ result.hashCalls = 0 ∧ result.hashCompressions = 0 ∧
      (∀ address, result.state.getMem address = s.getMem address) := by
  rw [show fuel + 1 = Nat.succ fuel by omega]
  simp [SigGolf.Riscv.execute, fetch_ecall s pc, selector]

private theorem first_step_fuel (fuel : Nat) (s : MachineState) (pc : s.pc = 0x103c) :
    SigGolf.Riscv.execute (fuel + 4) translated s =
      (fun result => result.charge 1 0 0) <$> SigGolf.Riscv.execute (fuel + 3) translated (jumpState s) := by
  rw [show fuel + 4 = Nat.succ (fuel + 3) by omega, SigGolf.Riscv.execute]
  simp [fetch_site s pc, ordinaryStep, jumpState, memoryArgumentsValid, instructionCycles]

private theorem second_step_fuel (fuel : Nat) (s : MachineState) (pc : s.pc = 0x1040) :
    SigGolf.Riscv.execute (fuel + 3) translated s =
      (fun result => result.charge 1 0 0) <$> SigGolf.Riscv.execute (fuel + 2) translated
        (execInstrBr s (.ADDI .x5 .x0 1)) := by
  rw [show fuel + 3 = Nat.succ (fuel + 2) by omega, SigGolf.Riscv.execute]
  simp [fetch_addi s pc, ordinaryStep, memoryArgumentsValid, instructionCycles]

private theorem third_step_fuel (fuel : Nat) (s : MachineState) (pc : s.pc = 0x1044) :
    SigGolf.Riscv.execute (fuel + 2) translated s =
      (fun result => result.charge 1 0 0) <$> SigGolf.Riscv.execute (fuel + 1) translated
        (execInstrBr s (.XORI .x10 .x10 1)) := by
  rw [show fuel + 2 = Nat.succ (fuel + 1) by omega, SigGolf.Riscv.execute]
  simp [fetch_xori s pc, ordinaryStep, memoryArgumentsValid, instructionCycles]

private theorem four_result_fuel (fuel : Nat) (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x103c) :
    evalWithAnswerFn hash (SigGolf.Riscv.execute (fuel + 4) translated s) =
      (evalWithAnswerFn hash (SigGolf.Riscv.execute (fuel + 1) translated (verdictState s))).charge 3 0 0 := by
  rw [first_step_fuel fuel s pc, second_step_fuel fuel (jumpState s) (jump_pc s pc)]
  rw [show execInstrBr (jumpState s) (.ADDI .x5 .x0 1) = selectorState s from rfl]
  rw [third_step_fuel fuel (selectorState s) (selector_pc s pc)]
  rw [show execInstrBr (selectorState s) (.XORI .x10 .x10 1) = verdictState s from rfl]
  simp [verdictState, evalWithAnswerFn_map, Execution.charge]
  omega

theorem halt_stub_fuel (fuel : Nat) (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x103c) :
    let result := evalWithAnswerFn hash (SigGolf.Riscv.execute (fuel + 4) translated s)
    result.exit = (if s.getReg .x10 = 1 then .success else .failure) ∧
      result.cycles = 4 ∧ result.hashCalls = 0 ∧ result.hashCompressions = 0 ∧
      (∀ address, result.state.getMem address = s.getMem address) := by
  rw [four_result_fuel fuel hash s pc]
  have terminal := terminal_fuel fuel hash (verdictState s) (verdict_pc s pc) (verdict_selector s)
  dsimp only at terminal ⊢
  rcases terminal with ⟨hexit, hcycles, hcalls, hblocks, hmem⟩
  simp only [Execution.charge, verdict_register] at hexit hcycles ⊢
  simp [hexit, hcycles, hcalls, hblocks, hmem, verdict_mem]

#print axioms halt_stub_fuel

theorem halt_stub_pure_fuel (fuel : Nat) (s : MachineState)
    (pc : s.pc = 0x103c) :
    SigGolf.Riscv.execute (fuel + 4) translated s =
      pure ⟨if s.getReg .x10 = 1 then .success else .failure,
        verdictState s, 4, 0, 0⟩ := by
  rw [first_step_fuel fuel s pc,
    second_step_fuel fuel (jumpState s) (jump_pc s pc)]
  rw [show execInstrBr (jumpState s) (.ADDI .x5 .x0 1) = selectorState s from rfl]
  rw [third_step_fuel fuel (selectorState s) (selector_pc s pc)]
  rw [show execInstrBr (selectorState s) (.XORI .x10 .x10 1) = verdictState s from rfl]
  rw [show fuel + 1 = Nat.succ fuel by omega, SigGolf.Riscv.execute]
  simp [fetch_ecall (verdictState s) (verdict_pc s pc), verdict_selector,
    verdict_register, Execution.charge]

#print axioms halt_stub_pure_fuel

def OutcomeMatches (oldResult newResult : Execution) : Prop :=
  newResult.exit = oldResult.exit ∧
  newResult.cycles = oldResult.cycles + 3 ∧
  newResult.hashCalls = oldResult.hashCalls ∧
  newResult.hashCompressions = oldResult.hashCompressions ∧
  ∀ address, newResult.state.getMem address = oldResult.state.getMem address

private theorem trace_transport (oldImage : Image) (hash : Hash)
    (ordinary_fetch : ∀ (state : MachineState) (instruction : Instruction),
      fetch oldImage state = some instruction → instruction ≠ .base .ECALL →
      fetch translated state = some instruction)
    (halt_pc : ∀ (state : MachineState),
      fetch oldImage state = some (.base .ECALL) → state.pc = 0x103c)
    (ordinary_cost : ∀ (state : MachineState) (instruction : Instruction),
      fetch oldImage state = some instruction → instruction ≠ .base .ECALL →
      instructionCycles instruction = 1)
    {state : MachineState} {steps : Nat} {result : Execution}
    (trace : Executes hash oldImage state steps result)
    (zero : result.hashCalls = 0) :
    OutcomeMatches result
      (evalWithAnswerFn hash (SigGolf.Riscv.execute (steps + 3) translated state)) := by
  induction trace with
  | halt state hf hs =>
      have h := halt_stub hash state (halt_pc state hf)
      dsimp only at h ⊢
      rcases h with ⟨hexit, hcycles, hcalls, hblocks, hmem⟩
      exact ⟨hexit, by omega, hcalls, hblocks, hmem⟩
  | ordinary state next instruction steps tailResult hf he hs tail ih =>
      have tailZero : tailResult.hashCalls = 0 := by
        simpa [Execution.charge] using zero
      have ih := ih tailZero
      have nextStep :
          evalWithAnswerFn hash (SigGolf.Riscv.execute (steps + 1 + 3) translated state) =
            (evalWithAnswerFn hash (SigGolf.Riscv.execute (steps + 3) translated next)).charge 1 0 0 := by
        rw [show steps + 1 + 3 = Nat.succ (steps + 3) by omega, SigGolf.Riscv.execute]
        simp [ordinary_fetch state instruction hf he, hs, ordinary_cost state instruction hf he,
          evalWithAnswerFn_map]
      rw [nextStep]
      rcases ih with ⟨hexit, hcycles, hcalls, hblocks, hmem⟩
      exact ⟨hexit, by simp [Execution.charge] at *; omega,
        by simpa [Execution.charge] using hcalls,
        by simpa [Execution.charge] using hblocks,
        hmem⟩
  | hash state steps tailResult hf hs hv tail ih =>
      simp [Execution.charge] at zero

private theorem trace_transport_extra (extra : Nat) (oldImage : Image) (hash : Hash)
    (ordinary_fetch : ∀ (state : MachineState) (instruction : Instruction),
      fetch oldImage state = some instruction → instruction ≠ .base .ECALL →
      fetch translated state = some instruction)
    (halt_pc : ∀ (state : MachineState),
      fetch oldImage state = some (.base .ECALL) → state.pc = 0x103c)
    (ordinary_cost : ∀ (state : MachineState) (instruction : Instruction),
      fetch oldImage state = some instruction → instruction ≠ .base .ECALL →
      instructionCycles instruction = 1)
    {state : MachineState} {steps : Nat} {result : Execution}
    (trace : Executes hash oldImage state steps result)
    (zero : result.hashCalls = 0) :
    OutcomeMatches result
      (evalWithAnswerFn hash (SigGolf.Riscv.execute (extra + steps + 3) translated state)) := by
  induction trace with
  | halt state hf hs =>
      have h := halt_stub_fuel extra hash state (halt_pc state hf)
      dsimp only at h ⊢
      rcases h with ⟨hexit, hcycles, hcalls, hblocks, hmem⟩
      exact ⟨hexit, by omega, hcalls, hblocks, hmem⟩
  | ordinary state next instruction steps tailResult hf he hs tail ih =>
      have tailZero : tailResult.hashCalls = 0 := by
        simpa [Execution.charge] using zero
      have ih := ih tailZero
      have nextStep :
          evalWithAnswerFn hash (SigGolf.Riscv.execute (extra + steps + 1 + 3) translated state) =
            (evalWithAnswerFn hash (SigGolf.Riscv.execute (extra + steps + 3) translated next)).charge 1 0 0 := by
        rw [show extra + steps + 1 + 3 = Nat.succ (extra + steps + 3) by omega, SigGolf.Riscv.execute]
        simp [ordinary_fetch state instruction hf he, hs, ordinary_cost state instruction hf he,
          evalWithAnswerFn_map]
      rw [show extra + (steps + 1) + 3 = extra + steps + 1 + 3 by omega, nextStep]
      rcases ih with ⟨hexit, hcycles, hcalls, hblocks, hmem⟩
      exact ⟨hexit, by simp [Execution.charge] at *; omega,
        by simpa [Execution.charge] using hcalls,
        by simpa [Execution.charge] using hblocks,
        hmem⟩
  | hash state steps tailResult hf hs hv tail ih =>
      simp [Execution.charge] at zero

theorem old_expand_trace_transport (hash : Hash)
    {state : MachineState} {steps : Nat} {result : Execution}
    (trace : Executes hash oldExpand state steps result)
    (zero : result.hashCalls = 0) :
    OutcomeMatches result
      (evalWithAnswerFn hash (SigGolf.Riscv.execute (steps + 3) translated state)) :=
  trace_transport oldExpand hash ordinary_fetch_old halt_pc_old ordinary_cost_old trace zero

theorem old_expand_trace_transport_extra (extra : Nat) (hash : Hash)
    {state : MachineState} {steps : Nat} {result : Execution}
    (trace : Executes hash oldExpand state steps result)
    (zero : result.hashCalls = 0) :
    OutcomeMatches result
      (evalWithAnswerFn hash (SigGolf.Riscv.execute (extra + steps + 3) translated state)) :=
  trace_transport_extra extra oldExpand hash ordinary_fetch_old halt_pc_old ordinary_cost_old trace zero

#print axioms old_expand_trace_transport_extra

theorem old_expand_trace_pure_extra (extra : Nat) (hash : Hash)
    {state : MachineState} {steps : Nat} {result : Execution}
    (trace : Executes hash oldExpand state steps result)
    (zero : result.hashCalls = 0) :
    ∃ betaResult : Execution,
      SigGolf.Riscv.execute (extra + steps + 3) translated state = pure betaResult ∧
      OutcomeMatches result betaResult := by
  induction trace with
  | halt state hf hs =>
      refine ⟨⟨if state.getReg .x10 = 1 then .success else .failure,
        verdictState state, 4, 0, 0⟩, ?_, ?_⟩
      · exact halt_stub_pure_fuel extra state (halt_pc_old state hf)
      · simp [OutcomeMatches, verdict_mem]
  | ordinary state next instruction steps tailResult hf he hs tail ih =>
      have tailZero : tailResult.hashCalls = 0 := by
        simpa [Execution.charge] using zero
      obtain ⟨betaResult, betaRun, matched⟩ := ih tailZero
      refine ⟨betaResult.charge 1 0 0, ?_, ?_⟩
      · rw [show extra + (steps + 1) + 3 = Nat.succ (extra + steps + 3) by omega,
          SigGolf.Riscv.execute]
        simp [ordinary_fetch_old state instruction hf he, hs,
          ordinary_cost_old state instruction hf he, betaRun]
      · rcases matched with ⟨hexit, hcycles, hcalls, hblocks, hmem⟩
        exact ⟨hexit, by simp [Execution.charge] at *; omega,
          by simpa [Execution.charge] using hcalls,
          by simpa [Execution.charge] using hblocks,
          hmem⟩
  | hash state steps tailResult hf hs hv tail ih =>
      simp [Execution.charge] at zero

#print axioms old_expand_trace_pure_extra

theorem readBuffer_mem_eq (first second : MachineState) (address n : Nat)
    (same : ∀ a, first.getMem a = second.getMem a) :
    readBuffer first address n = readBuffer second address n := by
  have byte (a : Word) : first.getByte a = second.getByte a := by
    simp [MachineState.getByte, same]
  simp [readBuffer, byte]

theorem readOutput_mem_eq (sizes : Sizes) (layout : Layout)
    (phase : Phase) (first second : MachineState)
    (same : ∀ a, first.getMem a = second.getMem a) :
    readOutput sizes layout phase first = readOutput sizes layout phase second := by
  cases phase <;> simp [readOutput, readBuffer_mem_eq first second _ _ same] <;> rfl

theorem initialState_same_data (sizes : Sizes) (layout : Layout)
    (oldImage newImage : Image) (phase : Phase) (input : Input sizes phase)
    (oldValid : oldImage.Valid sizes layout)
    (newValid : newImage.Valid sizes layout)
    (sameData : oldImage.data = newImage.data) :
    initialState ({ sizes := sizes, layout := layout, image := fun _ => oldImage } : Submission) phase input =
    initialState ({ sizes := sizes, layout := layout, image := fun _ => newImage } : Submission) phase input := by
  simp [initialState, oldValid, newValid, sameData, dataBase]

#print axioms initialState_same_data
#print axioms readOutput_mem_eq
#print axioms old_expand_trace_transport
#print axioms halt_stub
#print axioms halt_terminal
end SigGolfCandidate.BetaExpand
