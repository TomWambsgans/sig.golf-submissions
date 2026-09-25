import SigGolfCandidate.SphincsMaskedKeygenPrefix

namespace SigGolfCandidate.SphincsMaskedChainStep
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def prepareSchedule : List (Word × Instr) := [
  (0x1270, .LUI .x28 67),
  (0x1274, .ADDI .x28 .x28 (80)),
  (0x1278, .LD .x6 .x28 (0)),
  (0x127c, .SLLI .x6 .x6 (3)),
  (0x1280, .LUI .x28 67),
  (0x1284, .ADDI .x28 .x28 (88)),
  (0x1288, .LD .x7 .x28 (0)),
  (0x128c, .ADD .x6 .x6 .x7),
  (0x1290, .LUI .x28 67),
  (0x1294, .ADDI .x28 .x28 (16)),
  (0x1298, .SD .x28 .x6 (0)),
  (0x129c, .LUI .x6 69),
  (0x12a0, .ADDI .x6 .x6 (-1280)),
  (0x12a4, .LUI .x7 64),
  (0x12a8, .ADDI .x7 .x7 (40)),
  (0x12ac, .LWU .x13 .x6 (0)),
  (0x12b0, .SW .x7 .x13 (0)),
  (0x12b4, .LWU .x13 .x6 (4)),
  (0x12b8, .SW .x7 .x13 (4)),
  (0x12bc, .LWU .x13 .x6 (8)),
  (0x12c0, .SW .x7 .x13 (8)),
  (0x12c4, .LWU .x13 .x6 (12)),
  (0x12c8, .SW .x7 .x13 (12)),
  (0x12cc, .LWU .x13 .x6 (16)),
  (0x12d0, .SW .x7 .x13 (16)),
  (0x12d4, .ADDI .x6 .x0 (257)),
  (0x12d8, .LUI .x28 67),
  (0x12dc, .ADDI .x28 .x28 (0)),
  (0x12e0, .LD .x7 .x28 (0)),
  (0x12e4, .SLLI .x7 .x7 (16)),
  (0x12e8, .ADD .x6 .x6 .x7),
  (0x12ec, .LUI .x7 64),
  (0x12f0, .ADDI .x7 .x7 (0)),
  (0x12f4, .SW .x7 .x6 (0)),
  (0x12f8, .LUI .x28 67),
  (0x12fc, .ADDI .x28 .x28 (16)),
  (0x1300, .LD .x6 .x28 (0)),
  (0x1304, .SW .x7 .x6 (4)),
  (0x1308, .LUI .x28 67),
  (0x130c, .ADDI .x28 .x28 (8)),
  (0x1310, .LD .x6 .x28 (0)),
  (0x1314, .SD .x7 .x6 (8)),
  (0x1318, .LUI .x28 67),
  (0x131c, .ADDI .x28 .x28 (24)),
  (0x1320, .LD .x6 .x28 (0)),
  (0x1324, .SW .x7 .x6 (16)),
  (0x1328, .ADDI .x6 .x0 (116)),
  (0x132c, .LUI .x7 64),
  (0x1330, .ADDI .x7 .x7 (20)),
  (0x1334, .LWU .x13 .x6 (0)),
  (0x1338, .SW .x7 .x13 (0)),
  (0x133c, .LWU .x13 .x6 (4)),
  (0x1340, .SW .x7 .x13 (4)),
  (0x1344, .LWU .x13 .x6 (8)),
  (0x1348, .SW .x7 .x13 (8)),
  (0x134c, .LWU .x13 .x6 (12)),
  (0x1350, .SW .x7 .x13 (12)),
  (0x1354, .LWU .x13 .x6 (16)),
  (0x1358, .SW .x7 .x13 (16)),
  (0x135c, .LUI .x10 64),
  (0x1360, .ADDI .x10 .x10 (0)),
  (0x1364, .ADDI .x11 .x0 (480)),
  (0x1368, .LUI .x12 66),
  (0x136c, .ADDI .x12 .x12 (0)),
  (0x1370, .ADDI .x5 .x0 (1))]

def finishSchedule : List (Word × Instr) := [
  (0x1378, .LUI .x6 66),
  (0x137c, .ADDI .x6 .x6 (0)),
  (0x1380, .LUI .x7 69),
  (0x1384, .ADDI .x7 .x7 (-1280)),
  (0x1388, .LWU .x13 .x6 (0)),
  (0x138c, .SW .x7 .x13 (0)),
  (0x1390, .LWU .x13 .x6 (4)),
  (0x1394, .SW .x7 .x13 (4)),
  (0x1398, .LWU .x13 .x6 (8)),
  (0x139c, .SW .x7 .x13 (8)),
  (0x13a0, .LWU .x13 .x6 (12)),
  (0x13a4, .SW .x7 .x13 (12)),
  (0x13a8, .LWU .x13 .x6 (16)),
  (0x13ac, .SW .x7 .x13 (16)),
  (0x13b0, .LUI .x28 67),
  (0x13b4, .ADDI .x28 .x28 (88)),
  (0x13b8, .LD .x6 .x28 (0)),
  (0x13bc, .ADDI .x6 .x6 (1)),
  (0x13c0, .LUI .x28 67),
  (0x13c4, .ADDI .x28 .x28 (88)),
  (0x13c8, .SD .x28 .x6 (0)),
  (0x13cc, .LUI .x28 67),
  (0x13d0, .ADDI .x28 .x28 (88)),
  (0x13d4, .LD .x6 .x28 (0)),
  (0x13d8, .ADDI .x7 .x0 (7)),
  (0x13dc, .BNE .x6 .x7 (-364))]

def prepareState (s : MachineState) : MachineState := runSchedule prepareSchedule s
def finishState (s : MachineState) : MachineState := runSchedule finishSchedule s

theorem prepare_code : ∀ entry ∈ prepareSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.keygen entry.1 = some (.base entry.2) := by
  decide

theorem finish_code : ∀ entry ∈ finishSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.keygen entry.1 = some (.base entry.2) := by
  decide

theorem prepare_checked (s : MachineState) (pc : s.pc = 0x1270) :
    Checked prepareSchedule s := by
  simp [Checked, prepareSchedule, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

theorem finish_checked (s : MachineState) (pc : s.pc = 0x1378) :
    Checked finishSchedule s := by
  simp [Checked, finishSchedule, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

theorem prepare_block (s : MachineState) (pc : s.pc = 0x1270) :
    OrdinarySteps SphincsMaskedImages.keygen s 65 (prepareState s) :=
  checked_sound _ prepareSchedule prepare_code s (prepare_checked s pc)

theorem finish_block (s : MachineState) (pc : s.pc = 0x1378) :
    OrdinarySteps SphincsMaskedImages.keygen s 26 (finishState s) :=
  checked_sound _ finishSchedule finish_code s (finish_checked s pc)

theorem prepare_pc (s : MachineState) (pc : s.pc = 0x1270) :
    (prepareState s).pc = 0x1374 := by
  simp [prepareState, runSchedule, prepareSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

theorem prepare_registers (s : MachineState) :
    (prepareState s).getReg .x10 = 0x40000 ∧
    (prepareState s).getReg .x11 = 480 ∧
    (prepareState s).getReg .x12 = 0x42000 ∧
    (prepareState s).getReg .x5 = 1 := by
  simp [prepareState, runSchedule, prepareSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32]

def answerState (hash : Hash) (s : MachineState) : MachineState :=
  writeHash (prepareState s) (hash (hashInput (prepareState s)))

def stepState (hash : Hash) (s : MachineState) : MachineState := finishState (answerState hash s)

theorem step_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x1270) :
    Trace hash SphincsMaskedImages.keygen s 92 99 1 1 (stepState hash s) := by
  obtain ⟨src, bits, dst, service⟩ := prepare_registers s
  have hfetch : fetch SphincsMaskedImages.keygen (prepareState s) = some (.base .ECALL) := by
    rw [SphincsVerifierFtsRootCopy.fetch_at, prepare_pc s pc]
    decide
  have valid : hashArgumentsValid (prepareState s) = true := by
    simp [hashArgumentsValid, src, bits, dst, accessValid, rangeValid, MEMORY_BYTES]
  have len : (hashInput (prepareState s)).1 = 480 := by simp [hashInput, bits]
  have oneStep := Trace.hash (hash := hash) (image := SphincsMaskedImages.keygen)
    (prepareState s) _ 0 0 0 0 hfetch service valid (Trace.refl _)
  have hashStep : Trace hash SphincsMaskedImages.keygen (prepareState s)
      1 8 1 1 (answerState hash s) := by
    simp only [len] at oneStep
    exact oneStep
  have apc : (answerState hash s).pc = 0x1378 := by
    simp [answerState, writeHash, prepare_pc s pc]
  exact (prepare_block s pc).trace.trans (hashStep.trans (finish_block _ apc).trace)


@[simp] theorem extract_replace_low (w : Word) (v : BitVec 32) :
    extractWord32 (replaceWord32 w 0 v) 0 = v := by
  ext j hj
  interval_cases j <;> simp [extractWord32, replaceWord32]

@[simp] theorem extract_replace_high (w : Word) (v : BitVec 32) :
    extractWord32 (replaceWord32 w 1 v) 1 = v := by
  ext j hj
  interval_cases j <;> simp [extractWord32, replaceWord32]

@[simp] theorem extract_replace_low_other (w : Word) (v : BitVec 32) :
    extractWord32 (replaceWord32 w 0 v) 1 = extractWord32 w 1 := by
  ext j hj
  interval_cases j <;> simp [extractWord32, replaceWord32]

@[simp] theorem extract_replace_high_other (w : Word) (v : BitVec 32) :
    extractWord32 (replaceWord32 w 1 v) 0 = extractWord32 w 0 := by
  ext j hj
  interval_cases j <;> simp [extractWord32, replaceWord32]

theorem finish_word32 (s : MachineState) (i : Fin 5) :
    (finishState s).getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) := by
  fin_cases i <;>
    simp [finishState, runSchedule, finishSchedule, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset]

theorem prepare_counter (s : MachineState) :
    (prepareState s).getMem 0x43058 = s.getMem 0x43058 := by
  simp [prepareState, runSchedule, prepareSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset]

theorem finish_counter (s : MachineState) :
    (finishState s).getMem 0x43058 = s.getMem 0x43058 + 1 := by
  simp [finishState, runSchedule, finishSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset]

theorem finish_pc (s : MachineState) (pc : s.pc = 0x1378) :
    (finishState s).pc = if s.getMem 0x43058 + 1 = 7 then 0x13e0 else 0x1270 := by
  simp [finishState, runSchedule, finishSchedule, execInstrBr, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]


theorem answer_counter (hash : Hash) (s : MachineState) :
    (answerState hash s).getMem 0x43058 = s.getMem 0x43058 := by
  have dst := (prepare_registers s).2.2.1
  simp [answerState, writeHash, dst, MachineState.writeWords]
  exact prepare_counter s

theorem step_counter (hash : Hash) (s : MachineState) :
    (stepState hash s).getMem 0x43058 = s.getMem 0x43058 + 1 := by
  rw [stepState, finish_counter, answer_counter]

theorem step_pc (hash : Hash) (s : MachineState) (pc : s.pc = 0x1270) :
    (stepState hash s).pc = if s.getMem 0x43058 + 1 = 7 then 0x13e0 else 0x1270 := by
  have apc : (answerState hash s).pc = 0x1378 := by
    simp [answerState, writeHash, prepare_pc s pc]
  rw [stepState, finish_pc _ apc, answer_counter]

def walk (hash : Hash) : Nat → MachineState → MachineState
  | 0, s => s
  | n + 1, s => stepState hash (walk hash n s)

/-- One invariant carries control, the step counter, and all four resource totals. -/
theorem walk_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x1270)
    (counter : s.getMem 0x43058 = 0) (n : Nat) (hn : n ≤ 7) :
    Trace hash SphincsMaskedImages.keygen s (92 * n) (99 * n) n n (walk hash n s) ∧
      (walk hash n s).getMem 0x43058 = BitVec.ofNat 64 n ∧
      (walk hash n s).pc = if n = 7 then 0x13e0 else 0x1270 := by
  induction n with
  | zero => exact ⟨Trace.refl _, counter, pc⟩
  | succ n ih =>
    obtain ⟨trace, count, loc⟩ := ih (by omega)
    have npc : (walk hash n s).pc = 0x1270 := by rw [loc, if_neg (by omega)]
    have next : BitVec.ofNat 64 n + 1 = BitVec.ofNat 64 (n + 1) := (BitVec.ofNat_add _ _).symm
    refine ⟨?_, ?_, ?_⟩
    · simpa only [walk, Nat.mul_succ] using trace.trans (step_trace hash _ npc)
    · rw [walk, step_counter, count, next]
    · rw [walk, step_pc hash _ npc, count, next]
      have eq : (BitVec.ofNat 64 (n + 1) : Word) = 7 ↔ n + 1 = 7 := by
        constructor
        · intro h
          have hh := congrArg BitVec.toNat h
          change (n + 1) % 2 ^ 64 = 7 at hh
          rw [Nat.mod_eq_of_lt (by omega)] at hh
          exact hh
        · intro h; rw [h]; rfl
      simp only [eq]

theorem seven_steps (hash : Hash) (s : MachineState) (pc : s.pc = 0x1270)
    (counter : s.getMem 0x43058 = 0) :
    Trace hash SphincsMaskedImages.keygen s 644 693 7 7 (walk hash 7 s) ∧
      (walk hash 7 s).getMem 0x43058 = 7 ∧ (walk hash 7 s).pc = 0x13e0 := by
  simpa using walk_trace hash s pc counter 7 (by decide)

def prepareWrites : List Word := [0x43010#64, 0x40000#64, 0x40008#64, 0x40010#64, 0x40018#64, 0x40020#64, 0x40028#64, 0x40030#64, 0x40038#64]

theorem prepare_frame (s : MachineState) (a : Word) (outside : a ∉ prepareWrites) :
    (prepareState s).getMem a = s.getMem a := by
  simp only [prepareWrites, List.mem_cons, List.not_mem_nil, not_or] at outside
  rcases outside with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [prepareState, runSchedule, prepareSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, h0, h1, h2, h3, h4, h5, h6, h7, h8]

def finishWrites : List Word := [0x43058#64, 0x44b00#64, 0x44b08#64, 0x44b10#64]

theorem finish_frame (s : MachineState) (a : Word) (outside : a ∉ finishWrites) :
    (finishState s).getMem a = s.getMem a := by
  simp only [finishWrites, List.mem_cons, List.not_mem_nil, not_or] at outside
  rcases outside with ⟨h0, h1, h2, h3⟩
  simp [finishState, runSchedule, finishSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, h0, h1, h2, h3]


/-- The protocol header, cached public parameter, and current chain value in 32-bit chunks. -/
def queryWord32 (s : MachineState) (i : Fin 15) : BitVec 32 :=
  if i.val = 0 then (257#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val = 1 then ((s.getMem 0x43050 <<< 3) + s.getMem 0x43058).setWidth 32
  else if i.val = 2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val = 3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val = 4 then (s.getMem 0x43018).setWidth 32
  else if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * (i.val - 5)))
  else s.getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * (i.val - 10)))

/-- Exact query serialization; only the lower 32 bits of address fields are serialized. -/
theorem prepare_words (s : MachineState) (i : Fin 15) :
    (prepareState s).getWord32 (BitVec.ofNat 64 (0x40000 + 4 * i.val)) = queryWord32 s i := by
  fin_cases i <;>
    simp [prepareState, runSchedule, prepareSchedule, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      MachineState.setWord32, MachineState.getWord32, alignToDword, byteOffset, queryWord32]

def answerWrites : List Word := [0x42000#64, 0x42008#64, 0x42010#64, 0x42018#64]
def stepWrites : List Word := prepareWrites ++ answerWrites ++ finishWrites

theorem step_frame (hash : Hash) (s : MachineState) (a : Word) (outside : a ∉ stepWrites) :
    (stepState hash s).getMem a = s.getMem a := by
  have all : (a ∉ prepareWrites ∧ a ∉ answerWrites) ∧ a ∉ finishWrites := by
    simpa only [stepWrites, List.mem_append, not_or] using outside
  obtain ⟨⟨hp, ha⟩, hf⟩ := all
  unfold stepState
  rw [finish_frame _ a hf]
  have dst := (prepare_registers s).2.2.1
  simp only [answerWrites, List.mem_cons, List.not_mem_nil, not_or] at ha
  rcases ha with ⟨h0, h1, h2, h3⟩
  simp [answerState, writeHash, dst, MachineState.writeWords, h0, h1, h2, h3]
  exact prepare_frame s a hp

theorem walk_frame (hash : Hash) (n : Nat) (s : MachineState) (a : Word)
    (outside : a ∉ stepWrites) : (walk hash n s).getMem a = s.getMem a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [walk, step_frame hash _ a outside, ih]


/-- The next chain value is the low 160 bits of this iteration's oracle answer. -/
theorem step_value_words (hash : Hash) (s : MachineState) (i : Fin 5) :
    (stepState hash s).getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * i.val)) =
      (hash (hashInput (prepareState s))).extractLsb' (32 * i.val) 32 := by
  rw [stepState, finish_word32]
  have dst := (prepare_registers s).2.2.1
  fin_cases i <;>
    simp [answerState, writeHash, dst, MachineState.writeWords,
      MachineState.getWord32, alignToDword, byteOffset, extractWord32]
  all_goals
    ext j hj
    interval_cases j <;> simp

/-- info: 'SigGolfCandidate.SphincsMaskedChainStep.step_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_trace

/-- info: 'SigGolfCandidate.SphincsMaskedChainStep.seven_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seven_steps

/-- info: 'SigGolfCandidate.SphincsMaskedChainStep.prepare_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prepare_words

/-- info: 'SigGolfCandidate.SphincsMaskedChainStep.step_value_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_value_words

/-- info: 'SigGolfCandidate.SphincsMaskedChainStep.walk_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walk_frame

end SigGolfCandidate.SphincsMaskedChainStep
