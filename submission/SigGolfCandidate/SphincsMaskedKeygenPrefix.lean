import SigGolfCandidate.SphincsMaskedImages
import SigGolfCandidate.Hypertree.KeygenTrace
import SigGolfCandidate.SphincsVerifierFtsRootCopy
import SigGolfCandidate.SphincsVerifierFtsRootCopyBytes
import SigGolfCandidate.SphincsBridge
import SigGolfCandidate.Memory
import RiscvZkvm.Rv64.Logic.MemRegionWrite

namespace SigGolfCandidate.SphincsMaskedKeygenPrefix
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private theorem extractByte_slice (value : BitVec 256) (i : Fin 32) :
    extractByte (value.extractLsb' (64 * (i.val / 8)) 64) (i.val % 8) =
      value.extractLsb' (8 * i.val) 8 := by
  ext j hj
  have hb : i.val % 8 * 8 + j < 64 := by omega
  have he : 64 * (i.val / 8) + (i.val % 8 * 8 + j) = 8 * i.val + j := by omega
  simp [extractByte, hb, he]

def prefixSchedule : List (Word × Instr) := [
  (0x1000, .ADDI .x6 .x0 (0)),
  (0x1004, .LUI .x28 67),
  (0x1008, .ADDI .x28 .x28 (0)),
  (0x100c, .SD .x28 .x6 (0)),
  (0x1010, .ADDI .x6 .x0 (0)),
  (0x1014, .LUI .x28 67),
  (0x1018, .ADDI .x28 .x28 (8)),
  (0x101c, .SD .x28 .x6 (0)),
  (0x1020, .ADDI .x6 .x0 (0)),
  (0x1024, .LUI .x28 67),
  (0x1028, .ADDI .x28 .x28 (16)),
  (0x102c, .SD .x28 .x6 (0)),
  (0x1030, .ADDI .x6 .x0 (0)),
  (0x1034, .LUI .x28 67),
  (0x1038, .ADDI .x28 .x28 (24)),
  (0x103c, .SD .x28 .x6 (0)),
  (0x1040, .ADDI .x6 .x0 (32)),
  (0x1044, .LUI .x7 64),
  (0x1048, .ADDI .x7 .x7 (40)),
  (0x104c, .ADDI .x10 .x0 (4)),
  (0x1050, .LD .x11 .x6 (0)),
  (0x1054, .SD .x7 .x11 (0)),
  (0x1058, .ADDI .x6 .x6 (8)),
  (0x105c, .ADDI .x7 .x7 (8)),
  (0x1060, .ADDI .x10 .x10 (-1)),
  (0x1064, .BNE .x10 .x0 (-20)),
  (0x1050, .LD .x11 .x6 (0)),
  (0x1054, .SD .x7 .x11 (0)),
  (0x1058, .ADDI .x6 .x6 (8)),
  (0x105c, .ADDI .x7 .x7 (8)),
  (0x1060, .ADDI .x10 .x10 (-1)),
  (0x1064, .BNE .x10 .x0 (-20)),
  (0x1050, .LD .x11 .x6 (0)),
  (0x1054, .SD .x7 .x11 (0)),
  (0x1058, .ADDI .x6 .x6 (8)),
  (0x105c, .ADDI .x7 .x7 (8)),
  (0x1060, .ADDI .x10 .x10 (-1)),
  (0x1064, .BNE .x10 .x0 (-20)),
  (0x1050, .LD .x11 .x6 (0)),
  (0x1054, .SD .x7 .x11 (0)),
  (0x1058, .ADDI .x6 .x6 (8)),
  (0x105c, .ADDI .x7 .x7 (8)),
  (0x1060, .ADDI .x10 .x10 (-1)),
  (0x1064, .BNE .x10 .x0 (-20)),
  (0x1068, .ADDI .x6 .x0 (1281)),
  (0x106c, .LUI .x28 67),
  (0x1070, .ADDI .x28 .x28 (0)),
  (0x1074, .LD .x7 .x28 (0)),
  (0x1078, .SLLI .x7 .x7 16),
  (0x107c, .ADD .x6 .x6 .x7),
  (0x1080, .LUI .x7 64),
  (0x1084, .ADDI .x7 .x7 (0)),
  (0x1088, .SW .x7 .x6 (0)),
  (0x108c, .LUI .x28 67),
  (0x1090, .ADDI .x28 .x28 (16)),
  (0x1094, .LD .x6 .x28 (0)),
  (0x1098, .SW .x7 .x6 (4)),
  (0x109c, .LUI .x28 67),
  (0x10a0, .ADDI .x28 .x28 (8)),
  (0x10a4, .LD .x6 .x28 (0)),
  (0x10a8, .SD .x7 .x6 (8)),
  (0x10ac, .LUI .x28 67),
  (0x10b0, .ADDI .x28 .x28 (24)),
  (0x10b4, .LD .x6 .x28 (0)),
  (0x10b8, .SW .x7 .x6 (16)),
  (0x10bc, .LUI .x10 64),
  (0x10c0, .ADDI .x10 .x10 (0)),
  (0x10c4, .ADDI .x11 .x0 (576)),
  (0x10c8, .LUI .x12 66),
  (0x10cc, .ADDI .x12 .x12 (0)),
  (0x10d0, .ADDI .x5 .x0 (1))]

def runSchedule : List (Word × Instr) → MachineState → MachineState
  | [], s => s
  | (_, i) :: rest, s => runSchedule rest (execInstrBr s i)

def Checked : List (Word × Instr) → MachineState → Prop
  | [], _ => True
  | (pc, i) :: rest, s => s.pc = pc ∧
      ordinaryStep s (.base i) = some (execInstrBr s i) ∧
      Checked rest (execInstrBr s i)

theorem schedule_code : ∀ entry ∈ prefixSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.keygen entry.1 = some (.base entry.2) := by
  decide

theorem checked_sound (image : Image) (schedule : List (Word × Instr))
    (code : ∀ entry ∈ schedule, SphincsVerifierFtsRootCopy.instructionAt image entry.1 = some (.base entry.2))
    (s : MachineState) (checked : Checked schedule s) :
    OrdinarySteps image s schedule.length (runSchedule schedule s) := by
  induction schedule generalizing s with
  | nil => exact OrdinarySteps.refl s
  | cons entry rest ih =>
    rcases entry with ⟨pc, i⟩
    rcases checked with ⟨hpc, hs, hrest⟩
    apply OrdinarySteps.step s (execInstrBr s i) _ (.base i) rest.length
    · rw [SphincsVerifierFtsRootCopy.fetch_at, hpc]
      exact code (pc, i) (by simp)
    · exact hs
    · exact ih (fun entry h => code entry (by simp [h])) _ hrest

def firstHashState (s : MachineState) : MachineState := runSchedule prefixSchedule s

theorem prefix_checked (s : MachineState) (pc : s.pc = 0x1000) :
    Checked prefixSchedule s := by
  simp [Checked, prefixSchedule, execInstrBr, ordinaryStep, memoryArgumentsValid,
    accessValid, rangeValid, MEMORY_BYTES, signExtend12, signExtend13,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

theorem prefix_block (s : MachineState) (pc : s.pc = 0x1000) :
    OrdinarySteps SphincsMaskedImages.keygen s 71 (firstHashState s) :=
  checked_sound _ prefixSchedule schedule_code s (prefix_checked s pc)

theorem firstHash_pc (s : MachineState) (pc : s.pc = 0x1000) :
    (firstHashState s).pc = 0x10d4 := by
  simp [firstHashState, runSchedule, prefixSchedule, execInstrBr, signExtend12,
    signExtend13, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32, alignToDword, byteOffset, pc]

theorem firstHash_registers (s : MachineState) :
    (firstHashState s).getReg .x10 = 0x40000 ∧
    (firstHashState s).getReg .x11 = 576 ∧
    (firstHashState s).getReg .x12 = 0x42000 ∧
    (firstHashState s).getReg .x5 = 1 := by
  simp [firstHashState, runSchedule, prefixSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.setWord32]

def inputWord (s : MachineState) (i : Fin 9) : Word :=
  if i.val = 0 then 0x501 else if i.val < 5 then 0
  else s.getMem (BitVec.ofNat 64 (0x20 + 8 * (i.val - 5)))

theorem firstHash_words (s : MachineState)
    (zero : ∀ i : Fin 3, s.getMem (BitVec.ofNat 64 (0x40010 + 8 * i.val)) = 0)
    (i : Fin 9) :
    (firstHashState s).getMem (BitVec.ofNat 64 (0x40000 + 8 * i.val)) = inputWord s i := by
  have z0 := zero 0
  have z1 := zero 1
  have z2 := zero 2
  norm_num at z0 z1 z2
  fin_cases i <;>
    simp [firstHashState, runSchedule, prefixSchedule, execInstrBr, signExtend12,
      inputWord, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      MachineState.setWord32, alignToDword, byteOffset, replaceWord32, z0, z1, z2]
  all_goals
    ext j hj
    interval_cases j <;> simp

open SphincsSecurity SigGolfCandidate.SphincsBridge

def parameterPayload (seed : MasterSeed) : List Byte :=
  (keygenHashInput 0 .parameter seed).map UInt8.toBitVec

theorem parameterPayload_length (seed : MasterSeed) : (parameterPayload seed).length = 72 := by
  simp [parameterPayload, keygenHashInput, fieldBytes, bytesLE]

theorem parameterPayload_eq (seed : MasterSeed) :
    parameterPayload seed = ([1, 5] ++ List.replicate 38 0) ++ SigGolf.bytes (n := 32) seed := by
  unfold parameterPayload keygenHashInput
  rw [List.map_append, SphincsBridge.bytesLE_eq_vmBytes]
  congr 1

def parameterWord (seed : MasterSeed) (i : Fin 9) : Word :=
  if i.val = 0 then 0x501 else if i.val < 5 then 0
  else seed.extractLsb' (64 * (i.val - 5)) 64

theorem parameterPayload_byte (seed : MasterSeed) (i : Fin 72) :
    extractByte (parameterWord seed ⟨i.val / 8, by omega⟩) (i.val % 8) =
      (parameterPayload seed)[i.val]'(by rw [parameterPayload_length]; exact i.isLt) := by
  simp only [parameterPayload_eq]
  by_cases hi : i.val < 40
  · have hlt : i.val / 8 < 5 := by omega
    rw [List.getElem_append_left (by simpa using hi)]
    have bound := i.isLt
    rcases i with ⟨i, bound⟩
    interval_cases i <;> simp [parameterWord, extractByte]
  · have hj : i.val - 40 < 32 := by omega
    have hdiv : i.val / 8 - 5 = (i.val - 40) / 8 := by omega
    have hmod : i.val % 8 = (i.val - 40) % 8 := by omega
    rw [List.getElem_append_right (by simpa using (show 40 ≤ i.val by omega))]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
    simp only [parameterWord, if_neg (show i.val / 8 ≠ 0 by omega),
      if_neg (show ¬ i.val / 8 < 5 by omega), hdiv, hmod]
    simpa [SigGolf.bytes] using extractByte_slice seed ⟨i.val - 40, hj⟩

theorem firstHash_parameterWords (s : MachineState) (seed : MasterSeed)
    (zero : ∀ i : Fin 3, s.getMem (BitVec.ofNat 64 (0x40010 + 8 * i.val)) = 0)
    (key : ∀ i : Fin 4, s.getMem (BitVec.ofNat 64 (0x20 + 8 * i.val)) =
      seed.extractLsb' (64 * i.val) 64) (i : Fin 9) :
    (firstHashState s).getMem (BitVec.ofNat 64 (0x40000 + 8 * i.val)) =
      parameterWord seed i := by
  rw [firstHash_words s zero i]
  unfold inputWord parameterWord
  split_ifs
  · rfl
  · rfl
  · exact key ⟨i.val - 5, by omega⟩

/-- The exact 576-bit query sent to the shared oracle. -/
theorem firstHash_input (s : MachineState) (seed : MasterSeed)
    (zero : ∀ i : Fin 3, s.getMem (BitVec.ofNat 64 (0x40010 + 8 * i.val)) = 0)
    (key : ∀ i : Fin 4, s.getMem (BitVec.ofNat 64 (0x20 + 8 * i.val)) =
      seed.extractLsb' (64 * i.val) 64) :
    hashInput (firstHashState s) = toQuery (keygenHashInput 0 .parameter seed) := by
  apply Serialization.hashInput_of_list (firstHashState s) 0x40000 (parameterPayload seed)
  · exact (firstHash_registers s).1
  · rw [parameterPayload_length, (firstHash_registers s).2.1]
    rfl
  · intro i hi
    have bound : i < 72 := by simpa [parameterPayload_length] using hi
    rw [SphincsVerifierFtsRootCopyBytes.getByte_word _ 0x40000 i (by decide) (by omega)]
    change extractByte ((firstHashState s).getMem (BitVec.ofNat 64 (0x40000 + 8 * (i / 8))))
      (i % 8) = _
    rw [firstHash_parameterWords s seed zero key ⟨i / 8, by omega⟩]
    exact parameterPayload_byte seed ⟨i, bound⟩

def afterHashState (hash : SigGolfCandidate.Legacy.Hash) (s : MachineState) (seed : MasterSeed) : MachineState :=
  writeHash (firstHashState s) (hash (toQuery (keygenHashInput 0 .parameter seed)))

theorem firstHash_trace (hash : SigGolfCandidate.Legacy.Hash) (s : MachineState) (seed : MasterSeed)
    (pc : s.pc = 0x1000)
    (zero : ∀ i : Fin 3, s.getMem (BitVec.ofNat 64 (0x40010 + 8 * i.val)) = 0)
    (key : ∀ i : Fin 4, s.getMem (BitVec.ofNat 64 (0x20 + 8 * i.val)) =
      seed.extractLsb' (64 * i.val) 64) :
    Trace hash SphincsMaskedImages.keygen s 72 87 1 2 (afterHashState hash s seed) := by
  obtain ⟨src, bits, dst, service⟩ := firstHash_registers s
  have hfetch : fetch SphincsMaskedImages.keygen (firstHashState s) = some (.base .ECALL) := by
    rw [SphincsVerifierFtsRootCopy.fetch_at, firstHash_pc s pc]
    decide
  have valid : hashArgumentsValid (firstHashState s) = true := by
    simp [hashArgumentsValid, src, bits, dst, accessValid, rangeValid, MEMORY_BYTES]
  have len : (hashInput (firstHashState s)).1 = 576 := by simp [hashInput, bits]
  have oneStep := Trace.hash (hash := hash) (image := SphincsMaskedImages.keygen)
    (firstHashState s) _ 0 0 0 0 hfetch service valid (Trace.refl _)
  have hashStep : Trace hash SphincsMaskedImages.keygen (firstHashState s)
      1 16 1 2 (afterHashState hash s seed) := by
    simp only [len] at oneStep
    change Trace hash SphincsMaskedImages.keygen (firstHashState s) 1 16 1 2
      (writeHash (firstHashState s) (hash (hashInput (firstHashState s)))) at oneStep
    rw [firstHash_input s seed zero key] at oneStep
    exact oneStep
  exact (prefix_block s pc).trace.trans hashStep

theorem afterHash_pc (hash : SigGolfCandidate.Legacy.Hash) (s : MachineState) (seed : MasterSeed)
    (pc : s.pc = 0x1000) : (afterHashState hash s seed).pc = 0x10d8 := by
  simp [afterHashState, writeHash, firstHash_pc s pc]

theorem afterHash_words (hash : SigGolfCandidate.Legacy.Hash) (s : MachineState) (seed : MasterSeed)
    (i : Fin 4) :
    (afterHashState hash s seed).getMem (BitVec.ofNat 64 (0x42000 + 8 * i.val)) =
      (hash (toQuery (keygenHashInput 0 .parameter seed))).extractLsb' (64 * i.val) 64 := by
  have dst := (firstHash_registers s).2.2.1
  fin_cases i <;> simp [afterHashState, writeHash, dst, MachineState.writeWords]

/-- The first 160 answer bits are the abstract seeded public parameter. -/
theorem afterHash_parameter (hash : SigGolfCandidate.Legacy.Hash) (s : MachineState) (seed : MasterSeed) :
    readBuffer (afterHashState hash s seed) 0x42000 20 =
      truncateHash (hash (toQuery (keygenHashInput 0 .parameter seed))) := by
  apply Memory.readBuffer_of_bytes
  intro i hi
  rw [SphincsVerifierFtsRootCopyBytes.getByte_word _ 0x42000 i (by decide) (by omega)]
  change extractByte ((afterHashState hash s seed).getMem
    (BitVec.ofNat 64 (0x42000 + 8 * (i / 8)))) (i % 8) = _
  rw [afterHash_words hash s seed ⟨i / 8, by omega⟩]
  rw [extractByte_slice _ ⟨i, by omega⟩]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by change 8 * i + 8 ≤ 160; omega)).symm

theorem afterHash_deriveKey (hash : SigGolfCandidate.Legacy.Hash) (s : MachineState) (seed : MasterSeed) :
    readBuffer (afterHashState hash s seed) 0x42000 20 =
      evalWithAnswerFn (adaptOracle hash)
        (deriveKey 0 .parameter seed : OracleComp SphincsSecurity.HashSpec Digest) := by
  rw [afterHash_parameter]
  have evalHash (input : SphincsSecurity.HashInput) :
      evalWithAnswerFn (adaptOracle hash)
        (Concrete.oracleHash input : OracleComp SphincsSecurity.HashSpec HashOutput) =
          adaptOracle hash input := by
    simp only [Concrete.oracleHash, HasQuery.query]
    exact simulateQ_spec_query (spec := SphincsSecurity.HashSpec) (r := Id) (adaptOracle hash) input
  simp only [deriveKey, evalWithAnswerFn_bind, evalWithAnswerFn_pure, evalHash]
  rfl

def entryState (seed : MasterSeed) : MachineState :=
  (({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords (BitVec.ofNat 64 0x20) (SigGolf.bytes (n := 32) seed)).setReg .x2 (BitVec.ofNat 64 0x1000000)

theorem entry_loaded (submission : Submission) (seed : MasterSeed)
    (image : submission.image .keygen = SphincsMaskedImages.keygen)
    (valid : (submission.image .keygen).Valid submission.sizes submission.layout)
    (address : submission.layout.secretKey = 0x20) :
    initialState submission .keygen seed = some (entryState seed) := by
  unfold initialState
  rw [if_pos valid]
  have hd : (submission.image .keygen).data = [] := by rw [image]; rfl
  have hb : dataBase (submission.image .keygen) = 0x1000000 := by rw [image]; decide
  simp only [hd, hb, inputBuffers, List.foldl_cons, List.foldl_nil, address]
  rw [MachineState.writeBytesAsWords]
  rfl

theorem entry_byte (seed : MasterSeed) (i : Nat) (hi : i < 32) :
    (entryState seed).getByte (BitVec.ofNat 64 (0x20 + i)) = seed.extractLsb' (8 * i) 8 := by
  simp only [entryState, Memory.getByte_setReg]
  exact Memory.write_value_byte _ 0x20 32 seed i (by decide) (by decide) hi

theorem entry_word (seed : MasterSeed) (i : Fin 4) :
    (entryState seed).getMem (BitVec.ofNat 64 (0x20 + 8 * i.val)) =
      seed.extractLsb' (64 * i.val) 64 := by
  apply eq_of_forall_extractByte
  intro j hj
  have whole : 8 * i.val + j < 32 := by omega
  have quot : (8 * i.val + j) / 8 = i.val := by omega
  have rem : (8 * i.val + j) % 8 = j := by omega
  have h := entry_byte seed (8 * i.val + j) whole
  rw [SphincsVerifierFtsRootCopyBytes.getByte_word _ 0x20 (8 * i.val + j) (by decide) (by omega)] at h
  simp only [quot, rem, SphincsVerifierFtsRootCopy.wordAddress] at h
  rw [h]
  symm
  simpa only [quot, rem] using extractByte_slice seed ⟨8 * i.val + j, whole⟩

theorem entry_zero (seed : MasterSeed) (i : Fin 3) :
    (entryState seed).getMem (BitVec.ofNat 64 (0x40010 + 8 * i.val)) = 0 := by
  simp only [entryState, MachineState.getMem_setReg]
  rw [Memory.write_preserves _ 0x20 (SigGolf.bytes (n := 32) seed) _ (by simp [SigGolf.bytes])]
  · rfl
  · right
    fin_cases i <;> simp [SigGolf.bytes]

theorem entry_pc (seed : MasterSeed) : (entryState seed).pc = 0x1000 := by
  simp only [entryState, MachineState.pc_setReg, MachineState.pc_writeBytesAsWords]

/-- The actual loader state executes the first seeded derivation with exact accounting. -/
theorem loaded_trace (hash : SigGolfCandidate.Legacy.Hash) (seed : MasterSeed) :
    Trace hash SphincsMaskedImages.keygen (entryState seed) 72 87 1 2
      (afterHashState hash (entryState seed) seed) :=
  firstHash_trace hash _ seed (entry_pc seed) (entry_zero seed) (entry_word seed)

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenPrefix.afterHash_deriveKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms afterHash_deriveKey

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenPrefix.loaded_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loaded_trace

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenPrefix.afterHash_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms afterHash_parameter

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenPrefix.firstHash_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstHash_trace

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenPrefix.firstHash_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstHash_input

end SigGolfCandidate.SphincsMaskedKeygenPrefix
