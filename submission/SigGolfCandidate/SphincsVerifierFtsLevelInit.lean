import SigGolfCandidate.SphincsVerifierFtsResult

/-! Enter the first FORS authentication-path level with the copied leaf root intact. -/

namespace SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierFtsResult
set_option maxRecDepth 16384

def levelInitState (state : MachineState) : MachineState :=
  let state := execInstrBr state (.ADDI .x6 .x0 1)
  let state := execInstrBr state (.LUI .x28 0x43)
  let state := execInstrBr state (.ADDI .x28 .x28 72)
  execInstrBr state (.SD .x28 .x6 0)

theorem levelInit_pc (state : MachineState) (pc : state.pc = 0x1904) :
    (levelInitState state).pc = 0x1914 := by
  simp [levelInitState, execInstrBr, pc]

theorem levelInit_block (state : MachineState) (pc : state.pc = 0x1904) :
    OrdinarySteps SphincsImages.verify state 4 (levelInitState state) := by
  let s1 := execInstrBr state (.ADDI .x6 .x0 1)
  let s2 := execInstrBr s1 (.LUI .x28 0x43)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 72)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  have p1 : s1.pc = 0x1908 := by simp [s1, execInstrBr, pc]
  have p2 : s2.pc = 0x190c := by simp [s2, execInstrBr, p1]
  have p3 : s3.pc = 0x1910 := by simp [s3, execInstrBr, p2]
  apply OrdinarySteps.step state s1 _ (.base (.ADDI .x6 .x0 1)) 3
  · rw [fetch_index SphincsImages.verify state 577 (by decide)
      (by simpa using pc)]
    decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x43)) 2
  · rw [fetch_index SphincsImages.verify s1 578 (by decide)
      (by simpa using p1)]
    decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 72)) 1
  · rw [fetch_index SphincsImages.verify s2 579 (by decide)
      (by simpa using p2)]
    decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 0
  · rw [fetch_index SphincsImages.verify s3 580 (by decide)
      (by simpa using p3)]
    decide
  · simp [s4, ordinaryStep, memoryArgumentsValid, accessValid,
      rangeValid, MEMORY_BYTES, s1, s2, s3, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem levelInit_mem (state : MachineState) (address : Word) :
    (levelInitState state).getMem address =
      if address = 0x43048 then 1 else state.getMem address := by
  simp [levelInitState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem levelInit_level (state : MachineState) :
    (levelInitState state).getMem 0x43048 = 1 := by
  simp [levelInit_mem]

theorem levelInit_current (state : MachineState) (i : Nat) (hi : i < 20) :
    (levelInitState state).getByte (BitVec.ofNat 64 (0x44a00 + i)) =
      state.getByte (BitVec.ofNat 64 (0x44a00 + i)) := by
  simp only [MachineState.getByte]
  rw [levelInit_mem]
  have separate : alignToDword (BitVec.ofNat 64 (0x44a00 + i)) ≠
      (274504#64) := by
    interval_cases i <;> decide
  split_ifs with equal
  · exact False.elim (separate equal)
  · rfl

theorem levelInit_lowByte_frame (state : MachineState) (address : Word)
    (low : (alignToDword address).toNat < 0x40000) :
    (levelInitState state).getByte address = state.getByte address := by
  simp only [MachineState.getByte]
  rw [levelInit_mem]
  have separate : alignToDword address ≠ (274504#64) := by
    intro equal
    have values := congrArg BitVec.toNat equal
    have fixed : (274504#64 : Word).toNat = 274504 := by decide
    rw [fixed] at values
    omega
  split_ifs with equal
  · exact False.elim (separate equal)
  · rfl

theorem levelInit_allWitness_frame (state : MachineState) (i : Nat)
    (hi : i < SphincsWire.signatureBytes) :
    (levelInitState state).getByte (BitVec.ofNat 64 (0x22ca0 + i)) =
      state.getByte (BitVec.ofNat 64 (0x22ca0 + i)) := by
  let address : Word := BitVec.ofNat 64 (0x22ca0 + i)
  have low : (alignToDword address).toNat < 0x40000 := by
    have length := SphincsWire.signatureBytes_eq
    have small : 0x22ca0 + i < 2 ^ 64 := by omega
    have range : 0x22ca0 + i < 0x40000 := by omega
    have aligned : (alignToDword address).toNat ≤ address.toNat := by
      unfold alignToDword
      rw [BitVec.toNat_and]
      exact Nat.and_le_left
    have exactAddress : address.toNat = 0x22ca0 + i := by
      simp only [address, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt small
    omega
  exact levelInit_lowByte_frame state address low

theorem levelInit_preserve_FtsWitness (state : MachineState)
    (signature : SphincsSecurity.Signature)
    (witness : SphincsVerifierFtsEarlyFrame.FtsWitness state signature) :
    SphincsVerifierFtsEarlyFrame.FtsWitness (levelInitState state)
      signature := by
  apply SphincsVerifierFtsEarlyFrame.FtsWitness.transport
    state _ signature witness
  intro i hi
  exact levelInit_allWitness_frame state i hi

theorem firstFtsLevelStart (state : MachineState)
    (signature : SphincsSecurity.Signature) (answer : BitVec 256)
    (pc : state.pc = 0x18c8)
    (source : state.getReg .x10 = 0x40000)
    (bits : state.getReg .x11 = 480)
    (destination : state.getReg .x12 = 0x42000)
    (witness : SphincsVerifierFtsEarlyFrame.FtsWitness state signature) :
    let hashed := writeHash state answer
    let start := levelInitState (resultState hashed)
    OrdinarySteps SphincsImages.verify hashed 18 start ∧
      start.pc = 0x1914 ∧
      start.getMem 0x43048 = 1 ∧
      SphincsVerifierFtsEarlyFrame.FtsWitness start signature ∧
      ∀ i, (hi : i < 20) →
        start.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
          (SphincsSecurity.truncateHash answer).extractLsb' (8 * i) 8 := by
  let hashed := writeHash state answer
  let copied := resultState hashed
  let start := levelInitState copied
  obtain ⟨_, _, copiedTrace, copiedPc, copiedWitness, copiedBytes⟩ :=
    firstFtsHash_result state signature answer pc source bits destination witness
  exact ⟨by simpa [start, copied] using
      copiedTrace.append (levelInit_block copied copiedPc),
    levelInit_pc copied copiedPc,
    levelInit_level copied,
    levelInit_preserve_FtsWitness copied signature copiedWitness,
    fun i hi => (levelInit_current copied i hi).trans (copiedBytes i hi)⟩

theorem hashReady_mem_frame (state : MachineState) (address : Word)
    (notTag : address ≠ alignToDword (0x40000#64))
    (notPosition : address ≠ alignToDword (0x40004#64))
    (notTree : address ≠ 0x40008)
    (notIndex : address ≠ alignToDword (0x40010#64))
    (notCopy : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x40014 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val))) :
    (SphincsVerifierFtsSetup.ftsHashReadyState state).getMem address =
      state.getMem address := by
  let tagged := SphincsVerifierFtsHeader.tagState state
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  let header := SphincsVerifierFtsHeader.headerState state
  let pointers := SphincsVerifierFtsParameter.parameterPointers header
  have tagPointer : tagged.getReg .x7 = 0x40000 :=
    SphincsVerifierFtsHeader.tag_hash_pointer state
  have positionPointer : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagPointer
  have treePointer : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionPointer
  have tagFrame : tagged.getMem address = state.getMem address := by
    simp [tagged, SphincsVerifierFtsHeader.tagState,
      SphincsVerifierFtsHeader.tagBeforeStore, execInstrBr,
      signExtend12, setWord32_eq,
      MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, notTag]
  have positionFrame : positioned.getMem address = tagged.getMem address := by
    simp [positioned, SphincsVerifierHeader.positionState,
      SphincsVerifierHeader.positionBeforeStore, execInstrBr,
      signExtend12, setWord32_eq, tagPointer, notPosition,
      MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  have treeFrame : treed.getMem address = positioned.getMem address := by
    simp [treed, SphincsVerifierHeader.treeState,
      SphincsVerifierHeader.treeBeforeStore, execInstrBr,
      signExtend12, positionPointer, notTree,
      MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
    intro h
    exact (notTree h).elim
  have indexFrame : header.getMem address = treed.getMem address := by
    change (SphincsVerifierHeader.indexState treed).getMem address = _
    simp [SphincsVerifierHeader.indexState,
      SphincsVerifierHeader.indexBeforeStore, execInstrBr,
      signExtend12, setWord32_eq, treePointer, notIndex,
      MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  have copiedFrame : (SphincsVerifierCopy.copyRootState pointers).getMem
      address = pointers.getMem address := by
    apply SphincsVerifierCopyMemory.copyRoot_mem_frame
    intro offset
    rw [(SphincsVerifierFtsParameter.parameterPointers_regs header).2]
    exact notCopy offset
  change (SphincsVerifierFtsSetup.hashRegistersState
    (SphincsVerifierCopy.copyRootState pointers)).getMem address = _
  rw [SphincsVerifierFtsWitnessFrame.firstFtsHashRegisters_mem_frame,
    copiedFrame,
    SphincsVerifierFtsWitnessFrame.firstFtsParameterPointers_mem_frame,
    indexFrame, treeFrame, positionFrame, tagFrame]

theorem hashReady_pointer_frame (state : MachineState) :
    (SphincsVerifierFtsSetup.ftsHashReadyState state).getMem 0x43028 =
      state.getMem 0x43028 := by
  apply hashReady_mem_frame
  all_goals try { intro offset; fin_cases offset <;> decide }
  all_goals decide

theorem hashReady_selector_frame (state : MachineState) :
    (SphincsVerifierFtsSetup.ftsHashReadyState state).getMem 0x43070 =
      state.getMem 0x43070 := by
  apply hashReady_mem_frame
  all_goals try { intro offset; fin_cases offset <;> decide }
  all_goals decide

theorem hashReady_counter_frame (state : MachineState) :
    (SphincsVerifierFtsSetup.ftsHashReadyState state).getMem 0x43040 =
      state.getMem 0x43040 := by
  apply hashReady_mem_frame
  all_goals try { intro offset; fin_cases offset <;> decide }
  all_goals decide

theorem writeHash_mem_frame (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) (address : Word)
    (not0 : address ≠ 0x42000) (not8 : address ≠ 0x42008)
    (not16 : address ≠ 0x42010) (not24 : address ≠ 0x42018) :
    (writeHash state answer).getMem address = state.getMem address := by
  change address ≠ (270336#64) at not0
  change address ≠ (270344#64) at not8
  change address ≠ (270352#64) at not16
  change address ≠ (270360#64) at not24
  simp [writeHash, MachineState.writeWords, destination,
    MachineState.getMem_setMem_ne, not0, not8, not16, not24]

theorem result_mem_frame (state : MachineState) (address : Word)
    (outside : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x44a00 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val))) :
    (resultState state).getMem address = state.getMem address := by
  change (SphincsVerifierCopy.copyRootState
    (resultPointers state)).getMem address = _
  rw [SphincsVerifierCopyMemory.copyRoot_mem_frame]
  · exact resultPointers_mem state address
  · intro offset
    rw [(resultPointers_regs state).2]
    exact outside offset

theorem levelStart_mem_frame (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) (address : Word)
    (notLevel : address ≠ 0x43048)
    (not0 : address ≠ 0x42000) (not8 : address ≠ 0x42008)
    (not16 : address ≠ 0x42010) (not24 : address ≠ 0x42018)
    (notCopy : ∀ offset : Fin 5,
      address ≠ alignToDword
        (0x44a00 + signExtend12
          (4#12 * BitVec.ofNat 12 offset.val))) :
    (levelInitState (resultState (writeHash state answer))).getMem address =
      state.getMem address := by
  rw [levelInit_mem, if_neg notLevel,
    result_mem_frame _ address notCopy,
    writeHash_mem_frame state answer destination address not0 not8 not16 not24]

theorem levelStart_pointer_frame (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (levelInitState (resultState (writeHash state answer))).getMem 0x43028 =
      state.getMem 0x43028 := by
  apply levelStart_mem_frame state answer destination
  all_goals try { intro offset; fin_cases offset <;> decide }
  all_goals decide

theorem levelStart_selector_frame (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (levelInitState (resultState (writeHash state answer))).getMem 0x43070 =
      state.getMem 0x43070 := by
  apply levelStart_mem_frame state answer destination
  all_goals try { intro offset; fin_cases offset <;> decide }
  all_goals decide

theorem levelStart_counter_frame (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000) :
    (levelInitState (resultState (writeHash state answer))).getMem 0x43040 =
      state.getMem 0x43040 := by
  apply levelStart_mem_frame state answer destination
  all_goals try { intro offset; fin_cases offset <;> decide }
  all_goals decide

theorem firstFts_levelStart_scratch (advanced : MachineState)
    (answer : BitVec 256) :
    let ready := SphincsVerifierFtsSetup.ftsHashReadyState advanced
    let start := levelInitState (resultState (writeHash ready answer))
    start.getMem 0x43028 = advanced.getMem 0x43028 ∧
      start.getMem 0x43070 = advanced.getMem 0x43070 ∧
      start.getMem 0x43040 = advanced.getMem 0x43040 := by
  let ready := SphincsVerifierFtsSetup.ftsHashReadyState advanced
  have destination : ready.getReg .x12 = 0x42000 :=
    (SphincsVerifierFtsSetup.ftsHashReady_regs advanced).2.2.1
  exact ⟨(levelStart_pointer_frame ready answer destination).trans
      (hashReady_pointer_frame advanced),
    (levelStart_selector_frame ready answer destination).trans
      (hashReady_selector_frame advanced),
    (levelStart_counter_frame ready answer destination).trans
      (hashReady_counter_frame advanced)⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLevelInit.firstFtsLevelStart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms firstFtsLevelStart

end SigGolfCandidate.SphincsVerifierFtsLevelInit
