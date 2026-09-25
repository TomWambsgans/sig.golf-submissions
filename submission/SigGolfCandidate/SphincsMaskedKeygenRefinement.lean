import SigGolfCandidate.SphincsMaskedMaskSemantics
import SigGolfCandidate.SphincsReadBufferBytes

namespace SigGolfCandidate.SphincsMaskedKeygenRefinement
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedChainDomain SphincsMaskedSecretDomain SphincsMaskedLeafRefinement
open SphincsVerifierFtsRootCopy SphincsBridge SphincsSecurity
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def readySchedule : List (Word × Instr) := [
  (0x10d8, .LUI .x6 66),
  (0x10dc, .ADDI .x6 .x6 (0)),
  (0x10e0, .ADDI .x7 .x0 (116)),
  (0x10e4, .LWU .x13 .x6 (0)),
  (0x10e8, .SW .x7 .x13 (0)),
  (0x10ec, .LWU .x13 .x6 (4)),
  (0x10f0, .SW .x7 .x13 (4)),
  (0x10f4, .LWU .x13 .x6 (8)),
  (0x10f8, .SW .x7 .x13 (8)),
  (0x10fc, .LWU .x13 .x6 (12)),
  (0x1100, .SW .x7 .x13 (12)),
  (0x1104, .LWU .x13 .x6 (16)),
  (0x1108, .SW .x7 .x13 (16)),
  (0x110c, .ADDI .x6 .x0 (0)),
  (0x1110, .LUI .x28 67),
  (0x1114, .ADDI .x28 .x28 (32)),
  (0x1118, .SD .x28 .x6 (0))]

def ready (s : MachineState) := runSchedule readySchedule s

theorem ready_code : ∀ e ∈ readySchedule, instructionAt SphincsMaskedImages.keygen e.1 = some (.base e.2) := by decide

theorem ready_checked (s : MachineState) (pc : s.pc=0x10d8) : Checked readySchedule s := by
  simp [readySchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,pc]

theorem ready_block (s : MachineState) (pc : s.pc=0x10d8) :
    OrdinarySteps SphincsMaskedImages.keygen s 17 (ready s) :=
  checked_sound _ readySchedule ready_code s (ready_checked s pc)

theorem ready_pc (s : MachineState) (pc : s.pc=0x10d8) : (ready s).pc=0x111c := by
  simp [ready,runSchedule,readySchedule,execInstrBr,MachineState.setWord32,pc]

theorem ready_counter (s : MachineState) : (ready s).getMem 0x43020=0 := by
  simp [ready,runSchedule,readySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,MachineState.setWord32]

theorem ready_parameter_words (s : MachineState) (i : Fin 5) :
    (ready s).getWord32 (BitVec.ofNat 64 (0x74+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) := by
  fin_cases i <;> simp [ready,runSchedule,readySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

def parameter (hash : Hash) (seed : MasterSeed) : Digest :=
  truncateHash (hash (toQuery (keygenHashInput 0 .parameter seed)))

theorem afterHash_answer_words (hash : Hash) (s : MachineState) (seed : MasterSeed) (i : Fin 5) :
    (afterHashState hash s seed).getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) =
      (hash (toQuery (keygenHashInput 0 .parameter seed))).extractLsb' (32*i.val) 32 := by
  have dst := (firstHash_registers s).2.2.1
  fin_cases i <;> simp [afterHashState,writeHash,dst,MachineState.writeWords,
    MachineState.getWord32,alignToDword,byteOffset,extractWord32]
  all_goals ext j hj;interval_cases j <;> simp

theorem afterHash_parameter_words (hash : Hash) (s : MachineState) (seed : MasterSeed) :
    Words20 (afterHashState hash s seed) 0x42000 (parameter hash seed) := by
  intro i
  rw [afterHash_answer_words]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm


theorem entry_words32 (seed : MasterSeed) : Words32 (entryState seed) seed := by
  intro i
  have k0 := entry_word seed 0
  have k1 := entry_word seed 1
  have k2 := entry_word seed 2
  have k3 := entry_word seed 3
  norm_num at k0 k1 k2 k3
  fin_cases i <;> simp [MachineState.getWord32,alignToDword,byteOffset,k0,k1,k2,k3,extractWord32]
  all_goals ext j hj;interval_cases j <;> simp

def leavesEntry (hash : Hash) (seed : MasterSeed) := ready (afterHashState hash (entryState seed) seed)

theorem firstHash_key_frame (s : MachineState) (i : Fin 8) :
    (firstHashState s).getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) := by
  fin_cases i <;> simp [firstHashState,runSchedule,prefixSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

theorem firstHash_controls (s : MachineState) :
    (firstHashState s).getMem 0x43000=0 ∧ (firstHashState s).getMem 0x43008=0 := by
  simp [firstHashState,runSchedule,prefixSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,MachineState.setWord32,alignToDword,byteOffset]

theorem afterHash_controls (hash : Hash) (s : MachineState) (seed : MasterSeed) :
    (afterHashState hash s seed).getMem 0x43000=0 ∧ (afterHashState hash s seed).getMem 0x43008=0 := by
  have dst := (firstHash_registers s).2.2.1
  simpa [afterHashState,writeHash,dst,MachineState.writeWords] using firstHash_controls s

theorem afterHash_key_frame (hash : Hash) (s : MachineState) (seed : MasterSeed) (i : Fin 8) :
    (afterHashState hash s seed).getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) := by
  have dst := (firstHash_registers s).2.2.1
  have frame : (afterHashState hash s seed).getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) =
      (firstHashState s).getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) := by
    fin_cases i <;> simp [afterHashState,writeHash,dst,MachineState.writeWords,
      MachineState.getWord32,alignToDword,byteOffset]
  exact frame.trans (firstHash_key_frame s i)

theorem ready_controls (s : MachineState) :
    (ready s).getMem 0x43000=s.getMem 0x43000 ∧ (ready s).getMem 0x43008=s.getMem 0x43008 := by
  simp [ready,runSchedule,readySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,MachineState.setWord32,alignToDword,byteOffset]

theorem ready_key_frame (s : MachineState) (i : Fin 8) :
    (ready s).getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) = s.getWord32 (BitVec.ofNat 64 (0x20+4*i.val)) := by
  fin_cases i <;> simp [ready,runSchedule,readySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

theorem leavesEntry_context (hash : Hash) (seed : MasterSeed) :
    KeyContext (leavesEntry hash seed) (parameter hash seed) seed := by
  have before := afterHash_controls hash (entryState seed) seed
  have after := ready_controls (afterHashState hash (entryState seed) seed)
  refine ⟨after.1.trans before.1,after.2.trans before.2,?_,?_⟩
  · intro i
    rw [leavesEntry,ready_parameter_words]
    exact afterHash_parameter_words hash (entryState seed) seed i
  · intro i
    rw [leavesEntry,ready_key_frame,afterHash_key_frame]
    exact entry_words32 seed i


theorem leavesEntry_trace (hash : Hash) (seed : MasterSeed) :
    Trace hash SphincsMaskedImages.keygen (entryState seed) 89 104 1 2 (leavesEntry hash seed) ∧
      (leavesEntry hash seed).pc=0x111c ∧ (leavesEntry hash seed).getMem 0x43020=0 := by
  have pc := afterHash_pc hash (entryState seed) seed (entry_pc seed)
  exact ⟨(loaded_trace hash seed).trans (ready_block _ pc).trace,ready_pc _ pc,ready_counter _⟩

def root (hash : Hash) (seed : MasterSeed) : Digest :=
  evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
    (Seeded.treeRoot (parameter hash seed) topLayer Concrete.rootTree seed : OracleComp SphincsSecurity.HashSpec Digest)

def publicKey (hash : Hash) (seed : MasterSeed) : SigGolf.PublicKey :=
  (hash (toQuery (SphincsWire.commitmentInput {root := root hash seed,parameter := parameter hash seed}))).extractLsb' 0 128

def flatNode (level node : Nat) : Nat := 4096-2^(12-level)+node

theorem flatNode_bounds (level : Fin 12) (node : Nat) (bound : node<SphincsMaskedParentLevels.width level.val) :
    flatNode level.val node<4095 ∧
      SphincsMaskedParentLevels.cacheBase level.val+20*node = 0x88+20*flatNode level.val node := by
  fin_cases level <;> norm_num [flatNode,SphincsMaskedParentLevels.width,SphincsMaskedParentLevels.cacheBase] at bound ⊢ <;> omega

structure FinalSemantics (hash : Hash) (seed : MasterSeed) (s : MachineState) : Prop where
  publicWords : ∀ i : Fin 4, s.getWord32 (BitVec.ofNat 64 (0x40+4*i.val)) = (publicKey hash seed).extractLsb' (32*i.val) 32
  parameterWords : Words20 s 0x74 (parameter hash seed)
  rootWords : Words20 s 0x60 (root hash seed ^^^ SphincsMaskedMaskSemantics.padValue hash (parameter hash seed) seed 4094)
  nodes : ∀ level : Fin 12, ∀ node, node<SphincsMaskedParentLevels.width level.val →
    Words20 s (SphincsMaskedParentLevels.cacheBase level.val+20*node)
      (SphincsMaskedParentLevels.treeValue hash (parameter hash seed) seed level.val node ^^^
        SphincsMaskedMaskSemantics.padValue hash (parameter hash seed) seed (flatNode level.val node))
  tag : Words20 s 0x2004c (truncateHash (hash (toQuery (SphincsCacheSecretDomains.macInput (parameter hash seed) seed
    (SphincsMaskedMacDomain.ciphertext s)))))

theorem commitment_words32 (s : MachineState) (value : BitVec 256)
    (words : ∀ i : Fin 2, s.getMem (wordAddress 0x40 i.val) = value.extractLsb' (64*i.val) 64) (i : Fin 4) :
    s.getWord32 (BitVec.ofNat 64 (0x40+4*i.val)) = value.extractLsb' (32*i.val) 32 := by
  have h0 := words 0
  have h1 := words 1
  norm_num [wordAddress] at h0 h1
  fin_cases i <;> simp [MachineState.getWord32,alignToDword,byteOffset,h0,h1,extractWord32]
  all_goals ext j hj;interval_cases j <;> simp

/-- Complete concrete execution of the exact masked keygen image from the beta loader state. -/
theorem keygen_executes (hash : Hash) (seed : MasterSeed) :
    ∃ final, Executes hash SphincsMaskedImages.keygen (entryState seed) 85168809
      ⟨.success,final,92369576,860161,1007616⟩ ∧ FinalSemantics hash seed final := by
  obtain ⟨firstTrace,pc,count⟩ := leavesEntry_trace hash seed
  obtain ⟨leaves,leafTrace,leafCount,leafPc,leafKey,leafValues⟩ := leaves_contract hash (leavesEntry hash seed)
    (parameter hash seed) seed (leavesEntry_context hash seed) pc count 2048 (by decide)
  have leafLocation : leaves.pc=0x15cc := by simpa using leafPc
  obtain ⟨parents,parentTrace,parentPc,parentBase,parentKey,parentValues⟩ :=
    SphincsMaskedParentLevels.parents_contract hash leaves (parameter hash seed) seed leafLocation leafKey
      (fun leaf => leafValues leaf leaf.isLt)
  have rootValue : Words20 parents 0x14060 (root hash seed) := parentValues 11 (by decide) 0 (by decide)
  obtain ⟨committed,commitTrace,commitPc,commitKey,commitRoot,commitPublic,commitFrame⟩ :=
    SphincsMaskedKeygenCommitment.commitment_contract hash parents (parameter hash seed) (root hash seed) seed
      parentPc parentBase parentKey rootValue
  let final := SphincsMaskedKeygenTail.final hash committed
  have done := SphincsMaskedKeygenTail.tail_executes hash committed commitPc
  have trace := firstTrace.trans (leafTrace.trans (parentTrace.trans commitTrace))
  refine ⟨final,?_,?_⟩
  · simpa [Execution.charge] using trace.then_executes done
  have finalValues := SphincsMaskedMaskSemantics.final_values hash committed commitPc (parameter hash seed) seed commitKey.2.2.1 commitKey.2.2.2
  refine ⟨?_,finalValues.1,?_,?_,finalValues.2.2.2.2⟩
  · intro i
    rw [SphincsMaskedMaskSemantics.final_protected_word hash committed commitPc _ (by omega) (by omega)
      (Or.inl (by omega)) (Or.inl (by omega)),commitment_words32 committed _ commitPublic i]
    exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm
  · apply SphincsMaskedMaskSemantics.final_root_value hash committed commitPc (parameter hash seed) seed
      commitKey.2.2.1 commitKey.2.2.2
    intro i
    rw [commitFrame _ (by omega) (by omega) (by omega)]
    exact rootValue i
  · intro level node bound
    obtain ⟨nodeBound,address⟩ := flatNode_bounds level node bound
    let index : Fin 4095 := ⟨flatNode level.val node,nodeBound⟩
    have plain : Words20 committed (0x88+20*index.val)
        (SphincsMaskedParentLevels.treeValue hash (parameter hash seed) seed level.val node) := by
      rw [← address]
      intro i
      rw [commitFrame _ (by rw [address];omega) (by rw [address];omega) (by rw [address];omega)]
      exact parentValues level.val (by omega) node bound i
    rw [address]
    exact SphincsMaskedMaskSemantics.final_node_value hash committed commitPc (parameter hash seed) seed
      commitKey.2.2.1 commitKey.2.2.2 index _ plain

theorem read_publicKey (hash : Hash) (seed : MasterSeed) (s : MachineState) (sem : FinalSemantics hash seed s) :
    readBuffer s 0x40 16=publicKey hash seed := by
  apply Memory.readBuffer_of_bytes
  intro i hi
  have byte := SphincsVerifierFtsGenericBytes.variableWord_byte s (0x40+4*(i/4))
    (by omega) (by omega) 0 ⟨i%4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at byte
  rw [show 0x40+4*(i/4)+i%4=0x40+i by omega] at byte
  rw [byte,sem.publicWords ⟨i/4,by omega⟩]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have inside : 8*(i%4)+j<32 := by omega
  simp [BitVec.getLsbD_extractLsb',hj,inside,show 32*(i/4)+(8*(i%4)+j)=8*i+j by omega]

def cacheCiphertext (cache : SigGolf.Cache) : SphincsSecurity.HashInput :=
  List.ofFn fun i : Fin 131052 => UInt8.ofBitVec (cache.extractLsb' (8*i.val) 8)

structure CacheSemantics (hash : Hash) (seed : MasterSeed) (cache : SigGolf.Cache) : Prop where
  parameterWords : cache.extractLsb' (8*20) 160=parameter hash seed
  rootWords : cache.extractLsb' 0 160=root hash seed ^^^ SphincsMaskedMaskSemantics.padValue hash (parameter hash seed) seed 4094
  nodes : ∀ level : Fin 12, ∀ node, node<SphincsMaskedParentLevels.width level.val →
    cache.extractLsb' (8*(SphincsMaskedParentLevels.cacheBase level.val+20*node-0x60)) 160=
      SphincsMaskedParentLevels.treeValue hash (parameter hash seed) seed level.val node ^^^
        SphincsMaskedMaskSemantics.padValue hash (parameter hash seed) seed (flatNode level.val node)
  tag : cache.extractLsb' (8*131052) 160=truncateHash (hash (toQuery
    (SphincsCacheSecretDomains.macInput (parameter hash seed) seed (cacheCiphertext cache))))

theorem read_words20 (s : MachineState) (offset : Nat) (value : BitVec 160)
    (bound : offset+20≤CACHE_BYTES) (aligned : offset%4=0)
    (words : Words20 s (0x60+offset) value) :
    (readBuffer s 0x60 CACHE_BYTES).extractLsb' (8*offset) 160=value := by
  apply SphincsReadBufferBytes.readBuffer_slice_of_bytes s 0x60 CACHE_BYTES offset 20 value bound
  intro i hi
  exact SphincsMaskedPublicKeyDomain.words20_byte s (0x60+offset) value (by dsimp [CACHE_BYTES] at bound;omega) (by omega) words ⟨i,hi⟩

theorem read_ciphertext (s : MachineState) :
    cacheCiphertext (readBuffer s 0x60 CACHE_BYTES)=SphincsMaskedMacDomain.ciphertext s := by
  apply congrArg List.ofFn
  funext i
  rw [SphincsReadBufferBytes.readBuffer_byte s 0x60 CACHE_BYTES i.val (by dsimp [CACHE_BYTES];omega)]

theorem read_cache (hash : Hash) (seed : MasterSeed) (s : MachineState) (sem : FinalSemantics hash seed s) :
    CacheSemantics hash seed (readBuffer s 0x60 CACHE_BYTES) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact read_words20 s 20 _ (by decide) (by decide) sem.parameterWords
  · exact read_words20 s 0 _ (by decide) (by decide) sem.rootWords
  · intro level node bound
    obtain ⟨small,address⟩ := flatNode_bounds level node bound
    apply read_words20 s _ _ (by rw [address];dsimp [CACHE_BYTES];omega) (by rw [address];omega)
    rw [show 0x60+(SphincsMaskedParentLevels.cacheBase level.val+20*node-0x60)=
      SphincsMaskedParentLevels.cacheBase level.val+20*node by rw [address];omega]
    exact sem.nodes level node bound
  · rw [read_ciphertext]
    exact read_words20 s 131052 _ (by decide) (by decide) sem.tag

/-- Organizer-level keygen refinement for any submission using this exact image and standard
keygen input/output addresses. The returned cache fields and full ciphertext MAC are explicit. -/
theorem keygen_runWith (submission : Submission) (hash : Hash) (seed : MasterSeed)
    (image : submission.image .keygen=SphincsMaskedImages.keygen)
    (valid : (submission.image .keygen).Valid submission.sizes submission.layout)
    (secretAddress : submission.layout.secretKey=0x20)
    (publicAddress : submission.layout.publicKey=0x40) (cacheAddress : submission.layout.cache=0x60) :
    ∃ cache : SigGolf.Cache,
      submission.runWith hash .keygen seed=⟨some (publicKey hash seed,cache),true,92369576,860161,1007616⟩ ∧
      CacheSemantics hash seed cache := by
  obtain ⟨final,run,sem⟩ := keygen_executes hash seed
  have loaded := entry_loaded submission seed image valid secretAddress
  have exactRun : Executes hash (submission.image .keygen) (entryState seed) 85168809
      ⟨.success,final,92369576,860161,1007616⟩ := by rw [image];exact run
  have result := runWith_of_executes submission hash .keygen seed (entryState seed) 85168809
    ⟨.success,final,92369576,860161,1007616⟩ loaded exactRun (by decide)
  refine ⟨readBuffer final 0x60 CACHE_BYTES,?_,read_cache hash seed final sem⟩
  simpa [readOutput,publicAddress,cacheAddress,read_publicKey hash seed final sem,
    show (Exit.success != Exit.unfinished)=true by decide] using result

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenRefinement.leavesEntry_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leavesEntry_context

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenRefinement.keygen_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygen_executes

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenRefinement.keygen_runWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygen_runWith

end SigGolfCandidate.SphincsMaskedKeygenRefinement
