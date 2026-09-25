import SigGolfCandidate.SphincsMaskedParentLevels

namespace SigGolfCandidate.SphincsMaskedKeygenCommitment
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedParentCode SphincsMaskedParentLevels
open SphincsMaskedChainDomain SphincsMaskedSecretDomain SphincsMaskedLeafRefinement
open SphincsVerifierFtsRootCopy SphincsVerifierCopy SphincsVerifierCopyMemory
open SphincsVerifierFtsCopyAccess SphincsVerifierMessageCopy SphincsVerifierFtsPriorRoots
open SphincsBridge SphincsSecurity
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def rootCopied (s : MachineState) := copyRootState (rootSetup s)

theorem rootSetup_registers (s : MachineState) (base : s.getMem 0x43068 = 0x14060) :
    (rootSetup s).getReg .x6 = 0x14060 ∧ (rootSetup s).getReg .x7 = 0x60 := by
  change s.getMem 0x43068#64 = 0x14060 at base
  simp [rootSetup,runSchedule,rootSetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,base]

theorem rootSetup_frame (s : MachineState) (a : Word) : (rootSetup s).getMem a = s.getMem a := by
  simp [rootSetup,runSchedule,rootSetupSchedule,execInstrBr]

theorem root_copy_code : Copy20Code SphincsMaskedImages.keygen 555 := by
  constructor <;> intro i <;> fin_cases i <;> decide

theorem rootCopy_block (s : MachineState) (pc : s.pc = 0x189c) (base : s.getMem 0x43068 = 0x14060) :
    OrdinarySteps SphincsMaskedImages.keygen s 14 (rootCopied s) := by
  have regs := rootSetup_registers s base
  exact ordinary_trans _ _ _ _ 4 10 (rootSetup_block s pc)
    (copy20_block_general SphincsMaskedImages.keygen 555 root_copy_code (rootSetup s) 0x14060 0x60
      (rootSetup_pc s pc) regs.1 regs.2 (by decide) (by decide) (by decide) (by decide) (by decide))

theorem rootCopy_pc (s : MachineState) (pc : s.pc = 0x189c) : (rootCopied s).pc = 0x18d4 := by
  rw [rootCopied,SphincsMaskedParentNode.copyRoot_pc,rootSetup_pc s pc];rfl

theorem fixedCopy_data (s : MachineState) (src : s.getReg .x6 = 0x14060) (dst : s.getReg .x7 = 0x60) (i : Fin 5) :
    (copyRootState s).getWord32 (BitVec.ofNat 64 (0x60 + 4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x14060 + 4*i.val)) := by
  fin_cases i <;>
    simp [copyRootState,copyWordState,execInstrBr,src,dst,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,extractWord32]
  all_goals ext b hb;interval_cases b <;> simp [replaceWord32]

theorem rootCopy_value (s : MachineState) (root : BitVec 160) (base : s.getMem 0x43068 = 0x14060)
    (value : Words20 s 0x14060 root) : Words20 (rootCopied s) 0x60 root := by
  intro i
  have regs := rootSetup_registers s base
  rw [rootCopied,fixedCopy_data _ regs.1 regs.2 i]
  simpa only [MachineState.getWord32,rootSetup_frame] using value i

theorem rootCopy_key (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (base : s.getMem 0x43068 = 0x14060) (ctx : KeyContext s parameter seed) :
    KeyContext (rootCopied s) parameter seed := by
  obtain ⟨layer,tree,par,key⟩ := ctx
  have dst := (rootSetup_registers s base).2
  refine ⟨?_,?_,?_,?_⟩
  · change (copyRootState (rootSetup s)).getMem _ = _
    rw [copyRoot_mem_frame]
    · exact (rootSetup_frame s _).trans layer
    · intro i;rw [dst];fin_cases i <;> decide
  · change (copyRootState (rootSetup s)).getMem _ = _
    rw [copyRoot_mem_frame]
    · exact (rootSetup_frame s _).trans tree
    · intro i;rw [dst];fin_cases i <;> decide
  · intro i
    change (copyRootState (rootSetup s)).getWord32 _ = _
    rw [copyRoot_word_frame]
    · simpa only [MachineState.getWord32,rootSetup_frame] using par i
    · intro j;rw [dst];fin_cases i <;> fin_cases j <;> decide
  · intro i
    change (copyRootState (rootSetup s)).getWord32 _ = _
    rw [copyRoot_word_frame]
    · simpa only [MachineState.getWord32,rootSetup_frame] using key i
    · intro j;rw [dst];fin_cases i <;> fin_cases j <;> decide

def queryWord (s : MachineState) (i : Fin 15) : BitVec 32 :=
  if i.val = 0 then 3329
  else if i.val < 5 then 0
  else if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x60 + 4*(i.val-5)))
  else s.getWord32 (BitVec.ofNat 64 (0x74 + 4*(i.val-10)))

theorem prepare_words (s : MachineState) (i : Fin 15) :
    (commitPrepare s).getWord32 (BitVec.ofNat 64 (0x40000 + 4*i.val)) = queryWord s i := by
  fin_cases i <;>
    simp [commitPrepare,runSchedule,commitPrepareSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,extractWord32,queryWord]
  all_goals ext b hb;interval_cases b <;> simp [replaceWord32]

theorem prepare_registers (s : MachineState) :
    (commitPrepare s).getReg .x10 = 0x40000 ∧ (commitPrepare s).getReg .x11 = 480 ∧
      (commitPrepare s).getReg .x12 = 0x42000 ∧ (commitPrepare s).getReg .x5 = 1 := by
  simp [commitPrepare,runSchedule,commitPrepareSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

theorem prepared_byte (s : MachineState) (i : Fin 60) :
    (commitPrepare s).getByte (BitVec.ofNat 64 (0x40000 + i.val)) =
      (queryWord s ⟨i.val / 4,by omega⟩).extractLsb' (8*(i.val%4)) 8 := by
  have h := SphincsVerifierFtsGenericBytes.variableWord_byte (commitPrepare s)
    (0x40000 + 4*(i.val/4)) (by omega) (by omega) 0 ⟨i.val%4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  rw [show 0x40000 + 4*(i.val/4) + i.val%4 = 0x40000+i.val by omega] at h
  rw [h,prepare_words s ⟨i.val/4,by omega⟩]

theorem query_eq (s : MachineState) (parameter root : BitVec 160)
    (par : Words20 s 0x74 parameter) (val : Words20 s 0x60 root) :
    hashInput (commitPrepare s) = toQuery (SphincsWire.commitmentInput {root := root,parameter := parameter}) := by
  apply Serialization.hashInput_of_list (commitPrepare s) 0x40000
    ((SphincsWire.commitmentInput {root := root,parameter := parameter}).map UInt8.toBitVec)
  · exact (prepare_registers s).1
  · rw [List.length_map,SphincsWire.commitmentInput_length,(prepare_registers s).2.1];rfl
  · intro i hi
    have bound : i < 60 := by simpa only [List.length_map,SphincsWire.commitmentInput_length] using hi
    rw [prepared_byte s ⟨i,bound⟩]
    have p0 := par 0
    have p1 := par 1
    have p2 := par 2
    have p3 := par 3
    have p4 := par 4
    have v0 := val 0
    have v1 := val 1
    have v2 := val 2
    have v3 := val 3
    have v4 := val 4
    norm_num at p0 p1 p2 p3 p4 v0 v1 v2 v3 v4
    interval_cases i <;>
      simp [queryWord,p0,p1,p2,p3,p4,v0,v1,v2,v3,v4,SphincsWire.commitmentInput,
        fieldBytes,tweakFields,bytesLE,SphincsWire.digestBytes,protocolDomainSep]
    all_goals ext b hb;interval_cases b <;> simp [replaceWord32]

def answer (hash : Hash) (s : MachineState) := writeHash (commitPrepare s) (hash (hashInput (commitPrepare s)))

theorem hash_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x18d4) :
    Trace hash SphincsMaskedImages.keygen s 71 78 1 1 (answer hash s) := by
  obtain ⟨src,bits,dst,service⟩ := prepare_registers s
  have fetch : fetch SphincsMaskedImages.keygen (commitPrepare s) = some (.base .ECALL) := by
    rw [fetch_at,commitPrepare_pc s pc];decide
  have valid : hashArgumentsValid (commitPrepare s) = true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (commitPrepare s)).1 = 480 := by simp [hashInput,bits]
  have step := Trace.hash (hash := hash) (image := SphincsMaskedImages.keygen) (commitPrepare s) _ 0 0 0 0 fetch service valid (Trace.refl _)
  have hs : Trace hash SphincsMaskedImages.keygen (commitPrepare s) 1 8 1 1 (answer hash s) := by
    simp only [len] at step;exact step
  exact (commitPrepare_block s pc).trace.trans hs

theorem answer_pc (hash : Hash) (s : MachineState) (pc : s.pc = 0x18d4) : (answer hash s).pc = 0x19f0 := by
  simp [answer,writeHash,commitPrepare_pc s pc]

theorem copySetup_registers (s : MachineState) :
    (commitCopySetup s).getReg .x6 = 0x42000 ∧ (commitCopySetup s).getReg .x7 = 0x40 ∧
      (commitCopySetup s).getReg .x10 = 2 := by
  simp [commitCopySetup,runSchedule,commitCopySetupSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem copy_code : CopyCode SphincsMaskedImages.keygen 0x1a00 := by decide

theorem copy_result (s : MachineState) (pc : s.pc = 0x19f0) :
    ∃ final, OrdinarySteps SphincsMaskedImages.keygen s 16 final ∧ final.pc = 0x1a18 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x40 i.val) = s.getMem (wordAddress 0x42000 i.val)) ∧
      (∀ a, a ≠ 0x40#64 → a ≠ 0x48#64 → final.getMem a = s.getMem a) := by
  have regs := copySetup_registers s
  have inv : CopyInvariant 0x1a00 0x42000 0x40 2 2 (commitCopySetup s) :=
    ⟨by decide,by decide,commitCopySetup_pc s pc,regs.1,regs.2.1,regs.2.2⟩
  obtain ⟨final,trace,done,words,frame⟩ := copy_all SphincsMaskedImages.keygen 0x1a00 copy_code
    0x42000 0x40 2 (commitCopySetup s) inv (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))
  refine ⟨final,ordinary_trans _ _ _ _ 4 12 (commitCopySetup_block s pc) trace,done.2.2.1,?_,?_⟩
  · intro i
    rw [words i.val i.isLt]
    simp [commitCopySetup,runSchedule,commitCopySetupSchedule,execInstrBr]
  · intro a h0 h1
    rw [frame]
    · simp [commitCopySetup,runSchedule,commitCopySetupSchedule,execInstrBr]
    · intro i hi
      interval_cases i <;> simp_all [wordAddress]

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenCommitment.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_eq

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenCommitment.copy_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copy_result


theorem prepare_low_frame (s : MachineState) (a : Word) (low : a.toNat < 0x40000) :
    (commitPrepare s).getMem a = s.getMem a := by
  have h0 := SphincsMaskedParentDomain.low_ne a 0x43000#64 low (by decide)
  have h1 := SphincsMaskedParentDomain.low_ne a 0x43008#64 low (by decide)
  have h2 := SphincsMaskedParentDomain.low_ne a 0x43010#64 low (by decide)
  have h3 := SphincsMaskedParentDomain.low_ne a 0x43018#64 low (by decide)
  have h4 := SphincsMaskedParentDomain.low_ne a 0x40000#64 low (by decide)
  have h5 := SphincsMaskedParentDomain.low_ne a 0x40008#64 low (by decide)
  have h6 := SphincsMaskedParentDomain.low_ne a 0x40010#64 low (by decide)
  have h7 := SphincsMaskedParentDomain.low_ne a 0x40018#64 low (by decide)
  have h8 := SphincsMaskedParentDomain.low_ne a 0x40020#64 low (by decide)
  have h9 := SphincsMaskedParentDomain.low_ne a 0x40028#64 low (by decide)
  have h10 := SphincsMaskedParentDomain.low_ne a 0x40030#64 low (by decide)
  have h11 := SphincsMaskedParentDomain.low_ne a 0x40038#64 low (by decide)
  simp [commitPrepare,runSchedule,commitPrepareSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]

theorem answer_low_frame (hash : Hash) (s : MachineState) (a : Word) (low : a.toNat < 0x40000) :
    (answer hash s).getMem a = s.getMem a := by
  have h0 := SphincsMaskedParentDomain.low_ne a 0x42000#64 low (by decide)
  have h1 := SphincsMaskedParentDomain.low_ne a 0x42008#64 low (by decide)
  have h2 := SphincsMaskedParentDomain.low_ne a 0x42010#64 low (by decide)
  have h3 := SphincsMaskedParentDomain.low_ne a 0x42018#64 low (by decide)
  have dst := (prepare_registers s).2.2.1
  simp [answer,writeHash,dst,MachineState.writeWords,h0,h1,h2,h3]
  exact prepare_low_frame s a low

theorem prepare_controls (s : MachineState) :
    (commitPrepare s).getMem 0x43000 = 0 ∧ (commitPrepare s).getMem 0x43008 = 0 := by
  simp [commitPrepare,runSchedule,commitPrepareSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

theorem answer_key (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (ctx : KeyContext s parameter seed) : KeyContext (answer hash s) parameter seed := by
  have dst := (prepare_registers s).2.2.1
  refine ⟨?_,?_,?_,?_⟩
  · simp [answer,writeHash,dst,MachineState.writeWords];exact (prepare_controls s).1
  · simp [answer,writeHash,dst,MachineState.writeWords];exact (prepare_controls s).2
  · intro i
    simp only [MachineState.getWord32]
    rw [answer_low_frame hash s _ (by fin_cases i <;> decide)]
    exact ctx.2.2.1 i
  · intro i
    simp only [MachineState.getWord32]
    rw [answer_low_frame hash s _ (by fin_cases i <;> decide)]
    exact ctx.2.2.2 i

theorem answer_word (hash : Hash) (s : MachineState) (i : Fin 2) :
    (answer hash s).getMem (wordAddress 0x42000 i.val) =
      (hash (hashInput (commitPrepare s))).extractLsb' (64*i.val) 64 := by
  have dst := (prepare_registers s).2.2.1
  fin_cases i <;> simp [answer,writeHash,dst,MachineState.writeWords,wordAddress]

theorem cache_cell_lower (address : Nat) (lower : 0x88 ≤ address) (upper : address < 0x40000) :
    0x88 ≤ (alignToDword (BitVec.ofNat 64 address)).toNat := by
  have ha : (BitVec.ofNat 64 0x88).toNat % 8 = 0 := by decide
  have hover : (BitVec.ofNat 64 0x88).toNat + (address - 0x88) < 2 ^ 64 := by
    change 0x88 + (address - 0x88) < 2 ^ 64;omega
  have aligned := alignToDword_add_ofNat_of_aligned ha hover
  rw [← BitVec.ofNat_add] at aligned
  rw [show 0x88 + (address - 0x88) = address by omega] at aligned
  rw [aligned,← BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  omega

theorem rootCopy_cache_word (s : MachineState) (base : s.getMem 0x43068 = 0x14060)
    (address : Nat) (lower : 0x88 ≤ address) (upper : address < 0x40000) (aligned : address % 4 = 0) :
    (rootCopied s).getWord32 (BitVec.ofNat 64 address) = s.getWord32 (BitVec.ofNat 64 address) := by
  have dst := (rootSetup_registers s base).2
  change (copyRootState (rootSetup s)).getWord32 _ = _
  rw [copyRoot_word_frame]
  · simp only [MachineState.getWord32,rootSetup_frame]
  · intro i
    rw [dst]
    have location : (0x60 : Word) + signExtend12 (4#12 * BitVec.ofNat 12 i.val) = BitVec.ofNat 64 (0x60 + 4*i.val) := by
      fin_cases i <;> decide
    rw [location]
    exact wordLaneDistinct _ _ (by omega) (by omega) (by omega) aligned (by omega)

/-- The exact root copy and commitment leave the 128-bit public key in its organizer output slot. -/
theorem commitment_contract (hash : Hash) (s : MachineState) (parameter root : BitVec 160) (seed : MasterSeed)
    (pc : s.pc = 0x189c) (base : s.getMem 0x43068 = 0x14060)
    (ctx : KeyContext s parameter seed) (value : Words20 s 0x14060 root) :
    ∃ final, Trace hash SphincsMaskedImages.keygen s 101 108 1 1 final ∧ final.pc = 0x1a18 ∧
      KeyContext final parameter seed ∧ Words20 final 0x60 root ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x40 i.val) =
        (hash (toQuery (SphincsWire.commitmentInput {root := root,parameter := parameter}))).extractLsb' (64*i.val) 64) ∧
      (∀ address, 0x88 ≤ address → address < 0x40000 → address % 4 = 0 →
        final.getWord32 (BitVec.ofNat 64 address) = s.getWord32 (BitVec.ofNat 64 address)) := by
  have rootCtx := rootCopy_key s parameter seed base ctx
  have rootValue := rootCopy_value s root base value
  have rpc := rootCopy_pc s pc
  have apc := answer_pc hash (rootCopied s) rpc
  obtain ⟨final,copyTrace,finalPc,words,frame⟩ := copy_result (answer hash (rootCopied s)) apc
  have answerCtx := answer_key hash (rootCopied s) parameter seed rootCtx
  have finalCtx : KeyContext final parameter seed := by
    refine ⟨?_,?_,?_,?_⟩
    · exact (frame _ (by decide) (by decide)).trans answerCtx.1
    · exact (frame _ (by decide) (by decide)).trans answerCtx.2.1
    · intro i
      simp only [MachineState.getWord32]
      rw [frame _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
      exact answerCtx.2.2.1 i
    · intro i
      simp only [MachineState.getWord32]
      rw [frame _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
      exact answerCtx.2.2.2 i
  refine ⟨final,(rootCopy_block s pc base).trace.trans ((hash_trace hash (rootCopied s) rpc).trans copyTrace.trace),finalPc,finalCtx,?_,?_,?_⟩
  · intro i
    simp only [MachineState.getWord32]
    rw [frame _ (by fin_cases i <;> decide) (by fin_cases i <;> decide),
      answer_low_frame hash (rootCopied s) _ (by fin_cases i <;> decide)]
    exact rootValue i
  · intro i
    rw [words i,answer_word,query_eq (rootCopied s) parameter root rootCtx.2.2.1 rootValue]
  · intro address lower upper aligned
    have lowerCell := cache_cell_lower address lower upper
    have lowCell := SphincsMaskedParentDomain.low_cell address upper
    simp only [MachineState.getWord32]
    rw [frame _ (by intro eq;rw [eq] at lowerCell;exact (by decide : ¬ 0x88 ≤ (0x40#64).toNat) lowerCell)
      (by intro eq;rw [eq] at lowerCell;exact (by decide : ¬ 0x88 ≤ (0x48#64).toNat) lowerCell),answer_low_frame hash (rootCopied s) _ lowCell]
    exact rootCopy_cache_word s base address lower upper aligned

/-- Parent-tree computation through the public commitment, stopping before cache masking and MAC. -/
theorem parents_commitment (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (pc : s.pc = 0x15cc) (ctx : KeyContext s parameter seed)
    (leaves : ∀ leaf : LeafIndex, Words20 s (0x88 + 20*leaf.val) (leafValue hash parameter seed leaf)) :
    ∃ final, Trace hash SphincsMaskedImages.keygen s 254375 285087 2048 4095 final ∧ final.pc = 0x1a18 ∧
      KeyContext final parameter seed ∧
      let root := evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Seeded.treeRoot parameter topLayer Concrete.rootTree seed : OracleComp SphincsSecurity.HashSpec Digest)
      Words20 final 0x60 root ∧ (∀ i : Fin 2, final.getMem (wordAddress 0x40 i.val) =
        (hash (toQuery (SphincsWire.commitmentInput {root := root,parameter := parameter}))).extractLsb' (64*i.val) 64) := by
  obtain ⟨mid,treeTrace,loc,base,key,root⟩ := parents_root hash s parameter seed pc ctx leaves
  obtain ⟨final,commitTrace,finalPc,finalKey,rootValue,publicValue,_⟩ :=
    commitment_contract hash mid parameter _ seed loc base key root
  exact ⟨final,treeTrace.trans commitTrace,finalPc,finalKey,rootValue,publicValue⟩

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenCommitment.commitment_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms commitment_contract

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenCommitment.parents_commitment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parents_commitment

end SigGolfCandidate.SphincsMaskedKeygenCommitment
