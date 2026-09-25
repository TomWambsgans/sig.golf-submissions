import SigGolfCandidate.SphincsMaskedKeygenTail

namespace SigGolfCandidate.SphincsMaskedMaskSemantics
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedMaskCode SphincsMaskedMaskNode SphincsMaskedMaskXor
open SphincsMaskedMaskLoop SphincsMaskedChainDomain SphincsMaskedSecretDomain SphincsMaskedLeafRefinement
open SphincsVerifierFtsRootCopy SphincsSecurity SphincsBridge SphincsCacheSecretDomains
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem applyXor_word_frame (s : MachineState) (base read : Nat)
    (ptr : s.getReg .x6 = BitVec.ofNat 64 base) (small : base+20 < 2^64)
    (readSmall : read<2^64) (aligned : base%4=0) (readAligned : read%4=0)
    (outside : ∀ i : Fin 5, base+4*i.val ≠ read) :
    (applyXor s).getWord32 (BitVec.ofNat 64 read) = s.getWord32 (BitVec.ofNat 64 read) := by
  rw [applyXor_eq]
  rw [xorWord_lane_frame 4 _ base read (by simp [xorWord,execInstrBr,MachineState.getReg_setReg_ne,MachineState.setWord32,ptr])
    small readSmall aligned readAligned (outside 4)]
  rw [xorWord_lane_frame 3 _ base read (by simp [xorWord,execInstrBr,MachineState.getReg_setReg_ne,MachineState.setWord32,ptr])
    small readSmall aligned readAligned (outside 3)]
  rw [xorWord_lane_frame 2 _ base read (by simp [xorWord,execInstrBr,MachineState.getReg_setReg_ne,MachineState.setWord32,ptr])
    small readSmall aligned readAligned (outside 2)]
  rw [xorWord_lane_frame 1 _ base read (by simp [xorWord,execInstrBr,MachineState.getReg_setReg_ne,MachineState.setWord32,ptr])
    small readSmall aligned readAligned (outside 1)]
  exact xorWord_lane_frame 0 s base read ptr small readSmall aligned readAligned (outside 0)

theorem low_cell (read : Nat) (bound : read<0x40000) :
    (alignToDword (BitVec.ofNat 64 read)).toNat < 0x40000 := by
  unfold alignToDword
  rw [BitVec.toNat_and]
  apply lt_of_le_of_lt Nat.and_le_left
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact bound

theorem low_ne (read : Nat) (bound : read<0x40000) (a : Word) (high : 0x40000≤a.toNat) :
    alignToDword (BitVec.ofNat 64 read) ≠ a := by
  intro eq
  have h := low_cell read bound
  rw [eq] at h
  omega

theorem answer_low_word (hash : Hash) (s : MachineState) (read : Nat) (bound : read<0x40000) :
    (answer hash s).getWord32 (BitVec.ofNat 64 read) = s.getWord32 (BitVec.ofNat 64 read) := by
  simp only [MachineState.getWord32]
  rw [answer_frame]
  intro member
  have high : ∀ a ∈ answerWrites, 0x40000≤a.toNat := by simp [answerWrites,prepareWrites]
  exact low_ne read bound _ (high _ member) rfl

theorem finish_low_word (s : MachineState) (read : Nat) (bound : read<0x40000) :
    (finish s).getWord32 (BitVec.ofNat 64 read) = s.getWord32 (BitVec.ofNat 64 read) := by
  simp only [MachineState.getWord32]
  rw [finish_frame _ _ (low_ne read bound _ (by decide)) (low_ne read bound _ (by decide))]

theorem next_other_word (hash : Hash) (s : MachineState) (node read : Nat)
    (ctl : Controls s node) (bound : node<4095) (readSmall : read<0x40000) (readAligned : read%4=0)
    (outside : ∀ i : Fin 5, 0x88+20*node+4*i.val ≠ read) :
    (next hash s).getWord32 (BitVec.ofNat 64 read) = s.getWord32 (BitVec.ofNat 64 read) := by
  have aptr := (answer_frame hash s 0x430d8 (by decide)).trans ctl.pointer
  have ptr := (xorSetup_registers (answer hash s)).1.trans aptr
  rw [next,finish_low_word _ read readSmall,applyXor_word_frame _ _ read ptr (by omega)
    (by omega) (by omega) readAligned outside]
  simp only [MachineState.getWord32,xorSetup_frame]
  exact answer_low_word hash s read readSmall

theorem next_high_frame (hash : Hash) (s : MachineState) (node : Nat)
    (ctl : Controls s node) (bound : node<4095) (a : Word) (high : 0x40000≤a.toNat)
    (outside : a ∉ answerWrites) (h0 : a≠0x430d0#64) (h1 : a≠0x430d8#64) :
    (next hash s).getMem a = s.getMem a := by
  have aptr := (answer_frame hash s 0x430d8 (by decide)).trans ctl.pointer
  have ptr := (xorSetup_registers (answer hash s)).1.trans aptr
  rw [next,finish_frame _ a h0 h1,applyXor_high_frame _ _ ptr (by omega) a high,xorSetup_frame,answer_frame hash s a outside]

def Fixed (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed) : Prop :=
  KeyContext s parameter seed ∧ s.getMem 0x43018#64=0

theorem next_fixed (hash : Hash) (s : MachineState) (node : Nat) (parameter : BitVec 160) (seed : MasterSeed)
    (ctl : Controls s node) (bound : node<4095) (fixed : Fixed s parameter seed) :
    Fixed (next hash s) parameter seed := by
  obtain ⟨⟨layer,tree,par,key⟩,index⟩ := fixed
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · exact (next_high_frame hash s node ctl bound _ (by decide) (by decide) (by decide) (by decide)).trans layer
  · exact (next_high_frame hash s node ctl bound _ (by decide) (by decide) (by decide) (by decide)).trans tree
  · intro i
    rw [next_other_word hash s node _ ctl bound (by omega) (by omega) (by intro j;omega)]
    exact par i
  · intro i
    rw [next_other_word hash s node _ ctl bound (by omega) (by omega) (by intro j;omega)]
    exact key i
  · exact (next_high_frame hash s node ctl bound _ (by decide) (by decide) (by decide) (by decide)).trans index

theorem answer_words (hash : Hash) (s : MachineState) (i : Fin 5) :
    (answer hash s).getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) =
      (hash (hashInput (prepare s))).extractLsb' (32*i.val) 32 := by
  have dst := (prepare_registers s).2.2.1
  fin_cases i <;> simp [answer,writeHash,dst,MachineState.writeWords,
    MachineState.getWord32,alignToDword,byteOffset,extractWord32]
  all_goals ext b hb;interval_cases b <;> simp

def padValue (hash : Hash) (parameter : BitVec 160) (seed : MasterSeed) (node : Nat) : Digest :=
  truncateHash (hash (toQuery (padInput parameter seed (BitVec.ofNat 32 node))))

theorem next_data (hash : Hash) (s : MachineState) (node : Nat) (parameter : BitVec 160) (seed : MasterSeed)
    (ctl : Controls s node) (bound : node<4095) (fixed : Fixed s parameter seed) (i : Fin 5) :
    (next hash s).getWord32 (BitVec.ofNat 64 (0x88+20*node+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x88+20*node+4*i.val)) ^^^
        (padValue hash parameter seed node).extractLsb' (32*i.val) 32 := by
  have aptr := (answer_frame hash s 0x430d8 (by decide)).trans ctl.pointer
  have regs := xorSetup_registers (answer hash s)
  have ptr := regs.1.trans aptr
  rw [next,finish_low_word _ _ (by omega),applyXor_data _ _ ptr regs.2 (by omega) (by omega)]
  have frame (a : Word) : (xorSetup (answer hash s)).getWord32 a = (answer hash s).getWord32 a := by
    simp only [MachineState.getWord32,xorSetup_frame]
  rw [frame,frame,answer_low_word _ _ _ (by omega),answer_words]
  have ctx : SphincsMaskedMaskNode.Context s parameter seed (BitVec.ofNat 32 node) := by
    refine ⟨fixed.1.1,fixed.1.2.1,fixed.2,?_,fixed.1.2.2.1,fixed.1.2.2.2⟩
    have counter := ctl.counter
    change s.getMem 0x430d0#64 = BitVec.ofNat 64 node at counter
    rw [counter]
    exact (BitVec.setWidth_ofNat_of_le_of_lt (by decide : 32≤64) (by omega : node<2^32)).symm
  rw [query_eq s parameter seed _ ctx]
  congr 1
  exact (BitVec.extractLsb'_extractLsb'_of_le (by dsimp [digestBits];omega)).symm

theorem nodes_semantics (hash : Hash) (s : MachineState) (node count : Nat)
    (parameter : BitVec 160) (seed : MasterSeed)
    (pc : s.pc = if node=4095 then 0x1c14 else 0x1a78)
    (ctl : Controls s node) (bound : node+count≤4095) (fixed : Fixed s parameter seed) :
    Fixed (nodes hash count s) parameter seed ∧
      ∀ j : Fin 4095, ∀ i : Fin 5,
        (nodes hash count s).getWord32 (BitVec.ofNat 64 (0x88+20*j.val+4*i.val)) =
          if node≤j.val ∧ j.val<node+count then
            s.getWord32 (BitVec.ofNat 64 (0x88+20*j.val+4*i.val)) ^^^
              (padValue hash parameter seed j.val).extractLsb' (32*i.val) 32
          else s.getWord32 (BitVec.ofNat 64 (0x88+20*j.val+4*i.val)) := by
  induction count generalizing s node with
  | zero =>
    refine ⟨fixed,?_⟩
    intro j i
    simp [nodes,show ¬(node≤j.val ∧ j.val<node) by omega]
  | succ count ih =>
    have nodeBound : node<4095 := by omega
    have entry : s.pc=0x1a78 := by simpa [show node≠4095 by omega] using pc
    obtain ⟨run,control,loc⟩ := node_contract hash s node entry ctl nodeBound
    obtain ⟨fixedAfter,values⟩ := ih (next hash s) (node+1) loc control (by omega)
      (next_fixed hash s node parameter seed ctl nodeBound fixed)
    refine ⟨fixedAfter,?_⟩
    intro j i
    change (nodes hash count (next hash s)).getWord32 _ = _
    rw [values]
    by_cases equal : j.val=node
    · simp only [equal]
      rw [if_neg (by omega),next_data hash s node parameter seed ctl nodeBound fixed i,if_pos (by omega)]
    · have same := next_other_word hash s node (0x88+20*j.val+4*i.val) ctl nodeBound
        (by omega) (by omega) (by intro k;omega)
      rw [same]
      by_cases selected : node≤j.val ∧ j.val<node+(count+1)
      · rw [if_pos selected,if_pos (by omega)]
      · rw [if_neg selected,if_neg (by omega)]

def initWrites : List Word := [0x43000#64,0x43008#64,0x43010#64,0x43018#64,0x430d0#64,0x430d8#64]

theorem init_frame (s : MachineState) (a : Word) (outside : a∉initWrites) :
    (init s).getMem a = s.getMem a := by
  simp only [initWrites,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := outside
  simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3,h4,h5]

theorem init_low_word (s : MachineState) (read : Nat) (small : read<0x40000) :
    (init s).getWord32 (BitVec.ofNat 64 read) = s.getWord32 (BitVec.ofNat 64 read) := by
  simp only [MachineState.getWord32]
  rw [init_frame]
  intro member
  have high : ∀ a ∈ initWrites, 0x40000≤a.toNat := by simp [initWrites]
  exact low_ne read small _ (high _ member) rfl

theorem init_fixed (s : MachineState) (parameter : BitVec 160) (seed : MasterSeed)
    (par : Words20 s 0x74 parameter) (key : Words32 s seed) : Fixed (init s) parameter seed := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · intro i;rw [init_low_word s _ (by omega)];exact par i
  · intro i;rw [init_low_word s _ (by omega)];exact key i
  · simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

def rootReady (s : MachineState) := execInstrBr (execInstrBr (execInstrBr s
  (.LUI .x6 20)) (.ADDI .x6 .x6 96)) (.ADDI .x7 .x0 96)

theorem rootCopy_eq (s : MachineState) : rootCopy s = SphincsVerifierCopy.copyRootState (rootReady s) := rfl

theorem rootCopy_word_frame (s : MachineState) (read : Nat) (small : read<2^64) (aligned : read%4=0)
    (outside : ∀ i : Fin 5, 0x60+4*i.val≠read) :
    (rootCopy s).getWord32 (BitVec.ofNat 64 read) = s.getWord32 (BitVec.ofNat 64 read) := by
  rw [rootCopy_eq,SphincsVerifierFtsPriorRoots.copyRoot_word_frame]
  · simp [rootReady,execInstrBr,MachineState.getWord32]
  · intro i
    have address : (rootReady s).getReg .x7 + signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
        BitVec.ofNat 64 (0x60+4*i.val) := by
      fin_cases i <;> simp [rootReady,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    rw [address]
    exact SphincsVerifierFtsPriorRoots.wordLaneDistinct _ _ (by omega) small (by omega) aligned (outside i)

theorem rootCopy_data (s : MachineState) (i : Fin 5) :
    (rootCopy s).getWord32 (BitVec.ofNat 64 (0x60+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x14060+4*i.val)) := by
  fin_cases i <;> simp [rootCopy,runSchedule,rootCopySchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getWord32,MachineState.setWord32,alignToDword,byteOffset]

theorem masked_values (hash : Hash) (s : MachineState) (pc : s.pc=0x1a18)
    (parameter : BitVec 160) (seed : MasterSeed) (par : Words20 s 0x74 parameter) (key : Words32 s seed) :
    Words20 (masked hash s) 0x74 parameter ∧ Words32 (masked hash s) seed ∧
    (∀ j : Fin 4095, ∀ i : Fin 5,
      (masked hash s).getWord32 (BitVec.ofNat 64 (0x88+20*j.val+4*i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x88+20*j.val+4*i.val)) ^^^
          (padValue hash parameter seed j.val).extractLsb' (32*i.val) 32) ∧
    (∀ i : Fin 5, (masked hash s).getWord32 (BitVec.ofNat 64 (0x60+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x14060+4*i.val)) ^^^
        (padValue hash parameter seed 4094).extractLsb' (32*i.val) 32) := by
  obtain ⟨fixed,values⟩ := nodes_semantics hash (init s) 0 4095 parameter seed
    (by simpa using init_pc s pc) (init_controls s) (by decide) (init_fixed s parameter seed par key)
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    rw [masked,rootCopy_word_frame _ _ (by omega) (by omega) (by intro j;omega)]
    exact fixed.1.2.2.1 i
  · intro i
    rw [masked,rootCopy_word_frame _ _ (by omega) (by omega) (by intro j;omega)]
    exact fixed.1.2.2.2 i
  · intro j i
    rw [masked,rootCopy_word_frame _ _ (by omega) (by omega) (by intro k;omega),values,
      if_pos (by omega),init_low_word s _ (by omega)]
  · intro i
    rw [masked,rootCopy_data]
    have value := values 4094 i
    norm_num only [Fin.val_natCast] at value
    change (nodes hash 4095 (init s)).getWord32 (BitVec.ofNat 64 (0x14060+4*i.val)) = _ at value
    rw [value,if_pos (by omega),init_low_word s _ (by omega)]
    rfl

def tagReady (s : MachineState) := execInstrBr (execInstrBr (execInstrBr (execInstrBr s
  (.LUI .x6 132)) (.ADDI .x6 .x6 0)) (.LUI .x7 32)) (.ADDI .x7 .x7 76)

theorem tagCopy_eq (s : MachineState) : tagCopy s = SphincsVerifierCopy.copyRootState (tagReady s) := rfl

theorem tagCopy_word_frame (s : MachineState) (read : Nat) (small : read<0x2004c) (aligned : read%4=0) :
    (tagCopy s).getWord32 (BitVec.ofNat 64 read) = s.getWord32 (BitVec.ofNat 64 read) := by
  rw [tagCopy_eq,SphincsVerifierFtsPriorRoots.copyRoot_word_frame]
  · simp [tagReady,execInstrBr,MachineState.getWord32]
  · intro i
    have address : (tagReady s).getReg .x7 + signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
        BitVec.ofNat 64 (0x2004c+4*i.val) := by
      fin_cases i <;> simp [tagReady,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    rw [address]
    exact SphincsVerifierFtsPriorRoots.wordLaneDistinct _ _ (by omega) (by omega) (by omega) aligned (by omega)

theorem final_word (hash : Hash) (s : MachineState) (read : Nat) (small : read<0x2004c) (aligned : read%4=0) :
    (SphincsMaskedKeygenTail.final hash s).getWord32 (BitVec.ofNat 64 read) =
      (masked hash s).getWord32 (BitVec.ofNat 64 read) := by
  unfold SphincsMaskedKeygenTail.final
  simp only [MachineState.getWord32,SphincsMaskedKeygenTail.haltPrepare_frame]
  change (tagCopy (SphincsMaskedMacTrace.result hash 0x1c48 (masked hash s))).getWord32 _ = _
  rw [tagCopy_word_frame _ read small aligned]
  simp only [MachineState.getWord32]
  rw [SphincsMaskedMacRestoration.result_low_frame _ _ _ _ (low_cell read (by omega))]

theorem final_ciphertext (hash : Hash) (s : MachineState) :
    SphincsMaskedMacDomain.ciphertext (SphincsMaskedKeygenTail.final hash s) =
      SphincsMaskedMacDomain.ciphertext (masked hash s) := by
  apply congrArg List.ofFn
  funext i
  apply congrArg UInt8.ofBitVec
  have byte (t : MachineState) := SphincsVerifierFtsGenericBytes.variableWord_byte t
    (0x60+4*(i.val/4)) (by omega) (by omega) 0 ⟨i.val%4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at byte
  have address : 0x60+4*(i.val/4)+i.val%4 = 0x60+i.val := by omega
  simp only [address] at byte
  rw [byte,byte,final_word hash s _ (by omega) (by omega)]

/-- The successful machine output preserves the seeded parameter and contains exactly the
masked node values, duplicated masked root, and a MAC of its own returned ciphertext. -/
theorem final_values (hash : Hash) (s : MachineState) (pc : s.pc=0x1a18)
    (parameter : BitVec 160) (seed : MasterSeed) (par : Words20 s 0x74 parameter) (key : Words32 s seed) :
    Words20 (SphincsMaskedKeygenTail.final hash s) 0x74 parameter ∧
    Words32 (SphincsMaskedKeygenTail.final hash s) seed ∧
    (∀ j : Fin 4095, ∀ i : Fin 5,
      (SphincsMaskedKeygenTail.final hash s).getWord32 (BitVec.ofNat 64 (0x88+20*j.val+4*i.val)) =
        s.getWord32 (BitVec.ofNat 64 (0x88+20*j.val+4*i.val)) ^^^
          (padValue hash parameter seed j.val).extractLsb' (32*i.val) 32) ∧
    (∀ i : Fin 5, (SphincsMaskedKeygenTail.final hash s).getWord32 (BitVec.ofNat 64 (0x60+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x14060+4*i.val)) ^^^
        (padValue hash parameter seed 4094).extractLsb' (32*i.val) 32) ∧
    Words20 (SphincsMaskedKeygenTail.final hash s) 0x2004c
      (truncateHash (hash (toQuery (macInput parameter seed
        (SphincsMaskedMacDomain.ciphertext (SphincsMaskedKeygenTail.final hash s)))))) := by
  obtain ⟨parAfter,keyAfter,values,root⟩ := masked_values hash s pc parameter seed par key
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i;rw [final_word hash s _ (by omega) (by omega)];exact parAfter i
  · intro i;rw [final_word hash s _ (by omega) (by omega)];exact keyAfter i
  · intro j i;rw [final_word hash s _ (by omega) (by omega)];exact values j i
  · intro i;rw [final_word hash s _ (by omega) (by omega)];exact root i
  · rw [final_ciphertext]
    exact SphincsMaskedKeygenTail.final_tag hash s parameter seed parAfter keyAfter

theorem nodes_protected_word (hash : Hash) (s : MachineState) (node count read : Nat)
    (pc : s.pc = if node=4095 then 0x1c14 else 0x1a78)
    (ctl : Controls s node) (bound : node+count≤4095) (small : read<0x40000) (aligned : read%4=0)
    (outside : read<0x88 ∨ 0x14074≤read) :
    (nodes hash count s).getWord32 (BitVec.ofNat 64 read) = s.getWord32 (BitVec.ofNat 64 read) := by
  induction count generalizing s node with
  | zero => rfl
  | succ count ih =>
    have nodeBound : node<4095 := by omega
    have entry : s.pc=0x1a78 := by simpa [show node≠4095 by omega] using pc
    obtain ⟨run,control,loc⟩ := node_contract hash s node entry ctl nodeBound
    rw [nodes,ih (next hash s) (node+1) loc control (by omega)]
    exact next_other_word hash s node read ctl nodeBound small aligned (by intro j;rcases outside with h|h <;> omega)

/-- Public-key words and cache padding survive the entire masking/authentication suffix. -/
theorem final_protected_word (hash : Hash) (s : MachineState) (pc : s.pc=0x1a18)
    (read : Nat) (small : read<0x2004c) (aligned : read%4=0)
    (outsideTree : read<0x88 ∨ 0x14074≤read) (outsideHeader : read<0x60 ∨ 0x74≤read) :
    (SphincsMaskedKeygenTail.final hash s).getWord32 (BitVec.ofNat 64 read) =
      s.getWord32 (BitVec.ofNat 64 read) := by
  rw [final_word hash s read small aligned,masked,rootCopy_word_frame _ read (by omega) aligned
    (by intro i;rcases outsideHeader with h|h <;> omega),
    nodes_protected_word hash (init s) 0 4095 read (by simpa using init_pc s pc)
      (init_controls s) (by decide) (by omega) aligned outsideTree,init_low_word s read (by omega)]

theorem final_node_value (hash : Hash) (s : MachineState) (pc : s.pc=0x1a18)
    (parameter : BitVec 160) (seed : MasterSeed) (par : Words20 s 0x74 parameter) (key : Words32 s seed)
    (node : Fin 4095) (value : Digest) (plain : Words20 s (0x88+20*node.val) value) :
    Words20 (SphincsMaskedKeygenTail.final hash s) (0x88+20*node.val)
      (value ^^^ padValue hash parameter seed node.val) := by
  have words := (final_values hash s pc parameter seed par key).2.2.1
  intro i
  rw [words node i,plain i]
  simp [BitVec.extractLsb'_xor]

theorem final_root_value (hash : Hash) (s : MachineState) (pc : s.pc=0x1a18)
    (parameter : BitVec 160) (seed : MasterSeed) (par : Words20 s 0x74 parameter) (key : Words32 s seed)
    (value : Digest) (plain : Words20 s 0x14060 value) :
    Words20 (SphincsMaskedKeygenTail.final hash s) 0x60
      (value ^^^ padValue hash parameter seed 4094) := by
  have words := (final_values hash s pc parameter seed par key).2.2.2.1
  intro i
  rw [words i,plain i]
  simp [BitVec.extractLsb'_xor]

/-- info: 'SigGolfCandidate.SphincsMaskedMaskSemantics.next_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms next_data

/-- info: 'SigGolfCandidate.SphincsMaskedMaskSemantics.nodes_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodes_semantics

/-- info: 'SigGolfCandidate.SphincsMaskedMaskSemantics.masked_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms masked_values

/-- info: 'SigGolfCandidate.SphincsMaskedMaskSemantics.final_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms final_values

/-- info: 'SigGolfCandidate.SphincsMaskedMaskSemantics.final_protected_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms final_protected_word

/-- info: 'SigGolfCandidate.SphincsMaskedMaskSemantics.final_root_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms final_root_value

end SigGolfCandidate.SphincsMaskedMaskSemantics
