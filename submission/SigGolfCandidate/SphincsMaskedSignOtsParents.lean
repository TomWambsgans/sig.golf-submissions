import SigGolfCandidate.SphincsMaskedSignOtsTree

namespace SigGolfCandidate.SphincsMaskedSignOtsParents
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy SphincsMaskedSignOtsShift
open SphincsMaskedParentCode SphincsMaskedParentNode SphincsMaskedChainDomain
open SphincsVerifierCopy SphincsVerifierCopyMemory SphincsVerifierMessageCopy
open SphincsVerifierFtsCopyAccess SphincsVerifierFtsPriorRoots SphincsVerifierFtsGenericCopyData
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def offset (location : Fin 5) : Nat := chainOffset location+1
def delta (location : Fin 5) : Word := BitVec.ofNat 64 (4*offset location)
theorem offset_bound (location : Fin 5) : offset location ≤ 7356 := by fin_cases location <;> decide

def sharedLength : Nat := 124
/-- All signer parent nodes are exact relocations of the domain-three keygen block. -/
theorem image (location : Fin 5) :
    (SphincsMaskedImages.sign.code.drop (392+offset location)).take 124=
      (SphincsMaskedImages.keygen.code.drop 392).take 124 := by
  fin_cases location <;> rfl

theorem word (location : Fin 5) (i : Fin 124) :
    SphincsMaskedImages.sign.code[392+offset location+i.val]?=
      SphincsMaskedImages.keygen.code[392+i.val]? := by
  have eq:=congrArg (fun words : List (BitVec 32) => words[i.val]?) (image location)
  simpa only [List.getElem?_take_of_lt i.isLt,List.getElem?_drop] using eq

theorem instruction_transfer (location : Fin 5) (pc : Word)
    (lower : 0x1620 ≤ pc.toNat) (upper : pc.toNat<0x1810) (aligned : pc.toNat%4=0) :
    instructionAt SphincsMaskedImages.sign (pc+delta location)=
      instructionAt SphincsMaskedImages.keygen pc := by
  let i : Fin 124:=⟨(pc.toNat-0x1620)/4,by omega⟩
  have bound:=offset_bound location
  have original : pc=BitVec.ofNat 64 (0x1000+4*(392+i.val)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [i];omega)]
    dsimp [i];omega
  have translated : pc+delta location=BitVec.ofNat 64 (0x1000+4*(392+offset location+i.val)) := by
    rw [original,delta,←BitVec.ofNat_add]
    congr 1;omega
  rw [translated,SphincsMaskedSignOtsShift.fetch_index _ _ (by omega),original,SphincsMaskedSignOtsShift.fetch_index _ _ (by omega),word location i]

theorem encoded_of (location : Fin 5) (code : List (Word × Instr))
    (inside : ∀ e∈code,0x1620 ≤ e.1.toNat ∧ e.1.toNat<0x1810 ∧ e.1.toNat%4=0)
    (source : ∀ e∈code,instructionAt SphincsMaskedImages.keygen e.1=some (.base e.2)) :
    ∀ e∈code,instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  intro e he
  obtain ⟨lo,hi,align⟩:=inside e he
  rw [instruction_transfer location e.1 lo hi align]
  exact source e he

theorem leftSetup_block (location : Fin 5) (s : MachineState) (pc : s.pc=0x1620) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 12
      (shift (delta location) (leftSetup s)) :=
  block_shift _ _ leftSetupSchedule (by decide)
    (encoded_of location _ (by decide) leftSetup_code) s (leftSetup_checked s pc)

theorem rightSetup_block (location : Fin 5) (s : MachineState) (pc : s.pc=0x1678) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 3
      (shift (delta location) (rightSetup s)) :=
  block_shift _ _ rightSetupSchedule (by decide)
    (encoded_of location _ (by decide) rightSetup_code) s (rightSetup_checked s pc)

theorem hashPrepare_block (location : Fin 5) (s : MachineState) (pc : s.pc=0x16ac) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 52
      (shift (delta location) (hashPrepare s)) :=
  block_shift _ _ hashPrepareSchedule (by decide)
    (encoded_of location _ (by decide) hashPrepare_code) s (hashPrepare_checked s pc)

theorem storeSetup_block (location : Fin 5) (s : MachineState) (pc : s.pc=0x1780) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 12
      (shift (delta location) (storeSetup s)) :=
  block_shift _ _ storeSetupSchedule (by decide)
    (encoded_of location _ (by decide) storeSetup_code) s (storeSetup_checked s pc)

theorem nodeFinish_block (location : Fin 5) (s : MachineState) (pc : s.pc=0x17d8) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 14
      (shift (delta location) (nodeFinish s)) :=
  block_shift _ _ nodeFinishSchedule (by decide)
    (encoded_of location _ (by decide) nodeFinish_code) s (nodeFinish_checked s pc)

theorem copy_code (location : Fin 5) (index : Nat) (lo : 392 ≤ index) (hi : index+10 ≤ 516)
    (source : Copy20Code SphincsMaskedImages.keygen index) :
    Copy20Code SphincsMaskedImages.sign (index+offset location) := by
  constructor
  · intro i
    have eq:=congrArg (fun x : Option (BitVec 32) => x.bind decodeInstruction) (word location ⟨index+2*i.val-392,by omega⟩)
    dsimp only at eq
    have addr : 392+(index+2*i.val-392)=index+2*i.val := by omega
    simp only [addr] at eq
    have shifted : 392+offset location+(index+2*i.val-392)=index+offset location+2*i.val := by omega
    rw [shifted] at eq
    exact eq.trans (source.load i)
  · intro i
    have eq:=congrArg (fun x : Option (BitVec 32) => x.bind decodeInstruction) (word location ⟨index+2*i.val+1-392,by omega⟩)
    dsimp only at eq
    have addr : 392+(index+2*i.val+1-392)=index+2*i.val+1 := by omega
    simp only [addr] at eq
    have shifted : 392+offset location+(index+2*i.val+1-392)=index+offset location+2*i.val+1 := by omega
    rw [shifted] at eq
    exact eq.trans (source.store i)

theorem copy_block (location : Fin 5) (index source target : Nat) (s : MachineState)
    (lo : 392 ≤ index) (hi : index+10 ≤ 516) (code : Copy20Code SphincsMaskedImages.keygen index)
    (pc : s.pc=BitVec.ofNat 64 (0x1000+4*index))
    (src : s.getReg .x6=BitVec.ofNat 64 source) (dst : s.getReg .x7=BitVec.ofNat 64 target)
    (sourceAlign : source%4=0) (sourceBound : source+20 ≤ 0x60000)
    (targetAlign : target%4=0) (targetBound : target+20 ≤ 0x60000) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 10
      (shift (delta location) (copyRootState s)) := by
  have loc : (shift (delta location) s).pc=BitVec.ofNat 64 (0x1000+4*(index+offset location)) := by
    rw [shift_pc,pc,delta,←BitVec.ofNat_add]
    congr 1;omega
  have copied:=copy20_block_general SphincsMaskedImages.sign (index+offset location)
    (copy_code location index lo hi code) (shift (delta location) s) source target loc
    (by simpa using src) (by simpa using dst) sourceAlign (by dsimp [MEMORY_BYTES];omega)
    targetAlign (by dsimp [MEMORY_BYTES];omega) (by have := offset_bound location;omega)
  rw [copyRoot_shift] at copied
  exact copied

theorem children_block (location : Fin 5) (s : MachineState) (base node : Nat) (pc : s.pc=0x1620)
    (hb : s.getMem 0x43068=BitVec.ofNat 64 base) (hn : s.getMem 0x43088=BitVec.ofNat 64 node)
    (bounded : base+40*node+40 ≤ 0x60000) (aligned : base%4=0) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 35
      (shift (delta location) (children s)) := by
  have left:=leftSetup_registers s base node hb hn
  have first:=copy_block location 404 (base+40*node) 0x40028 (leftSetup s)
    (by decide) (by decide) left_copy_code (leftSetup_pc s pc) left.1 left.2
    (by omega) (by omega) (by decide) (by decide)
  have source:=(copyRoot_registers (leftSetup s)).1.trans left.1
  have right:=rightSetup_registers (leftCopied s) (base+40*node) source
  have last:=copy_block location 417 (base+40*node+20) 0x4003c (rightSetup (leftCopied s))
    (by decide) (by decide) right_copy_code (rightSetup_pc _ (leftCopied_pc s pc)) right.1 right.2
    (by omega) (by omega) (by decide) (by decide)
  exact ordinary_trans _ _ _ _ 12 23 (leftSetup_block location s pc)
    (ordinary_trans _ _ _ _ 10 13 first (ordinary_trans _ _ _ _ 3 10
      (rightSetup_block location _ (leftCopied_pc s pc)) last))

theorem answer_trace (location : Fin 5) (hash : Hash) (s : MachineState) (base node : Nat) (pc : s.pc=0x1620)
    (hb : s.getMem 0x43068=BitVec.ofNat 64 base) (hn : s.getMem 0x43088=BitVec.ofNat 64 node)
    (bounded : base+40*node+40 ≤ 0x60000) (aligned : base%4=0) :
    Trace hash SphincsMaskedImages.sign (shift (delta location) s) 88 103 1 2
      (shift (delta location) (answer hash s)) := by
  obtain ⟨src,bits,dst,service⟩:=hashPrepare_registers (children s)
  have fetched : fetch SphincsMaskedImages.sign (shift (delta location) (hashPrepare (children s)))=some (.base .ECALL) := by
    rw [fetch_at,shift_pc,hashPrepare_pc _ (children_pc s pc)]
    rw [instruction_transfer location 0x177c (by decide) (by decide) (by decide)]
    decide
  have valid : hashArgumentsValid (hashPrepare (children s))=true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (hashPrepare (children s))).1=640 := by simp [hashInput,bits]
  have hashing : Trace hash SphincsMaskedImages.sign (shift (delta location) (hashPrepare (children s))) 1 16 1 2
      (shift (delta location) (answer hash s)) := by
    have one:=hash_block_shift (delta location) hash SphincsMaskedImages.sign _ fetched service valid
    simpa only [len,answer,show compressions 640=2 from by decide,Nat.reduceMul] using one
  exact (children_block location s base node pc hb hn bounded aligned).trace.trans
    ((hashPrepare_block location _ (children_pc s pc)).trace.trans hashing)

theorem stored_control (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : target + 20 * node + 20  ≤  0x60000) (above : 0x50000  ≤  target)
    (a : Word) (low : a.toNat < 0x50000) :
    (stored s).getMem a = s.getMem a := by
  change (copyRootState (storeSetup s)).getMem a = _
  rw [copyRoot_mem_frame]
  · exact storeSetup_frame s a
  · intro i
    rw [(storeSetup_registers s target node ht hn).2]
    have address : BitVec.ofNat 64 (target + 20 * node) + signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
        BitVec.ofNat 64 (target + 20 * node + 4 * i.val) := by
      fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [address]
    intro eq
    let offset := target + 20*node + 4*i.val - 0x50000
    have ha : (BitVec.ofNat 64 0x50000).toNat % 8 = 0 := by decide
    have hover : (BitVec.ofNat 64 0x50000).toNat + offset < 2^64 := by
      change 0x50000 + offset < 2^64;dsimp [offset];omega
    have aligned := alignToDword_add_ofNat_of_aligned ha hover
    rw [← BitVec.ofNat_add] at aligned
    have lower : 0x50000  ≤  (alignToDword (BitVec.ofNat 64 (target+20*node+4*i.val))).toNat := by
      rw [show target+20*node+4*i.val = 0x50000 + offset by dsimp [offset];omega,
        aligned,← BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      omega
    rw [← eq] at lower;omega

theorem node_trace (location : Fin 5) (hash : Hash) (s : MachineState) (base target node count : Nat) (pc : s.pc = 0x1620)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (ht : s.getMem 0x43080 = BitVec.ofNat 64 target)
    (hn : s.getMem 0x43088 = BitVec.ofNat 64 node) (hc : s.getMem 0x43090 = BitVec.ofNat 64 count)
    (sourceBound : base + 40 * node + 40  ≤  0x60000) (sourceAlign : base % 4 = 0)
    (targetBound : target + 20 * node + 20  ≤  0x60000) (targetAlign : target % 4 = 0) (above : 0x50000  ≤  target)
    (countBound : count < 2048) :
    Trace hash SphincsMaskedImages.sign (shift (delta location) s) 124 139 1 2
      (shift (delta location) (next hash s)) ∧
      (next hash s).getMem 0x43088 = BitVec.ofNat 64 (node + 1) ∧
      (next hash s).pc = if node + 1 = count then 0x1810 else 0x1620 := by
  have atarget : (answer hash s).getMem 0x43080 = BitVec.ofNat 64 target :=
    (answer_frame hash s _ (by decide)).trans ht
  have anode : (answer hash s).getMem 0x43088 = BitVec.ofNat 64 node :=
    (answer_frame hash s _ (by decide)).trans hn
  have acount : (answer hash s).getMem 0x43090 = BitVec.ofNat 64 count :=
    (answer_frame hash s _ (by decide)).trans hc
  have regs := storeSetup_registers (answer hash s) target node atarget anode
  have apc := answer_pc hash s pc
  have copied:=copy_block location 492 0x42000 (target+20*node) (storeSetup (answer hash s))
    (by decide) (by decide) store_code (storeSetup_pc _ apc) regs.1 regs.2
    (by decide) (by decide) (by omega) targetBound
  have storedNode := (stored_control (answer hash s) target node atarget anode targetBound above 0x43088 (by decide)).trans anode
  have storedCount := (stored_control (answer hash s) target node atarget anode targetBound above 0x43090 (by decide)).trans acount
  refine ⟨?_,?_,?_⟩
  · exact (answer_trace location hash s base node pc hb hn sourceBound sourceAlign).trans
      ((storeSetup_block location _ apc).trace.trans (copied.trace.trans (nodeFinish_block location _ (stored_pc _ apc)).trace))
  · change (nodeFinish (stored (answer hash s))).getMem _ = _
    rw [nodeFinish_counter,storedNode]
    exact (BitVec.ofNat_add _ _).symm
  · change (nodeFinish (stored (answer hash s))).pc = _
    rw [nodeFinish_pc _ (stored_pc _ apc),storedNode,storedCount]
    rw [show BitVec.ofNat 64 node + 1 = BitVec.ofNat 64 (node + 1) from (BitVec.ofNat_add _ _).symm]
    have eq : (BitVec.ofNat 64 (node + 1) : Word) = BitVec.ofNat 64 count ↔ node + 1 = count := by
      constructor
      · intro h
        have h := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show node + 1 < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show count < 2 ^ 64 by omega)] at h
        exact h
      · intro h;rw [h]
    simp only [eq]


set_option backward.isDefEq.respectTransparency false
open SphincsSecurity SphincsBridge SphincsMaskedParentDomain

theorem children_left (s : MachineState) (base node : Nat)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (above : 0x50000  ≤  base) (bounded : base+40*node+40  ≤  0x60000)
    (aligned : base%4=0) (i : Fin 5) :
    (children s).getWord32 (BitVec.ofNat 64 (0x40028+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (base+40*node+4*i.val)) := by
  have regs := leftSetup_registers s base node hb hn
  have source := (copyRoot_registers (leftSetup s)).1.trans regs.1
  have right := rightSetup_registers (leftCopied s) (base+40*node) source
  change (copyRootState (rightSetup (leftCopied s))).getWord32 _ = _
  rw [copyRoot_word_frame]
  · simp only [MachineState.getWord32,rightSetup_frame]
    change (copyRootState (leftSetup s)).getWord32 _ = _
    rw [SphincsMaskedSignForestParents.copy_data _ (base+40*node) 0x40028 (by omega) (by decide) (by omega) (by decide)
      (Or.inr (by omega)) regs.1 regs.2 i]
    simp only [MachineState.getWord32,leftSetup_frame]
  · intro j;rw [right.2];fin_cases i <;> fin_cases j <;> decide

theorem children_right (s : MachineState) (base node : Nat)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (above : 0x50000  ≤  base) (bounded : base+40*node+40  ≤  0x60000)
    (aligned : base%4=0) (i : Fin 5) :
    (children s).getWord32 (BitVec.ofNat 64 (0x4003c+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (base+40*node+20+4*i.val)) := by
  have regs := leftSetup_registers s base node hb hn
  have source := (copyRoot_registers (leftSetup s)).1.trans regs.1
  have right := rightSetup_registers (leftCopied s) (base+40*node) source
  change (copyRootState (rightSetup (leftCopied s))).getWord32 _ = _
  rw [SphincsMaskedSignForestParents.copy_data _ (base+40*node+20) 0x4003c (by omega) (by decide) (by omega) (by decide)
    (Or.inr (by omega)) right.1 right.2 i]
  simp only [MachineState.getWord32,rightSetup_frame]
  change (copyRootState (leftSetup s)).getWord32 _ = _
  rw [copyRoot_word_frame]
  · simp only [MachineState.getWord32,leftSetup_frame]
  · intro j;rw [regs.2]
    have address : (0x40028 : Word) + signExtend12 (4#12 * BitVec.ofNat 12 j.val) =
        BitVec.ofNat 64 (0x40028+4*j.val) := by fin_cases j <;> decide
    rw [address]
    exact wordLaneDistinct _ _ (by omega) (by omega) (by omega) (by omega) (by omega)


theorem next_data (hash : Hash) (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (above : 0x50000  ≤  target) (bounded : target+20*node+20  ≤  0x60000)
    (aligned : target%4=0) (i : Fin 5) :
    (next hash s).getWord32 (BitVec.ofNat 64 (target+20*node+4*i.val)) =
      (answer hash s).getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) := by
  have atarget := (answer_frame hash s _ (by decide)).trans ht
  have anode := (answer_frame hash s _ (by decide)).trans hn
  have regs := storeSetup_registers (answer hash s) target node atarget anode
  change (nodeFinish (stored (answer hash s))).getWord32 _ = _
  simp only [MachineState.getWord32]
  rw [nodeFinish_frame]
  · change (copyRootState (storeSetup (answer hash s))).getWord32 _ = _
    rw [SphincsMaskedSignForestParents.copy_data _ 0x42000 (target+20*node) (by decide) (by omega) (by decide) (by omega)
      (Or.inl (by omega)) regs.1 regs.2 i]
    simp only [MachineState.getWord32,storeSetup_frame]
  · intro eq
    have lower := SphincsMaskedSignForestParents.cache_cell_lower (target+20*node+4*i.val) (by omega) (by omega)
    rw [eq] at lower;contradiction

theorem answer_words (hash : Hash) (s : MachineState) (i : Fin 5) :
    (answer hash s).getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) =
      (hash (hashInput (hashPrepare (children s)))).extractLsb' (32*i.val) 32 := by
  have dst := (hashPrepare_registers (children s)).2.2.1
  fin_cases i <;>
    simp [answer,writeHash,dst,MachineState.writeWords,MachineState.getWord32,alignToDword,byteOffset,extractWord32]
  all_goals ext b hb;interval_cases b <;> simp

/-- The concrete parent slot receives the low 160 bits of the actual oracle answer. -/
theorem node_value (hash : Hash) (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (above : 0x50000  ≤  target) (bounded : target+20*node+20  ≤  0x60000) (aligned : target%4=0) :
    Words20 (next hash s) (target+20*node)
      ((hash (hashInput (hashPrepare (children s)))).extractLsb' 0 160) := by
  intro i
  rw [next_data hash s target node ht hn above bounded aligned i,answer_words]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

theorem next_control (hash : Hash) (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (above : 0x50000  ≤  target) (bounded : target+20*node+20  ≤  0x60000)
    (a : Word) (low : a.toNat < 0x50000) (outside : a ∉ preWrites) (notNode : a ≠ 0x43088#64) :
    (next hash s).getMem a = s.getMem a := by
  have atarget := (answer_frame hash s _ (by decide)).trans ht
  have anode := (answer_frame hash s _ (by decide)).trans hn
  change (nodeFinish (stored (answer hash s))).getMem a = _
  rw [nodeFinish_frame _ a notNode,stored_control _ target node atarget anode bounded above a low,
    answer_frame hash s a outside]

theorem next_prior_word (hash : Hash) (s : MachineState) (target node address : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (above : 0x50000  ≤  target) (bounded : target+20*node+20  ≤  0x60000) (aligned : target%4=0)
    (readLower : 0x50000  ≤  address) (readUpper : address < target+20*node) (readAlign : address%4=0) :
    (next hash s).getWord32 (BitVec.ofNat 64 address) = s.getWord32 (BitVec.ofNat 64 address) := by
  have atarget := (answer_frame hash s _ (by decide)).trans ht
  have anode := (answer_frame hash s _ (by decide)).trans hn
  have regs := storeSetup_registers (answer hash s) target node atarget anode
  change (nodeFinish (stored (answer hash s))).getWord32 _ = _
  have lower := SphincsMaskedSignForestParents.cache_cell_lower address readLower (by omega)
  simp only [MachineState.getWord32]
  rw [nodeFinish_frame _ _ (by intro eq;rw [eq] at lower;contradiction)]
  change (copyRootState (storeSetup (answer hash s))).getWord32 _ = _
  rw [copyRoot_word_frame]
  · simp only [MachineState.getWord32,storeSetup_frame]
    rw [answer_frame]
    intro member
    have upper : ∀ a ∈ preWrites, a.toNat < 0x50000 := by
      simp [preWrites,payloadWrites,headerWrites,answerWrites]
    have bad := upper _ member
    omega
  · intro i
    rw [regs.2]
    have addr : BitVec.ofNat 64 (target+20*node) + signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
        BitVec.ofNat 64 (target+20*node+4*i.val) := by
      fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [addr]
    exact wordLaneDistinct _ _ (by omega) (by omega) (by omega) readAlign (by omega)



namespace Domain

def Context (s : MachineState) (parameter left right : Digest) (lay : Layer) (treeIdx : TreeIndex)
    (level node : Nat) : Prop :=
  s.getMem 0x43000#64=BitVec.ofNat 64 lay.val ∧ s.getMem 0x43008#64=BitVec.ofNat 64 treeIdx.val ∧
  s.getMem 0x43048#64=BitVec.ofNat 64 level ∧ s.getMem 0x43088#64=BitVec.ofNat 64 node ∧
  Words20 s 0x74 parameter ∧ Words20 s 0x40028 left ∧ Words20 s 0x4003c right

def input (parameter left right : Digest) (lay : Layer) (treeIdx : TreeIndex) (level node : Nat) : HashInput :=
  tweakableHashInput parameter (.node lay treeIdx level node) (Concrete.nodePayload left right)
def payload (parameter left right : Digest) (lay : Layer) (treeIdx : TreeIndex) (level node : Nat) : List Byte :=
  (input parameter left right lay treeIdx level node).map UInt8.toBitVec

theorem payload_length (parameter left right : Digest) (lay : Layer) (treeIdx : TreeIndex) (level node : Nat) :
    (payload parameter left right lay treeIdx level node).length=80 := by
  simp [payload,input,tweakableHashInput,tweakBytes,hashDomainFields,tweakFields,fieldBytes,bytesLE,Concrete.nodePayload]

theorem context_byte (s : MachineState) (parameter left right : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (level node : Nat)
    (ctx : Context s parameter left right lay treeIdx level node) (i : Fin 80) :
    (queryWord s ⟨i.val / 4,by omega⟩).extractLsb' (8 * (i.val % 4)) 8 =
      (payload parameter left right lay treeIdx level node)[i.val]'(by rw [payload_length];exact i.isLt) := by
  obtain ⟨layer,tree,lev,idx,par,lft,rgt⟩ := ctx
  have p0 := par 0
  have p1 := par 1
  have p2 := par 2
  have p3 := par 3
  have p4 := par 4
  have l0 := lft 0
  have l1 := lft 1
  have l2 := lft 2
  have l3 := lft 3
  have l4 := lft 4
  have r0 := rgt 0
  have r1 := rgt 1
  have r2 := rgt 2
  have r3 := rgt 3
  have r4 := rgt 4
  norm_num at p0 p1 p2 p3 p4 l0 l1 l2 l3 l4 r0 r1 r2 r3 r4
  have treeWidth : (BitVec.ofNat 64 treeIdx.val).setWidth 32=BitVec.ofNat 32 treeIdx.val := by simp
  fin_cases i <;>
    simp [queryWord,layer,tree,lev,idx,p0,p1,p2,p3,p4,l0,l1,l2,l3,l4,r0,r1,r2,r3,r4,
      extractWord32,payload,input,tweakableHashInput,tweakBytes,hashDomainFields,tweakFields,
      fieldBytes,bytesLE,Concrete.nodePayload,topLayer,Concrete.rootTree,protocolDomainSep]
  all_goals first
    | (fin_cases lay <;> decide)
    | (rw [←treeWidth];exact BitVec.extractLsb'_setWidth_of_le (by decide))
    | (solve | simp [BitVec.setWidth_ushiftRight_eq_extractLsb,SphincsMaskedSignForestDomain.nested_extract])

theorem query_eq (s : MachineState) (parameter left right : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (level node : Nat)
    (ctx : Context s parameter left right lay treeIdx level node) :
    hashInput (hashPrepare s) = toQuery (input parameter left right lay treeIdx level node) := by
  apply Serialization.hashInput_of_list (hashPrepare s) 0x40000 (payload parameter left right lay treeIdx level node)
  · exact (hashPrepare_registers s).1
  · rw [payload_length,(hashPrepare_registers s).2.1];rfl
  · intro i hi
    have bound : i < 80 := by simpa only [payload_length] using hi
    rw [prepared_byte s ⟨i,bound⟩]
    exact context_byte s parameter left right lay treeIdx level node ctx ⟨i,bound⟩

theorem children_context (s : MachineState) (parameter left right : BitVec 160) (lay : Layer) (treeIdx : TreeIndex) (base level node : Nat)
    (layer : s.getMem 0x43000 = BitVec.ofNat 64 lay.val) (tree : s.getMem 0x43008 = BitVec.ofNat 64 treeIdx.val)
    (lev : s.getMem 0x43048 = BitVec.ofNat 64 level) (idx : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (bounded : base + 40 * node + 40  ≤  0x60000) (above : 0x50000  ≤  base) (aligned : base%4=0)
    (par : Words20 s 0x74 parameter)
    (lft : Words20 s (base + 40 * node) left) (rgt : Words20 s (base + 40 * node + 20) right) :
    Context (children s) parameter left right lay treeIdx level node := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact (children_frame s _ (by decide)).trans layer
  · exact (children_frame s _ (by decide)).trans tree
  · exact (children_frame s _ (by decide)).trans lev
  · exact (children_frame s _ (by decide)).trans idx
  · intro i
    simp only [MachineState.getWord32]
    rw [children_frame s _ (by fin_cases i <;> decide)]
    exact par i
  · intro i;exact (children_left s base node hb idx above bounded aligned i).trans (lft i)
  · intro i;exact (children_right s base node hb idx above bounded aligned i).trans (rgt i)


theorem node_value (hash : Hash) (s : MachineState) (parameter left right : Digest)
    (lay : Layer) (treeIdx : TreeIndex) (base target level node : Nat)
    (layer : s.getMem 0x43000=BitVec.ofNat 64 lay.val) (tree : s.getMem 0x43008=BitVec.ofNat 64 treeIdx.val)
    (lev : s.getMem 0x43048=BitVec.ofNat 64 level) (idx : s.getMem 0x43088=BitVec.ofNat 64 node)
    (hb : s.getMem 0x43068=BitVec.ofNat 64 base) (ht : s.getMem 0x43080=BitVec.ofNat 64 target)
    (sourceBound : base+40*node+40 ≤ 0x60000) (sourceAbove : 0x50000 ≤ base) (sourceAlign : base%4=0)
    (targetBound : target+20*node+20 ≤ 0x60000) (targetAbove : 0x50000 ≤ target) (targetAlign : target%4=0)
    (par : Words20 s 0x74 parameter) (hl : Words20 s (base+40*node) left) (hr : Words20 s (base+40*node+20) right) :
    Words20 (next hash s) (target+20*node)
      (truncateHash (hash (toQuery (input parameter left right lay treeIdx level node)))) := by
  have ctx:=children_context s parameter left right lay treeIdx base level node layer tree lev idx hb
    sourceBound sourceAbove sourceAlign par hl hr
  have value:=SphincsMaskedSignOtsParents.node_value hash s target node ht idx targetAbove targetBound targetAlign
  rw [query_eq _ parameter left right lay treeIdx level node ctx] at value
  exact value

end Domain


abbrev Controls := SphincsMaskedParentLevels.Controls
abbrev KeyContext := SphincsMaskedSignOtsTree.KeyContext

theorem next_key (hash : Hash) (s : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (target node : Nat) (ctx : KeyContext s parameter seed lay treeIdx)
    (ht : s.getMem 0x43080=BitVec.ofNat 64 target) (hn : s.getMem 0x43088=BitVec.ofNat 64 node)
    (above : 0x50000 ≤ target) (bounded : target+20*node+20 ≤ 0x60000) :
    KeyContext (next hash s) parameter seed lay treeIdx := by
  obtain ⟨layer,tree,par,key⟩:=ctx
  refine ⟨?_,?_,?_,?_⟩
  · exact (next_control hash s target node ht hn above bounded _ (by decide) (by decide) (by decide)).trans layer
  · exact (next_control hash s target node ht hn above bounded _ (by decide) (by decide) (by decide)).trans tree
  · intro i
    simp only [MachineState.getWord32]
    rw [next_control hash s target node ht hn above bounded _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact par i
  · intro i
    simp only [MachineState.getWord32]
    rw [next_control hash s target node ht hn above bounded _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact key i

def nodes (hash : Hash) : Nat → MachineState → MachineState
  | 0,s => s
  | n+1,s => next hash (nodes hash n s)

def parentValue (hash : Hash) (parameter : PublicParameter) (lay : Layer) (treeIdx : TreeIndex)
    (level node : Nat) (left right : Digest) : Digest :=
  truncateHash (hash (toQuery (Domain.input parameter left right lay treeIdx level node)))

/-- One reusable exact-image induction computes every node of a high-cache level.
    Both child words and the resulting domain-three query are proved, not assumed. -/
theorem nodes_contract (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex)
    (base target level count : Nat) (values : Nat → Digest)
    (pc : s.pc=0x1620) (ctx : KeyContext s parameter seed lay treeIdx)
    (controls : Controls s base target level count 0)
    (source : ∀ j,j<2*count → Words20 s (base+20*j) (values j))
    (sourceBound : base+40*count ≤ target) (targetBound : target+20*count ≤ 0x60000)
    (baseAlign : base%4=0) (targetAlign : target%4=0) (baseAbove : 0x50000 ≤ base)
    (positive : 0<count) (small : count<2048) (n : Nat) (hn : n ≤ count) :
    Trace hash SphincsMaskedImages.sign (shift (delta location) s) (124*n) (139*n) n (2*n)
      (shift (delta location) (nodes hash n s)) ∧
      Controls (nodes hash n s) base target level count n ∧ KeyContext (nodes hash n s) parameter seed lay treeIdx ∧
      (nodes hash n s).pc=(if n=count then 0x1810 else 0x1620) ∧
      (∀ j,j<n → Words20 (nodes hash n s) (target+20*j)
        (parentValue hash parameter lay treeIdx level j (values (2*j)) (values (2*j+1)))) ∧
      (∀ address,0x50000 ≤ address → address<target → address%4=0 →
        (nodes hash n s).getWord32 (BitVec.ofNat 64 address)=s.getWord32 (BitVec.ofNat 64 address)) ∧
      (∀ a,a.toNat<0x50000 → a∉preWrites → a≠0x43088#64 → (nodes hash n s).getMem a=s.getMem a) := by
  induction n with
  | zero =>
    refine ⟨Trace.refl _,controls,ctx,?_,?_,?_,?_⟩
    · simpa only [nodes,if_neg (by omega : 0≠count)] using pc
    · intro j hj;omega
    · intro _ _ _ _;rfl
    · intro _ _ _ _;rfl
  | succ n ih =>
    obtain ⟨trace,ctrl,key,loc,done,frame,lowFrame⟩:=ih (by omega)
    let mid:=nodes hash n s
    have npc : mid.pc=0x1620 := by rw [loc,if_neg (by omega)]
    have sb : base+40*n+40 ≤ 0x60000 := by omega
    have tb : target+20*n+20 ≤ 0x60000 := by omega
    have above : 0x50000 ≤ target := by omega
    obtain ⟨last,nextCount,nextPc⟩:=node_trace location hash mid base target n count npc ctrl.base ctrl.target
      ctrl.node ctrl.count sb baseAlign tb targetAlign above small
    have newControls : Controls (next hash mid) base target level count (n+1) := by
      refine ⟨?_,?_,?_,?_,nextCount⟩
      · exact (next_control hash mid target n ctrl.target ctrl.node above tb _ (by decide) (by decide) (by decide)).trans ctrl.base
      · exact (next_control hash mid target n ctrl.target ctrl.node above tb _ (by decide) (by decide) (by decide)).trans ctrl.target
      · exact (next_control hash mid target n ctrl.target ctrl.node above tb _ (by decide) (by decide) (by decide)).trans ctrl.level
      · exact (next_control hash mid target n ctrl.target ctrl.node above tb _ (by decide) (by decide) (by decide)).trans ctrl.count
    have left : Words20 mid (base+40*n) (values (2*n)) := by
      intro i
      rw [frame _ (by omega) (by omega) (by omega)]
      convert source (2*n) (by omega) i using 1 <;> congr 2 <;> omega
    have right : Words20 mid (base+40*n+20) (values (2*n+1)) := by
      intro i
      rw [frame _ (by omega) (by omega) (by omega)]
      convert source (2*n+1) (by omega) i using 1 <;> congr 2 <;> omega
    have newValue:=Domain.node_value hash mid parameter _ _ lay treeIdx base target level n key.1 key.2.1
      ctrl.level ctrl.node ctrl.base ctrl.target sb baseAbove baseAlign tb above targetAlign key.2.2.1 left right
    refine ⟨?_,newControls,next_key hash mid parameter seed lay treeIdx target n key ctrl.target ctrl.node above tb,nextPc,?_,?_,?_⟩
    · simpa only [nodes,Nat.mul_succ] using trace.trans last
    · intro j hj
      by_cases eq : j=n
      · subst j;exact newValue
      · intro i
        change (next hash mid).getWord32 _=_
        rw [next_prior_word hash mid target n _ ctrl.target ctrl.node above tb targetAlign (by omega) (by omega) (by omega)]
        exact done j (by omega) i
    · intro address lower upper align
      change (next hash mid).getWord32 _=_
      rw [next_prior_word hash mid target n address ctrl.target ctrl.node above tb targetAlign lower (by omega) align]
      exact frame address lower upper align
    · intro a low outside ne
      change (next hash mid).getMem a=_
      rw [next_control hash mid target n ctrl.target ctrl.node above tb a low outside ne]
      exact lowFrame a low outside ne


def treeValue (hash : Hash) (parameter : PublicParameter) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (level node : Nat) : Digest :=
  evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
    (Seeded.treeNode parameter lay treeIdx seed level node : OracleComp SphincsSecurity.HashSpec Digest)

theorem treeValue_succ (hash : Hash) (parameter : PublicParameter) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (level node : Nat) :
    treeValue hash parameter seed lay treeIdx (level+1) node=
      parentValue hash parameter lay treeIdx (level+1) node
        (treeValue hash parameter seed lay treeIdx level (2*node))
        (treeValue hash parameter seed lay treeIdx level (2*node+1)) := by
  simp only [treeValue,Seeded.treeNode,evalWithAnswerFn_bind,SphincsMaskedChainDomain.eval_hash]
  rfl

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsParents.node_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms node_trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsParents.Domain.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Domain.query_eq

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsParents.Domain.node_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Domain.node_value

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsParents.nodes_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodes_contract

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsParents.treeValue_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeValue_succ

end SigGolfCandidate.SphincsMaskedSignOtsParents
