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

namespace Levels
open SphincsMaskedSignOtsTree

def height (location : Fin 5) : Nat := if location.val<3 then 5 else 4
def width (location : Fin 5) (level : Nat) : Nat := if level ≤ height location then 2^(height location-level) else 0
def cacheBase (location : Fin 5) (level : Nat) : Nat := 0x50000+20*(2^(height location+1)-2^(height location+1-level))
def totalNodes (location : Fin 5) (levels : Nat) : Nat := 2^(height location)-2^(height location-levels)

def initSchedule (location : Fin 5) : List (Word × Instr) := [
  (0x15c8, .ADDI .x6 .x0 1),
  (0x15cc, .LUI .x28 67),
  (0x15d0, .ADDI .x28 .x28 72),
  (0x15d4, .SD .x28 .x6 0),
  (0x15d8, .LUI .x6 80),
  (0x15dc, .ADDI .x6 .x6 0),
  (0x15e0, .LUI .x28 67),
  (0x15e4, .ADDI .x28 .x28 104),
  (0x15e8, .SD .x28 .x6 0),
  (0x15ec, .LUI .x6 80),
  (0x15f0, .ADDI .x6 .x6 (BitVec.ofNat 12 (20*width location 0))),
  (0x15f4, .LUI .x28 67),
  (0x15f8, .ADDI .x28 .x28 128),
  (0x15fc, .SD .x28 .x6 0),
  (0x1600, .ADDI .x6 .x0 (BitVec.ofNat 12 (width location 1))),
  (0x1604, .LUI .x28 67),
  (0x1608, .ADDI .x28 .x28 144),
  (0x160c, .SD .x28 .x6 0)]


def init (location : Fin 5) (s : MachineState) := runSchedule (initSchedule location) s

def finishSchedule (location : Fin 5) : List (Word × Instr) := [
  (0x1810, .LUI .x28 67),
  (0x1814, .ADDI .x28 .x28 (128)),
  (0x1818, .LD .x6 .x28 (0)),
  (0x181c, .LUI .x28 67),
  (0x1820, .ADDI .x28 .x28 (104)),
  (0x1824, .SD .x28 .x6 (0)),
  (0x1828, .LUI .x28 67),
  (0x182c, .ADDI .x28 .x28 (144)),
  (0x1830, .LD .x7 .x28 (0)),
  (0x1834, .SLLI .x10 .x7 (2)),
  (0x1838, .SLLI .x11 .x7 (4)),
  (0x183c, .ADD .x10 .x10 .x11),
  (0x1840, .ADD .x6 .x6 .x10),
  (0x1844, .LUI .x28 67),
  (0x1848, .ADDI .x28 .x28 (128)),
  (0x184c, .SD .x28 .x6 (0)),
  (0x1850, .LUI .x28 67),
  (0x1854, .ADDI .x28 .x28 (144)),
  (0x1858, .LD .x6 .x28 (0)),
  (0x185c, .SRLI .x6 .x6 (1)),
  (0x1860, .LUI .x28 67),
  (0x1864, .ADDI .x28 .x28 (144)),
  (0x1868, .SD .x28 .x6 (0)),
  (0x186c, .LUI .x28 67),
  (0x1870, .ADDI .x28 .x28 (72)),
  (0x1874, .LD .x6 .x28 (0)),
  (0x1878, .ADDI .x6 .x6 (1)),
  (0x187c, .LUI .x28 67),
  (0x1880, .ADDI .x28 .x28 (72)),
  (0x1884, .SD .x28 .x6 (0)),
  (0x1888, .LUI .x28 67),
  (0x188c, .ADDI .x28 .x28 (72)),
  (0x1890, .LD .x6 .x28 (0)),
  (0x1894, .ADDI .x7 .x0 (BitVec.ofNat 12 (height location+1))),
  (0x1898, .BNE .x6 .x7 (-648))]


def finish (location : Fin 5) (s : MachineState) := runSchedule (finishSchedule location) s

theorem init_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (370+offset location) (initSchedule location) := by
  fin_cases location <;> rfl

theorem init_encoded (location : Fin 5) : ∀ e∈initSchedule location,
    instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  apply encoded_of_block _ (370+offset location) _ _ (init_image location)
  · have := offset_bound location
    change 370+offset location+18 ≤ 11000;omega
  · intro i
    have addr : ∀ i : Fin (initSchedule location).length,
        (initSchedule location)[i.val].1=BitVec.ofNat 64 (0x1000+4*(370+i.val)) := by
      change ∀ i : Fin 18,_
      intro i;fin_cases i <;> rfl
    rw [addr i,delta,←BitVec.ofNat_add]
    congr 1;omega

theorem init_checked (location : Fin 5) (s : MachineState) (pc : s.pc=0x15c8) :
    Checked (initSchedule location) s := by
  simp [initSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem init_block (location : Fin 5) (s : MachineState) (pc : s.pc=0x15c8) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 18
      (shift (delta location) (init location s)) := by
  apply block_shift _ _ (initSchedule location) _ (init_encoded location) s (init_checked location s pc)
  simp [initSchedule,Supported]

theorem entry_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (388+offset location) (levelEntrySchedule) := by
  fin_cases location <;> rfl

theorem entry_encoded (location : Fin 5) : ∀ e∈levelEntrySchedule,
    instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  apply encoded_of_block _ (388+offset location) _ _ (entry_image location)
  · have := offset_bound location
    change 388+offset location+4 ≤ 11000;omega
  · intro i
    have addr : ∀ i : Fin (levelEntrySchedule).length,
        (levelEntrySchedule)[i.val].1=BitVec.ofNat 64 (0x1000+4*(388+i.val)) := by
      change ∀ i : Fin 4,_
      intro i;fin_cases i <;> rfl
    rw [addr i,delta,←BitVec.ofNat_add]
    congr 1;omega

theorem entry_block (location : Fin 5) (s : MachineState) (pc : s.pc=0x1610) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 4
      (shift (delta location) (levelEntry s)) := by
  apply block_shift _ _ (levelEntrySchedule) _ (entry_encoded location) s (levelEntry_checked s pc)
  simp [levelEntrySchedule,Supported]

theorem finish_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (516+offset location) (finishSchedule location) := by
  fin_cases location <;> rfl

theorem finish_encoded (location : Fin 5) : ∀ e∈finishSchedule location,
    instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  apply encoded_of_block _ (516+offset location) _ _ (finish_image location)
  · have := offset_bound location
    change 516+offset location+35 ≤ 11000;omega
  · intro i
    have addr : ∀ i : Fin (finishSchedule location).length,
        (finishSchedule location)[i.val].1=BitVec.ofNat 64 (0x1000+4*(516+i.val)) := by
      change ∀ i : Fin 35,_
      intro i;fin_cases i <;> rfl
    rw [addr i,delta,←BitVec.ofNat_add]
    congr 1;omega

theorem finish_checked (location : Fin 5) (s : MachineState) (pc : s.pc=0x1810) :
    Checked (finishSchedule location) s := by
  simp [finishSchedule,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem finish_block (location : Fin 5) (s : MachineState) (pc : s.pc=0x1810) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 35
      (shift (delta location) (finish location s)) := by
  apply block_shift _ _ (finishSchedule location) _ (finish_encoded location) s (finish_checked location s pc)
  simp [finishSchedule,Supported]

theorem init_pc (location : Fin 5) (s : MachineState) (pc : s.pc=0x15c8) :
    (init location s).pc=0x1610 := by
  simp [init,initSchedule,runSchedule,execInstrBr,pc]

structure LevelControls (location : Fin 5) (s : MachineState) (k : Nat) : Prop where
  base : s.getMem 0x43068=BitVec.ofNat 64 (cacheBase location k)
  target : s.getMem 0x43080=BitVec.ofNat 64 (cacheBase location (k+1))
  level : s.getMem 0x43048=BitVec.ofNat 64 (k+1)
  count : s.getMem 0x43090=BitVec.ofNat 64 (width location (k+1))

def loopWrites : List Word := [0x43048#64,0x43068#64,0x43080#64,0x43088#64,0x43090#64]

theorem init_controls (location : Fin 5) (s : MachineState) : LevelControls location (init location s) 0 := by
  constructor <;> fin_cases location <;>
    simp [init,initSchedule,runSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,cacheBase,width,height]

theorem init_frame (location : Fin 5) (s : MachineState) (a : Word) (outside : a∉loopWrites) :
    (init location s).getMem a=s.getMem a := by
  simp only [loopWrites,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4⟩:=outside
  simp [init,initSchedule,runSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3,h4]

theorem finish_frame (location : Fin 5) (s : MachineState) (a : Word) (outside : a∉loopWrites) :
    (finish location s).getMem a=s.getMem a := by
  simp only [loopWrites,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4⟩:=outside
  simp [finish,finishSchedule,runSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3,h4]

theorem layout (location : Fin 5) : ∀ k : Fin (height location),
    cacheBase location k.val+40*width location (k.val+1)=cacheBase location (k.val+1) ∧
    cacheBase location (k.val+1)+20*width location (k.val+1)=cacheBase location (k.val+2) ∧
    cacheBase location (k.val+2) ≤ 0x53000 ∧
    cacheBase location k.val%4=0 ∧ cacheBase location (k.val+1)%4=0 ∧
    0x50000 ≤ cacheBase location k.val ∧ 0x50000 ≤ cacheBase location (k.val+1) ∧
    0<width location (k.val+1) ∧ width location (k.val+1)<2048 ∧
    2*width location (k.val+1)=width location k.val ∧
    width location (k.val+1)/2=width location (k.val+2) ∧
    totalNodes location (k.val+1)=totalNodes location k.val+width location (k.val+1) := by
  fin_cases location <;> decide

theorem earlier_layout (location : Fin 5) : ∀ (k : Fin (height location)) (l : Fin (height location+1)),l.val ≤ k.val →
    cacheBase location l.val+20*width location l.val ≤ cacheBase location (k.val+1) ∧
    cacheBase location l.val%4=0 ∧ 0x50000 ≤ cacheBase location l.val := by
  fin_cases location <;> decide

theorem entry_controls (location : Fin 5) (s : MachineState) (k : Nat) (ctx : LevelControls location s k) :
    Controls (levelEntry s) (cacheBase location k) (cacheBase location (k+1)) (k+1) (width location (k+1)) 0 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (SphincsMaskedParentLevels.levelEntry_frame s _ (by decide)).trans ctx.base
  · exact (SphincsMaskedParentLevels.levelEntry_frame s _ (by decide)).trans ctx.target
  · exact (SphincsMaskedParentLevels.levelEntry_frame s _ (by decide)).trans ctx.level
  · exact (SphincsMaskedParentLevels.levelEntry_frame s _ (by decide)).trans ctx.count
  · simp [levelEntry,runSchedule,levelEntrySchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem finish_controls (location : Fin 5) (s : MachineState) (k : Fin (height location))
    (ctx : Controls s (cacheBase location k.val) (cacheBase location (k.val+1)) (k.val+1)
      (width location (k.val+1)) (width location (k.val+1))) :
    LevelControls location (finish location s) (k.val+1) := by
  have target:=ctx.target
  have count:=ctx.count
  have level:=ctx.level
  change s.getMem 0x43080#64=_ at target
  change s.getMem 0x43090#64=_ at count
  change s.getMem 0x43048#64=_ at level
  constructor <;>
    simp [finish,finishSchedule,runSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,target,count,level]
  all_goals fin_cases location <;> fin_cases k <;> decide

theorem finish_pc (location : Fin 5) (s : MachineState) (k : Fin (height location))
    (pc : s.pc=0x1810) (level : s.getMem 0x43048=BitVec.ofNat 64 (k.val+1)) :
    (finish location s).pc=if k.val+1=height location then 0x189c else 0x1610 := by
  change s.getMem 0x43048#64=_ at level
  simp [finish,finishSchedule,runSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc,level]
  fin_cases location <;> fin_cases k <;> decide


theorem loop_key (s t : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (ctx : KeyContext s parameter seed lay treeIdx)
    (frame : ∀ a,a∉loopWrites → t.getMem a=s.getMem a) : KeyContext t parameter seed lay treeIdx := by
  obtain ⟨layer,tree,par,key⟩:=ctx
  refine ⟨(frame _ (by decide)).trans layer,(frame _ (by decide)).trans tree,?_,?_⟩
  · intro i
    simp only [MachineState.getWord32]
    rw [frame _ (by fin_cases i <;> decide)]
    exact par i
  · intro i
    simp only [MachineState.getWord32]
    rw [frame _ (by fin_cases i <;> decide)]
    exact key i

theorem entry_frame (s : MachineState) (a : Word) (outside : a∉loopWrites) :
    (levelEntry s).getMem a=s.getMem a := by
  apply SphincsMaskedParentLevels.levelEntry_frame
  intro eq;apply outside;simp [loopWrites,eq]

theorem word_frame (s t : MachineState) (frame : ∀ a,a∉loopWrites → t.getMem a=s.getMem a)
    (address : Nat) (lower : 0x50000 ≤ address) (upper : address<0x60000) :
    t.getWord32 (BitVec.ofNat 64 address)=s.getWord32 (BitVec.ofNat 64 address) :=
  SphincsMaskedSignForestParents.cache_word_frame s t frame address lower upper

theorem level_contract (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex)
    (k : Fin (height location)) (pc : s.pc=0x1610) (ctx : KeyContext s parameter seed lay treeIdx)
    (ctrl : LevelControls location s k.val)
    (source : ∀ node,node<width location k.val → Words20 s (cacheBase location k.val+20*node)
      (treeValue hash parameter seed lay treeIdx k.val node)) :
    ∃ final,Trace hash SphincsMaskedImages.sign (shift (delta location) s)
      (39+124*width location (k.val+1)) (39+139*width location (k.val+1))
      (width location (k.val+1)) (2*width location (k.val+1)) (shift (delta location) final) ∧
      LevelControls location final (k.val+1) ∧ KeyContext final parameter seed lay treeIdx ∧
      final.pc=(if k.val+1=height location then 0x189c else 0x1610) ∧
      (∀ node,node<width location (k.val+1) → Words20 final (cacheBase location (k.val+1)+20*node)
        (treeValue hash parameter seed lay treeIdx (k.val+1) node)) ∧
      (∀ address,0x50000 ≤ address → address<cacheBase location (k.val+1) → address%4=0 →
        final.getWord32 (BitVec.ofNat 64 address)=s.getWord32 (BitVec.ofNat 64 address)) ∧
      (∀ a,a.toNat<0x50000 → a∉preWrites → a∉loopWrites → final.getMem a=s.getMem a) := by
  obtain ⟨sourceEnd,targetEnd,targetBound,baseAlign,targetAlign,baseAbove,targetAbove,positive,small,twice,half,total⟩:=layout location k
  have entryKey:=loop_key s (levelEntry s) parameter seed lay treeIdx ctx (entry_frame s)
  have entryValues : ∀ j,j<2*width location (k.val+1) → Words20 (levelEntry s)
      (cacheBase location k.val+20*j) (treeValue hash parameter seed lay treeIdx k.val j) := by
    intro j hj i
    rw [word_frame s _ (entry_frame s) _ (by omega) (by omega)]
    exact source j (by omega) i
  obtain ⟨nodeTrace,nodeCtrl,nodeKey,nodePc,values,frame,lowFrame⟩:=nodes_contract location hash (levelEntry s)
    parameter seed lay treeIdx (cacheBase location k.val) (cacheBase location (k.val+1)) (k.val+1)
    (width location (k.val+1)) (treeValue hash parameter seed lay treeIdx k.val)
    (levelEntry_pc s pc) entryKey (entry_controls location s k.val ctrl) entryValues
    (by omega) (by omega) baseAlign targetAlign baseAbove positive small (width location (k.val+1)) (by omega)
  let mid:=nodes hash (width location (k.val+1)) (levelEntry s)
  have midPc : mid.pc=0x1810 := by simpa using nodePc
  refine ⟨finish location mid,?_,finish_controls location mid k nodeCtrl,
    loop_key mid _ parameter seed lay treeIdx nodeKey (finish_frame location mid),
    finish_pc location mid k midPc nodeCtrl.level,?_,?_,?_⟩
  · have trace:=(entry_block location s pc).trace.trans (nodeTrace.trans (finish_block location mid midPc).trace)
    convert trace using 1 <;> omega
  · intro node hn i
    rw [word_frame mid _ (finish_frame location mid) _ (by omega) (by omega),treeValue_succ]
    exact values node hn i
  · intro address lower upper align
    rw [word_frame mid _ (finish_frame location mid) address lower (by omega),frame address lower upper align,
      word_frame s _ (entry_frame s) address lower (by omega)]
  · intro a low outside loop
    rw [finish_frame location mid a loop,lowFrame a low outside (by intro eq;apply loop;simp [loopWrites,eq]),entry_frame s a loop]

theorem levels_contract (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex)
    (pc : s.pc=0x1610) (ctx : KeyContext s parameter seed lay treeIdx) (ctrl : LevelControls location s 0)
    (leaves : ∀ node,node<width location 0 → Words20 s (cacheBase location 0+20*node)
      (treeValue hash parameter seed lay treeIdx 0 node))
    (n : Nat) (hn : n ≤ height location) :
    ∃ final,Trace hash SphincsMaskedImages.sign (shift (delta location) s)
      (39*n+124*totalNodes location n) (39*n+139*totalNodes location n)
      (totalNodes location n) (2*totalNodes location n) (shift (delta location) final) ∧
      LevelControls location final n ∧ KeyContext final parameter seed lay treeIdx ∧
      final.pc=(if n=height location then 0x189c else 0x1610) ∧
      (∀ level,level ≤ n → ∀ node,node<width location level → Words20 final (cacheBase location level+20*node)
        (treeValue hash parameter seed lay treeIdx level node)) ∧
      (∀ a,a.toNat<0x50000 → a∉preWrites → a∉loopWrites → final.getMem a=s.getMem a) := by
  have positive : 0<height location := by fin_cases location <;> decide
  induction n with
  | zero =>
    refine ⟨s,?_,ctrl,ctx,?_,?_,by intro a _ _ _;rfl⟩
    · simpa [totalNodes] using (Trace.refl (hash:=hash) (image:=SphincsMaskedImages.sign) (shift (delta location) s))
    · simpa only [if_neg (by omega : 0≠height location)] using pc
    · intro level hl node hn
      have eq : level=0 := by omega
      subst level;exact leaves node hn
  | succ n ih =>
    obtain ⟨mid,first,midCtrl,midKey,midPc,old,firstFrame⟩:=ih (by omega)
    have npc : mid.pc=0x1610 := by rw [midPc,if_neg (by omega)]
    let k : Fin (height location):=⟨n,by omega⟩
    obtain ⟨final,last,finalCtrl,finalKey,finalPc,new,frame,lastFrame⟩:=
      level_contract location hash mid parameter seed lay treeIdx k npc midKey midCtrl (old n (by omega))
    refine ⟨final,?_,finalCtrl,finalKey,finalPc,?_,?_⟩
    · have total : totalNodes location (n+1)=totalNodes location n+width location (n+1) :=
        (layout location k).2.2.2.2.2.2.2.2.2.2.2
      have trace:=first.trans last
      dsimp [k] at trace
      rw [total]
      convert trace using 1 <;> omega
    · intro level hl node hnode
      by_cases eq : level=n+1
      · subst level;exact new node hnode
      · have le : level ≤ n := by omega
        have before:=earlier_layout location k ⟨level,by omega⟩ le
        change cacheBase location level+20*width location level ≤ cacheBase location (n+1) ∧
          cacheBase location level%4=0 ∧ 0x50000 ≤ cacheBase location level at before
        dsimp only [k] at frame
        intro i
        rw [frame _ (by omega) (by omega) (by omega)]
        exact old level le node hnode i
    · intro a low outside loop
      exact (lastFrame a low outside loop).trans (firstFrame a low outside loop)


theorem leafValue_treeValue (hash : Hash) (parameter : PublicParameter) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : Fin 32) :
    SphincsMaskedSignOtsTree.leafValue hash parameter seed lay treeIdx (subtreeLeaf leaf)=
      treeValue hash parameter seed lay treeIdx 0 leaf.val := by
  have leafEq : Concrete.leafOfNat leaf.val=subtreeLeaf leaf := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (by change leaf.val<2048;omega)
  simp only [treeValue,Seeded.treeNode,leafEq,SphincsMaskedSignOtsTree.leafValue]

theorem key_shift (d : Word) (s : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (ctx : KeyContext s parameter seed lay treeIdx) :
    KeyContext (shift d s) parameter seed lay treeIdx := by
  obtain ⟨layer,tree,par,key⟩:=ctx
  refine ⟨by simpa using layer,by simpa using tree,?_,?_⟩
  · intro i;rw [shift_word];exact par i
  · intro i;rw [shift_word];exact key i

/-- Actual signer parent loop from the leaf-cache exit to the root-copy entry.
    It retains every cached level, so subsequent authentication-path reads are covered. -/
theorem parents_contract (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex)
    (pc : s.pc=0x15cc+chainDelta location) (ctx : KeyContext s parameter seed lay treeIdx)
    (leaves : ∀ leaf : Fin 32,leaf.val<Finish.width location → Words20 s (0x50000+20*leaf.val)
      (SphincsMaskedSignOtsTree.leafValue hash parameter seed lay treeIdx (subtreeLeaf leaf))) :
    ∃ final,Trace hash SphincsMaskedImages.sign s
      (18+39*height location+124*totalNodes location (height location))
      (18+39*height location+139*totalNodes location (height location))
      (totalNodes location (height location)) (2*totalNodes location (height location)) final ∧
      final.pc=0x189c+delta location ∧
      final.getMem 0x43068=BitVec.ofNat 64 (cacheBase location (height location)) ∧
      KeyContext final parameter seed lay treeIdx ∧
      (∀ level,level ≤ height location → ∀ node,node<width location level →
        Words20 final (cacheBase location level+20*node) (treeValue hash parameter seed lay treeIdx level node)) ∧
      (∀ a,a.toNat<0x50000 → a∉preWrites → a∉loopWrites → final.getMem a=s.getMem a) := by
  let v:=s.setPC 0x15c8
  have entryPc : s.pc=0x15c8+delta location := by
    rw [pc];fin_cases location <;> decide
  have vctx : KeyContext v parameter seed lay treeIdx := ctx
  have widthEq : width location 0=Finish.width location := by fin_cases location <;> decide
  have widthBound : width location 0 ≤ 32 := by fin_cases location <;> decide
  have baseZero : cacheBase location 0=0x50000 := by simp [cacheBase]
  have key:=loop_key v (init location v) parameter seed lay treeIdx vctx (init_frame location v)
  have initial : ∀ node,node<width location 0 → Words20 (init location v) (cacheBase location 0+20*node)
      (treeValue hash parameter seed lay treeIdx 0 node) := by
    intro node hn i
    let leaf : Fin 32:=⟨node,by omega⟩
    have val:=leaves leaf (by simpa only [widthEq] using hn) i
    rw [leafValue_treeValue] at val
    rw [word_frame v _ (init_frame location v) _ (by rw [baseZero];omega) (by rw [baseZero];omega),baseZero]
    exact val
  obtain ⟨final,trace,ctrl,key,loc,values,frame⟩:=levels_contract location hash (init location v)
    parameter seed lay treeIdx (init_pc location v rfl) key (init_controls location v) initial (height location) (by omega)
  have first:=(init_block location v rfl).trace (hash:=hash)
  rw [SphincsMaskedSignOtsDomain.rebase_eq _ _ s entryPc] at first
  refine ⟨shift (delta location) final,?_,?_,?_,key_shift _ _ parameter seed lay treeIdx key,?_,?_⟩
  · convert first.trans trace using 1 <;> omega
  · rw [shift_pc,loc,if_pos rfl]
  · rw [shift_mem];exact ctrl.base
  · intro level hl node hn i
    rw [shift_word];exact values level hl node hn i
  · intro a low outside loop
    rw [shift_mem,frame a low outside loop,init_frame location v a loop]
    rfl

/-- Each concrete subtree root has the abstract seeded tree-node value. -/
theorem parents_root (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex)
    (pc : s.pc=0x15cc+chainDelta location) (ctx : KeyContext s parameter seed lay treeIdx)
    (leaves : ∀ leaf : Fin 32,leaf.val<Finish.width location → Words20 s (0x50000+20*leaf.val)
      (SphincsMaskedSignOtsTree.leafValue hash parameter seed lay treeIdx (subtreeLeaf leaf))) :
    ∃ final,Trace hash SphincsMaskedImages.sign s
      (18+39*height location+124*totalNodes location (height location))
      (18+39*height location+139*totalNodes location (height location))
      (totalNodes location (height location)) (2*totalNodes location (height location)) final ∧
      final.pc=0x189c+delta location ∧ KeyContext final parameter seed lay treeIdx ∧
      Words20 final (cacheBase location (height location))
        (treeValue hash parameter seed lay treeIdx (height location) 0) := by
  obtain ⟨final,trace,loc,base,key,values,frame⟩:=parents_contract location hash s parameter seed lay treeIdx pc ctx leaves
  refine ⟨final,trace,loc,key,?_⟩
  simpa using values (height location) (by omega) 0 (by simp [width])

end Levels

namespace RootCopy
open SphincsMaskedSignOtsTree

def code : List (Word × Instr) := [
  (0x189c,.LUI .x28 67),(0x18a0,.ADDI .x28 .x28 104),(0x18a4,.LD .x6 .x28 0),
  (0x18a8,.LUI .x7 83),(0x18ac,.ADDI .x7 .x7 0)]
def setup (s : MachineState) := runSchedule code s
def state (s : MachineState) := copyRootState (setup s)

theorem image (location : Fin 5) : DecodedBlock SphincsMaskedImages.sign (551+offset location) code := by
  fin_cases location <;> rfl

theorem encoded (location : Fin 5) : ∀ e∈code,
    instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  apply encoded_of_block _ (551+offset location) _ _ (image location)
  · have := offset_bound location
    change 551+offset location+5 ≤ 11000;omega
  · intro i
    have addr : ∀ i : Fin code.length,code[i.val].1=BitVec.ofNat 64 (0x1000+4*(551+i.val)) := by decide
    rw [addr i,delta,←BitVec.ofNat_add]
    congr 1;omega

theorem checked (s : MachineState) (pc : s.pc=0x189c) : Checked code s := by
  simp [code,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem setup_block (location : Fin 5) (s : MachineState) (pc : s.pc=0x189c) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 5 (shift (delta location) (setup s)) :=
  block_shift _ _ code (by decide) (encoded location) s (checked s pc)

theorem registers (s : MachineState) (base : Nat) (hb : s.getMem 0x43068=BitVec.ofNat 64 base) :
    (setup s).getReg .x6=BitVec.ofNat 64 base ∧ (setup s).getReg .x7=0x53000 := by
  change s.getMem 0x43068#64=_ at hb
  simp [setup,code,runSchedule,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,hb]

theorem setup_pc (s : MachineState) (pc : s.pc=0x189c) : (setup s).pc=0x18b0 := by
  simp [setup,code,runSchedule,execInstrBr,pc]

theorem setup_frame (s : MachineState) (a : Word) : (setup s).getMem a=s.getMem a := by
  simp [setup,code,runSchedule,execInstrBr]

theorem copy_image (location : Fin 5) :
    (SphincsMaskedImages.sign.code.drop (556+offset location)).take 10=
      (SphincsMaskedImages.keygen.code.drop 492).take 10 := by
  fin_cases location <;> rfl

theorem copy_word (location : Fin 5) (i : Fin 10) :
    SphincsMaskedImages.sign.code[556+offset location+i.val]?=
      SphincsMaskedImages.keygen.code[492+i.val]? := by
  have eq:=congrArg (fun words : List (BitVec 32) => words[i.val]?) (copy_image location)
  simpa only [List.getElem?_take_of_lt i.isLt,List.getElem?_drop] using eq

theorem copy_code (location : Fin 5) : Copy20Code SphincsMaskedImages.sign (556+offset location) := by
  constructor
  · intro i
    rw [copy_word location ⟨2*i.val,by omega⟩]
    exact SphincsMaskedParentNode.store_code.load i
  · intro i
    rw [show 556+offset location+2*i.val+1=556+offset location+(2*i.val+1) by omega,
      copy_word location ⟨2*i.val+1,by omega⟩]
    convert SphincsMaskedParentNode.store_code.store i using 1 <;> congr 2 <;> omega

theorem block (location : Fin 5) (s : MachineState) (base : Nat) (pc : s.pc=0x189c)
    (hb : s.getMem 0x43068=BitVec.ofNat 64 base) (align : base%4=0) (bound : base+20 ≤ 0x53000) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 15
      (shift (delta location) (state s)) := by
  have regs:=registers s base hb
  have loc : (shift (delta location) (setup s)).pc=BitVec.ofNat 64 (0x1000+4*(556+offset location)) := by
    rw [shift_pc,setup_pc s pc,delta]
    change BitVec.ofNat 64 0x18b0+BitVec.ofNat 64 (4*offset location)=_
    rw [←BitVec.ofNat_add]
    congr 1;omega
  have copied:=copy20_block_general SphincsMaskedImages.sign (556+offset location) (copy_code location)
    (shift (delta location) (setup s)) base 0x53000 loc
    (by simpa using regs.1) (by simpa using regs.2) align (by dsimp [MEMORY_BYTES];omega)
    (by decide) (by decide) (by have := offset_bound location;omega)
  rw [copyRoot_shift] at copied
  exact ordinary_trans _ _ _ _ 5 10 (setup_block location s pc) copied

theorem value (s : MachineState) (base : Nat) (hb : s.getMem 0x43068=BitVec.ofNat 64 base)
    (align : base%4=0) (bound : base+20 ≤ 0x53000) (i : Fin 5) :
    (state s).getWord32 (BitVec.ofNat 64 (0x53000+4*i.val))=
      s.getWord32 (BitVec.ofNat 64 (base+4*i.val)) := by
  have regs:=registers s base hb
  rw [state,SphincsMaskedSignForestParents.copy_data _ base 0x53000
    (by omega) (by decide) align (by decide) (Or.inl bound) regs.1 regs.2 i]
  simp only [MachineState.getWord32,setup_frame]

theorem frame (s : MachineState) (a : Word)
    (outside : a≠0x53000#64 ∧ a≠0x53008#64 ∧ a≠0x53010#64) :
    (state s).getMem a=s.getMem a := by
  rw [state,copyRoot_mem_frame]
  · exact setup_frame s a
  · intro i
    have dst : (setup s).getReg .x7=0x53000 := by
      simp [setup,code,runSchedule,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    rw [dst]
    fin_cases i <;> simp_all [signExtend12,alignToDword]

theorem pc (s : MachineState) (loc : s.pc=0x189c) : (state s).pc=0x18d8 := by
  rw [state,SphincsMaskedParentNode.copyRoot_pc,setup_pc s loc];rfl

end RootCopy

namespace RootCopy

theorem key_context (s : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (ctx : KeyContext s parameter seed lay treeIdx) :
    KeyContext (state s) parameter seed lay treeIdx := by
  obtain ⟨layer,tree,par,key⟩:=ctx
  refine ⟨(frame s _ (by decide)).trans layer,(frame s _ (by decide)).trans tree,?_,?_⟩
  · intro i
    simp only [MachineState.getWord32]
    rw [frame s _ (by fin_cases i <;> decide)]
    exact par i
  · intro i
    simp only [MachineState.getWord32]
    rw [frame s _ (by fin_cases i <;> decide)]
    exact key i

theorem word_frame (s : MachineState) (address : Nat) (bound : address<0x53000) :
    (state s).getWord32 (BitVec.ofNat 64 address)=s.getWord32 (BitVec.ofNat 64 address) := by
  have upper : (alignToDword (BitVec.ofNat 64 address)).toNat<0x53000 := by
    simp only [alignToDword,BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : address<2^64)]
    exact lt_of_le_of_lt Nat.and_le_left bound
  simp only [MachineState.getWord32]
  rw [frame]
  constructor
  · intro eq;rw [eq] at upper;contradiction
  constructor
  · intro eq;rw [eq] at upper;contradiction
  · intro eq;rw [eq] at upper;contradiction

end RootCopy

/-- The tree-height parameter selected by each lower-layer bytecode block. -/
def signerLayer (location : Fin 5) : Layer := ⟨location.val+1,by change location.val+1<6;omega⟩

theorem signerLayer_height (location : Fin 5) : Levels.height location=layerHeight (signerLayer location) := by
  fin_cases location <;> decide

/-- All lower-layer parent nodes and the root copy, with the exact cache values
    retained for the subsequent authentication-path serialization. -/
theorem parents_root_copy (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex)
    (pc : s.pc=0x15cc+chainDelta location) (ctx : KeyContext s parameter seed lay treeIdx)
    (leaves : ∀ leaf : Fin 32,leaf.val<SphincsMaskedSignOtsTree.Finish.width location →
      Words20 s (0x50000+20*leaf.val)
        (SphincsMaskedSignOtsTree.leafValue hash parameter seed lay treeIdx (SphincsMaskedSignOtsTree.subtreeLeaf leaf))) :
    ∃ final,Trace hash SphincsMaskedImages.sign s
      (33+39*Levels.height location+124*Levels.totalNodes location (Levels.height location))
      (33+39*Levels.height location+139*Levels.totalNodes location (Levels.height location))
      (Levels.totalNodes location (Levels.height location)) (2*Levels.totalNodes location (Levels.height location)) final ∧
      final.pc=0x18d8+delta location ∧ KeyContext final parameter seed lay treeIdx ∧
      Words20 final 0x53000 (treeValue hash parameter seed lay treeIdx (Levels.height location) 0) ∧
      (∀ level,level ≤ Levels.height location → ∀ node,node<Levels.width location level →
        Words20 final (Levels.cacheBase location level+20*node) (treeValue hash parameter seed lay treeIdx level node)) ∧
      (∀ a,a.toNat<0x50000 → a∉preWrites → a∉Levels.loopWrites → final.getMem a=s.getMem a) := by
  obtain ⟨mid,parents,midPc,base,key,values,firstFrame⟩:=Levels.parents_contract location hash s parameter seed lay treeIdx pc ctx leaves
  have bounds : ∀ level : Fin (Levels.height location+1),
      Levels.cacheBase location level.val+20*Levels.width location level.val ≤ 0x53000 := by
    fin_cases location <;> decide
  have rootWidth : Levels.width location (Levels.height location)=1 := by simp [Levels.width]
  have rootBound : Levels.cacheBase location (Levels.height location)+20 ≤ 0x53000 := by
    have h:=bounds ⟨Levels.height location,by omega⟩
    simpa only [rootWidth,Nat.mul_one] using h
  have rootAlign : Levels.cacheBase location (Levels.height location)%4=0 := by fin_cases location <;> decide
  let v:=mid.setPC 0x189c
  have copied:=RootCopy.block location v (Levels.cacheBase location (Levels.height location)) rfl base rootAlign rootBound
  rw [SphincsMaskedSignOtsDomain.rebase_eq _ _ mid midPc] at copied
  let final:=shift (delta location) (RootCopy.state v)
  refine ⟨final,?_,?_,Levels.key_shift _ _ parameter seed lay treeIdx (RootCopy.key_context v parameter seed lay treeIdx key),?_,?_,?_⟩
  · convert parents.trans copied.trace using 1 <;> omega
  · rw [shift_pc,RootCopy.pc v rfl]
  · intro i
    rw [shift_word,RootCopy.value v _ base rootAlign rootBound i,SphincsMaskedSignOtsTree.word_setPC]
    simpa using values (Levels.height location) (by omega) 0 (by rw [rootWidth];omega) i
  · intro level hlevel node hnode i
    have h:=bounds ⟨level,by omega⟩
    change Levels.cacheBase location level+20*Levels.width location level ≤ 0x53000 at h
    rw [shift_word,RootCopy.word_frame v _ (by omega),SphincsMaskedSignOtsTree.word_setPC]
    exact values level hlevel node hnode i
  · intro a low outside loop
    have separate : a≠0x53000#64 ∧ a≠0x53008#64 ∧ a≠0x53010#64 := by
      constructor
      · intro eq;rw [eq] at low;contradiction
      constructor
      · intro eq;rw [eq] at low;contradiction
      · intro eq;rw [eq] at low;contradiction
    rw [shift_mem,RootCopy.frame v a separate,MachineState.getMem_setPC]
    exact firstFrame a low outside loop

/-- At the matching layer, the root is exactly the abstract seeded treeRoot. -/
theorem parents_abstract_root (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (treeIdx : TreeIndex)
    (pc : s.pc=0x15cc+chainDelta location) (ctx : KeyContext s parameter seed (signerLayer location) treeIdx)
    (leaves : ∀ leaf : Fin 32,leaf.val<SphincsMaskedSignOtsTree.Finish.width location →
      Words20 s (0x50000+20*leaf.val)
        (SphincsMaskedSignOtsTree.leafValue hash parameter seed (signerLayer location) treeIdx (SphincsMaskedSignOtsTree.subtreeLeaf leaf))) :
    ∃ final,Trace hash SphincsMaskedImages.sign s
      (33+39*Levels.height location+124*Levels.totalNodes location (Levels.height location))
      (33+39*Levels.height location+139*Levels.totalNodes location (Levels.height location))
      (Levels.totalNodes location (Levels.height location)) (2*Levels.totalNodes location (Levels.height location)) final ∧
      final.pc=0x18d8+delta location ∧ Words20 final 0x53000
        (evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
          (Seeded.treeRoot parameter (signerLayer location) treeIdx seed : OracleComp SphincsSecurity.HashSpec Digest)) := by
  obtain ⟨final,trace,loc,key,value,cache,frame⟩:=parents_root_copy location hash s parameter seed (signerLayer location) treeIdx pc ctx leaves
  refine ⟨final,trace,loc,?_⟩
  simpa only [treeValue,Seeded.treeRoot,signerLayer_height] using value


/-- Complete subtree construction from the exact leaf-loop entry through the
    root-copy exit. It requires only the live key context and zero leaf counter. -/
theorem subtree_root (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (treeIdx : TreeIndex)
    (pc : s.pc=0x111c+chainDelta location) (counter : s.getMem 0x43020=0)
    (ctx : KeyContext s parameter seed (signerLayer location) treeIdx) :
    ∃ final,Trace hash SphincsMaskedImages.sign s
      (41220*SphincsMaskedSignOtsTree.Finish.width location+33+39*Levels.height location+
        124*Levels.totalNodes location (Levels.height location))
      (44683*SphincsMaskedSignOtsTree.Finish.width location+33+39*Levels.height location+
        139*Levels.totalNodes location (Levels.height location))
      (417*SphincsMaskedSignOtsTree.Finish.width location+Levels.totalNodes location (Levels.height location))
      (485*SphincsMaskedSignOtsTree.Finish.width location+2*Levels.totalNodes location (Levels.height location)) final ∧
      final.pc=0x18d8+delta location ∧ KeyContext final parameter seed (signerLayer location) treeIdx ∧
      Words20 final 0x53000
        (evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
          (Seeded.treeRoot parameter (signerLayer location) treeIdx seed : OracleComp SphincsSecurity.HashSpec Digest)) ∧
      (∀ level,level ≤ Levels.height location → ∀ node,node<Levels.width location level →
        Words20 final (Levels.cacheBase location level+20*node)
          (treeValue hash parameter seed (signerLayer location) treeIdx level node)) ∧
      (∀ a,SphincsMaskedSignOtsTree.Frame.Retained a → a.toNat<0x50000 → a∉preWrites → a∉Levels.loopWrites →
        final.getMem a=s.getMem a) := by
  obtain ⟨mid,leaves,midPc,count,key,values,firstFrame⟩:=SphincsMaskedSignOtsTree.all_leaves location hash s
    parameter seed (signerLayer location) treeIdx ctx pc counter
  obtain ⟨final,parents,finalPc,finalKey,root,cache,lastFrame⟩:=parents_root_copy location hash mid
    parameter seed (signerLayer location) treeIdx midPc key values
  refine ⟨final,?_,finalPc,finalKey,?_,cache,?_⟩
  · convert leaves.trans parents using 1 <;> omega
  · simpa only [treeValue,Seeded.treeRoot,signerLayer_height] using root
  · intro a retained low outside loop
    exact (lastFrame a low outside loop).trans (firstFrame a retained)

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsParents.Levels.levels_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Levels.levels_contract

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsParents.Levels.parents_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Levels.parents_contract

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsParents.RootCopy.block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RootCopy.block

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsParents.parents_root_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parents_root_copy

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsParents.parents_abstract_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parents_abstract_root

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsParents.subtree_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms subtree_root

end SigGolfCandidate.SphincsMaskedSignOtsParents
