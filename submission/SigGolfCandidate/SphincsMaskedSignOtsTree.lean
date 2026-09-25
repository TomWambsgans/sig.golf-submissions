import SigGolfCandidate.SphincsMaskedSignOtsDomain

namespace SigGolfCandidate.SphincsMaskedSignOtsTree
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy SphincsMaskedSignOtsShift
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A single contiguous image certificate avoids repeated traversal of late code positions. -/
def DecodedBlock (image : Image) (start : Nat) (code : List (Word × Instr)) : Prop :=
  ((image.code.drop start).take code.length).map decodeInstruction=
    code.map (fun e => some (.base e.2))

theorem decoded_at (image : Image) (start : Nat) (code : List (Word × Instr))
    (block : DecodedBlock image start code) (i : Fin code.length) (bound : start+i.val<11000) :
    instructionAt image (BitVec.ofNat 64 (0x1000+4*(start+i.val)))=some (.base code[i.val].2) := by
  have eq:=congrArg (fun words : List (Option Instruction) => words[i.val]?.join) block
  simp only [List.getElem?_map,List.getElem?_take_of_lt i.isLt,List.getElem?_drop,
    List.getElem?_eq_getElem i.isLt,Option.map_some,Option.join_some] at eq
  rw [SphincsMaskedSignOtsShift.fetch_index image _ bound]
  cases h : image.code[start+i.val]? <;> simpa [h,Option.join] using eq

theorem encoded_of_block (image : Image) (start : Nat) (code : List (Word × Instr))
    (delta : Word) (block : DecodedBlock image start code) (bound : start+code.length≤11000)
    (addresses : ∀ i : Fin code.length,code[i.val].1+delta=BitVec.ofNat 64 (0x1000+4*(start+i.val))) :
    ∀ e∈code,instructionAt image (e.1+delta)=some (.base e.2) := by
  intro e he
  obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.mp he
  rw [addresses ⟨i,hi⟩]
  exact decoded_at image start code block ⟨i,hi⟩ (by omega)

namespace Store
open SphincsMaskedSignForestLoop

def offset (location : Fin 5) : Nat := chainOffset location-647
def delta (location : Fin 5) : Word := BitVec.ofNat 64 (4*offset location)

theorem offset_bound (location : Fin 5) : 808≤offset location ∧ offset location≤6708 := by
  fin_cases location <;> decide

theorem entry_pc (location : Fin 5) : 0x1f64+delta location=0x1548+chainDelta location := by
  fin_cases location <;> decide

theorem setup_image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (985+offset location) storeSetupSchedule := by
  fin_cases location <;> rfl

theorem setup_encoded (location : Fin 5) : ∀ e∈storeSetupSchedule,
    instructionAt SphincsMaskedImages.sign (e.1+delta location)=some (.base e.2) := by
  apply encoded_of_block _ (985+offset location) _ _ (setup_image location)
  · have := offset_bound location
    change 985+offset location+11≤11000;omega
  · intro i
    have addr : ∀ i : Fin storeSetupSchedule.length,
        storeSetupSchedule[i.val].1=BitVec.ofNat 64 (0x1000+4*(985+i.val)) := by decide
    rw [addr i,delta,←BitVec.ofNat_add]
    congr 1;omega

open SphincsVerifierCopy SphincsVerifierMessageCopy SphincsVerifierFtsCopyAccess

theorem setup_block (location : Fin 5) (s : MachineState) (pc : s.pc=0x1f64) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 11
      (shift (delta location) (storeSetup s)) :=
  block_shift _ _ _ (by decide) (setup_encoded location) s (storeSetup_checked s pc)

theorem copy_image (location : Fin 5) :
    (SphincsMaskedImages.sign.code.drop (996+offset location)).take 10=
      (SphincsMaskedImages.sign.code.drop 996).take 10 := by
  fin_cases location <;> rfl

theorem copy_word (location : Fin 5) (i : Fin 10) :
    SphincsMaskedImages.sign.code[996+offset location+i.val]?=
      SphincsMaskedImages.sign.code[996+i.val]? := by
  have eq:=congrArg (fun words : List (BitVec 32) => words[i.val]?) (copy_image location)
  simpa only [List.getElem?_take_of_lt i.isLt,List.getElem?_drop] using eq

theorem copy_code (location : Fin 5) : Copy20Code SphincsMaskedImages.sign (996+offset location) := by
  constructor
  · intro i
    rw [copy_word location ⟨2*i.val,by omega⟩]
    exact SphincsMaskedSignForestLoop.store_code.load i
  · intro i
    rw [show 996+offset location+2*i.val+1=996+offset location+(2*i.val+1) by omega,
      copy_word location ⟨2*i.val+1,by omega⟩]
    convert SphincsMaskedSignForestLoop.store_code.store i using 1 <;> congr 2 <;> omega

/-- The same21-instruction store block writes each WOTS leaf to the temporary tree cache. -/
theorem stored_block (location : Fin 5) (s : MachineState) (leaf : Fin 256)
    (pc : s.pc=0x1f64) (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 21
      (shift (delta location) (stored s)) := by
  have regs:=storeSetup_registers s leaf.val counter
  have bound:=offset_bound location
  have loc : (shift (delta location) (storeSetup s)).pc=BitVec.ofNat 64 (0x1000+4*(996+offset location)) := by
    rw [shift_pc,storeSetup_pc s pc,delta]
    change BitVec.ofNat 64 0x1f90+BitVec.ofNat 64 (4*offset location)=_
    rw [←BitVec.ofNat_add]
    congr 1;omega
  have copied:=copy20_block_general SphincsMaskedImages.sign (996+offset location) (copy_code location)
    (shift (delta location) (storeSetup s)) 0x42000 (0x50000+20*leaf.val) loc
    (by simpa using regs.1) (by simpa using regs.2) (by decide) (by decide)
    (by omega) (by dsimp [MEMORY_BYTES];omega) (by omega)
  rw [copyRoot_shift] at copied
  exact ordinary_trans _ _ _ _ 11 10 (setup_block location s pc) copied

/-- Exact storage semantics, including the adjacent20-byte slots sharing64-bit cells. -/
theorem stored_value (location : Fin 5) (s : MachineState) (leaf : Fin 256)
    (pc : s.pc=0x1f64) (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    OrdinarySteps SphincsMaskedImages.sign (shift (delta location) s) 21
      (shift (delta location) (stored s)) ∧
    (∀ i : Fin 5, (shift (delta location) (stored s)).getWord32
      (BitVec.ofNat 64 (0x50000+20*leaf.val+4*i.val))=
      s.getWord32 (BitVec.ofNat 64 (0x42000+4*i.val))) :=
by
  refine ⟨stored_block location s leaf pc counter,?_⟩
  intro i
  rw [shift_word]
  exact stored_data s leaf counter i

end Store
namespace Finish

def width (location : Fin 5) : Nat := if location.val<3 then 32 else 16

def code (location : Fin 5) : List (Word × Instr) := [
  (0x159c,.LUI .x28 67),(0x15a0,.ADDI .x28 .x28 32),(0x15a4,.LD .x6 .x28 0),
  (0x15a8,.ADDI .x6 .x6 1),(0x15ac,.LUI .x28 67),(0x15b0,.ADDI .x28 .x28 32),
  (0x15b4,.SD .x28 .x6 0),(0x15b8,.LUI .x28 67),(0x15bc,.ADDI .x28 .x28 32),
  (0x15c0,.LD .x6 .x28 0),(0x15c4,.ADDI .x7 .x0 (BitVec.ofNat 12 (width location))),
  (0x15c8,.BNE .x6 .x7 (-1196))]

def state (location : Fin 5) (s : MachineState) : MachineState := runSchedule (code location) s

theorem image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (359+chainOffset location) (code location) := by
  fin_cases location <;> rfl

theorem encoded (location : Fin 5) : ∀ e∈code location,
    instructionAt SphincsMaskedImages.sign (e.1+chainDelta location)=some (.base e.2) := by
  apply encoded_of_block _ (359+chainOffset location) _ _ (image location)
  · have := SphincsMaskedSignOtsShift.offset_bound location
    change 359+chainOffset location+12≤11000;omega
  · intro i
    have addr : ∀ i : Fin (code location).length,
        (code location)[i.val].1=BitVec.ofNat 64 (0x1000+4*(359+i.val)) := by
      change ∀ i : Fin 12,_
      intro i;fin_cases i <;> rfl
    rw [addr i,delta_value,←BitVec.ofNat_add]
    congr 1;omega

theorem checked (location : Fin 5) (s : MachineState) (pc : s.pc=0x159c) : Checked (code location) s := by
  simp [code,Checked,execInstrBr,ordinaryStep,memoryArgumentsValid,
    accessValid,rangeValid,MEMORY_BYTES,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem block (location : Fin 5) (s : MachineState) (pc : s.pc=0x159c) :
    OrdinarySteps SphincsMaskedImages.sign (shift (chainDelta location) s) 12
      (shift (chainDelta location) (state location s)) := by
  apply block_shift _ _ _ _ (encoded location) s (checked location s pc)
  intro e he
  have all : ∀ location,∀ e∈code location,Supported e.2 := by intro location;simp [code,Supported]
  exact all location e he

theorem counter (location : Fin 5) (s : MachineState) :
    (state location s).getMem 0x43020=s.getMem 0x43020+1 := by
  simp [state,code,runSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem pc (location : Fin 5) (s : MachineState) (loc : s.pc=0x159c) :
    (state location s).pc=if s.getMem 0x43020+1=BitVec.ofNat 64 (width location) then 0x15cc else 0x111c := by
  fin_cases location <;>
    simp [state,code,width,runSchedule,execInstrBr,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,loc]

theorem frame (location : Fin 5) (s : MachineState) (a : Word) (outside : a≠0x43020#64) :
    (state location s).getMem a=s.getMem a := by
  simp [state,code,runSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,outside]

end Finish

namespace Entry
open SphincsMaskedLeafLoop

theorem image (location : Fin 5) :
    DecodedBlock SphincsMaskedImages.sign (71+chainOffset location) entrySchedule := by
  fin_cases location <;> rfl

theorem encoded (location : Fin 5) : ∀ e∈entrySchedule,
    instructionAt SphincsMaskedImages.sign (e.1+chainDelta location)=some (.base e.2) := by
  apply encoded_of_block _ (71+chainOffset location) _ _ (image location)
  · have := SphincsMaskedSignOtsShift.offset_bound location
    change 71+chainOffset location+4≤11000;omega
  · intro i
    have addr : ∀ i : Fin entrySchedule.length,
        entrySchedule[i.val].1=BitVec.ofNat 64 (0x1000+4*(71+i.val)) := by decide
    rw [addr i,delta_value,←BitVec.ofNat_add]
    congr 1;omega

theorem block (location : Fin 5) (s : MachineState) (pc : s.pc=0x111c) :
    OrdinarySteps SphincsMaskedImages.sign (shift (chainDelta location) s) 4
      (shift (chainDelta location) (entry s)) :=
  block_shift _ _ _ (by decide) (encoded location) s (entry_checked s pc)

end Entry

namespace Payload
open SphincsMaskedLeafLoop

theorem add_swap (a b c : Word) : (a+b)+c=(a+c)+b := by
  rw [BitVec.add_assoc,BitVec.add_comm b c,←BitVec.add_assoc]

theorem copy_code (location : Fin 5) : CopyCode SphincsMaskedImages.sign (0x1488+chainDelta location) := by
  obtain ⟨c0,c1,c2,c3,c4,c5⟩:=payload_copy_code
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [instruction_transfer location 0x1488 (by decide) (by decide) (by decide)];exact c0
  · rw [add_swap,instruction_transfer location (0x1488+4) (by decide) (by decide) (by decide)];exact c1
  · rw [add_swap,instruction_transfer location (0x1488+8) (by decide) (by decide) (by decide)];exact c2
  · rw [add_swap,instruction_transfer location (0x1488+12) (by decide) (by decide) (by decide)];exact c3
  · rw [add_swap,instruction_transfer location (0x1488+16) (by decide) (by decide) (by decide)];exact c4
  · rw [add_swap,instruction_transfer location (0x1488+20) (by decide) (by decide) (by decide)];exact c5

theorem setup_block (location : Fin 5) (s : MachineState) (pc : s.pc=0x1464) :
    OrdinarySteps SphincsMaskedImages.sign (shift (chainDelta location) s) 9
      (shift (chainDelta location) (copySetup s)) :=
  block_shift _ _ _ (by decide) (encoded_of location copySetupSchedule (by decide) copySetup_code)
    s (copySetup_checked s pc)

/-- Exact copying of the complete1,040-byte endpoint payload, including its control frame. -/
theorem copy (location : Fin 5) (s : MachineState) (pc : s.pc=0x1464) :
    ∃ t, OrdinarySteps SphincsMaskedImages.sign (shift (chainDelta location) s) 789 t ∧
      t.pc=0x14a0+chainDelta location ∧ t.getMem 0x43010=0 ∧
      (∀ i : Fin 1040,t.getByte (BitVec.ofNat 64 (0x40028+i.val))=
        s.getByte (BitVec.ofNat 64 (0x44300+i.val))) ∧
      (∀ a, a≠0x43010#64 → (∀ i, i<130 → a≠wordAddress 0x40028 i) → t.getMem a=s.getMem a) := by
  have regs:=copySetup_registers s
  have inv : CopyInvariant (0x1488+chainDelta location) 0x44300 0x40028 130 130
      (shift (chainDelta location) (copySetup s)) := by
    refine ⟨by decide,by decide,?_,?_,?_,?_⟩
    · simpa [shift_pc] using congrArg (fun p => p+chainDelta location) (copySetup_pc s pc)
    · simpa using regs.1
    · simpa using regs.2.1
    · simpa using regs.2.2
  obtain ⟨t,run,done,copied,frame⟩:=copy_all SphincsMaskedImages.sign (0x1488+chainDelta location)
    (copy_code location) 0x44300 0x40028 130 (shift (chainDelta location) (copySetup s)) inv
    (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))
  refine ⟨t,ordinary_trans _ _ _ _ 9 780 (setup_block location s pc) run,?_,?_,?_,?_⟩
  · simpa [add_swap] using done.2.2.1
  · rw [frame,shift_mem,SphincsMaskedLeafRefinement.copySetup_position]
    intro i hi eq
    have h:=congrArg BitVec.toNat eq
    change 0x43010=(0x40028+8*i)%2^64 at h
    omega
  · intro i
    apply SphincsVerifierFtsRootCopyBytes.bytes_eq_of_words s t 0x44300 0x40028 1040
      (by decide) (by decide) (by decide) (by decide) _ i.val i.isLt
    intro j hj
    rw [copied j hj,shift_mem,SphincsMaskedLeafRefinement.copySetup_frame]
    intro eq
    have h:=congrArg BitVec.toNat eq
    simp only [wordAddress,BitVec.toNat_ofNat] at h
    omega
  · intro a pos outside
    rw [frame a outside,shift_mem,SphincsMaskedLeafRefinement.copySetup_frame s a pos]

end Payload

namespace Frame
open SphincsMaskedChainLoop SphincsMaskedChainStep SphincsMaskedChainEndpoints
open SphincsVerifierCopyMemory

def controls : List Word := [0x43000#64,0x43008#64,0x43078#64,0x430a0#64,0x430a8#64,
  0x44a00#64,0x44a08#64,0x44a10#64]
def Protected (a : Word) : Prop :=
  a.toNat<0x40000 ∨ 0x50000≤a.toNat ∨ a∈controls ∨ a=0x43020#64
def Busy (a : Word) : Prop :=
  0x40000≤a.toNat ∧ a.toNat<0x50000 ∧ a∉controls ∧ a≠0x43020#64
instance (a : Word) : Decidable (Busy a) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def Retained (a : Word) : Prop := a.toNat<0x40000 ∨ 0x53000≤a.toNat ∨ a∈controls

theorem retained_protected (a : Word) (ha : Retained a) : Protected a := by
  rcases ha with low | high | control
  · exact Or.inl low
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl control))

theorem protected_ne (a b : Word) (ha : Protected a) (hb : Busy b) : a≠b := by
  intro eq;subst b
  have lo:=hb.1
  have hi:=hb.2.1
  rcases ha with low | high | control | leaf
  · omega
  · omega
  · exact hb.2.2.1 control
  · exact hb.2.2.2 leaf

theorem outside (writes : List Word) (busy : ∀ b∈writes,Busy b) (a : Word) (ha : Protected a) : a∉writes := by
  intro member
  exact protected_ne a a ha (busy a member) rfl

theorem chain_value (hash : Hash) (s : MachineState) (a : Word) (ha : Protected a) :
    (chainValue hash s).getMem a=s.getMem a := by
  rw [chainValue,walk_frame hash 7 _ a (outside _ (by simp [stepWrites,prepareWrites,answerWrites,finishWrites,Busy,controls]) a ha)]
  exact initialChain_frame hash s a (outside _ (by simp [initialWrites,secretPrepareWrites,answerWrites,secretFinishWrites,Busy,controls]) a ha)

theorem endpoint_busy : ∀ (c : Fin 52) (i : Fin 5),Busy (SphincsMaskedChainFrame.endpointCell c i) := by decide

theorem endpoint_store (s : MachineState) (c : Fin 52) (counter : s.getMem 0x43050=BitVec.ofNat 64 c.val)
    (a : Word) (ha : Protected a) : (endpointStored s).getMem a=s.getMem a := by
  change (SphincsVerifierCopy.copyRootState (endpointSetup s)).getMem a=_
  rw [copyRoot_mem_frame]
  · exact endpointSetup_frame s a
  · intro i
    rw [(endpointSetup_registers s c.val counter).2]
    have addr : BitVec.ofNat 64 (0x44300+20*c.val)+signExtend12 (4#12*BitVec.ofNat 12 i.val)=
        BitVec.ofNat 64 (0x44300+20*c.val+4*i.val) := by
      fin_cases i <;> simp [signExtend12,←BitVec.ofNat_add]
    rw [addr]
    exact protected_ne a (SphincsMaskedChainFrame.endpointCell c i) ha (endpoint_busy c i)

theorem chain_next (hash : Hash) (s : MachineState) (c : Fin 52)
    (counter : s.getMem 0x43050=BitVec.ofNat 64 c.val) (a : Word) (ha : Protected a) :
    (chainNext hash s).getMem a=s.getMem a := by
  change (endpointFinish (endpointStored (chainValue hash s))).getMem a=_
  rw [endpointFinish_frame _ a (protected_ne a _ ha (by decide)),
    endpoint_store _ c ((chainValue_counter hash s).trans counter) a ha,chain_value hash s a ha]

theorem chains (hash : Hash) (s : MachineState) (pc : s.pc=0x112c) (counter : s.getMem 0x43050=0)
    (n : Nat) (hn : n≤52) (a : Word) (ha : Protected a) :
    (SphincsMaskedChainLoop.chains hash n s).getMem a=s.getMem a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [SphincsMaskedChainLoop.chains,chain_next hash _ ⟨n,by omega⟩
      (SphincsMaskedChainLoop.chains_trace hash s pc counter n (by omega)).2.1 a ha]
    exact ih (by omega)

theorem entry (s : MachineState) (a : Word) (ha : Protected a) :
    (SphincsMaskedLeafLoop.entry s).getMem a=s.getMem a :=
  SphincsMaskedLeafRefinement.entry_frame s a (protected_ne a _ ha (by decide))

theorem payload_busy : ∀ i : Fin 130,Busy (wordAddress 0x40028 i.val) := by decide

theorem payload_outside (a : Word) (ha : Protected a) (i : Nat) (hi : i<130) : a≠wordAddress 0x40028 i :=
  protected_ne a _ ha (payload_busy ⟨i,hi⟩)

theorem leaf_hash (hash : Hash) (s : MachineState) (a : Word) (ha : Protected a) :
    (SphincsMaskedLeafLoop.answerState hash s).getMem a=s.getMem a := by
  have dst:=(SphincsMaskedLeafLoop.hashPrepare_registers s).2.2.1
  have h0:=protected_ne a 0x42000#64 ha (by decide)
  have h1:=protected_ne a 0x42008#64 ha (by decide)
  have h2:=protected_ne a 0x42010#64 ha (by decide)
  have h3:=protected_ne a 0x42018#64 ha (by decide)
  simp [SphincsMaskedLeafLoop.answerState,writeHash,dst,MachineState.writeWords,h0,h1,h2,h3]
  apply SphincsMaskedLeafDomain.hashPrepare_frame
  exact outside _ (by simp [SphincsMaskedLeafDomain.headerWrites,Busy,controls]) a ha

theorem retained_ne_cache (a b : Word) (ha : Retained a) (hb : 0x50000≤b.toNat ∧ b.toNat<0x53000) : a≠b := by
  intro eq;subst b
  rcases ha with low | high | control
  · omega
  · omega
  · have bound : ∀ b∈controls,b.toNat<0x50000 := by simp [controls]
    have := bound a control
    omega

theorem store_cell_bound : ∀ (leaf : Fin 256) (i : Fin 5),
    0x50000≤(alignToDword (BitVec.ofNat 64 (0x50000+20*leaf.val+4*i.val))).toNat ∧
    (alignToDword (BitVec.ofNat 64 (0x50000+20*leaf.val+4*i.val))).toNat<0x53000 := by
  intro leaf i
  refine ⟨SphincsMaskedSignForestLoop.cache_cell_lower leaf i,?_⟩
  unfold alignToDword
  rw [BitVec.toNat_and]
  apply lt_of_le_of_lt Nat.and_le_left
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 0x50000+20*leaf.val+4*i.val<2^64)]
  omega

theorem store (s : MachineState) (leaf : Fin 256) (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val)
    (a : Word) (ha : Retained a) : (SphincsMaskedSignForestLoop.stored s).getMem a=s.getMem a := by
  open SphincsMaskedSignForestLoop in
  change (SphincsVerifierCopy.copyRootState (storeSetup s)).getMem a=_
  rw [copyRoot_mem_frame]
  · exact SphincsMaskedSignForestLoop.storeSetup_frame s a
  · intro i
    rw [(SphincsMaskedSignForestLoop.storeSetup_registers s leaf.val counter).2]
    have addr : BitVec.ofNat 64 (0x50000+20*leaf.val)+signExtend12 (4#12*BitVec.ofNat 12 i.val)=
        BitVec.ofNat 64 (0x50000+20*leaf.val+4*i.val) := by
      fin_cases i <;> simp [signExtend12,←BitVec.ofNat_add]
    rw [addr]
    exact retained_ne_cache a _ ha (store_cell_bound leaf i)

theorem retained_ne_leaf (a : Word) (ha : Retained a) : a≠0x43020#64 := by
  rcases ha with low | high | control
  · intro eq;subst a;contradiction
  · intro eq;subst a;contradiction
  · have all : ∀ b∈controls,b≠0x43020#64 := by simp [controls]
    exact all a control

end Frame

open SphincsSecurity SphincsBridge SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsMaskedChainLoop SphincsMaskedLeafLoop
open SphincsMaskedSignOtsDomain

def KeyContext (s : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) : Prop :=
  s.getMem 0x43000#64=BitVec.ofNat 64 lay.val ∧
  s.getMem 0x43008#64=BitVec.ofNat 64 treeIdx.val ∧ Words20 s 0x74 parameter ∧ Words32 s seed

theorem context_transport (s t : MachineState) (parameter : PublicParameter) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (ctx : KeyContext s parameter seed lay treeIdx)
    (frame : ∀ a,Frame.Retained a → t.getMem a=s.getMem a) : KeyContext t parameter seed lay treeIdx := by
  obtain ⟨layer,tree,par,key⟩:=ctx
  refine ⟨(frame _ (by simp [Frame.Retained,Frame.controls])).trans layer,
    (frame _ (by simp [Frame.Retained,Frame.controls])).trans tree,?_,?_⟩
  · intro i
    simp only [MachineState.getWord32]
    rw [frame _ (Or.inl (by fin_cases i <;> decide))]
    exact par i
  · intro i
    simp only [MachineState.getWord32]
    rw [frame _ (Or.inl (by fin_cases i <;> decide))]
    exact key i

def leafValue (hash : Hash) (parameter : PublicParameter) (seed : MasterSeed)
    (lay : Layer) (treeIdx : TreeIndex) (leaf : LeafIndex) : Digest :=
  evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
    (do let pk ← Seeded.oneTimePublicKey parameter lay treeIdx leaf seed
        Concrete.leafHash parameter lay treeIdx leaf pk : OracleComp SphincsSecurity.HashSpec Digest)

set_option backward.isDefEq.respectTransparency false in
/-- Secret derivation, all52 chains, payload serialization, and the actual leaf HASH
    compose without an assumed semantic or execution contract. -/
theorem leaf_body (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex)
    (leaf : LeafIndex) (ctx : KeyContext s parameter seed lay treeIdx)
    (pc : s.pc=0x111c+chainDelta location) (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 41187 44650 417 485 t ∧
      t.pc=0x1548+chainDelta location ∧ t.getMem 0x43020=BitVec.ofNat 64 leaf.val ∧
      KeyContext t parameter seed lay treeIdx ∧ Words20 t 0x42000 (leafValue hash parameter seed lay treeIdx leaf) ∧
      (∀ a,Frame.Protected a → t.getMem a=s.getMem a) := by
  let v:=s.setPC 0x111c
  let start:=SphincsMaskedLeafLoop.entry v
  let endpoints:=SphincsMaskedChainLoop.chains hash 52 start
  let values:=evalWithAnswerFn (spec:=SphincsSecurity.HashSpec) (adaptOracle hash)
    (Seeded.oneTimePublicKey parameter lay treeIdx leaf seed : OracleComp SphincsSecurity.HashSpec (ChainIndex → Digest))
  have startCtx : KeyContext start parameter seed lay treeIdx := by
    apply context_transport v start parameter seed lay treeIdx ctx
    intro a ha
    exact Frame.entry v a (Frame.retained_protected a ha)
  have startPc : start.pc=0x112c:=entry_pc v rfl
  have startCount : start.getMem 0x43050=0:=entry_counter v
  have startLeaf : start.getMem 0x43020=BitVec.ofNat 64 leaf.val := (entry_leaf v).trans counter
  have secretCtx : SphincsMaskedSignOtsDomain.Secret.Context start parameter seed lay treeIdx leaf ⟨0,by decide⟩ :=
    ⟨startCtx.1,startCtx.2.1,startLeaf,startCount,startCtx.2.2⟩
  have endPc : endpoints.pc=0x1464:=
    (SphincsMaskedChainLoop.fifty_two_chains hash start startPc startCount).2.2
  have endFrame : ∀ a,Frame.Protected a → endpoints.getMem a=s.getMem a := by
    intro a ha
    rw [Frame.chains hash start startPc startCount 52 (by decide) a ha,Frame.entry v a ha]
    rfl
  have endCtx : KeyContext endpoints parameter seed lay treeIdx :=
    context_transport s endpoints parameter seed lay treeIdx ctx (fun a ha => endFrame a (Frame.retained_protected a ha))
  have endIndex : endpoints.getMem 0x43018=BitVec.ofNat 64 leaf.val :=
    (SphincsMaskedLeafRefinement.endpoints_index hash start startPc startCount).trans startLeaf
  obtain ⟨copied,copyTrace,copyPc,copyPos,copyBytes,copyFrame⟩:=Payload.copy location endpoints endPc
  have copiedFrame : ∀ a,Frame.Protected a → copied.getMem a=s.getMem a := by
    intro a ha
    rw [copyFrame a (Frame.protected_ne a _ ha (by decide)) (Frame.payload_outside a ha),endFrame a ha]
  have copiedCtx : KeyContext copied parameter seed lay treeIdx :=
    context_transport s copied parameter seed lay treeIdx ctx (fun a ha => copiedFrame a (Frame.retained_protected a ha))
  have copiedIndex : copied.getMem 0x43018=BitVec.ofNat 64 leaf.val := by
    rw [copyFrame _ (by decide)]
    · exact endIndex
    · exact SphincsMaskedLeafRefinement.payload_outside _ (by simp [SphincsMaskedLeafRefinement.Protected])
  have header : SphincsMaskedSignOtsDomain.Leaf.HeaderContext copied parameter lay treeIdx leaf :=
    ⟨copiedCtx.1,copiedCtx.2.1,copiedIndex,copyPos,copiedCtx.2.2.1⟩
  have payload : ∀ i : Fin 1040,copied.getByte (BitVec.ofNat 64 (0x40028+i.val))=
      (values ⟨i.val/20,by change i.val/20<52;omega⟩).extractLsb' (8*(i.val%20)) 8 := by
    intro i
    rw [copyBytes i]
    have bytes:=SphincsMaskedSignOtsDomain.PublicKey.publicKey_bytes hash start parameter seed lay treeIdx leaf
      secretCtx startPc ⟨i.val/20,by change i.val/20<52;omega⟩ ⟨i.val%20,Nat.mod_lt _ (by decide)⟩
    have addr : 0x44300+20*(i.val/20)+i.val%20=0x44300+i.val := by omega
    simpa only [addr] using bytes
  let final:=shift (chainDelta location) (SphincsMaskedLeafLoop.answerState hash (copied.setPC 0x14a0))
  have finalFrame : ∀ a,Frame.Protected a → final.getMem a=s.getMem a := by
    intro a ha
    simp only [final,shift_mem]
    rw [Frame.leaf_hash hash _ a ha,MachineState.getMem_setPC]
    exact copiedFrame a ha
  obtain ⟨hashTrace,value⟩:=signer_leaf_hash location hash copied parameter lay treeIdx leaf values header copyPc payload
  have first:=Entry.block location v rfl
  rw [rebase_eq _ _ s pc] at first
  refine ⟨final,?_,?_,(finalFrame _ (Or.inr (Or.inr (Or.inr rfl)))).trans counter,
    context_transport s final parameter seed lay treeIdx ctx (fun a ha => finalFrame a (Frame.retained_protected a ha)),?_,finalFrame⟩
  · exact first.trace.trans ((SphincsMaskedSignOtsShift.fifty_two_chains location hash start startPc startCount).trans
      (copyTrace.trace.trans hashTrace))
  · rw [shift_pc,SphincsMaskedLeafLoop.answer_pc hash _ rfl]
  · simpa only [leafValue,evalWithAnswerFn_bind,final,values] using value

@[simp] theorem word_setPC (s : MachineState) (pc a : Word) :
    (s.setPC pc).getWord32 a=s.getWord32 a := rfl

namespace Cache
open SphincsMaskedSignForestLoop

def stored (location : Fin 5) (s : MachineState) : MachineState :=
  shift (Store.delta location) (SphincsMaskedSignForestLoop.stored (s.setPC 0x1f64))
def next (location : Fin 5) (s : MachineState) : MachineState :=
  shift (chainDelta location) (Finish.state location ((stored location s).setPC 0x159c))

theorem stored_trace (location : Fin 5) (s : MachineState) (leaf : Fin 256)
    (pc : s.pc=0x1548+chainDelta location) (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    OrdinarySteps SphincsMaskedImages.sign s 21 (stored location s) := by
  have trace:=Store.stored_block location (s.setPC 0x1f64) leaf rfl counter
  rw [SphincsMaskedSignOtsDomain.rebase_eq _ _ s (pc.trans (Store.entry_pc location).symm)] at trace
  exact trace

theorem stored_pc (location : Fin 5) (s : MachineState) :
    (stored location s).pc=0x159c+chainDelta location := by
  rw [stored,shift_pc,SphincsMaskedSignForestLoop.stored_pc _ rfl]
  fin_cases location <;> decide

theorem stored_counter (location : Fin 5) (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    (stored location s).getMem 0x43020=s.getMem 0x43020 := by
  rw [stored,shift_mem]
  exact SphincsMaskedSignForestLoop.stored_leaf (s.setPC 0x1f64) leaf counter

theorem stored_data (location : Fin 5) (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) (i : Fin 5) :
    (stored location s).getWord32 (BitVec.ofNat 64 (0x50000+20*leaf.val+4*i.val))=
      s.getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) := by
  rw [stored,shift_word]
  exact SphincsMaskedSignForestLoop.stored_data (s.setPC 0x1f64) leaf counter i

theorem stored_other (location : Fin 5) (s : MachineState) (leaf other : Fin 256) (ne : leaf≠other)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) (i : Fin 5) :
    (stored location s).getWord32 (BitVec.ofNat 64 (0x50000+20*other.val+4*i.val))=
      s.getWord32 (BitVec.ofNat 64 (0x50000+20*other.val+4*i.val)) := by
  rw [stored,shift_word]
  have old:=SphincsMaskedSignForestLoop.nextLeaf_other (s.setPC 0x1f64) leaf other ne counter i
  rw [SphincsMaskedSignForestLoop.nextLeaf,SphincsMaskedSignForestLoop.finish_cache_word] at old
  exact old

theorem stored_frame (location : Fin 5) (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) (a : Word) (ha : Frame.Retained a) :
    (stored location s).getMem a=s.getMem a := by
  rw [stored,shift_mem]
  exact Frame.store (s.setPC 0x1f64) leaf counter a ha

theorem next_trace (location : Fin 5) (s : MachineState) (leaf : Fin 256)
    (pc : s.pc=0x1548+chainDelta location) (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    OrdinarySteps SphincsMaskedImages.sign s 33 (next location s) := by
  have last:=Finish.block location ((stored location s).setPC 0x159c) rfl
  rw [SphincsMaskedSignOtsDomain.rebase_eq _ _ _ (stored_pc location s)] at last
  exact ordinary_trans _ _ _ _ 21 12 (stored_trace location s leaf pc counter) last

theorem next_counter (location : Fin 5) (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    (next location s).getMem 0x43020=BitVec.ofNat 64 (leaf.val+1) := by
  rw [next,shift_mem,Finish.counter]
  rw [MachineState.getMem_setPC]
  rw [stored_counter location s leaf counter,counter]
  exact (BitVec.ofNat_add _ _).symm

theorem next_pc (location : Fin 5) (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    (next location s).pc=if leaf.val+1=Finish.width location then 0x15cc+chainDelta location else 0x111c+chainDelta location := by
  rw [next,shift_pc,Finish.pc _ _ rfl]
  rw [MachineState.getMem_setPC]
  rw [stored_counter location s leaf counter,counter]
  have eq : BitVec.ofNat 64 leaf.val+1=BitVec.ofNat 64 (Finish.width location) ↔ leaf.val+1=Finish.width location := by
    have bound : Finish.width location≤32 := by fin_cases location <;> decide
    rw [show BitVec.ofNat 64 leaf.val+1=BitVec.ofNat 64 (leaf.val+1) from (BitVec.ofNat_add _ _).symm]
    constructor
    · intro h
      have h:=congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : leaf.val+1<2^64),
        Nat.mod_eq_of_lt (by omega : Finish.width location<2^64)] at h
      exact h
    · intro h;rw [h]
  simp only [eq]
  split <;> rfl

theorem finish_word_frame (location : Fin 5) (s : MachineState) (leaf : Fin 256) (i : Fin 5) :
    (Finish.state location s).getWord32 (BitVec.ofNat 64 (0x50000+20*leaf.val+4*i.val))=
      s.getWord32 (BitVec.ofNat 64 (0x50000+20*leaf.val+4*i.val)) := by
  simp only [MachineState.getWord32]
  rw [Finish.frame]
  intro eq
  have bound:=cache_cell_lower leaf i
  rw [eq] at bound
  contradiction

theorem next_data (location : Fin 5) (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) (i : Fin 5) :
    (next location s).getWord32 (BitVec.ofNat 64 (0x50000+20*leaf.val+4*i.val))=
      s.getWord32 (BitVec.ofNat 64 (0x42000+4*i.val)) := by
  rw [next,shift_word,finish_word_frame,word_setPC]
  exact stored_data location s leaf counter i

theorem next_other (location : Fin 5) (s : MachineState) (leaf other : Fin 256) (ne : leaf≠other)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) (i : Fin 5) :
    (next location s).getWord32 (BitVec.ofNat 64 (0x50000+20*other.val+4*i.val))=
      s.getWord32 (BitVec.ofNat 64 (0x50000+20*other.val+4*i.val)) := by
  rw [next,shift_word,finish_word_frame,word_setPC]
  exact stored_other location s leaf other ne counter i

theorem next_frame (location : Fin 5) (s : MachineState) (leaf : Fin 256)
    (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) (a : Word) (ha : Frame.Retained a) :
    (next location s).getMem a=s.getMem a := by
  rw [next,shift_mem,Finish.frame _ _ a (Frame.retained_ne_leaf a ha),MachineState.getMem_setPC]
  exact stored_frame location s leaf counter a ha

end Cache

/-- The global leaf-index type also represents each16/32-leaf subtree index. -/
def subtreeLeaf (leaf : Fin 32) : LeafIndex := ⟨leaf.val,by have := leaf.isLt;change leaf.val<2048;omega⟩

theorem leaf_contract (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex)
    (leaf : Fin 32) (ctx : KeyContext s parameter seed lay treeIdx)
    (pc : s.pc=0x111c+chainDelta location) (counter : s.getMem 0x43020=BitVec.ofNat 64 leaf.val) :
    ∃ t, Trace hash SphincsMaskedImages.sign s 41220 44683 417 485 t ∧
      t.pc=(if leaf.val+1=Finish.width location then 0x15cc+chainDelta location else 0x111c+chainDelta location) ∧
      t.getMem 0x43020=BitVec.ofNat 64 (leaf.val+1) ∧ KeyContext t parameter seed lay treeIdx ∧
      Words20 t (0x50000+20*leaf.val) (leafValue hash parameter seed lay treeIdx (subtreeLeaf leaf)) ∧
      (∀ other : Fin 32,other≠leaf → ∀ i : Fin 5,
        t.getWord32 (BitVec.ofNat 64 (0x50000+20*other.val+4*i.val))=
          s.getWord32 (BitVec.ofNat 64 (0x50000+20*other.val+4*i.val))) ∧
      (∀ a,Frame.Retained a → t.getMem a=s.getMem a) := by
  obtain ⟨mid,body,midPc,midCount,midCtx,value,bodyFrame⟩:=
    leaf_body location hash s parameter seed lay treeIdx (subtreeLeaf leaf) ctx pc counter
  let idx : Fin 256:=⟨leaf.val,by omega⟩
  let final:=Cache.next location mid
  have finalFrame : ∀ a,Frame.Retained a → final.getMem a=s.getMem a := by
    intro a ha
    exact (Cache.next_frame location mid idx midCount a ha).trans (bodyFrame a (Frame.retained_protected a ha))
  refine ⟨final,body.trans (Cache.next_trace location mid idx midPc midCount).trace,
    Cache.next_pc location mid idx midCount,Cache.next_counter location mid idx midCount,
    context_transport s final parameter seed lay treeIdx ctx finalFrame,?_,?_,finalFrame⟩
  · intro i
    rw [Cache.next_data location mid idx midCount i]
    exact value i
  · intro other ne i
    let otherIdx : Fin 256:=⟨other.val,by omega⟩
    have different : idx≠otherIdx := by
      intro h
      apply ne
      exact Fin.ext (congrArg Fin.val h).symm
    rw [Cache.next_other location mid idx otherIdx different midCount i]
    simp only [MachineState.getWord32]
    rw [bodyFrame _ (Or.inr (Or.inl (SphincsMaskedSignForestLoop.cache_cell_lower otherIdx i)))]

/-- A single invariant fills either subtree size, retaining every prior leaf and
    the current signer message/root/pointer state. -/
theorem leaves_contract (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex)
    (ctx : KeyContext s parameter seed lay treeIdx) (pc : s.pc=0x111c+chainDelta location)
    (counter : s.getMem 0x43020=0) (n : Nat) (hn : n≤Finish.width location) :
    ∃ t, Trace hash SphincsMaskedImages.sign s (41220*n) (44683*n) (417*n) (485*n) t ∧
      t.pc=(if n=Finish.width location then 0x15cc+chainDelta location else 0x111c+chainDelta location) ∧
      t.getMem 0x43020=BitVec.ofNat 64 n ∧ KeyContext t parameter seed lay treeIdx ∧
      (∀ leaf : Fin 32,leaf.val<n → Words20 t (0x50000+20*leaf.val)
        (leafValue hash parameter seed lay treeIdx (subtreeLeaf leaf))) ∧
      (∀ a,Frame.Retained a → t.getMem a=s.getMem a) := by
  have widthBounds : 0<Finish.width location ∧ Finish.width location≤32 := by fin_cases location <;> decide
  induction n with
  | zero =>
    refine ⟨s,Trace.refl _,?_,counter,ctx,by intro leaf h;omega,by intro a ha;rfl⟩
    simpa only [if_neg (by omega : 0≠Finish.width location)] using pc
  | succ n ih =>
    obtain ⟨mid,first,midPc,midCount,midCtx,previous,firstFrame⟩:=ih (by omega)
    have loc : mid.pc=0x111c+chainDelta location := by rw [midPc,if_neg (by omega)]
    let current : Fin 32:=⟨n,by omega⟩
    obtain ⟨final,last,done,count,finalCtx,newValue,other,lastFrame⟩:=
      leaf_contract location hash mid parameter seed lay treeIdx current midCtx loc midCount
    refine ⟨final,?_,done,count,finalCtx,?_,?_⟩
    · simpa only [Nat.mul_succ] using first.trans last
    · intro leaf hleaf
      by_cases eq : leaf=current
      · subst leaf;exact newValue
      · intro i
        rw [other leaf eq i]
        have ne : leaf.val≠n:=fun h => eq (Fin.ext h)
        exact previous leaf (by omega) i
    · intro a ha
      exact (lastFrame a ha).trans (firstFrame a ha)

/-- All temporary WOTS leaf-cache entries equal the seeded abstract subtree. -/
theorem all_leaves (location : Fin 5) (hash : Hash) (s : MachineState)
    (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (treeIdx : TreeIndex)
    (ctx : KeyContext s parameter seed lay treeIdx) (pc : s.pc=0x111c+chainDelta location)
    (counter : s.getMem 0x43020=0) :
    ∃ t, Trace hash SphincsMaskedImages.sign s (41220*Finish.width location) (44683*Finish.width location)
      (417*Finish.width location) (485*Finish.width location) t ∧
      t.pc=0x15cc+chainDelta location ∧ t.getMem 0x43020=BitVec.ofNat 64 (Finish.width location) ∧
      KeyContext t parameter seed lay treeIdx ∧
      (∀ leaf : Fin 32,leaf.val<Finish.width location → Words20 t (0x50000+20*leaf.val)
        (leafValue hash parameter seed lay treeIdx (subtreeLeaf leaf))) ∧
      (∀ a,Frame.Retained a → t.getMem a=s.getMem a) := by
  simpa using leaves_contract location hash s parameter seed lay treeIdx ctx pc counter (Finish.width location) (by omega)

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsTree.leaf_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_body

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsTree.leaf_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaf_contract

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsTree.leaves_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leaves_contract

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsTree.all_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms all_leaves

end SigGolfCandidate.SphincsMaskedSignOtsTree
