import SigGolfCandidate.SphincsMaskedSignForestSemantics

namespace SigGolfCandidate.SphincsMaskedSignOtsShift
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Rebase a computation without changing its data registers or memory. -/
def shift (delta : Word) (s : MachineState) : MachineState := s.setPC (s.pc+delta)

/-- Instructions whose data effects do not depend on the program counter. -/
abbrev Supported : Instr → Prop
  | .ADDI .. | .LUI .. | .LD .. | .SD .. | .LWU .. | .SW .. | .ADD .. |
    .SLLI .. | .SRLI .. | .ANDI .. | .BNE .. | .BEQ .. | .SB .. | .LBU .. | .ECALL => True
  | _ => False

instance (i : Instr) : Decidable (Supported i) := by cases i <;> infer_instance

@[simp] theorem shift_reg (delta : Word) (s : MachineState) (r : Reg) :
    (shift delta s).getReg r=s.getReg r := by cases r <;> rfl
@[simp] theorem shift_mem (delta : Word) (s : MachineState) (a : Word) :
    (shift delta s).getMem a=s.getMem a := rfl
@[simp] theorem shift_pc (delta : Word) (s : MachineState) : (shift delta s).pc=s.pc+delta := rfl

@[simp] theorem shift_word (delta : Word) (s : MachineState) (a : Word) :
    (shift delta s).getWord32 a=s.getWord32 a := rfl
@[simp] theorem shift_byte (delta : Word) (s : MachineState) (a : Word) :
    (shift delta s).getByte a=s.getByte a := rfl

theorem setReg_pc (s : MachineState) (pc : Word) (r : Reg) (v : Word) :
    (s.setPC pc).setReg r v=(s.setReg r v).setPC pc := by cases r <;> rfl

theorem setMem_pc (s : MachineState) (pc a v : Word) :
    (s.setPC pc).setMem a v=(s.setMem a v).setPC pc := rfl

theorem setWord_pc (s : MachineState) (pc a : Word) (v : BitVec 32) :
    (s.setPC pc).setWord32 a v=(s.setWord32 a v).setPC pc := rfl

theorem setByte_pc (s : MachineState) (pc a : Word) (v : Byte) :
    (s.setPC pc).setByte a v=(s.setByte a v).setPC pc := rfl

theorem setPC_twice (s : MachineState) (p q : Word) : (s.setPC p).setPC q=s.setPC q := rfl

theorem add_left_comm (a b c : Word) : a+(b+c)=b+(a+c) := by
  rw [←BitVec.add_assoc,BitVec.add_comm a b,BitVec.add_assoc]

/-- One branch-aware instruction commutes with a fixed PC translation. -/
theorem exec_shift (delta : Word) (s : MachineState) (i : Instr) (ok : Supported i) :
    execInstrBr (shift delta s) i=shift delta (execInstrBr s i) := by
  cases i <;> simp_all [Supported]
  all_goals
    simp only [execInstrBr,shift_reg,shift_mem,shift_word,shift_byte,shift_pc]
    first
    | (split <;> simp [shift,setPC_twice,setReg_pc,setMem_pc,setWord_pc,setByte_pc,BitVec.add_assoc,BitVec.add_comm,add_left_comm])
    | simp [shift,setPC_twice,setReg_pc,setMem_pc,setWord_pc,setByte_pc,BitVec.add_assoc,BitVec.add_comm,add_left_comm]

@[simp] theorem memory_shift (delta : Word) (s : MachineState) (i : Instr) :
    memoryArgumentsValid (shift delta s) i=memoryArgumentsValid s i := by
  cases i <;> simp [memoryArgumentsValid]

theorem ordinary_shift (delta : Word) (s : MachineState) (i : Instr) (ok : Supported i)
    (step : ordinaryStep s (.base i)=some (execInstrBr s i)) :
    ordinaryStep (shift delta s) (.base i)=some (execInstrBr (shift delta s) i) := by
  cases i <;> simp_all [Supported,ordinaryStep]

/-- Relocate a finite instruction schedule; offsets inside branch instructions remain fixed. -/
def schedule (delta : Word) (code : List (Word × Instr)) : List (Word × Instr) :=
  code.map (fun e => (e.1+delta,e.2))

theorem run_shift (delta : Word) (code : List (Word × Instr))
    (ok : ∀ e∈code,Supported e.2) (s : MachineState) :
    runSchedule (schedule delta code) (shift delta s)=shift delta (runSchedule code s) := by
  induction code generalizing s with
  | nil => rfl
  | cons e rest ih =>
    simp only [schedule,List.map_cons,runSchedule]
    rw [exec_shift delta s e.2 (ok e (by simp))]
    exact ih (by intro e he;exact ok e (by simp [he])) _

theorem checked_shift (delta : Word) (code : List (Word × Instr))
    (ok : ∀ e∈code,Supported e.2) (s : MachineState) (checked : Checked code s) :
    Checked (schedule delta code) (shift delta s) := by
  induction code generalizing s with
  | nil => trivial
  | cons e rest ih =>
    obtain ⟨pc,step,tail⟩ := checked
    refine ⟨by simp [schedule,shift_pc,pc],ordinary_shift delta s e.2 (ok e (by simp)) step,?_⟩
    rw [exec_shift delta s e.2 (ok e (by simp))]
    exact ih (by intro e he;exact ok e (by simp [he])) _ tail

/-- Existing checked blocks can be reused at every matching bytecode location. -/
theorem block_shift (image : Image) (delta : Word) (code : List (Word × Instr))
    (supported : ∀ e∈code,Supported e.2)
    (encoded : ∀ e∈code,instructionAt image (e.1+delta)=some (.base e.2))
    (s : MachineState) (checked : Checked code s) :
    OrdinarySteps image (shift delta s) code.length (shift delta (runSchedule code s)) := by
  have run := checked_sound image (schedule delta code) (by
    intro e he
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp he
    exact encoded original member) _ (checked_shift delta code supported s checked)
  rw [run_shift delta code supported s] at run
  simpa only [schedule,List.length_map] using run


@[simp] theorem hashInput_shift (delta : Word) (s : MachineState) :
    hashInput (shift delta s)=hashInput s := rfl

@[simp] theorem hashValid_shift (delta : Word) (s : MachineState) :
    hashArgumentsValid (shift delta s)=hashArgumentsValid s := rfl

theorem writeHash_shift (delta : Word) (s : MachineState) (answer : BitVec 256) :
    writeHash (shift delta s) answer=shift delta (writeHash s answer) := by
  simp [writeHash,MachineState.writeWords,shift,setMem_pc,setPC_twice,
    BitVec.add_assoc,BitVec.add_comm,add_left_comm]


/-- A relocated HASH preserves the exact oracle query and answer bytes. -/
theorem hash_block_shift (delta : Word) (hash : Hash) (image : Image) (s : MachineState)
    (fetched : fetch image (shift delta s)=some (.base .ECALL))
    (service : s.getReg .x5=1) (valid : hashArgumentsValid s=true) :
    Trace hash image (shift delta s) 1 (8*compressions (hashInput s).1) 1
      (compressions (hashInput s).1) (shift delta (writeHash s (hash (hashInput s)))) := by
  have one:=Trace.hash (hash:=hash) (image:=image) (shift delta s) _ 0 0 0 0
    fetched (by simpa using service) (by simpa using valid) (Trace.refl _)
  simpa only [hashInput_shift,writeHash_shift,Nat.zero_add] using one

/-- The five lower-layer OTS tree bodies share the keygen chain bytecode.
    Index zero denotes layer one; index four denotes layer five. -/
def chainDelta (layer : Fin 5) : Word :=
  if layer.val=0 then 0x72ec else if layer.val=1 then 0x5be0 else
  if layer.val=2 then 0x44d4 else if layer.val=3 then 0x2dc8 else 0x16bc


def chainOffset (layer : Fin 5) : Nat :=
  if layer.val=0 then 7355 else if layer.val=1 then 5880 else
  if layer.val=2 then 4405 else if layer.val=3 then 2930 else 1455

theorem delta_value (layer : Fin 5) : chainDelta layer=BitVec.ofNat 64 (4*chainOffset layer) := by
  fin_cases layer <;> decide

theorem offset_bound (layer : Fin 5) : chainOffset layer≤7355 := by fin_cases layer <;> decide

/-- Certify the 263-word shared block once per layer, rather than refetching
    the entire signer prefix for every instruction in every trace. -/
theorem chain_image (layer : Fin 5) :
    (SphincsMaskedImages.sign.code.drop (75+chainOffset layer)).take 263 =
      (SphincsMaskedImages.keygen.code.drop 75).take 263 := by
  fin_cases layer <;> rfl

theorem chain_word (layer : Fin 5) (i : Fin 263) :
    SphincsMaskedImages.sign.code[75+chainOffset layer+i.val]?=
      SphincsMaskedImages.keygen.code[75+i.val]? := by
  have eq:=congrArg (fun words : List (BitVec 32) => words[i.val]?) (chain_image layer)
  simpa only [List.getElem?_take_of_lt i.isLt,List.getElem?_drop] using eq

theorem fetch_index (image : Image) (i : Nat) (bound : i<11000) :
    instructionAt image (BitVec.ofNat 64 (0x1000+4*i))=
      image.code[i]?.bind decodeInstruction := by
  have small : 0x1000+4*i<2^64 := by omega
  unfold instructionAt fetch
  change (if (BitVec.ofNat 64 (0x1000+4*i)).toNat < 0x1000 ||
      (BitVec.ofNat 64 (0x1000+4*i)).toNat % 4 != 0 then none else
      image.code[((BitVec.ofNat 64 (0x1000+4*i)).toNat-0x1000)/4]?.bind decodeInstruction)=_
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have aligned : (0x1000+4*i)%4=0 := by omega
  simp [show ¬0x1000+4*i<0x1000 by omega,aligned]

/-- Shared-block byte equality transfers decoded fetches at arbitrary interior PCs. -/
theorem instruction_transfer (layer : Fin 5) (pc : Word)
    (lower : 0x112c≤pc.toNat) (upper : pc.toNat<0x1548) (aligned : pc.toNat%4=0) :
    instructionAt SphincsMaskedImages.sign (pc+chainDelta layer)=
      instructionAt SphincsMaskedImages.keygen pc := by
  let i : Fin 263 := ⟨(pc.toNat-0x112c)/4,by omega⟩
  have bound:=offset_bound layer
  have original : pc=BitVec.ofNat 64 (0x1000+4*(75+i.val)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [i];omega)]
    dsimp [i];omega
  have translated : pc+chainDelta layer=BitVec.ofNat 64 (0x1000+4*(75+chainOffset layer+i.val)) := by
    rw [original,delta_value,←BitVec.ofNat_add]
    congr 1;omega
  rw [translated,fetch_index _ _ (by omega),original,fetch_index _ _ (by omega),chain_word layer i]

open SphincsMaskedChainLoop

theorem prepare_supported : ∀ e∈secretPrepareSchedule,Supported e.2 := by decide

theorem prepare_encoded (layer : Fin 5) : ∀ e∈secretPrepareSchedule,
    instructionAt SphincsMaskedImages.sign (e.1+chainDelta layer)=some (.base e.2) := by
  intro e he
  have inside : ∀ e∈secretPrepareSchedule,0x112c≤e.1.toNat ∧ e.1.toNat<0x1548 ∧ e.1.toNat%4=0 := by decide
  have bounds:=inside e he
  rw [instruction_transfer layer e.1 bounds.1 bounds.2.1 bounds.2.2]
  exact secretPrepare_code e he

theorem finish_supported : ∀ e∈secretFinishSchedule,Supported e.2 := by decide

theorem finish_encoded (layer : Fin 5) : ∀ e∈secretFinishSchedule,
    instructionAt SphincsMaskedImages.sign (e.1+chainDelta layer)=some (.base e.2) := by
  intro e he
  have inside : ∀ e∈secretFinishSchedule,0x112c≤e.1.toNat ∧ e.1.toNat<0x1548 ∧ e.1.toNat%4=0 := by decide
  have bounds:=inside e he
  rw [instruction_transfer layer e.1 bounds.1 bounds.2.1 bounds.2.2]
  exact secretFinish_code e he

/-- Concrete transfer of the 80-instruction keygen chain prologue to every lower layer. -/
theorem prepare_block (layer : Fin 5) (s : MachineState) (pc : s.pc=0x112c) :
    OrdinarySteps SphincsMaskedImages.sign (shift (chainDelta layer) s) 80
      (shift (chainDelta layer) (secretPrepare s)) :=
  block_shift _ _ _ prepare_supported (prepare_encoded layer) s (secretPrepare_checked s pc)

/-- All five translated initializers query the same bytes and derive the same
    chain seed as the proven keygen initializer, under arbitrary memory/oracle. -/
theorem initial_chain (layer : Fin 5) (hash : Hash) (s : MachineState) (pc : s.pc=0x112c) :
    Trace hash SphincsMaskedImages.sign (shift (chainDelta layer) s) 99 114 1 2
      (shift (chainDelta layer) (initialChain hash s)) := by
  let delta:=chainDelta layer
  obtain ⟨src,bits,dst,service⟩ := secretPrepare_registers s
  have fetched : fetch SphincsMaskedImages.sign (shift delta (secretPrepare s))=some (.base .ECALL) := by
    rw [fetch_at,shift_pc,secretPrepare_pc s pc]
    rw [instruction_transfer layer 0x1224 (by decide) (by decide) (by decide)]
    decide
  have valid : hashArgumentsValid (secretPrepare s)=true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (secretPrepare s)).1=576 := by simp [hashInput,bits]
  have hashing : Trace hash SphincsMaskedImages.sign (shift delta (secretPrepare s)) 1 16 1 2
      (shift delta (secretAnswer hash s)) := by
    have one:=hash_block_shift delta hash SphincsMaskedImages.sign (secretPrepare s) fetched service valid
    simpa only [len,secretAnswer,show compressions 576=2 from by decide,Nat.reduceMul] using one
  have apc : (secretAnswer hash s).pc=0x1228 := by
    simp [secretAnswer,writeHash,secretPrepare_pc s pc]
  have last := block_shift SphincsMaskedImages.sign delta secretFinishSchedule
    finish_supported (finish_encoded layer) (secretAnswer hash s) (secretFinish_checked _ apc)
  exact (prepare_block layer s pc).trace.trans (hashing.trans last.trace)

namespace Step
open SphincsMaskedChainStep

theorem prepare_supported : ∀ e∈prepareSchedule,Supported e.2 := by decide

theorem prepare_encoded (layer : Fin 5) : ∀ e∈prepareSchedule,
    instructionAt SphincsMaskedImages.sign (e.1+chainDelta layer)=some (.base e.2) := by
  intro e he
  have inside : ∀ e∈prepareSchedule,0x112c≤e.1.toNat ∧ e.1.toNat<0x1548 ∧ e.1.toNat%4=0 := by decide
  have bounds:=inside e he
  rw [instruction_transfer layer e.1 bounds.1 bounds.2.1 bounds.2.2]
  exact prepare_code e he

theorem finish_supported : ∀ e∈finishSchedule,Supported e.2 := by decide

theorem finish_encoded (layer : Fin 5) : ∀ e∈finishSchedule,
    instructionAt SphincsMaskedImages.sign (e.1+chainDelta layer)=some (.base e.2) := by
  intro e he
  have inside : ∀ e∈finishSchedule,0x112c≤e.1.toNat ∧ e.1.toNat<0x1548 ∧ e.1.toNat%4=0 := by decide
  have bounds:=inside e he
  rw [instruction_transfer layer e.1 bounds.1 bounds.2.1 bounds.2.2]
  exact finish_code e he

/-- The same chain-step block is reused at all five lower-layer locations. -/
theorem chain_step (layer : Fin 5) (hash : Hash) (s : MachineState) (pc : s.pc=0x1270) :
    Trace hash SphincsMaskedImages.sign (shift (chainDelta layer) s) 92 99 1 1
      (shift (chainDelta layer) (stepState hash s)) := by
  let delta:=chainDelta layer
  obtain ⟨src,bits,dst,service⟩ := prepare_registers s
  have fetched : fetch SphincsMaskedImages.sign (shift delta (prepareState s))=some (.base .ECALL) := by
    rw [fetch_at,shift_pc,prepare_pc s pc]
    rw [instruction_transfer layer 0x1374 (by decide) (by decide) (by decide)]
    decide
  have valid : hashArgumentsValid (prepareState s)=true := by
    simp [hashArgumentsValid,src,bits,dst,accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput (prepareState s)).1=480 := by simp [hashInput,bits]
  have hashing : Trace hash SphincsMaskedImages.sign (shift delta (prepareState s)) 1 8 1 1
      (shift delta (answerState hash s)) := by
    have one:=hash_block_shift delta hash SphincsMaskedImages.sign (prepareState s) fetched service valid
    simpa only [len,answerState,show compressions 480=1 from by decide,Nat.reduceMul] using one
  have apc : (answerState hash s).pc=0x1378 := by simp [answerState,writeHash,prepare_pc s pc]
  have first := block_shift SphincsMaskedImages.sign delta prepareSchedule
    prepare_supported (prepare_encoded layer) s (prepare_checked s pc)
  have last := block_shift SphincsMaskedImages.sign delta finishSchedule
    finish_supported (finish_encoded layer) (answerState hash s) (finish_checked _ apc)
  exact first.trace.trans (hashing.trans last.trace)

/-- Relocation commutes with the seven-step invariant and preserves exact cost. -/
theorem chain_walk (layer : Fin 5) (hash : Hash) (s : MachineState) (pc : s.pc=0x1270)
    (counter : s.getMem 0x43058=0) (n : Nat) (bound : n≤7) :
    Trace hash SphincsMaskedImages.sign (shift (chainDelta layer) s) (92*n) (99*n) n n
      (shift (chainDelta layer) (walk hash n s)) := by
  induction n with
  | zero => exact Trace.refl _
  | succ n ih =>
    have old := SphincsMaskedChainStep.walk_trace hash s pc counter n (by omega)
    have here : (walk hash n s).pc=0x1270 := by rw [old.2.2,if_neg (by omega)]
    simpa only [walk,Nat.mul_succ] using (ih (by omega)).trans (chain_step layer hash _ here)

end Step

/-- Complete secret derivation plus seven chain steps, shared by all lower
    layers. The result has exactly the proven keygen computation's data. -/
theorem chain_value (layer : Fin 5) (hash : Hash) (s : MachineState) (pc : s.pc=0x112c) :
    Trace hash SphincsMaskedImages.sign (shift (chainDelta layer) s) 743 807 8 9
      (shift (chainDelta layer) (chainValue hash s)) :=
  (initial_chain layer hash s pc).trans (Step.chain_walk layer hash (initialChain hash s)
    (initialChain_pc hash s pc) (initialChain_step_zero hash s) 7 (by decide))

/-- Reuse a source schedule anywhere inside the certified common block. -/
theorem encoded_of (layer : Fin 5) (code : List (Word × Instr))
    (inside : ∀ e∈code,0x112c≤e.1.toNat ∧ e.1.toNat<0x1548 ∧ e.1.toNat%4=0)
    (source : ∀ e∈code,instructionAt SphincsMaskedImages.keygen e.1=some (.base e.2)) :
    ∀ e∈code,instructionAt SphincsMaskedImages.sign (e.1+chainDelta layer)=some (.base e.2) := by
  intro e he
  obtain ⟨lo,hi,align⟩:=inside e he
  rw [instruction_transfer layer e.1 lo hi align]
  exact source e he

open SphincsVerifierCopy SphincsVerifierMessageCopy SphincsVerifierFtsCopyAccess

theorem copyRoot_shift (delta : Word) (s : MachineState) :
    copyRootState (shift delta s)=shift delta (copyRootState s) := by
  simp [copyRootState,copyWordState,exec_shift,Supported]

theorem endpoint_copy_code (layer : Fin 5) :
    Copy20Code SphincsMaskedImages.sign (259+chainOffset layer) := by
  constructor
  · intro i
    have same:=chain_word layer ⟨184+2*i.val,by omega⟩
    have left : 75+chainOffset layer+(184+2*i.val)=259+chainOffset layer+2*i.val := by omega
    have right : 75+(184+2*i.val)=259+2*i.val := by omega
    simp only [left,right] at same
    rw [same]
    exact SphincsMaskedChainLoop.endpoint_copy_code.load i
  · intro i
    have same:=chain_word layer ⟨185+2*i.val,by omega⟩
    have left : 75+chainOffset layer+(185+2*i.val)=259+chainOffset layer+2*i.val+1 := by omega
    have right : 75+(185+2*i.val)=259+2*i.val+1 := by omega
    simp only [left,right] at same
    rw [same]
    exact SphincsMaskedChainLoop.endpoint_copy_code.store i

/-- Store one complete 20-byte endpoint and advance the 52-chain loop. -/
theorem endpoint_block (layer : Fin 5) (s : MachineState) (c : Fin 52)
    (pc : s.pc=0x13e0) (chain : s.getMem 0x43050=BitVec.ofNat 64 c.val) :
    OrdinarySteps SphincsMaskedImages.sign (shift (chainDelta layer) s) 33
      (shift (chainDelta layer) (endpointNext s)) := by
  let delta:=chainDelta layer
  have first:=block_shift SphincsMaskedImages.sign delta endpointSetupSchedule (by decide)
    (encoded_of layer endpointSetupSchedule (by decide) endpointSetup_code) s (endpointSetup_checked s pc)
  have regs:=endpointSetup_registers s c.val chain
  have bound:=offset_bound layer
  have loc : (shift delta (endpointSetup s)).pc=BitVec.ofNat 64 (0x1000+4*(259+chainOffset layer)) := by
    rw [shift_pc,endpointSetup_pc s pc,show delta=BitVec.ofNat 64 (4*chainOffset layer) from delta_value layer]
    change BitVec.ofNat 64 0x140c+BitVec.ofNat 64 (4*chainOffset layer)=_
    rw [←BitVec.ofNat_add]
    congr 1;omega
  have copied:=copy20_block_general SphincsMaskedImages.sign (259+chainOffset layer)
    (endpoint_copy_code layer) (shift delta (endpointSetup s)) 0x44b00 (0x44300+20*c.val)
    loc (by simpa using regs.1) (by simpa using regs.2)
    (by decide) (by decide) (by omega) (by dsimp [MEMORY_BYTES];omega) (by omega)
  rw [copyRoot_shift] at copied
  have last:=block_shift SphincsMaskedImages.sign delta endpointFinishSchedule (by decide)
    (encoded_of layer endpointFinishSchedule (by decide) endpointFinish_code)
    (endpointStored s) (endpointFinish_checked _ (endpointStored_pc s pc))
  exact ordinary_trans _ _ _ _ 11 22 first (ordinary_trans _ _ _ _ 10 12 copied last)

/-- The52-chain induction reuses the established virtual-state counter/PC invariant. -/
theorem chains_trace (layer : Fin 5) (hash : Hash) (s : MachineState) (pc : s.pc=0x112c)
    (counter : s.getMem 0x43050=0) (n : Nat) (bound : n≤52) :
    Trace hash SphincsMaskedImages.sign (shift (chainDelta layer) s)
      (776*n) (840*n) (8*n) (9*n) (shift (chainDelta layer) (chains hash n s)) := by
  induction n with
  | zero => exact Trace.refl _
  | succ n ih =>
    have old:=SphincsMaskedChainLoop.chains_trace hash s pc counter n (by omega)
    have here : (chains hash n s).pc=0x112c := by rw [old.2.2,if_neg (by omega)]
    have steps:=SphincsMaskedChainStep.seven_steps hash (initialChain hash (chains hash n s))
      (initialChain_pc hash _ here) (initialChain_step_zero hash _)
    have count : (chainValue hash (chains hash n s)).getMem 0x43050=BitVec.ofNat 64 n :=
      (chainValue_counter hash _).trans old.2.1
    have next:=(chain_value layer hash _ here).trans
      (endpoint_block layer _ ⟨n,by omega⟩ steps.2.2 count).trace
    simpa only [chains,Nat.mul_succ,chainNext,chainValue,Nat.reduceAdd,Nat.add_zero] using (ih (by omega)).trans next

/-- All 416 oracle calls and 468 compressions for the complete endpoint array,
    independent of the incoming data and of the chosen lower signing layer. -/
theorem fifty_two_chains (layer : Fin 5) (hash : Hash) (s : MachineState) (pc : s.pc=0x112c)
    (counter : s.getMem 0x43050=0) :
    Trace hash SphincsMaskedImages.sign (shift (chainDelta layer) s) 40352 43680 416 468
      (shift (chainDelta layer) (chains hash 52 s)) :=
  chains_trace layer hash s pc counter 52 (by decide)

/-- User-facing actual-PC version, requiring only the live loop counter. -/
theorem endpoint_array (layer : Fin 5) (hash : Hash) (s : MachineState)
    (pc : s.pc=0x112c+chainDelta layer) (counter : s.getMem 0x43050=0) :
    Trace hash SphincsMaskedImages.sign s 40352 43680 416 468
      (shift (chainDelta layer) (chains hash 52 (s.setPC 0x112c))) := by
  have rebased : shift (chainDelta layer) (s.setPC 0x112c)=s := by
    unfold shift
    rw [show (s.setPC 0x112c).pc=0x112c from rfl,←pc,setPC_twice]
    cases s;rfl
  have trace:=fifty_two_chains layer hash (s.setPC 0x112c) rfl counter
  rw [rebased] at trace
  exact trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsShift.initial_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initial_chain

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsShift.Step.chain_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Step.chain_walk

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsShift.chain_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chain_value

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsShift.chains_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chains_trace

/-- info: 'SigGolfCandidate.SphincsMaskedSignOtsShift.endpoint_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms endpoint_array

end SigGolfCandidate.SphincsMaskedSignOtsShift
