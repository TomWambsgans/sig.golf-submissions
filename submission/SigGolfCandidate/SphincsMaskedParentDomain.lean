import SigGolfCandidate.SphincsMaskedParentNode

namespace SigGolfCandidate.SphincsMaskedParentDomain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedParentCode SphincsMaskedParentNode
open SphincsMaskedChainDomain SphincsMaskedChainEndpoints SphincsMaskedPublicKeyDomain
open SphincsVerifierCopy SphincsVerifierCopyMemory SphincsVerifierFtsPriorRoots
open SphincsVerifierFtsGenericCopyData SphincsBridge SphincsSecurity
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem children_left (s : MachineState) (base node : Nat)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : base + 40 * node + 40 ≤ 0x40000) (i : Fin 5) :
    (children s).getWord32 (BitVec.ofNat 64 (0x40028 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (base + 40 * node + 4 * i.val)) := by
  have lregs := leftSetup_registers s base node hb hn
  have source := (copyRoot_registers (leftSetup s)).1.trans lregs.1
  have rregs := rightSetup_registers (leftCopied s) (base + 40 * node) source
  change (copyRootState (rightSetup (leftCopied s))).getWord32 _ = _
  rw [copyRoot_word_frame]
  · simp only [MachineState.getWord32,rightSetup_frame]
    change (leftCopied s).getWord32 _ = _
    rw [leftCopied,copyRoot_data_belowHash _ (base + 40 * node) 0x40028 (by omega) (Or.inl rfl) lregs.1 lregs.2 i]
    simp only [MachineState.getWord32,leftSetup_frame]
  · intro j
    rw [rregs.2]
    fin_cases i <;> fin_cases j <;> decide

theorem children_right (s : MachineState) (base node : Nat)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : base + 40 * node + 40 ≤ 0x40000) (i : Fin 5) :
    (children s).getWord32 (BitVec.ofNat 64 (0x4003c + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (base + 40 * node + 20 + 4 * i.val)) := by
  have lregs := leftSetup_registers s base node hb hn
  have source := (copyRoot_registers (leftSetup s)).1.trans lregs.1
  have rregs := rightSetup_registers (leftCopied s) (base + 40 * node) source
  change (copyRootState (rightSetup (leftCopied s))).getWord32 _ = _
  rw [copyRoot_data_belowHash _ (base + 40 * node + 20) 0x4003c (by omega) (Or.inr rfl) rregs.1 rregs.2 i]
  simp only [MachineState.getWord32,rightSetup_frame]
  change (leftCopied s).getWord32 _ = _
  rw [leftCopied,copyRoot_source_frame _ (base + 40 * node + 20) 0x40028 (by omega) (Or.inl rfl) lregs.2 i]
  simp only [MachineState.getWord32,leftSetup_frame]

def queryWord (s : MachineState) (i : Fin 20) : BitVec 32 :=
  if i.val = 0 then (769#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val = 1 then (s.getMem 0x43048).setWidth 32
  else if i.val = 2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val = 3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val = 4 then (s.getMem 0x43088).setWidth 32
  else if i.val < 10 then s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * (i.val - 5)))
  else s.getWord32 (BitVec.ofNat 64 (0x40000 + 4 * i.val))

theorem prepare_words (s : MachineState) (i : Fin 20) :
    (hashPrepare s).getWord32 (BitVec.ofNat 64 (0x40000 + 4 * i.val)) = queryWord s i := by
  fin_cases i <;>
    simp [hashPrepare,runSchedule,hashPrepareSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,queryWord]

def Context (s : MachineState) (parameter left right : BitVec 160) (level node : Nat) : Prop :=
  s.getMem 0x43000#64 = 0 ∧ s.getMem 0x43008#64 = 0 ∧
  s.getMem 0x43048#64 = BitVec.ofNat 64 level ∧ s.getMem 0x43088#64 = BitVec.ofNat 64 node ∧
  Words20 s 0x74 parameter ∧ Words20 s 0x40028 left ∧ Words20 s 0x4003c right

def input (parameter left right : BitVec 160) (level node : Nat) : HashInput :=
  tweakableHashInput parameter (.node topLayer Concrete.rootTree level node) (Concrete.nodePayload left right)

def payload (parameter left right : BitVec 160) (level node : Nat) : List Byte :=
  (input parameter left right level node).map UInt8.toBitVec

theorem payload_length (parameter left right : BitVec 160) (level node : Nat) :
    (payload parameter left right level node).length = 80 := by
  simp [payload,input,tweakableHashInput,tweakBytes,hashDomainFields,tweakFields,fieldBytes,bytesLE,Concrete.nodePayload]

theorem prepared_byte (s : MachineState) (i : Fin 80) :
    (hashPrepare s).getByte (BitVec.ofNat 64 (0x40000 + i.val)) =
      (queryWord s ⟨i.val / 4,by omega⟩).extractLsb' (8 * (i.val % 4)) 8 := by
  have h := SphincsVerifierFtsGenericBytes.variableWord_byte (hashPrepare s)
    (0x40000 + 4 * (i.val / 4)) (by omega) (by omega) 0 ⟨i.val % 4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  rw [show 0x40000 + 4 * (i.val / 4) + i.val % 4 = 0x40000 + i.val by omega] at h
  rw [h,prepare_words s ⟨i.val / 4,by omega⟩]

theorem context_byte (s : MachineState) (parameter left right : BitVec 160) (level node : Nat)
    (ctx : Context s parameter left right level node) (i : Fin 80) :
    (queryWord s ⟨i.val / 4,by omega⟩).extractLsb' (8 * (i.val % 4)) 8 =
      (payload parameter left right level node)[i.val]'(by rw [payload_length];exact i.isLt) := by
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
  fin_cases i <;>
    simp [queryWord,layer,tree,lev,idx,p0,p1,p2,p3,p4,l0,l1,l2,l3,l4,r0,r1,r2,r3,r4,
      extractWord32,payload,input,tweakableHashInput,tweakBytes,hashDomainFields,tweakFields,
      fieldBytes,bytesLE,Concrete.nodePayload,topLayer,Concrete.rootTree,protocolDomainSep]
  all_goals ext b hb;interval_cases b <;> simp

theorem query_eq (s : MachineState) (parameter left right : BitVec 160) (level node : Nat)
    (ctx : Context s parameter left right level node) :
    hashInput (hashPrepare s) = toQuery (input parameter left right level node) := by
  apply Serialization.hashInput_of_list (hashPrepare s) 0x40000 (payload parameter left right level node)
  · exact (hashPrepare_registers s).1
  · rw [payload_length,(hashPrepare_registers s).2.1];rfl
  · intro i hi
    have bound : i < 80 := by simpa only [payload_length] using hi
    rw [prepared_byte s ⟨i,bound⟩]
    exact context_byte s parameter left right level node ctx ⟨i,bound⟩

theorem children_context (s : MachineState) (parameter left right : BitVec 160) (base level node : Nat)
    (layer : s.getMem 0x43000 = 0) (tree : s.getMem 0x43008 = 0)
    (lev : s.getMem 0x43048 = BitVec.ofNat 64 level) (idx : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (bounded : base + 40 * node + 40 ≤ 0x40000)
    (par : Words20 s 0x74 parameter)
    (lft : Words20 s (base + 40 * node) left) (rgt : Words20 s (base + 40 * node + 20) right) :
    Context (children s) parameter left right level node := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact (children_frame s _ (by decide)).trans layer
  · exact (children_frame s _ (by decide)).trans tree
  · exact (children_frame s _ (by decide)).trans lev
  · exact (children_frame s _ (by decide)).trans idx
  · intro i
    simp only [MachineState.getWord32]
    rw [children_frame s _ (by fin_cases i <;> decide)]
    exact par i
  · intro i;exact (children_left s base node hb idx bounded i).trans (lft i)
  · intro i;exact (children_right s base node hb idx bounded i).trans (rgt i)

/-- info: 'SigGolfCandidate.SphincsMaskedParentDomain.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_eq

/-- info: 'SigGolfCandidate.SphincsMaskedParentDomain.children_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms children_context


private def StoreInvariant (original : MachineState) (destination count : Nat) (s : MachineState) : Prop :=
  s.getReg .x6 = 0x42000 ∧ s.getReg .x7 = BitVec.ofNat 64 destination ∧
  (∀ i : Fin 5, s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) = original.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val))) ∧
  (∀ i : Fin 5, i.val < count → s.getWord32 (BitVec.ofNat 64 (destination + 4 * i.val)) = original.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)))

private theorem storeStep (original s : MachineState) (destination : Nat)
    (bounded : destination + 20 ≤ 0x40000) (aligned : destination % 4 = 0) (slot : Fin 5)
    (inv : StoreInvariant original destination slot.val s) :
    StoreInvariant original destination (slot.val + 1) (copyWordState slot s) := by
  obtain ⟨src,dst,source,copied⟩ := inv
  obtain ⟨srcAfter,dstAfter⟩ := copyWord_pointers slot s
  refine ⟨srcAfter.trans src,dstAfter.trans dst,?_,?_⟩
  · intro i
    rw [copyWord_lane_frame s destination (0x42000 + 4 * i.val) slot dst
      (by omega) (by omega) aligned (by omega) (by omega)]
    exact source i
  · intro i hi
    by_cases eq : slot = i
    · subst i
      rw [SphincsVerifierCopy20DataGeneral.copyWord_data_general slot s 0x42000 destination src dst]
      exact source slot
    · have ne : slot.val ≠ i.val := fun h => eq (Fin.ext h)
      rw [copyWord_lane_frame s destination (destination + 4 * i.val) slot dst
        (by omega) (by omega) aligned (by omega) (by omega)]
      exact copied i (by omega)

theorem store_data (s : MachineState) (destination : Nat)
    (bounded : destination + 20 ≤ 0x40000) (aligned : destination % 4 = 0)
    (src : s.getReg .x6 = 0x42000) (dst : s.getReg .x7 = BitVec.ofNat 64 destination) (i : Fin 5) :
    (copyRootState s).getWord32 (BitVec.ofNat 64 (destination + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) := by
  have inv : StoreInvariant s destination 0 s := ⟨src,dst,fun _ => rfl,by intro _ h;omega⟩
  have s0 := storeStep s s destination bounded aligned 0 inv
  have s1 := storeStep s (copyWordState 0 s) destination bounded aligned 1 s0
  have s2 := storeStep s (copyWordState 1 (copyWordState 0 s)) destination bounded aligned 2 s1
  have s3 := storeStep s (copyWordState 2 (copyWordState 1 (copyWordState 0 s))) destination bounded aligned 3 s2
  have s4 := storeStep s (copyWordState 3 (copyWordState 2 (copyWordState 1 (copyWordState 0 s)))) destination bounded aligned 4 s3
  exact s4.2.2.2 i (by omega)

theorem low_cell (address : Nat) (bounded : address < 0x40000) :
    (alignToDword (BitVec.ofNat 64 address)).toNat < 0x40000 := by
  unfold alignToDword
  rw [BitVec.toNat_and]
  apply lt_of_le_of_lt Nat.and_le_left
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact bounded

theorem low_ne (a b : Word) (ha : a.toNat < 0x40000) (hb : 0x40000 ≤ b.toNat) : a ≠ b := by
  intro eq;rw [eq] at ha;omega

theorem next_data (hash : Hash) (s : MachineState) (target node : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : target + 20 * node + 20 ≤ 0x40000) (aligned : target % 4 = 0) (i : Fin 5) :
    (next hash s).getWord32 (BitVec.ofNat 64 (target + 20 * node + 4 * i.val)) =
      (answer hash s).getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) := by
  have atarget := (answer_frame hash s _ (by decide)).trans ht
  have anode := (answer_frame hash s _ (by decide)).trans hn
  have regs := storeSetup_registers (answer hash s) target node atarget anode
  change (nodeFinish (stored (answer hash s))).getWord32 _ = _
  simp only [MachineState.getWord32]
  rw [nodeFinish_frame _ _ (low_ne _ _ (low_cell _ (by omega)) (by decide))]
  change (copyRootState (storeSetup (answer hash s))).getWord32 _ = _
  rw [store_data _ (target + 20 * node) bounded (by omega) regs.1 regs.2 i]
  simp only [MachineState.getWord32,storeSetup_frame]

theorem answer_words (hash : Hash) (s : MachineState) (i : Fin 5) :
    (answer hash s).getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
      (hash (hashInput (hashPrepare (children s)))).extractLsb' (32 * i.val) 32 := by
  have dst := (hashPrepare_registers (children s)).2.2.1
  fin_cases i <;>
    simp [answer,writeHash,dst,MachineState.writeWords,MachineState.getWord32,alignToDword,byteOffset,extractWord32]
  all_goals ext b hb;interval_cases b <;> simp

theorem node_value (hash : Hash) (s : MachineState) (parameter left right : BitVec 160)
    (base target level node : Nat)
    (layer : s.getMem 0x43000 = 0) (tree : s.getMem 0x43008 = 0)
    (lev : s.getMem 0x43048 = BitVec.ofNat 64 level) (idx : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (hb : s.getMem 0x43068 = BitVec.ofNat 64 base) (ht : s.getMem 0x43080 = BitVec.ofNat 64 target)
    (sourceBound : base + 40 * node + 40 ≤ 0x40000)
    (targetBound : target + 20 * node + 20 ≤ 0x40000) (targetAlign : target % 4 = 0)
    (par : Words20 s 0x74 parameter)
    (lft : Words20 s (base + 40 * node) left) (rgt : Words20 s (base + 40 * node + 20) right) :
    Words20 (next hash s) (target + 20 * node)
      (truncateHash (hash (toQuery (input parameter left right level node)))) := by
  intro i
  rw [next_data hash s target node ht idx targetBound targetAlign i,answer_words,
    query_eq (children s) parameter left right level node
      (children_context s parameter left right base level node layer tree lev idx hb sourceBound par lft rgt)]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

theorem answer_low_word (hash : Hash) (s : MachineState) (address : Nat) (bounded : address < 0x40000) :
    (answer hash s).getWord32 (BitVec.ofNat 64 address) = s.getWord32 (BitVec.ofNat 64 address) := by
  simp only [MachineState.getWord32]
  rw [answer_frame]
  intro member
  have high : ∀ a ∈ preWrites, 0x40000 ≤ a.toNat := by simp [preWrites,payloadWrites,headerWrites,answerWrites]
  exact (low_ne _ _ (low_cell address bounded) (high _ member)) rfl

theorem next_other_word (hash : Hash) (s : MachineState) (target node address : Nat)
    (ht : s.getMem 0x43080 = BitVec.ofNat 64 target) (hn : s.getMem 0x43088 = BitVec.ofNat 64 node)
    (bounded : target + 20 * node + 20 ≤ 0x40000) (aligned : target % 4 = 0)
    (readBound : address < 0x40000) (readAlign : address % 4 = 0)
    (outside : ∀ j : Fin 5, target + 20 * node + 4 * j.val ≠ address) :
    (next hash s).getWord32 (BitVec.ofNat 64 address) = s.getWord32 (BitVec.ofNat 64 address) := by
  have atarget := (answer_frame hash s _ (by decide)).trans ht
  have anode := (answer_frame hash s _ (by decide)).trans hn
  have regs := storeSetup_registers (answer hash s) target node atarget anode
  change (nodeFinish (stored (answer hash s))).getWord32 _ = _
  simp only [MachineState.getWord32]
  rw [nodeFinish_frame _ _ (low_ne _ _ (low_cell address readBound) (by decide))]
  change (copyRootState (storeSetup (answer hash s))).getWord32 _ = _
  rw [copyRoot_word_frame]
  · simp only [MachineState.getWord32,storeSetup_frame]
    exact answer_low_word hash s address readBound
  · intro i
    rw [regs.2]
    have eq : BitVec.ofNat 64 (target + 20 * node) + signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
        BitVec.ofNat 64 (target + 20 * node + 4 * i.val) := by
      fin_cases i <;> simp [signExtend12,← BitVec.ofNat_add]
    rw [eq]
    exact wordLaneDistinct _ _ (by omega) (by omega) (by omega) readAlign (outside i)

/-- info: 'SigGolfCandidate.SphincsMaskedParentDomain.node_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms node_value

/-- info: 'SigGolfCandidate.SphincsMaskedParentDomain.next_other_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms next_other_word

end SigGolfCandidate.SphincsMaskedParentDomain
