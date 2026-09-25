import SigGolfCandidate.SphincsMaskedPublicKeyDomain

namespace SigGolfCandidate.SphincsMaskedLeafDomain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedLeafLoop SphincsMaskedChainDomain
open SphincsMaskedPublicKeyDomain SphincsBridge SphincsSecurity
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def HeaderContext (s : MachineState) (parameter : BitVec 160) (leaf : LeafIndex) : Prop :=
  s.getMem 0x43000#64 = 0 ∧ s.getMem 0x43008#64 = 0 ∧
  s.getMem 0x43018#64 = BitVec.ofNat 64 leaf.val ∧ s.getMem 0x43010#64 = 0 ∧ Words20 s 0x74 parameter

def headerWord (s : MachineState) (i : Fin 10) : BitVec 32 :=
  if i.val = 0 then (513#64 + (s.getMem 0x43000 <<< 16)).setWidth 32
  else if i.val = 1 then (s.getMem 0x43010).setWidth 32
  else if i.val = 2 then extractWord32 (s.getMem 0x43008) 0
  else if i.val = 3 then extractWord32 (s.getMem 0x43008) 1
  else if i.val = 4 then (s.getMem 0x43018).setWidth 32
  else s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * (i.val - 5)))

theorem header_words (s : MachineState) (i : Fin 10) :
    (hashPrepare s).getWord32 (BitVec.ofNat 64 (0x40000 + 4 * i.val)) = headerWord s i := by
  fin_cases i <;>
    simp [hashPrepare,runSchedule,hashPrepareSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,headerWord]

def header (parameter : BitVec 160) (leaf : LeafIndex) : List Byte :=
  ((fieldBytes (hashDomainFields (.leaf topLayer Concrete.rootTree leaf))) ++ bytesLE 20 parameter).map UInt8.toBitVec

theorem header_length (parameter : BitVec 160) (leaf : LeafIndex) : (header parameter leaf).length = 40 := by
  simp [header,hashDomainFields,tweakFields,fieldBytes,bytesLE]

theorem header_byte (s : MachineState) (parameter : BitVec 160) (leaf : LeafIndex)
    (ctx : HeaderContext s parameter leaf) (i : Fin 40) :
    (hashPrepare s).getByte (BitVec.ofNat 64 (0x40000 + i.val)) =
      (header parameter leaf)[i.val]'(by rw [header_length];exact i.isLt) := by
  have h := SphincsVerifierFtsGenericBytes.variableWord_byte (hashPrepare s)
    (0x40000 + 4 * (i.val / 4)) (by omega) (by omega) 0 ⟨i.val % 4,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h
  rw [show 0x40000 + 4 * (i.val / 4) + i.val % 4 = 0x40000 + i.val by omega] at h
  rw [h,header_words s ⟨i.val / 4,by omega⟩]
  obtain ⟨layer,tree,index,position,par⟩ := ctx
  have p0 := par 0
  have p1 := par 1
  have p2 := par 2
  have p3 := par 3
  have p4 := par 4
  norm_num at p0 p1 p2 p3 p4
  fin_cases i <;>
    simp [headerWord,layer,tree,index,position,p0,p1,p2,p3,p4,extractWord32,
      header,hashDomainFields,tweakFields,fieldBytes,bytesLE,protocolDomainSep,topLayer,Concrete.rootTree]
  all_goals ext b hb; interval_cases b <;> simp

def headerWrites : List Word := [0x40000#64,0x40008#64,0x40010#64,0x40018#64,0x40020#64]

theorem hashPrepare_frame (s : MachineState) (a : Word) (outside : a ∉ headerWrites) :
    (hashPrepare s).getMem a = s.getMem a := by
  simp only [headerWrites,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4⟩ := outside
  simp [hashPrepare,runSchedule,hashPrepareSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,h0,h1,h2,h3,h4]

theorem hashPrepare_payload (s : MachineState) (i : Fin 1040) :
    (hashPrepare s).getByte (BitVec.ofNat 64 (0x40028 + i.val)) =
      s.getByte (BitVec.ofNat 64 (0x40028 + i.val)) := by
  rw [SphincsVerifierFtsRootCopyBytes.getByte_word _ 0x40028 i.val (by decide) (by omega),
    SphincsVerifierFtsRootCopyBytes.getByte_word _ 0x40028 i.val (by decide) (by omega),hashPrepare_frame]
  simp only [headerWrites,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true]
  repeat' constructor
  all_goals
    intro eq
    have h := congrArg BitVec.toNat eq
    simp only [SphincsVerifierFtsRootCopy.wordAddress,BitVec.toNat_ofNat] at h
    omega

theorem leafPayload_flat (endpoints : ChainIndex → Digest) :
    Concrete.leafPayload endpoints = List.ofFn (fun byte : Fin (52 * 20) =>
      UInt8.ofBitVec ((endpoints ⟨byte.val / 20,by change byte.val / 20 < 52; omega⟩).extractLsb' (8 * (byte.val % 20)) 8)) := by
  let f : Fin (52 * 20) → UInt8 := fun byte =>
    UInt8.ofBitVec ((endpoints ⟨byte.val / 20,by change byte.val / 20 < 52; omega⟩).extractLsb' (8 * (byte.val % 20)) 8)
  rw [List.ofFn_mul f]
  unfold Concrete.leafPayload
  change (List.ofFn endpoints).flatMap (bytesLE 20) = _
  simp only [List.flatMap]
  congr 1

theorem leafPayload_length (endpoints : ChainIndex → Digest) :
    (Concrete.leafPayload endpoints).length = 1040 := by rw [leafPayload_flat,List.length_ofFn]

def input (parameter : BitVec 160) (leaf : LeafIndex) (endpoints : ChainIndex → Digest) : HashInput :=
  tweakableHashInput parameter (.leaf topLayer Concrete.rootTree leaf) (Concrete.leafPayload endpoints)

theorem input_split (parameter : BitVec 160) (leaf : LeafIndex) (endpoints : ChainIndex → Digest) :
    (input parameter leaf endpoints).map UInt8.toBitVec =
      header parameter leaf ++ (Concrete.leafPayload endpoints).map UInt8.toBitVec := by
  simp [input,tweakableHashInput,tweakBytes,header,List.append_assoc]

theorem query_eq (s : MachineState) (parameter : BitVec 160) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) (ctx : HeaderContext s parameter leaf)
    (payload : ∀ i : Fin 1040, s.getByte (BitVec.ofNat 64 (0x40028 + i.val)) =
      (endpoints ⟨i.val / 20,by change i.val / 20 < 52;omega⟩).extractLsb' (8 * (i.val % 20)) 8) :
    hashInput (hashPrepare s) = toQuery (input parameter leaf endpoints) := by
  apply Serialization.hashInput_of_list (hashPrepare s) 0x40000 ((input parameter leaf endpoints).map UInt8.toBitVec)
  · exact (hashPrepare_registers s).1
  · rw [input_split,List.length_append,header_length,List.length_map,leafPayload_length,
      (hashPrepare_registers s).2.1];rfl
  · intro i hi
    simp only [input_split] at hi ⊢
    have bound : i < 1080 := by simpa only [List.length_append,header_length,List.length_map,leafPayload_length] using hi
    by_cases h : i < 40
    · rw [List.getElem_append_left (by simpa only [header_length] using h)]
      exact header_byte s parameter leaf ctx ⟨i,h⟩
    · rw [List.getElem_append_right (by simpa only [header_length] using Nat.le_of_not_gt h)]
      simp only [header_length]
      have offset : 0x40000 + i = 0x40028 + (i - 40) := by omega
      rw [offset,hashPrepare_payload s ⟨i-40,by omega⟩,payload ⟨i-40,by omega⟩]
      simp only [leafPayload_flat,List.map_ofFn,List.getElem_ofFn,Function.comp_apply,UInt8.toBitVec_ofBitVec]

theorem answer_words (hash : Hash) (s : MachineState) (i : Fin 5) :
    (answerState hash s).getWord32 (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
      (hash (hashInput (hashPrepare s))).extractLsb' (32 * i.val) 32 := by
  have dst := (hashPrepare_registers s).2.2.1
  fin_cases i <;>
    simp [answerState,writeHash,dst,MachineState.writeWords,
      MachineState.getWord32,alignToDword,byteOffset,extractWord32]
  all_goals ext j hj; interval_cases j <;> simp

theorem cache_value (hash : Hash) (s : MachineState) (parameter : BitVec 160) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) (ctx : HeaderContext s parameter leaf)
    (counter : s.getMem 0x43020 = BitVec.ofNat 64 leaf.val)
    (payload : ∀ i : Fin 1040, s.getByte (BitVec.ofNat 64 (0x40028 + i.val)) =
      (endpoints ⟨i.val / 20,by change i.val / 20 < 52;omega⟩).extractLsb' (8 * (i.val % 20)) 8) :
    Words20 (nextLeaf (answerState hash s)) (0x88 + 20 * leaf.val)
      (evalWithAnswerFn (spec := SphincsSecurity.HashSpec) (adaptOracle hash)
        (Concrete.leafHash parameter topLayer Concrete.rootTree leaf endpoints : OracleComp SphincsSecurity.HashSpec Digest)) := by
  intro i
  rw [SphincsMaskedLeafCache.nextLeaf_data _ leaf ((answer_leaf hash s).trans counter) i,
    answer_words,query_eq s parameter leaf endpoints ctx payload]
  rw [Concrete.leafHash,SphincsMaskedChainDomain.eval_hash]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

/-- info: 'SigGolfCandidate.SphincsMaskedLeafDomain.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_eq

/-- info: 'SigGolfCandidate.SphincsMaskedLeafDomain.cache_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cache_value

end SigGolfCandidate.SphincsMaskedLeafDomain
