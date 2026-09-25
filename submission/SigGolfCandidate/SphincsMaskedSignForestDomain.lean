import SigGolfCandidate.SphincsMaskedSignForestEntry

namespace SigGolfCandidate.SphincsMaskedSignForestDomain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsSecurity SphincsBridge SphincsMaskedChainDomain
open SphincsMaskedKeygenPrefix
open SphincsMaskedSignForestEntry SphincsVerifierFtsGenericBytes
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def Context (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) : Prop :=
  s.getMem 0x43000 = BitVec.ofNat 64 tree.val ∧
  s.getMem 0x43008 = BitVec.ofNat 64 index.val ∧
  s.getMem 0x43010 = 0 ∧
  s.getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
  Words20 s 0x74 parameter ∧
  (∀ i : Fin 8, s.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * i.val)) =
    seed.extractLsb' (32 * i.val) 32)

def queryWord (s : MachineState) (i : Fin 18) : BitVec 32 :=
  if h : i.val < 10 then leafHeaderWord s ⟨i.val, h⟩
  else s.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * (i.val - 10)))

def payload (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) : List Byte :=
  (keygenHashInput parameter (.fts index tree leaf) seed).map UInt8.toBitVec

theorem payload_length (parameter : PublicParameter) (seed : MasterSeed)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) :
    (payload parameter seed index tree leaf).length = 72 := by
  simp [payload, keygenHashInput, keygenDomainFields, tweakFields,
    fieldBytes, bytesLE]

theorem seed_word32_preserved (s : MachineState) (i : Fin 8) :
    (leafHashReady s).getWord32
      (BitVec.ofNat 64 (0x40028 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x40028 + 4 * i.val)) := by
  fin_cases i <;>
    simp [leafHashReady, runSchedule, leafHashSchedule,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, MachineState.setWord32,
      MachineState.getWord32, alignToDword, byteOffset]

theorem prepared_word (s : MachineState) (i : Fin 18) :
    (leafHashReady s).getWord32
      (BitVec.ofNat 64 (0x40000 + 4 * i.val)) = queryWord s i := by
  by_cases hi : i.val < 10
  · simp only [queryWord, dif_pos hi]
    exact leafHash_headerWord s ⟨i.val, hi⟩
  · have hj : i.val - 10 < 8 := by omega
    simp only [queryWord, dif_neg hi, Fin.val_mk]
    have hadd : 0x40000 + 4 * i.val =
        0x40028 + 4 * (i.val - 10) := by omega
    rw [hadd]
    exact seed_word32_preserved s ⟨i.val - 10, hj⟩

theorem prepared_byte (s : MachineState) (i : Fin 72) :
    (leafHashReady s).getByte (BitVec.ofNat 64 (0x40000 + i.val)) =
      (queryWord s ⟨i.val / 4, by omega⟩).extractLsb'
        (8 * (i.val % 4)) 8 := by
  have h := variableWord_byte (leafHashReady s)
    (0x40000 + 4 * (i.val / 4)) (by omega) (by omega)
    0 ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at h
  rw [show 0x40000 + 4 * (i.val / 4) + i.val % 4 =
    0x40000 + i.val by omega] at h
  rw [h, prepared_word s ⟨i.val / 4, by omega⟩]

theorem nested_extract {n : Nat} (x : BitVec n)
    (start offset len width : Nat) (inside : offset + len ≤ width) :
    (x.extractLsb' start width).extractLsb' offset len =
      x.extractLsb' (start + offset) len := by
  ext bit bound
  have hbit : offset + bit < width := by omega
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb',
    hbit, Nat.add_assoc]

theorem context_byte (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) (ctx : Context s parameter seed index tree leaf)
    (i : Fin 72) :
    (queryWord s ⟨i.val / 4, by omega⟩).extractLsb'
      (8 * (i.val % 4)) 8 =
      (payload parameter seed index tree leaf)[i.val]'(by
        rw [payload_length]; exact i.isLt) := by
  obtain ⟨htree, hindex, hpos, hleaf, hparameter, hseed⟩ := ctx
  have p0 := hparameter 0
  have p1 := hparameter 1
  have p2 := hparameter 2
  have p3 := hparameter 3
  have p4 := hparameter 4
  have k0 := hseed 0
  have k1 := hseed 1
  have k2 := hseed 2
  have k3 := hseed 3
  have k4 := hseed 4
  have k5 := hseed 5
  have k6 := hseed 6
  have k7 := hseed 7
  norm_num at p0 p1 p2 p3 p4 k0 k1 k2 k3 k4 k5 k6 k7
  have treeWidth : (BitVec.ofNat 64 tree.val).setWidth 8 =
      BitVec.ofNat 8 tree.val := by simp
  have treeSmall : tree.val < 2 ^ 8 := by
    have h := tree.isLt
    norm_num [ftsTrees] at h ⊢
    omega
  have treeZext : (BitVec.ofNat 8 tree.val).setWidth 64 =
      BitVec.ofNat 64 tree.val :=
    BitVec.setWidth_ofNat_of_le_of_lt (by omega) treeSmall
  rw [← treeZext] at htree
  have indexWidth : (BitVec.ofNat 64 index.val).setWidth 32 =
      BitVec.ofNat 32 index.val := by simp
  have leafWidth : (BitVec.ofNat 64 leaf.val).setWidth 32 =
      BitVec.ofNat 32 leaf.val := by simp
  have htree' : s.getMem (274432#64) =
      (BitVec.ofNat 8 tree.val).setWidth 64 := by simpa using htree
  have hindex' : s.getMem (274440#64) =
      BitVec.ofNat 64 index.val := by simpa using hindex
  have hpos' : s.getMem (274448#64) = 0 := by simpa using hpos
  have hleaf' : s.getMem (274456#64) =
      BitVec.ofNat 64 leaf.val := by simpa using hleaf
  by_cases hi : i.val < 20
  · fin_cases i <;>
      simp [queryWord, leafHeaderWord, htree, hindex, hpos, hleaf,
        p0, p1, p2, p3, p4, k0, k1, k2, k3, k4, k5, k6, k7,
        payload, keygenHashInput, keygenDomainFields, tweakFields,
        fieldBytes, bytesLE, protocolDomainSep, extractWord32] at hi ⊢
    all_goals
      first
      | (rw [hindex']
         exact BitVec.extractLsb'_setWidth_of_le (by decide))
      | (rw [hindex']
         simp [BitVec.setWidth_ushiftRight_eq_extractLsb, nested_extract])
      | (rw [hleaf', leafWidth])
      | (rw [hpos']
         decide)
      | (rw [htree']
         fin_cases tree <;> decide)
  · fin_cases i <;>
      simp [queryWord, leafHeaderWord, htree, hindex, hpos, hleaf,
        p0, p1, p2, p3, p4, k0, k1, k2, k3, k4, k5, k6, k7,
        payload, keygenHashInput, keygenDomainFields, tweakFields,
        fieldBytes, bytesLE, protocolDomainSep, extractWord32] at hi ⊢
    all_goals exact nested_extract _ _ _ _ _ (by decide)

theorem query_eq (s : MachineState) (parameter : PublicParameter)
    (seed : MasterSeed) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) (ctx : Context s parameter seed index tree leaf) :
    hashInput (leafHashReady s) =
      toQuery (keygenHashInput parameter (.fts index tree leaf) seed) := by
  apply Serialization.hashInput_of_list (leafHashReady s) 0x40000
    (payload parameter seed index tree leaf)
  · exact (leafHash_registers s).1
  · rw [payload_length, (leafHash_registers s).2.1]
    rfl
  · intro i hi
    have bound : i < 72 := by simpa only [payload_length] using hi
    rw [prepared_byte s ⟨i, bound⟩]
    exact context_byte s parameter seed index tree leaf ctx ⟨i, bound⟩

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestDomain.context_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms context_byte

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestDomain.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_eq

end SigGolfCandidate.SphincsMaskedSignForestDomain
