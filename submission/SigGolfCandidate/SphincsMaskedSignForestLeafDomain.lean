import SigGolfCandidate.SphincsMaskedSignForestDomain
import SigGolfCandidate.SphincsMaskedSignForestLoop

namespace SigGolfCandidate.SphincsMaskedSignForestLeafDomain
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsSecurity SphincsBridge SphincsMaskedChainDomain
open SphincsMaskedKeygenPrefix
open SphincsMaskedSignForestEntry SphincsVerifierFtsGenericBytes
open SphincsMaskedSignForestLoop
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def ready (s : MachineState) : MachineState :=
  SphincsMaskedSignForestLoop.header (SphincsMaskedSignForestLoop.payload s)

def Context (s : MachineState) (parameter : PublicParameter)
    (secret : Digest) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) : Prop :=
  (SphincsMaskedSignForestLoop.payload s).getMem 0x43000 = BitVec.ofNat 64 tree.val ∧
  (SphincsMaskedSignForestLoop.payload s).getMem 0x43008 = BitVec.ofNat 64 index.val ∧
  (SphincsMaskedSignForestLoop.payload s).getMem 0x43010 = 0 ∧
  (SphincsMaskedSignForestLoop.payload s).getMem 0x43018 = BitVec.ofNat 64 leaf.val ∧
  Words20 (SphincsMaskedSignForestLoop.payload s) 0x74 parameter ∧
  Words20 s 0x42000 secret

def queryWord (s : MachineState) (i : Fin 15) : BitVec 32 :=
  if h : i.val < 10 then
    SphincsMaskedSignForestLoop.headerWord (SphincsMaskedSignForestLoop.payload s) ⟨i.val, h⟩
  else s.getWord32 (BitVec.ofNat 64 (0x42000 + 4 * (i.val - 10)))

def semanticPayload (parameter : PublicParameter) (secret : Digest)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) : List Byte :=
  (tweakableHashInput parameter (.ftsLeaf index tree leaf) (bytesLE 20 secret)).map UInt8.toBitVec

theorem semanticPayload_length (parameter : PublicParameter) (secret : Digest)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) :
    (semanticPayload parameter secret index tree leaf).length = 60 := by
  simp [semanticPayload, tweakableHashInput, tweakBytes, hashDomainFields, tweakFields,
    tweakBytes, fieldBytes, bytesLE]

theorem prepared_word (s : MachineState) (i : Fin 15) :
    (ready s).getWord32 (BitVec.ofNat 64 (0x40000 + 4 * i.val)) = queryWord s i := by
  by_cases hi : i.val < 10
  · simp only [queryWord, dif_pos hi, ready]
    exact SphincsMaskedSignForestLoop.header_word (SphincsMaskedSignForestLoop.payload s) ⟨i.val, hi⟩
  · have hj : i.val - 10 < 5 := by omega
    simp only [queryWord, dif_neg hi, Fin.val_mk, ready]
    have hadd : 0x40000 + 4 * i.val =
        0x40028 + 4 * (i.val - 10) := by omega
    rw [hadd]
    exact SphincsMaskedSignForestLoop.answer_payload_word s ⟨i.val - 10, hj⟩

theorem prepared_byte (s : MachineState) (i : Fin 60) :
    (ready s).getByte (BitVec.ofNat 64 (0x40000 + i.val)) =
      (queryWord s ⟨i.val / 4, by omega⟩).extractLsb'
        (8 * (i.val % 4)) 8 := by
  have h := variableWord_byte (ready s)
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
    (secret : Digest) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) (ctx : Context s parameter secret index tree leaf)
    (i : Fin 60) :
    (queryWord s ⟨i.val / 4, by omega⟩).extractLsb'
      (8 * (i.val % 4)) 8 =
      (semanticPayload parameter secret index tree leaf)[i.val]'(by
        rw [semanticPayload_length]; exact i.isLt) := by
  obtain ⟨htree, hindex, hpos, hleaf, hparameter, hsecret⟩ := ctx
  have p0 := hparameter 0
  have p1 := hparameter 1
  have p2 := hparameter 2
  have p3 := hparameter 3
  have p4 := hparameter 4
  have k0 := hsecret 0
  have k1 := hsecret 1
  have k2 := hsecret 2
  have k3 := hsecret 3
  have k4 := hsecret 4
  norm_num at p0 p1 p2 p3 p4 k0 k1 k2 k3 k4
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
  have htree' : (SphincsMaskedSignForestLoop.payload s).getMem (274432#64) =
      (BitVec.ofNat 8 tree.val).setWidth 64 := by simpa using htree
  have hindex' : (SphincsMaskedSignForestLoop.payload s).getMem (274440#64) =
      BitVec.ofNat 64 index.val := by simpa using hindex
  have hpos' : (SphincsMaskedSignForestLoop.payload s).getMem (274448#64) = 0 := by simpa using hpos
  have hleaf' : (SphincsMaskedSignForestLoop.payload s).getMem (274456#64) =
      BitVec.ofNat 64 leaf.val := by simpa using hleaf
  by_cases hi : i.val < 20
  · fin_cases i <;>
      simp [queryWord, SphincsMaskedSignForestLoop.headerWord, htree, hindex, hpos, hleaf,
        p0, p1, p2, p3, p4, k0, k1, k2, k3, k4,
        semanticPayload, tweakableHashInput, tweakBytes, hashDomainFields, tweakFields,
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
      simp [queryWord, SphincsMaskedSignForestLoop.headerWord, htree, hindex, hpos, hleaf,
        p0, p1, p2, p3, p4, k0, k1, k2, k3, k4,
        semanticPayload, tweakableHashInput, tweakBytes, hashDomainFields, tweakFields,
        fieldBytes, bytesLE, protocolDomainSep, extractWord32] at hi ⊢
    all_goals exact nested_extract _ _ _ _ _ (by decide)

theorem query_eq (s : MachineState) (parameter : PublicParameter)
    (secret : Digest) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) (ctx : Context s parameter secret index tree leaf) :
    hashInput (ready s) =
      toQuery (tweakableHashInput parameter (.ftsLeaf index tree leaf) (bytesLE 20 secret)) := by
  apply Serialization.hashInput_of_list (ready s) 0x40000
    (semanticPayload parameter secret index tree leaf)
  · exact (SphincsMaskedSignForestLoop.header_registers (SphincsMaskedSignForestLoop.payload s)).1
  · rw [semanticPayload_length]
    simp [ready, (SphincsMaskedSignForestLoop.header_registers (SphincsMaskedSignForestLoop.payload s)).2.1]
  · intro i hi
    have bound : i < 60 := by simpa only [semanticPayload_length] using hi
    rw [prepared_byte s ⟨i, bound⟩]
    exact context_byte s parameter secret index tree leaf ctx ⟨i, bound⟩

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLeafDomain.context_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms context_byte

/-- info: 'SigGolfCandidate.SphincsMaskedSignForestLeafDomain.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms query_eq

end SigGolfCandidate.SphincsMaskedSignForestLeafDomain
