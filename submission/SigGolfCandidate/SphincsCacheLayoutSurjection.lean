import SigGolfCandidate.SphincsMaskedKeygenPadding
import SigGolfCandidate.SphincsMacUniformExtract
import SigGolfCandidate.SphincsMaskedSignRootValue

/-! Every one of the 4095 cached Merkle nodes occupies a unique array slot. -/

namespace SigGolfCandidate.SphincsCacheLayoutSurjection
open SphincsSecurity
open SigGolfCandidate.SphincsCacheSecretDomains
set_option backward.isDefEq.respectTransparency false

theorem flatNode_surjective (index : Fin 4095) :
    ∃ level : Fin 12, ∃ node : Nat,
      node < SphincsMaskedParentLevels.width level.val ∧
      SphincsMaskedKeygenRefinement.flatNode level.val node = index.val := by
  let t := 4095 - index.val
  have ht : t ≠ 0 := by dsimp [t]; omega
  let k := Nat.log2 t
  have hkle : k ≤ 11 := by
    have hlt : t < 2 ^ 12 := by dsimp [t]; omega
    have hk : k < 12 := (Nat.log2_lt ht).mpr hlt
    omega
  have hlow : 2 ^ k ≤ t := (Nat.le_log2 ht).mp (by rfl)
  have hhigh : t < 2 ^ (k + 1) := (Nat.log2_lt ht).mp (by omega)
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
  have htop : 2 ^ (k + 1) ≤ 4096 := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show k + 1 ≤ 12 by omega)
    norm_num at h
    exact h
  let level : Fin 12 := ⟨11 - k, by omega⟩
  let base := 4096 - 2 ^ (k + 1)
  have hbase : base ≤ index.val := by dsimp [base, t] at *; omega
  have hwidth : index.val - base < 2 ^ k := by dsimp [base, t] at *; omega
  refine ⟨level, index.val - base, ?_, ?_⟩
  · simpa [SphincsMaskedParentLevels.width, level,
      show 11 - (11 - k) = k by omega] using hwidth
  · simp only [SphincsMaskedKeygenRefinement.flatNode, level]
    have hlevel : 12 - (11 - k) = k + 1 := by omega
    rw [hlevel]
    dsimp [base] at hbase ⊢
    omega

noncomputable def nodeCoordinate (index : Fin 4095) : Fin 12 × Nat :=
  let level := Classical.choose (flatNode_surjective index)
  let node := Classical.choose (Classical.choose_spec (flatNode_surjective index))
  (level, node)

theorem nodeCoordinate_spec (index : Fin 4095) :
    (nodeCoordinate index).2 <
      SphincsMaskedParentLevels.width (nodeCoordinate index).1.val ∧
    SphincsMaskedKeygenRefinement.flatNode
      (nodeCoordinate index).1.val (nodeCoordinate index).2 = index.val := by
  exact Classical.choose_spec (Classical.choose_spec (flatNode_surjective index))

theorem nodeCoordinate_root :
    nodeCoordinate (⟨4094, by decide⟩ : Fin 4095) =
      ((⟨11, by decide⟩ : Fin 12), 0) := by
  have hspec := nodeCoordinate_spec (⟨4094, by decide⟩ : Fin 4095)
  cases hcoord : nodeCoordinate (⟨4094, by decide⟩ : Fin 4095) with
  | mk level node =>
    simp only [hcoord] at hspec ⊢
    rcases hspec with ⟨hbound, hindex⟩
    fin_cases level <;>
      norm_num [SphincsMaskedParentLevels.width,
        SphincsMaskedKeygenRefinement.flatNode] at hbound hindex ⊢ <;>
      omega

theorem treeValue_top_eq_root (hash : SigGolf.Hash) (seed : MasterSeed) :
    SphincsMaskedParentLevels.treeValue hash
      (SphincsMaskedKeygenRefinement.parameter hash seed) seed 11 0 =
      SphincsMaskedKeygenRefinement.root hash seed := rfl

theorem cache_node_at (hash : SigGolf.Hash) (seed : MasterSeed)
    (cache : SigGolf.Cache)
    (sem : SphincsMaskedKeygenRefinement.CacheSemantics hash seed cache)
    (index : Fin 4095) :
    cache.extractLsb' (8 * (40 + 20 * index.val)) 160 =
      SphincsMaskedParentLevels.treeValue hash
        (SphincsMaskedKeygenRefinement.parameter hash seed) seed
        (nodeCoordinate index).1.val (nodeCoordinate index).2 ^^^
      SphincsMaskedMaskSemantics.padValue hash
        (SphincsMaskedKeygenRefinement.parameter hash seed) seed index.val := by
  have hspec := nodeCoordinate_spec index
  have haddress := (SphincsMaskedKeygenRefinement.flatNode_bounds
    (nodeCoordinate index).1 (nodeCoordinate index).2 hspec.1).2
  have hnode := sem.nodes (nodeCoordinate index).1 (nodeCoordinate index).2 hspec.1
  rw [haddress, hspec.2] at hnode
  simpa only [show 0x88 + 20 * index.val - 0x60 = 40 + 20 * index.val by omega,
    hspec.2] using hnode

theorem cache_node_at_finite_table
    (inputs : Finset SigGolf.Query) (parameter : PublicParameter)
    (seed : MasterSeed)
    (hpad : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (table : inputs → BitVec 256) (cache : SigGolf.Cache)
    (sem : SphincsMaskedKeygenRefinement.CacheSemantics
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table) seed cache)
    (hparameter : SphincsMaskedKeygenRefinement.parameter
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table) seed = parameter)
    (index : Fin 4095) :
    cache.extractLsb' (8 * (40 + 20 * index.val)) 160 =
      SphincsMacUniformExtract.ciphertextNodes inputs parameter seed hpad
        (fun i => ((nodeCoordinate i).1.val, (nodeCoordinate i).2)) table index := by
  let hash := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table
  have hpadAnswer : SphincsMaskedMaskSemantics.padValue hash parameter seed index.val =
      truncateHash
        (table (SphincsFiniteTableMasking.padAddresses inputs parameter seed hpad index)) := by
    unfold SphincsMaskedMaskSemantics.padValue
    exact congrArg truncateHash
      (SphincsOrganizerFiniteHash.finiteHashAnswer_none ∅ inputs table _
        (hpad index) (by rfl))
  have hnode := cache_node_at hash seed cache sem index
  rw [hparameter, hpadAnswer] at hnode
  simpa only [SphincsMacUniformExtract.ciphertextNodes,
    SphincsPadSetupIndependence.plaintextNodes,
    SphincsPadSetupIndependence.plaintextSetup, hparameter,
    BitVec.xor_comm] using hnode

theorem cache_root_header_at_finite_table
    (inputs : Finset SigGolf.Query) (parameter : PublicParameter)
    (seed : MasterSeed)
    (hpad : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (table : inputs → BitVec 256) (cache : SigGolf.Cache)
    (sem : SphincsMaskedKeygenRefinement.CacheSemantics
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table) seed cache)
    (hparameter : SphincsMaskedKeygenRefinement.parameter
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table) seed = parameter) :
    cache.extractLsb' 0 160 =
      SphincsMacUniformExtract.ciphertextNodes inputs parameter seed hpad
        (fun i => ((nodeCoordinate i).1.val, (nodeCoordinate i).2)) table
        (⟨4094, by decide⟩ : Fin 4095) := by
  let hash := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table
  have hpadAnswer : SphincsMaskedMaskSemantics.padValue hash parameter seed 4094 =
      truncateHash
        (table (SphincsFiniteTableMasking.padAddresses inputs parameter seed hpad
          (⟨4094, by decide⟩ : Fin 4095))) := by
    unfold SphincsMaskedMaskSemantics.padValue
    exact congrArg truncateHash
      (SphincsOrganizerFiniteHash.finiteHashAnswer_none ∅ inputs table _
        (hpad ⟨4094, by decide⟩) (by rfl))
  have hroot := sem.rootWords
  rw [hparameter, hpadAnswer] at hroot
  have htree : SphincsMaskedParentLevels.treeValue hash parameter seed 11 0 =
      SphincsMaskedKeygenRefinement.root hash seed := by
    rw [← hparameter]
    exact treeValue_top_eq_root hash seed
  have hword : cache.extractLsb' 0 160 =
      truncateHash
        (table (SphincsFiniteTableMasking.padAddresses inputs parameter seed hpad
          (⟨4094, by decide⟩ : Fin 4095))) ^^^
        SphincsMaskedParentLevels.treeValue hash parameter seed 11 0 := by
    rw [htree]
    exact hroot.trans (BitVec.xor_comm _ _)
  change cache.extractLsb' 0 160 =
    truncateHash
      (table (SphincsFiniteTableMasking.padAddresses inputs parameter seed hpad
        (⟨4094, by decide⟩ : Fin 4095))) ^^^
      SphincsMaskedParentLevels.treeValue hash
        (SphincsMaskedKeygenRefinement.parameter hash seed) seed
        (nodeCoordinate (⟨4094, by decide⟩ : Fin 4095)).1.val
        (nodeCoordinate (⟨4094, by decide⟩ : Fin 4095)).2
  rw [nodeCoordinate_root, hparameter]
  exact hword

def rootIndex : Fin 4095 := ⟨4094, by decide⟩

noncomputable def encodeCachePrefix (parameter : PublicParameter)
    (cipher : Fin 4095 → Digest) : HashInput :=
  List.ofFn fun i : Fin 131052 =>
    if hroot : i.val < 20 then
      UInt8.ofBitVec ((cipher rootIndex).extractLsb' (8 * i.val) 8)
    else if hparam : i.val < 40 then
      UInt8.ofBitVec (parameter.extractLsb' (8 * (i.val - 20)) 8)
    else if hnode : i.val < 81940 then
      let node : Fin 4095 := ⟨(i.val - 40) / 20, by omega⟩
      UInt8.ofBitVec ((cipher node).extractLsb' (8 * ((i.val - 40) % 20)) 8)
    else 0

theorem cacheCiphertext_eq_encodeCachePrefix
    (cache : SigGolf.Cache) (parameter : PublicParameter)
    (cipher : Fin 4095 → Digest)
    (hroot : cache.extractLsb' 0 160 = cipher rootIndex)
    (hparameter : cache.extractLsb' (8 * 20) 160 = parameter)
    (hnodes : ∀ index : Fin 4095,
      cache.extractLsb' (8 * (40 + 20 * index.val)) 160 = cipher index)
    (hpadding : SphincsMaskedKeygenPadding.CacheZeroPadding cache) :
    SphincsMaskedKeygenRefinement.cacheCiphertext cache =
      encodeCachePrefix parameter cipher := by
  unfold SphincsMaskedKeygenRefinement.cacheCiphertext encodeCachePrefix
  congr 1
  funext i
  by_cases h0 : i.val < 20
  · simp only [dif_pos h0]
    have hbyte := congrArg
      (fun value : BitVec 160 => UInt8.ofBitVec (value.extractLsb' (8 * i.val) 8)) hroot
    have hslice := SphincsMaskedSignRootValue.cache_slice_byte cache 0 i.val h0
    have hresult := (congrArg UInt8.ofBitVec hslice).symm.trans hbyte
    change UInt8.ofBitVec (cache.extractLsb' (8 * i.val) 8) =
      UInt8.ofBitVec ((cipher rootIndex).extractLsb' (8 * i.val) 8)
    simpa only [Nat.zero_add] using hresult
  · simp only [dif_neg h0]
    by_cases h1 : i.val < 40
    · simp only [dif_pos h1]
      have hlocal : i.val - 20 < 20 := by omega
      have hbyte := congrArg
        (fun value : BitVec 160 => UInt8.ofBitVec
          (value.extractLsb' (8 * (i.val - 20)) 8)) hparameter
      have hslice := SphincsMaskedSignRootValue.cache_slice_byte cache 20
        (i.val - 20) hlocal
      rw [show 20 + (i.val - 20) = i.val by omega] at hslice
      exact (congrArg UInt8.ofBitVec hslice).symm.trans hbyte
    · simp only [dif_neg h1]
      by_cases h2 : i.val < 81940
      · simp only [dif_pos h2]
        have hindex : (i.val - 40) / 20 < 4095 := by omega
        let node : Fin 4095 := ⟨(i.val - 40) / 20, hindex⟩
        have hlocal : (i.val - 40) % 20 < 20 := Nat.mod_lt _ (by decide)
        have hbyte := congrArg
          (fun value : BitVec 160 => UInt8.ofBitVec
            (value.extractLsb' (8 * ((i.val - 40) % 20)) 8)) (hnodes node)
        have hslice := SphincsMaskedSignRootValue.cache_slice_byte cache
          (40 + 20 * node.val) ((i.val - 40) % 20) hlocal
        rw [show 40 + 20 * node.val + (i.val - 40) % 20 = i.val by
          dsimp [node]; omega] at hslice
        exact (congrArg UInt8.ofBitVec hslice).symm.trans hbyte
      · simp only [dif_neg h2]
        have hzero := hpadding i.val (by omega) i.isLt
        simp [hzero]

theorem keygen_cacheCiphertext_eq_encoded
    (inputs : Finset SigGolf.Query) (parameter : PublicParameter)
    (seed : MasterSeed)
    (hpad : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (table : inputs → BitVec 256) (cache : SigGolf.Cache)
    (sem : SphincsMaskedKeygenRefinement.CacheSemantics
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table) seed cache)
    (padding : SphincsMaskedKeygenPadding.CacheZeroPadding cache)
    (hparameter : SphincsMaskedKeygenRefinement.parameter
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table) seed = parameter) :
    SphincsMaskedKeygenRefinement.cacheCiphertext cache =
      encodeCachePrefix parameter
        (SphincsMacUniformExtract.ciphertextNodes inputs parameter seed hpad
          (fun i => ((nodeCoordinate i).1.val, (nodeCoordinate i).2)) table) := by
  apply cacheCiphertext_eq_encodeCachePrefix
  · simpa only [rootIndex] using cache_root_header_at_finite_table
      inputs parameter seed hpad table cache sem hparameter
  · rw [← hparameter]
    exact sem.parameterWords
  · intro index
    exact cache_node_at_finite_table inputs parameter seed hpad table cache sem hparameter index
  · exact padding

theorem cache_prefix_byte_eq (first second : SigGolf.Cache)
    (hprefix : SphincsMaskedKeygenRefinement.cacheCiphertext first =
      SphincsMaskedKeygenRefinement.cacheCiphertext second)
    (i : Nat) (hi : i < 131052) :
    first.extractLsb' (8 * i) 8 = second.extractLsb' (8 * i) 8 := by
  have h := congrArg
    (fun bytes : HashInput => bytes[i]?) hprefix
  simp only [SphincsMaskedKeygenRefinement.cacheCiphertext,
    List.getElem?_ofFn, dif_pos hi] at h
  have hbyte := Option.some.inj h
  simpa using congrArg UInt8.toBitVec hbyte

theorem cache_eq_of_prefix_and_tag (first second : SigGolf.Cache)
    (hprefix : SphincsMaskedKeygenRefinement.cacheCiphertext first =
      SphincsMaskedKeygenRefinement.cacheCiphertext second)
    (htag : first.extractLsb' (8 * 131052) 160 =
      second.extractLsb' (8 * 131052) 160) :
    first = second := by
  ext bit hbit
  by_cases hp : bit < 8 * 131052
  · have hi : bit / 8 < 131052 := by omega
    have hbyte := cache_prefix_byte_eq first second hprefix (bit / 8) hi
    have hlocal := congrArg (fun word : BitVec 8 => word.getLsbD (bit % 8)) hbyte
    have hmod : bit % 8 < 8 := Nat.mod_lt _ (by decide)
    simp only [BitVec.getLsbD_extractLsb', hmod, decide_true,
      Bool.true_and] at hlocal
    rw [show 8 * (bit / 8) + bit % 8 = bit by omega] at hlocal
    simpa only [BitVec.getLsbD_eq_getElem hbit] using hlocal
  · have hlocalBound : bit - 8 * 131052 < 160 := by
      dsimp [SigGolf.CACHE_BYTES] at hbit
      omega
    have hlocal := congrArg
      (fun word : BitVec 160 => word.getLsbD (bit - 8 * 131052)) htag
    simp only [BitVec.getLsbD_extractLsb', hlocalBound, decide_true,
      Bool.true_and] at hlocal
    rw [show 8 * 131052 + (bit - 8 * 131052) = bit by omega] at hlocal
    simpa only [BitVec.getLsbD_eq_getElem hbit] using hlocal

theorem keygen_cache_tag_at_finite_table
    (inputs : Finset SigGolf.Query) (parameter : PublicParameter)
    (seed : MasterSeed)
    (hpad : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (hmac : ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery
        (macInput parameter seed (encodeCachePrefix parameter cipher)) ∈ inputs)
    (table : inputs → BitVec 256) (cache : SigGolf.Cache)
    (sem : SphincsMaskedKeygenRefinement.CacheSemantics
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table) seed cache)
    (padding : SphincsMaskedKeygenPadding.CacheZeroPadding cache)
    (hparameter : SphincsMaskedKeygenRefinement.parameter
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table) seed = parameter) :
    cache.extractLsb' (8 * 131052) 160 =
      truncateHash (table
        (SphincsMacUniformExtract.chosenMacAddress inputs parameter seed hpad
          (fun i => ((nodeCoordinate i).1.val, (nodeCoordinate i).2))
          (encodeCachePrefix parameter) hmac table)) := by
  have hprefix := keygen_cacheCiphertext_eq_encoded
    inputs parameter seed hpad table cache sem padding hparameter
  have htag := sem.tag
  rw [hparameter, hprefix] at htag
  have hanswer := SphincsOrganizerFiniteHash.finiteHashAnswer_none
    ∅ inputs table
    (SphincsBridge.toQuery
      (macInput parameter seed
        (encodeCachePrefix parameter
          (SphincsMacUniformExtract.ciphertextNodes inputs parameter seed hpad
            (fun i => ((nodeCoordinate i).1.val, (nodeCoordinate i).2)) table))))
    (hmac _) (by rfl)
  rw [hanswer] at htag
  simpa only [SphincsMacUniformExtract.chosenMacAddress] using htag

end SigGolfCandidate.SphincsCacheLayoutSurjection

/-- info: 'SigGolfCandidate.SphincsCacheLayoutSurjection.flatNode_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheLayoutSurjection.flatNode_surjective

/-- info: 'SigGolfCandidate.SphincsCacheLayoutSurjection.cache_node_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheLayoutSurjection.cache_node_at

/-- info: 'SigGolfCandidate.SphincsCacheLayoutSurjection.cache_node_at_finite_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheLayoutSurjection.cache_node_at_finite_table

/-- info: 'SigGolfCandidate.SphincsCacheLayoutSurjection.cache_root_header_at_finite_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheLayoutSurjection.cache_root_header_at_finite_table

/-- info: 'SigGolfCandidate.SphincsCacheLayoutSurjection.keygen_cacheCiphertext_eq_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheLayoutSurjection.keygen_cacheCiphertext_eq_encoded

/-- info: 'SigGolfCandidate.SphincsCacheLayoutSurjection.cache_eq_of_prefix_and_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheLayoutSurjection.cache_eq_of_prefix_and_tag

/-- info: 'SigGolfCandidate.SphincsCacheLayoutSurjection.keygen_cache_tag_at_finite_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheLayoutSurjection.keygen_cache_tag_at_finite_table
