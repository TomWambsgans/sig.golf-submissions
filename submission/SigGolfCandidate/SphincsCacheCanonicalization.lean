import SigGolfCandidate.SphincsDynamicPadSetup

/-! The public cache is uniquely determined by its encrypted nodes and MAC. -/

namespace SigGolfCandidate.SphincsCacheCanonicalization
open SigGolf SphincsSecurity
open SigGolfCandidate.SphincsCacheSecretDomains

def CacheFields (parameter : PublicParameter)
    (cipher : Fin 4095 → Digest) (tag : Digest)
    (cache : SigGolf.Cache) : Prop :=
  SphincsMaskedKeygenRefinement.cacheCiphertext cache =
      SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher ∧
    cache.extractLsb' (8 * 131052) 160 = tag

noncomputable def cacheFromFields (parameter : PublicParameter)
    (cipher : Fin 4095 → Digest) (tag : Digest) : SigGolf.Cache := by
  classical
  exact if h : ∃ cache, CacheFields parameter cipher tag cache then Classical.choose h else 0

theorem cacheFromFields_eq_of_fields (parameter : PublicParameter)
    (cipher : Fin 4095 → Digest) (tag : Digest)
    (cache : SigGolf.Cache) (hfields : CacheFields parameter cipher tag cache) :
    cacheFromFields parameter cipher tag = cache := by
  classical
  have hex : ∃ candidate, CacheFields parameter cipher tag candidate := ⟨cache, hfields⟩
  simp only [cacheFromFields, dif_pos hex]
  have hchosen := Classical.choose_spec hex
  exact SphincsCacheLayoutSurjection.cache_eq_of_prefix_and_tag
    (Classical.choose hex) cache (hchosen.1.trans hfields.1.symm)
    (hchosen.2.trans hfields.2.symm)

/-- For any fixed finite oracle table, an honest exact-image keygen cache is
the unique encoding of the public parameter, ciphertext nodes, and MAC tag. -/
theorem keygen_cache_is_canonical
    (inputs : Finset SigGolf.Query) (seed : MasterSeed)
    (hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery
        (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (hmac : ∀ parameter : PublicParameter, ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery
        (macInput parameter seed
          (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs)
    (table : inputs → BitVec 256) (cache : SigGolf.Cache)
    (sem : SphincsMaskedKeygenRefinement.CacheSemantics
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table) seed cache)
    (padding : SphincsMaskedKeygenPadding.CacheZeroPadding cache) :
    let setup := SphincsPadSetupIndependence.plaintextSetup inputs seed table
    let parameter := setup.1
    let cipher := SphincsMacUniformExtract.ciphertextNodes inputs parameter seed
      (hpad parameter) (fun i => ((SphincsCacheLayoutSurjection.nodeCoordinate i).1.val,
        (SphincsCacheLayoutSurjection.nodeCoordinate i).2)) table
    let mac := SphincsMacUniformExtract.chosenMacAddress inputs parameter seed
      (hpad parameter) (fun i => ((SphincsCacheLayoutSurjection.nodeCoordinate i).1.val,
        (SphincsCacheLayoutSurjection.nodeCoordinate i).2))
      (SphincsCacheLayoutSurjection.encodeCachePrefix parameter) (hmac parameter) table
    cache = cacheFromFields parameter cipher (truncateHash (table mac)) := by
  let parameter := (SphincsPadSetupIndependence.plaintextSetup inputs seed table).1
  have hparameter : SphincsMaskedKeygenRefinement.parameter
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table) seed = parameter := rfl
  have hprefix := SphincsCacheLayoutSurjection.keygen_cacheCiphertext_eq_encoded
    inputs parameter seed (hpad parameter) table cache sem padding hparameter
  have htag := SphincsCacheLayoutSurjection.keygen_cache_tag_at_finite_table
    inputs parameter seed (hpad parameter) (hmac parameter) table cache sem padding hparameter
  exact (cacheFromFields_eq_of_fields parameter _ _ cache ⟨hprefix, htag⟩).symm

/-- The actual organizer keygen run returns exactly the cache represented by
the finite-table setup coordinates, at its certified value and cost. -/
theorem organizer_keygen_cache_canonical
    (submission : SigGolf.Submission)
    (image : submission.image .keygen = SphincsMaskedImages.keygen)
    (valid : (submission.image .keygen).Valid submission.sizes submission.layout)
    (secretAddress : submission.layout.secretKey = 0x20)
    (publicAddress : submission.layout.publicKey = 0x40)
    (cacheAddress : submission.layout.cache = 0x60)
    (inputs : Finset SigGolf.Query) (seed : MasterSeed)
    (hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery
        (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (hmac : ∀ parameter : PublicParameter, ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery
        (macInput parameter seed
          (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs)
    (table : inputs → BitVec 256) :
    let hash := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table
    ∃ cache : SigGolf.Cache,
      submission.runWith hash .keygen seed =
        ⟨some (SphincsMaskedKeygenRefinement.publicKey hash seed, cache),
          true, 92369576, 860161, 1007616⟩ ∧
      let setup := SphincsPadSetupIndependence.plaintextSetup inputs seed table
      let parameter := setup.1
      let cipher := SphincsMacUniformExtract.ciphertextNodes inputs parameter seed
        (hpad parameter) (fun i => ((SphincsCacheLayoutSurjection.nodeCoordinate i).1.val,
          (SphincsCacheLayoutSurjection.nodeCoordinate i).2)) table
      let mac := SphincsMacUniformExtract.chosenMacAddress inputs parameter seed
        (hpad parameter) (fun i => ((SphincsCacheLayoutSurjection.nodeCoordinate i).1.val,
          (SphincsCacheLayoutSurjection.nodeCoordinate i).2))
        (SphincsCacheLayoutSurjection.encodeCachePrefix parameter) (hmac parameter) table
      cache = cacheFromFields parameter cipher (truncateHash (table mac)) := by
  let hash := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table
  obtain ⟨cache, hrun, hsem, hpadding⟩ :=
    SphincsMaskedKeygenPadding.keygen_runWith_canonical submission hash seed
      image valid secretAddress publicAddress cacheAddress
  refine ⟨cache, hrun, ?_⟩
  exact keygen_cache_is_canonical inputs seed hpad hmac table cache hsem hpadding

end SigGolfCandidate.SphincsCacheCanonicalization

/-- info: 'SigGolfCandidate.SphincsCacheCanonicalization.keygen_cache_is_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheCanonicalization.keygen_cache_is_canonical

/-- info: 'SigGolfCandidate.SphincsCacheCanonicalization.organizer_keygen_cache_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheCanonicalization.organizer_keygen_cache_canonical
