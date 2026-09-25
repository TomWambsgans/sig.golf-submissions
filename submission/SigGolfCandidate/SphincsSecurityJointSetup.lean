import SigGolfCandidate.SphincsPadBlockUniform
import SigGolfCandidate.SphincsCacheCanonicalization

/-! Finite lazy-oracle cover and the actual keygen cache's joint law. -/

namespace SigGolfCandidate.SphincsSecurityJointSetup
open SigGolf SphincsSecurity
open SigGolfCandidate.SphincsCacheSecretDomains
open SigGolfCandidate.SphincsOrganizerFiniteHash
open SigGolfCandidate.SphincsPadSetupIndependence
open SigGolfCandidate.SphincsMacUniformExtract
open SigGolfCandidate.SphincsCacheCanonicalization
set_option maxRecDepth 2048
set_option maxHeartbeats 300000

variable {α : Type}

noncomputable def padUniverse (seed : MasterSeed) : Finset SigGolf.Query :=
  (Set.finite_range (fun p : PublicParameter × Fin 4095 =>
    SphincsBridge.toQuery (padInput p.1 seed (BitVec.ofNat 32 p.2.val)))).toFinset

noncomputable def macUniverse (seed : MasterSeed) : Finset SigGolf.Query :=
  (Set.finite_range (fun p : PublicParameter × (Fin 4095 → Digest) =>
    SphincsBridge.toQuery
      (macInput p.1 seed (SphincsCacheLayoutSurjection.encodeCachePrefix p.1 p.2)))).toFinset

noncomputable def cover (program : OracleComp SigGolf.World α) (seed : MasterSeed) :
    Finset SigGolf.Query :=
  hashInputs program ∪ padUniverse seed ∪ macUniverse seed

theorem hashInputs_subset_cover (program : OracleComp SigGolf.World α) (seed : MasterSeed) :
    hashInputs program ⊆ cover program seed := by
  intro row hrow
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hrow)))

theorem pad_mem_cover (program : OracleComp SigGolf.World α) (seed : MasterSeed)
    (parameter : PublicParameter) (i : Fin 4095) :
    SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈
      cover program seed := by
  have h : SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ padUniverse seed := by
    unfold padUniverse
    simp only [Set.Finite.mem_toFinset, Set.mem_range]
    exact ⟨(parameter, i), rfl⟩
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))

theorem mac_mem_cover (program : OracleComp SigGolf.World α) (seed : MasterSeed)
    (parameter : PublicParameter) (cipher : Fin 4095 → Digest) :
    SphincsBridge.toQuery
      (macInput parameter seed
        (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈
      cover program seed := by
  have h : SphincsBridge.toQuery
      (macInput parameter seed
        (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ macUniverse seed := by
    unfold macUniverse
    simp only [Set.Finite.mem_toFinset, Set.mem_range]
    exact ⟨(parameter, cipher), rfl⟩
  exact Finset.mem_union.mpr (Or.inr h)

/-- The organizer's complete adaptive interaction can be evaluated from a
finite table that also covers every possible keygen pad and MAC address. -/
theorem setupAndInteract_finiteLaw_cover
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (seed : MasterSeed) (rounds : Nat) :
    let program := setupAndInteract submission adversary seed rounds
    let inputs := cover program seed
    𝒮[SigGolf.withRandomness program] =
      𝒮[do
        let table ← sampleHashTable inputs
        simulateQ (fixedOrganizerWorld (finiteHashAnswer ∅ inputs table)) program] := by
  dsimp only
  exact evalSPMF_romRun_eq_finiteHash
    (setupAndInteract submission adversary seed rounds)
    (cover (setupAndInteract submission adversary seed rounds) seed)
    (hashInputs_subset_cover _ _) ∅


noncomputable def coordinates (i : Fin 4095) : Nat × Nat :=
  ((SphincsCacheLayoutSurjection.nodeCoordinate i).1.val,
    (SphincsCacheLayoutSurjection.nodeCoordinate i).2)

noncomputable def actualCipher (inputs : Finset SigGolf.Query) (seed : MasterSeed)
    (hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (table : inputs → BitVec 256) : Fin 4095 → Digest :=
  ciphertextNodes inputs (plaintextSetup inputs seed table).1 seed
    (hpad _) coordinates table

noncomputable def actualMac (inputs : Finset SigGolf.Query) (seed : MasterSeed)
    (hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (hmac : ∀ parameter : PublicParameter, ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery
        (macInput parameter seed
          (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs)
    (table : inputs → BitVec 256) : inputs :=
  chosenMacAddress inputs (plaintextSetup inputs seed table).1 seed (hpad _)
    coordinates (SphincsCacheLayoutSurjection.encodeCachePrefix _) (hmac _)
    table

/-- The chosen MAC answer stays uniform even though the public parameter and
ciphertext prefix used to address it were chosen by the same random oracle. -/
theorem actual_mac_answer_fresh_joint
    (inputs : Finset SigGolf.Query) (seed : MasterSeed)
    (hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (hmac : ∀ parameter : PublicParameter, ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery
        (macInput parameter seed
          (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs) :
    let setup := plaintextSetup inputs seed
    let cipher := actualCipher inputs seed hpad
    let mac := actualMac inputs seed hpad hmac
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table => ((setup table, cipher table), table (mac table), table)) =
    (PMF.uniformOfFintype (inputs → BitVec 256)).bind (fun table =>
      (PMF.uniformOfFintype (BitVec 256)).map (fun answer =>
        ((setup table, cipher table), answer,
          Function.update table (mac table) answer))) := by
  let setup := plaintextSetup inputs seed
  let cipher := actualCipher inputs seed hpad
  let mac := actualMac inputs seed hpad hmac
  have hstable : ∀ table answer,
      (setup (Function.update table (mac table) answer),
        cipher (Function.update table (mac table) answer)) =
      (setup table, cipher table) := by
    intro table answer
    let parameter := (setup table).1
    have hfixed := plaintext_and_ciphertext_stable_at_mac
      inputs parameter seed (hpad parameter) coordinates
      (SphincsCacheLayoutSurjection.encodeCachePrefix parameter)
      (hmac parameter) table answer
    have hs : setup (Function.update table (mac table) answer) = setup table := by
      exact hfixed.1
    have hc : cipher (Function.update table (mac table) answer) = cipher table := by
      let updated := Function.update table (mac table) answer
      have hp : (setup updated).1 = parameter := congrArg Prod.fst hs
      have hleft : cipher updated =
          ciphertextNodes inputs parameter seed (hpad parameter) coordinates updated := by
        exact congrArg (fun p : PublicParameter =>
          ciphertextNodes inputs p seed (hpad p) coordinates updated) hp
      have hright : ciphertextNodes inputs parameter seed (hpad parameter)
          coordinates table = cipher table := rfl
      exact hleft.trans (hfixed.2.trans hright)
    exact Prod.ext hs hc
  have hindex : ∀ table answer,
      mac (Function.update table (mac table) answer) = mac table := by
    intro table answer
    have hobs := hstable table answer
    apply Subtype.ext
    have hpoint := congrArg (fun pair :
        (Digest × SigGolf.PublicKey × (Nat → Nat → Digest)) ×
          (Fin 4095 → Digest) =>
        SphincsBridge.toQuery (macInput pair.1.1 seed
          (SphincsCacheLayoutSurjection.encodeCachePrefix pair.1.1 pair.2))) hobs
    exact hpoint
  exact dynamic_answer_extraction mac (fun table => (setup table, cipher table))
    hindex hstable


/-- The exact serialized public cache has the same joint law as an independently
sampled MAC answer programmed into the finite oracle table. -/
theorem canonical_cache_mac_fresh_joint
    (inputs : Finset SigGolf.Query) (seed : MasterSeed)
    (hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (hmac : ∀ parameter : PublicParameter, ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery
        (macInput parameter seed
          (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs) :
    let setup := plaintextSetup inputs seed
    let cipher := actualCipher inputs seed hpad
    let mac := actualMac inputs seed hpad hmac
    (PMF.uniformOfFintype (inputs → BitVec 256)).map (fun table =>
      ((setup table).2.1,
        cacheFromFields (setup table).1 (cipher table)
          (truncateHash (table (mac table))), table)) =
    (PMF.uniformOfFintype (inputs → BitVec 256)).bind (fun table =>
      (PMF.uniformOfFintype (BitVec 256)).map (fun answer =>
        ((setup table).2.1,
          cacheFromFields (setup table).1 (cipher table)
            (truncateHash answer),
          Function.update table (mac table) answer))) := by
  let setup := plaintextSetup inputs seed
  let cipher := actualCipher inputs seed hpad
  let mac := actualMac inputs seed hpad hmac
  let extract : ((Digest × SigGolf.PublicKey × (Nat → Nat → Digest)) ×
      (Fin 4095 → Digest)) × BitVec 256 × (inputs → BitVec 256) →
      SigGolf.PublicKey × SigGolf.Cache × (inputs → BitVec 256) :=
    fun x => (x.1.1.2.1,
      cacheFromFields x.1.1.1 x.1.2 (truncateHash x.2.1), x.2.2)
  have h := congrArg (PMF.map extract)
    (actual_mac_answer_fresh_joint inputs seed hpad hmac)
  simp only [PMF.map_comp, PMF.map_bind] at h
  convert h using 1 <;> rfl


/-- The exact RISC-V keygen result, including all cache bytes and charges, is
the canonical value at every finite oracle table. -/
theorem exact_keygen_canonical_at_table
    (submission : SigGolf.Submission)
    (image : submission.image .keygen = SphincsMaskedImages.keygen)
    (valid : (submission.image .keygen).Valid submission.sizes submission.layout)
    (secretAddress : submission.layout.secretKey = 0x20)
    (publicAddress : submission.layout.publicKey = 0x40)
    (cacheAddress : submission.layout.cache = 0x60)
    (inputs : Finset SigGolf.Query) (seed : MasterSeed)
    (hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (hmac : ∀ parameter : PublicParameter, ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery
        (macInput parameter seed
          (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs)
    (table : inputs → BitVec 256) :
    let setup := plaintextSetup inputs seed table
    let cipher := actualCipher inputs seed hpad table
    let mac := actualMac inputs seed hpad hmac table
    submission.runWith (finiteHashAnswer ∅ inputs table) .keygen seed =
      ⟨some (setup.2.1,
        cacheFromFields setup.1 cipher (truncateHash (table mac))),
        true, 92369576, 860161, 1007616⟩ := by
  obtain ⟨cache, hrun, hcache⟩ :=
    organizer_keygen_cache_canonical submission image valid
      secretAddress publicAddress cacheAddress inputs seed hpad hmac table
  have hpk : SphincsMaskedKeygenRefinement.publicKey
      (finiteHashAnswer ∅ inputs table) seed =
        (plaintextSetup inputs seed table).2.1 := rfl
  rw [hpk, hcache] at hrun
  exact hrun


/-- Joint setup law for the actual public key and actual returned public cache.
The `getD` default is unreachable because exact keygen always succeeds. -/
theorem exact_keygen_public_cache_joint_fresh_mac
    (submission : SigGolf.Submission)
    (image : submission.image .keygen = SphincsMaskedImages.keygen)
    (valid : (submission.image .keygen).Valid submission.sizes submission.layout)
    (secretAddress : submission.layout.secretKey = 0x20)
    (publicAddress : submission.layout.publicKey = 0x40)
    (cacheAddress : submission.layout.cache = 0x60)
    (inputs : Finset SigGolf.Query) (seed : MasterSeed)
    (hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (hmac : ∀ parameter : PublicParameter, ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery
        (macInput parameter seed
          (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs) :
    let setup := plaintextSetup inputs seed
    let cipher := actualCipher inputs seed hpad
    let mac := actualMac inputs seed hpad hmac
    (PMF.uniformOfFintype (inputs → BitVec 256)).map (fun table =>
      let actual := (submission.runWith (finiteHashAnswer ∅ inputs table) .keygen seed).value.getD (0, 0)
      (actual.1, actual.2, table)) =
    (PMF.uniformOfFintype (inputs → BitVec 256)).bind (fun table =>
      (PMF.uniformOfFintype (BitVec 256)).map (fun answer =>
        ((setup table).2.1,
          cacheFromFields (setup table).1 (cipher table) (truncateHash answer),
          Function.update table (mac table) answer))) := by
  calc
    _ = (PMF.uniformOfFintype (inputs → BitVec 256)).map (fun table =>
        ((plaintextSetup inputs seed table).2.1,
          cacheFromFields (plaintextSetup inputs seed table).1
            (actualCipher inputs seed hpad table)
            (truncateHash (table (actualMac inputs seed hpad hmac table))), table)) := by
          congr 1
          funext table
          rw [exact_keygen_canonical_at_table submission image valid
            secretAddress publicAddress cacheAddress inputs seed hpad hmac table]
          simp only [Option.getD]
    _ = _ := canonical_cache_mac_fresh_joint inputs seed hpad hmac


/-- The pad-block resampling law holds in the same finite table that exactly
simulates the full adaptive organizer security interaction. -/
theorem setupAndInteract_pad_block_law
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (seed : MasterSeed) (rounds : Nat) :
    let inputs := cover (setupAndInteract submission adversary seed rounds) seed
    let setup := plaintextSetup inputs seed
    let hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
        SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs :=
      fun parameter i => pad_mem_cover _ seed parameter i
    let addresses := SphincsDynamicPadSetup.keygenPadAddresses inputs seed hpad
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table => (setup table,
        (fun i => table (addresses table i)), table)) =
    (PMF.uniformOfFintype (inputs → BitVec 256)).bind (fun table =>
      (PMF.uniformOfFintype (Fin 4095 → BitVec 256)).map (fun values =>
        (setup table, values,
          SphincsPadBlockUniform.blockUpdate (addresses table) values table))) := by
  exact SphincsPadBlockUniform.actual_pad_answers_fresh_joint _ seed
    (fun parameter i => pad_mem_cover _ seed parameter i)

/-- For that same adaptive interaction's finite oracle universe, the actual
RISC-V keygen output cache has a fresh dynamic-MAC joint law. -/
theorem setupAndInteract_keygen_joint_law
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (image : submission.image .keygen = SphincsMaskedImages.keygen)
    (valid : (submission.image .keygen).Valid submission.sizes submission.layout)
    (secretAddress : submission.layout.secretKey = 0x20)
    (publicAddress : submission.layout.publicKey = 0x40)
    (cacheAddress : submission.layout.cache = 0x60)
    (seed : MasterSeed) (rounds : Nat) :
    let inputs := cover (setupAndInteract submission adversary seed rounds) seed
    let setup := plaintextSetup inputs seed
    let hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
        SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs :=
      fun parameter i => pad_mem_cover _ seed parameter i
    let hmac : ∀ parameter : PublicParameter, ∀ cipher : Fin 4095 → Digest,
        SphincsBridge.toQuery
          (macInput parameter seed
            (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs :=
      fun parameter cipher => mac_mem_cover _ seed parameter cipher
    let cipher := actualCipher inputs seed hpad
    let mac := actualMac inputs seed hpad hmac
    (PMF.uniformOfFintype (inputs → BitVec 256)).map (fun table =>
      let actual := (submission.runWith (finiteHashAnswer ∅ inputs table) .keygen seed).value.getD (0, 0)
      (actual.1, actual.2, table)) =
    (PMF.uniformOfFintype (inputs → BitVec 256)).bind (fun table =>
      (PMF.uniformOfFintype (BitVec 256)).map (fun answer =>
        ((setup table).2.1,
          cacheFromFields (setup table).1 (cipher table) (truncateHash answer),
          Function.update table (mac table) answer))) := by
  exact exact_keygen_public_cache_joint_fresh_mac submission image valid
    secretAddress publicAddress cacheAddress _ seed
    (fun parameter i => pad_mem_cover _ seed parameter i)
    (fun parameter cipher => mac_mem_cover _ seed parameter cipher)

end SigGolfCandidate.SphincsSecurityJointSetup

/-- info: 'SigGolfCandidate.SphincsSecurityJointSetup.setupAndInteract_finiteLaw_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityJointSetup.setupAndInteract_finiteLaw_cover

/-- info: 'SigGolfCandidate.SphincsSecurityJointSetup.actual_mac_answer_fresh_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityJointSetup.actual_mac_answer_fresh_joint

/-- info: 'SigGolfCandidate.SphincsSecurityJointSetup.canonical_cache_mac_fresh_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityJointSetup.canonical_cache_mac_fresh_joint

/-- info: 'SigGolfCandidate.SphincsSecurityJointSetup.exact_keygen_canonical_at_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityJointSetup.exact_keygen_canonical_at_table

/-- info: 'SigGolfCandidate.SphincsSecurityJointSetup.exact_keygen_public_cache_joint_fresh_mac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityJointSetup.exact_keygen_public_cache_joint_fresh_mac

/-- info: 'SigGolfCandidate.SphincsSecurityJointSetup.setupAndInteract_pad_block_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityJointSetup.setupAndInteract_pad_block_law

/-- info: 'SigGolfCandidate.SphincsSecurityJointSetup.setupAndInteract_keygen_joint_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityJointSetup.setupAndInteract_keygen_joint_law
