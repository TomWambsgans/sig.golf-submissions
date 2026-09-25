import SigGolfCandidate.SphincsSecurityJointSetup
import SigGolfCandidate.SphincsTypedInteractionPlan
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.Security

/-! Transport exact setup laws through a probabilistic adaptive continuation. -/
namespace SigGolfCandidate.SphincsSecurityPostKeygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
open SigGolf SphincsSecurity OracleComp OracleSpec
open SigGolfCandidate.SphincsSecurityJointSetup
open SigGolfCandidate.SphincsOrganizerFiniteHash
open SigGolfCandidate.SphincsPadSetupIndependence
open SigGolfCandidate.SphincsCacheSecretDomains
open SigGolfCandidate.SphincsCacheCanonicalization

noncomputable def extendAfterSetup {A B C R : Type}
    (prior : PMF A) (middle : PMF B) (mk : A → B → C)
    (resume : C → SPMF R) : SPMF R :=
  (liftM prior : SPMF A) >>= fun a =>
    (liftM middle : SPMF B) >>= fun b => resume (mk a b)

theorem bind_fresh_setup {A B C R : Type}
    (prior : PMF A) (middle : PMF B) (mk : A → B → C)
    (resume : C → SPMF R) :
    ((liftM (prior.bind (fun a => middle.map (mk a))) : SPMF C) >>= resume) =
      extendAfterSetup prior middle mk resume := by
  rw [← PMF.monad_bind_eq_bind, liftM_bind]
  simp only [← PMF.monad_map_eq_map, liftM_map, extendAfterSetup]
  rw [bind_assoc]
  congr 1
  funext a
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp


theorem bind_liftM_map {A C R : Type}
    (prior : PMF A) (mk : A → C) (resume : C → SPMF R) :
    ((liftM (prior.map mk) : SPMF C) >>= resume) =
      ((liftM prior : SPMF A) >>= fun a => resume (mk a)) := by
  rw [← PMF.monad_map_eq_map, liftM_map]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp

/-- Sampling the secret key before any hash query leaves the lazy oracle
uninitialized; the per-key oracle simulation therefore starts from ∅. -/
theorem withRandomness_sample_bind {A B : Type}
    (sample : ProbComp A) (next : A → OracleComp SigGolf.World B) :
    SigGolf.withRandomness (liftM sample >>= next) =
      (sample >>= fun a => SigGolf.withRandomness (next a)) := by
  unfold SigGolf.withRandomness
  rw [simulateQ_bind]
  simp only [QueryImpl.simulateQ_add_liftM_left, StateT.run'_eq,
    StateT.run_bind, unifFwdImpl.simulateQ_run, bind_map_left,
    map_bind]

theorem withRandomness_map {A B : Type} (f : A → B)
    (program : OracleComp SigGolf.World A) :
    SigGolf.withRandomness (f <$> program) =
      f <$> SigGolf.withRandomness program := by
  unfold SigGolf.withRandomness
  rw [simulateQ_map, StateT.run'_map']

theorem securityExperiment_sample_decomposition
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (rounds : Nat) :
    submission.securityExperiment adversary rounds =
      (SigGolf.sampleSecretKey >>= fun seed =>
        Prod.snd <$> SigGolf.withRandomness
          (setupAndInteract submission adversary seed rounds)) := by
  have hseed (seed : SigGolf.SecretKey) :
      (do
        let keygen ← liftM (submission.run .keygen seed)
        let some (pk, cache) := keygen.value |
          return (⟨false, keygen.hashCalls⟩ : SigGolf.AttackResult)
        submission.interact adversary seed pk rounds
          (adversary.initial pk cache) {hashCalls := keygen.hashCalls}) =
      Prod.snd <$> setupAndInteract submission adversary seed rounds := by
    unfold setupAndInteract
    simp only [map_bind]
    congr 1
    funext keygen
    cases keygen.value with
    | none => simp
    | some pair =>
      rcases pair with ⟨pk, cache⟩
      simp [Functor.map_map, bind_pure_comp]
  unfold SigGolf.Submission.securityExperiment
  change SigGolf.withRandomness (liftM SigGolf.sampleSecretKey >>= fun seed =>
    (do
      let keygen ← liftM (submission.run .keygen seed)
      let some (pk, cache) := keygen.value |
        return (⟨false, keygen.hashCalls⟩ : SigGolf.AttackResult)
      submission.interact adversary seed pk rounds
        (adversary.initial pk cache) {hashCalls := keygen.hashCalls})) = _
  simp only [hseed, withRandomness_sample_bind, withRandomness_map]

/-- Pointwise fixed-secret-key laws lift through the actual organizer secret-key
sampler without projecting away the attack result or its hash-call count. -/
theorem securityExperiment_lift_seed_law
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (rounds : Nat)
    (game : SigGolf.SecretKey → SPMF SigGolf.AttackResult)
    (law : ∀ seed, Prod.snd <$> 𝒮[SigGolf.withRandomness
      (setupAndInteract submission adversary seed rounds)] = game seed) :
    𝒮[submission.securityExperiment adversary rounds] =
      ((liftM SigGolf.sampleSecretKey : SPMF SigGolf.SecretKey) >>= game) := by
  rw [securityExperiment_sample_decomposition]
  simp only [evalSPMF_bind, evalSPMF_map]
  congr 1
  funext seed
  exact law seed

/-- The continuation uses the fixed finite oracle table for HASH, but routes
private `.sample` actions to fresh uniform draws. It starts with the exact
860,161 keygen hash calls already charged. -/
noncomputable def organizerContinuation
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (seed : SphincsSecurity.MasterSeed) (rounds : Nat)
    (inputs : Finset SigGolf.Query)
    (row : SigGolf.PublicKey × SigGolf.Cache × (inputs → BitVec 256)) :
    SPMF SigGolf.AttackResult :=
  𝒮[simulateQ
    (fixedOrganizerWorld (finiteHashAnswer ∅ inputs row.2.2))
    (submission.interact adversary seed row.1 rounds
      (adversary.initial row.1 row.2.1) {hashCalls := 860161})]

theorem organizerContinuation_sample_fresh
    (hash : SigGolf.Hash) (n : Nat) :
    fixedOrganizerWorld hash (.inl n) = liftM (unifSpec.query n) := rfl

theorem organizerContinuation_hash_fixed
    (hash : SigGolf.Hash) (input : SigGolf.Query) :
    fixedOrganizerWorld hash (.inr input) = pure (hash input) := rfl

/-- The exact bytecode setup law is stable under the complete post-keygen
adaptive interaction. All later attacker samples remain fresh, and the
transcript starts with the proved keygen hash-call charge. -/
theorem exact_post_keygen_adaptive_coupling
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (image : submission.image .keygen = SphincsMaskedImages.keygen)
    (valid : (submission.image .keygen).Valid submission.sizes submission.layout)
    (secretAddress : submission.layout.secretKey = 0x20)
    (publicAddress : submission.layout.publicKey = 0x40)
    (cacheAddress : submission.layout.cache = 0x60)
    (seed : SphincsSecurity.MasterSeed) (rounds : Nat) :
    let inputs := cover (setupAndInteract submission adversary seed rounds) seed
    let setup := plaintextSetup inputs seed
    let hpad : ∀ parameter : SphincsSecurity.PublicParameter, ∀ i : Fin 4095,
        SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs :=
      fun parameter i => pad_mem_cover _ seed parameter i
    let hmac : ∀ parameter : SphincsSecurity.PublicParameter,
        ∀ cipher : Fin 4095 → SphincsSecurity.Digest,
        SphincsBridge.toQuery
          (macInput parameter seed
            (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs :=
      fun parameter cipher => mac_mem_cover _ seed parameter cipher
    let cipher := actualCipher inputs seed hpad
    let mac := actualMac inputs seed hpad hmac
    let prior := PMF.uniformOfFintype (inputs → BitVec 256)
    let middle := PMF.uniformOfFintype (BitVec 256)
    let resume := organizerContinuation submission adversary seed rounds inputs
    ((liftM (prior.map (fun table =>
      let actual := (submission.runWith (finiteHashAnswer ∅ inputs table) .keygen seed).value.getD (0, 0)
      (actual.1, actual.2, table))) : SPMF _) >>= resume) =
    extendAfterSetup prior middle
      (fun table answer =>
        ((setup table).2.1,
          cacheFromFields (setup table).1 (cipher table) (truncateHash answer),
          Function.update table (mac table) answer)) resume := by
  let inputs := cover (setupAndInteract submission adversary seed rounds) seed
  let setup := plaintextSetup inputs seed
  let hpad := fun parameter i => pad_mem_cover
    (setupAndInteract submission adversary seed rounds) seed parameter i
  let hmac := fun parameter cipher => mac_mem_cover
    (setupAndInteract submission adversary seed rounds) seed parameter cipher
  let cipher := actualCipher inputs seed hpad
  let mac := actualMac inputs seed hpad hmac
  let prior := PMF.uniformOfFintype (inputs → BitVec 256)
  let middle := PMF.uniformOfFintype (BitVec 256)
  let resume := organizerContinuation submission adversary seed rounds inputs
  have hsetup := setupAndInteract_keygen_joint_law submission adversary
    image valid secretAddress publicAddress cacheAddress seed rounds
  have hbind := congrArg (fun law : PMF (SigGolf.PublicKey × SigGolf.Cache ×
      (inputs → BitVec 256)) => (liftM law : SPMF _) >>= resume) hsetup
  exact hbind.trans (bind_fresh_setup prior middle
    (fun table answer =>
      ((setup table).2.1,
        cacheFromFields (setup table).1 (cipher table) (truncateHash answer),
        Function.update table (mac table) answer)) resume)


/-- Any hash-only RISC-V program becomes deterministic under the fixed table.
The independent `.sample` oracle is never invoked by such a program. -/
theorem fixedOrganizerWorld_lift_hash {R : Type}
    (hash : SigGolf.Hash) (computation : OracleComp SigGolf.HashSpec R) :
    simulateQ (fixedOrganizerWorld hash)
      (liftM computation : OracleComp SigGolf.World R) =
      pure (evalWithAnswerFn hash computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [liftM_pure, simulateQ_pure, evalWithAnswerFn_pure]
  | query_bind input next ih =>
      simp only [liftM_bind, simulateQ_bind, evalWithAnswerFn_bind]
      exact ih (hash input)


/-- Pointwise factorization of the complete fixed-table experiment into exact
keygen followed by a continuation with fresh private sampling. -/
theorem fixedOrganizerWorld_setupAndInteract
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (seed : SphincsSecurity.MasterSeed) (rounds : Nat)
    (hash : SigGolf.Hash) :
    simulateQ (fixedOrganizerWorld hash)
      (setupAndInteract submission adversary seed rounds) =
    let keygen := submission.runWith hash .keygen seed
    match keygen.value with
    | none => pure (none, ⟨false, keygen.hashCalls⟩)
    | some (pk, cache) =>
        (fun result => (some (pk, cache), result)) <$>
          simulateQ (fixedOrganizerWorld hash)
            (submission.interact adversary seed pk rounds
              (adversary.initial pk cache) {hashCalls := keygen.hashCalls}) := by
  unfold setupAndInteract
  rw [simulateQ_bind, fixedOrganizerWorld_lift_hash]
  simp only [pure_bind, Submission.runWith]
  cases hvalue : (evalWithAnswerFn hash (submission.run .keygen seed)).value with
  | none => rfl
  | some pair =>
      rcases pair with ⟨pk, cache⟩
      simp only [bind_pure_comp, simulateQ_map]



/-- Projection of the exact fixed-table experiment to the attack result.
No attacker sampling is collapsed into a fixed sample oracle. -/
theorem fixedOrganizerWorld_attack_projection
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (seed : SphincsSecurity.MasterSeed) (rounds : Nat)
    (hash : SigGolf.Hash) (pk : SigGolf.PublicKey) (cache : SigGolf.Cache)
    (hrun : (submission.runWith hash .keygen seed).value = some (pk, cache))
    (hcalls : (submission.runWith hash .keygen seed).hashCalls = 860161) :
    Prod.snd <$> simulateQ (fixedOrganizerWorld hash)
      (setupAndInteract submission adversary seed rounds) =
      simulateQ (fixedOrganizerWorld hash)
        (submission.interact adversary seed pk rounds
          (adversary.initial pk cache) {hashCalls := 860161}) := by
  rw [fixedOrganizerWorld_setupAndInteract]
  simp only [hrun, hcalls, Functor.map_map]
  change id <$> _ = _
  exact LawfulFunctor.id_map _


/-- At each finite oracle table, projecting the full organizer computation
produces precisely the adaptive continuation used in the setup coupling. -/
theorem finiteTableContinuation_at
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (image : submission.image .keygen = SphincsMaskedImages.keygen)
    (valid : (submission.image .keygen).Valid submission.sizes submission.layout)
    (secretAddress : submission.layout.secretKey = 0x20)
    (publicAddress : submission.layout.publicKey = 0x40)
    (cacheAddress : submission.layout.cache = 0x60)
    (inputs : Finset SigGolf.Query) (seed : SphincsSecurity.MasterSeed)
    (rounds : Nat)
    (hpad : ∀ parameter : SphincsSecurity.PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (hmac : ∀ parameter : SphincsSecurity.PublicParameter,
      ∀ cipher : Fin 4095 → SphincsSecurity.Digest,
      SphincsBridge.toQuery
        (macInput parameter seed
          (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs)
    (table : inputs → BitVec 256) :
    let setup := plaintextSetup inputs seed table
    let cipher := actualCipher inputs seed hpad table
    let mac := actualMac inputs seed hpad hmac table
    let hash := finiteHashAnswer ∅ inputs table
    Prod.snd <$> 𝒮[simulateQ (fixedOrganizerWorld hash)
      (setupAndInteract submission adversary seed rounds)] =
    organizerContinuation submission adversary seed rounds inputs
      (setup.2.1,
        cacheFromFields setup.1 cipher (SphincsSecurity.truncateHash (table mac)), table) := by
  let setup := plaintextSetup inputs seed table
  let cipher := actualCipher inputs seed hpad table
  let mac := actualMac inputs seed hpad hmac table
  let hash := finiteHashAnswer ∅ inputs table
  have hkey := exact_keygen_canonical_at_table submission image valid
    secretAddress publicAddress cacheAddress inputs seed hpad hmac table
  have hvalue : (submission.runWith hash .keygen seed).value =
      some (setup.2.1,
        cacheFromFields setup.1 cipher (SphincsSecurity.truncateHash (table mac))) :=
    congrArg SigGolf.RunResult.value hkey
  have hcalls : (submission.runWith hash .keygen seed).hashCalls = 860161 :=
    congrArg SigGolf.RunResult.hashCalls hkey
  have hproject := fixedOrganizerWorld_attack_projection submission adversary
    seed rounds hash setup.2.1
    (cacheFromFields setup.1 cipher (SphincsSecurity.truncateHash (table mac)))
    hvalue hcalls
  have hdist := congrArg (fun program : ProbComp SigGolf.AttackResult => 𝒮[program]) hproject
  simpa only [organizerContinuation, evalSPMF_map] using hdist


/-- The organizer's complete fixed-secret-key security experiment equals a
finite-table setup followed by fresh-sample adaptive interaction. -/
theorem organizer_full_fixed_seed_project
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (image : submission.image .keygen = SphincsMaskedImages.keygen)
    (valid : (submission.image .keygen).Valid submission.sizes submission.layout)
    (secretAddress : submission.layout.secretKey = 0x20)
    (publicAddress : submission.layout.publicKey = 0x40)
    (cacheAddress : submission.layout.cache = 0x60)
    (seed : SphincsSecurity.MasterSeed) (rounds : Nat) :
    let program := setupAndInteract submission adversary seed rounds
    let inputs := cover program seed
    let setup := plaintextSetup inputs seed
    let hpad : ∀ parameter : SphincsSecurity.PublicParameter, ∀ i : Fin 4095,
        SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs :=
      fun parameter i => pad_mem_cover _ seed parameter i
    let hmac : ∀ parameter : SphincsSecurity.PublicParameter,
        ∀ cipher : Fin 4095 → SphincsSecurity.Digest,
        SphincsBridge.toQuery
          (macInput parameter seed
            (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs :=
      fun parameter cipher => mac_mem_cover _ seed parameter cipher
    let cipher := actualCipher inputs seed hpad
    let mac := actualMac inputs seed hpad hmac
    Prod.snd <$> 𝒮[SigGolf.withRandomness program] =
      (liftM (PMF.uniformOfFintype (inputs → BitVec 256)) : SPMF _) >>= fun table =>
        organizerContinuation submission adversary seed rounds inputs
          ((setup table).2.1,
            cacheFromFields (setup table).1 (cipher table)
              (SphincsSecurity.truncateHash (table (mac table))), table) := by
  let program := setupAndInteract submission adversary seed rounds
  let inputs := cover program seed
  let setup := plaintextSetup inputs seed
  let hpad := fun parameter i => pad_mem_cover program seed parameter i
  let hmac := fun parameter cipher => mac_mem_cover program seed parameter cipher
  let cipher := actualCipher inputs seed hpad
  let mac := actualMac inputs seed hpad hmac
  have hfinite := congrArg (Functor.map Prod.snd)
    (setupAndInteract_finiteLaw_cover submission adversary seed rounds)
  simp only [evalSPMF_bind, sampleHashTable, evalSPMF_uniformSample, map_bind] at hfinite
  calc
    _ = (liftM (PMF.uniformOfFintype (inputs → BitVec 256)) : SPMF _) >>= fun table =>
        Prod.snd <$> 𝒮[simulateQ
          (fixedOrganizerWorld (finiteHashAnswer ∅ inputs table)) program] := by
          exact hfinite
    _ = _ := by
      apply bind_congr
      intro table
      exact finiteTableContinuation_at submission adversary image valid
        secretAddress publicAddress cacheAddress inputs seed rounds
        hpad hmac table


/-- Full fixed-secret-key security game, after exact bytecode keygen, with an
independently sampled MAC answer programmed into the oracle table. The
adversary's later private samples remain fresh and all keygen calls are charged. -/
theorem organizer_full_fixed_seed_programmed_mac
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (image : submission.image .keygen = SphincsMaskedImages.keygen)
    (valid : (submission.image .keygen).Valid submission.sizes submission.layout)
    (secretAddress : submission.layout.secretKey = 0x20)
    (publicAddress : submission.layout.publicKey = 0x40)
    (cacheAddress : submission.layout.cache = 0x60)
    (seed : SphincsSecurity.MasterSeed) (rounds : Nat) :
    let program := setupAndInteract submission adversary seed rounds
    let inputs := cover program seed
    let setup := plaintextSetup inputs seed
    let hpad : ∀ parameter : SphincsSecurity.PublicParameter, ∀ i : Fin 4095,
        SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs :=
      fun parameter i => pad_mem_cover _ seed parameter i
    let hmac : ∀ parameter : SphincsSecurity.PublicParameter,
        ∀ cipher : Fin 4095 → SphincsSecurity.Digest,
        SphincsBridge.toQuery
          (macInput parameter seed
            (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs :=
      fun parameter cipher => mac_mem_cover _ seed parameter cipher
    let cipher := actualCipher inputs seed hpad
    let mac := actualMac inputs seed hpad hmac
    let prior := PMF.uniformOfFintype (inputs → BitVec 256)
    let middle := PMF.uniformOfFintype (BitVec 256)
    let resume := organizerContinuation submission adversary seed rounds inputs
    Prod.snd <$> 𝒮[SigGolf.withRandomness program] =
      extendAfterSetup prior middle
        (fun table answer =>
          ((setup table).2.1,
            cacheFromFields (setup table).1 (cipher table)
              (SphincsSecurity.truncateHash answer),
            Function.update table (mac table) answer)) resume := by
  let program := setupAndInteract submission adversary seed rounds
  let inputs := cover program seed
  let setup := plaintextSetup inputs seed
  let hpad := fun parameter i => pad_mem_cover program seed parameter i
  let hmac := fun parameter cipher => mac_mem_cover program seed parameter cipher
  let cipher := actualCipher inputs seed hpad
  let mac := actualMac inputs seed hpad hmac
  let prior := PMF.uniformOfFintype (inputs → BitVec 256)
  let middle := PMF.uniformOfFintype (BitVec 256)
  let resume := organizerContinuation submission adversary seed rounds inputs
  let current := fun table : inputs → BitVec 256 =>
    ((setup table).2.1,
      cacheFromFields (setup table).1 (cipher table)
        (SphincsSecurity.truncateHash (table (mac table))), table)
  let programmed := fun table : inputs → BitVec 256 => fun answer : BitVec 256 =>
    ((setup table).2.1,
      cacheFromFields (setup table).1 (cipher table)
        (SphincsSecurity.truncateHash answer),
      Function.update table (mac table) answer)
  have hproject := organizer_full_fixed_seed_project submission adversary
    image valid secretAddress publicAddress cacheAddress seed rounds
  have hmap := bind_liftM_map prior current resume
  have hsetup := canonical_cache_mac_fresh_joint inputs seed hpad hmac
  have hpush := congrArg (fun law : PMF (SigGolf.PublicKey × SigGolf.Cache ×
      (inputs → BitVec 256)) => (liftM law : SPMF _) >>= resume) hsetup
  have hsplit := bind_fresh_setup prior middle programmed resume
  exact hproject.trans (hmap.symm.trans (hpush.trans hsplit))

/-- The programmed finite-table game for one sampled secret key. Its result
retains both the full attack outcome and every charged oracle call. -/
noncomputable def programmedSeedGame
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (rounds : Nat) (seed : SigGolf.SecretKey) :
    SPMF SigGolf.AttackResult :=
  let program := setupAndInteract submission adversary seed rounds
  let inputs := cover program seed
  let setup := plaintextSetup inputs seed
  let hpad : ∀ parameter : SphincsSecurity.PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs :=
    fun parameter i => pad_mem_cover _ seed parameter i
  let hmac : ∀ parameter : SphincsSecurity.PublicParameter,
      ∀ cipher : Fin 4095 → SphincsSecurity.Digest,
      SphincsBridge.toQuery
        (macInput parameter seed
          (SphincsCacheLayoutSurjection.encodeCachePrefix parameter cipher)) ∈ inputs :=
    fun parameter cipher => mac_mem_cover _ seed parameter cipher
  let cipher := actualCipher inputs seed hpad
  let mac := actualMac inputs seed hpad hmac
  let prior := PMF.uniformOfFintype (inputs → BitVec 256)
  let middle := PMF.uniformOfFintype (BitVec 256)
  let resume := organizerContinuation submission adversary seed rounds inputs
  extendAfterSetup prior middle
    (fun table answer =>
      ((setup table).2.1,
        cacheFromFields (setup table).1 (cipher table)
          (SphincsSecurity.truncateHash answer),
        Function.update table (mac table) answer)) resume

/-- The actual organizer experiment, including its uniform secret-key sampler,
has exactly the independent programmed-MAC law. No result projection discards
`won` or `hashCalls`. -/
theorem securityExperiment_programmed_mac
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (image : submission.image .keygen = SphincsMaskedImages.keygen)
    (valid : (submission.image .keygen).Valid submission.sizes submission.layout)
    (secretAddress : submission.layout.secretKey = 0x20)
    (publicAddress : submission.layout.publicKey = 0x40)
    (cacheAddress : submission.layout.cache = 0x60)
    (rounds : Nat) :
    𝒮[submission.securityExperiment adversary rounds] =
      ((liftM SigGolf.sampleSecretKey : SPMF SigGolf.SecretKey) >>=
        programmedSeedGame submission adversary rounds) := by
  apply securityExperiment_lift_seed_law
  intro seed
  simpa only [programmedSeedGame] using
    organizer_full_fixed_seed_programmed_mac submission adversary
      image valid secretAddress publicAddress cacheAddress seed rounds

/-- The organizer interaction with its two program services made explicit.
This is the exact interface needed to replace bytecode signing and checking by
reference services while retaining the full outcome and hash-call counter. -/
def interactWithServices {sizes : SigGolf.Sizes}
    (adversary : SigGolf.Adversary sizes)
    (sign : SigGolf.SigningRequest → OracleComp SigGolf.HashSpec
      (SigGolf.RunResult (SigGolf.Bytes sizes.signature)))
    (check : SigGolf.Transcript sizes → SigGolf.Forgery sizes →
      OracleComp SigGolf.HashSpec SigGolf.AttackResult) :
    Nat → adversary.State → SigGolf.Transcript sizes →
      OracleComp SigGolf.World SigGolf.AttackResult
  | 0, _, transcript => pure ⟨false, transcript.hashCalls⟩
  | rounds + 1, state, transcript =>
      match adversary.step state with
      | .submit candidate => liftM (check transcript candidate)
      | .hash input resume => do
          let answer ← liftM (SigGolf.HashSpec.query input)
          interactWithServices adversary sign check rounds (resume answer)
            {transcript with hashCalls := transcript.hashCalls + 1}
      | .sign request resume => do
          if transcript.signingRequests < SigGolf.LIFETIME then
            let result ← liftM (sign request)
            interactWithServices adversary sign check rounds (resume result.value)
              (transcript.record request.message result)
          else return ⟨false, transcript.hashCalls⟩
      | .sample n resume => do
          let answer ← liftM (unifSpec.query n)
          interactWithServices adversary sign check rounds (resume answer) transcript
      | .step next =>
          interactWithServices adversary sign check rounds next transcript

/-- Exact service-level simulation, including all hash calls. -/
theorem interactWithServices_congr {sizes : SigGolf.Sizes}
    (adversary : SigGolf.Adversary sizes)
    (sign₁ sign₂ : SigGolf.SigningRequest → OracleComp SigGolf.HashSpec
      (SigGolf.RunResult (SigGolf.Bytes sizes.signature)))
    (check₁ check₂ : SigGolf.Transcript sizes → SigGolf.Forgery sizes →
      OracleComp SigGolf.HashSpec SigGolf.AttackResult)
    (hsign : ∀ request, sign₁ request = sign₂ request)
    (hcheck : ∀ transcript candidate,
      check₁ transcript candidate = check₂ transcript candidate)
    (rounds : Nat) (state : adversary.State)
    (transcript : SigGolf.Transcript sizes) :
    interactWithServices adversary sign₁ check₁ rounds state transcript =
      interactWithServices adversary sign₂ check₂ rounds state transcript := by
  induction rounds generalizing state transcript with
  | zero => rfl
  | succ rounds ih =>
      cases haction : adversary.step state with
      | submit candidate =>
          simp only [interactWithServices, haction, hcheck]
      | hash input resume =>
          simp only [interactWithServices, haction]
          congr 1
          funext answer
          exact ih (resume answer) _
      | sign request resume =>
          simp only [interactWithServices, haction, hsign]
          split
          · congr 1
            funext result
            exact ih (resume result.value) _
          · rfl
      | sample n resume =>
          simp only [interactWithServices, haction]
          congr 1
          funext answer
          exact ih (resume answer) _
      | step next =>
          simpa only [interactWithServices, haction] using ih next transcript

/-- The explicit-service interpreter is exactly the organizer's interaction. -/
theorem interact_eq_services
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (secretKey : SigGolf.SecretKey) (pk : SigGolf.PublicKey)
    (rounds : Nat) (state : adversary.State)
    (transcript : SigGolf.Transcript submission.sizes) :
    submission.interact adversary secretKey pk rounds state transcript =
      interactWithServices adversary
        (submission.signingOracle secretKey)
        (submission.checkForgery pk) rounds state transcript := by
  induction rounds generalizing state transcript with
  | zero => rfl
  | succ rounds ih =>
      cases haction : adversary.step state with
      | submit candidate =>
          simp only [SigGolf.Submission.interact, interactWithServices, haction]
      | hash input resume =>
          simp only [SigGolf.Submission.interact, interactWithServices, haction]
          congr 1
          funext answer
          exact ih (resume answer) _
      | sign request resume =>
          simp only [SigGolf.Submission.interact, interactWithServices, haction]
          split
          · congr 1
            funext result
            exact ih (resume result.value) _
          · rfl
      | sample n resume =>
          simp only [SigGolf.Submission.interact, interactWithServices, haction]
          congr 1
          funext answer
          exact ih (resume answer) _
      | step next =>
          simpa only [SigGolf.Submission.interact, interactWithServices,
            haction] using ih next transcript

/-- The programmed finite-oracle continuation exposes precisely the signing
and final-checking services that must be refined to the reference game. -/
theorem organizerContinuation_eq_services
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (seed : SphincsSecurity.MasterSeed) (rounds : Nat)
    (inputs : Finset SigGolf.Query)
    (row : SigGolf.PublicKey × SigGolf.Cache × (inputs → BitVec 256)) :
    organizerContinuation submission adversary seed rounds inputs row =
      𝒮[simulateQ (fixedOrganizerWorld (finiteHashAnswer ∅ inputs row.2.2))
        (interactWithServices adversary
          (submission.signingOracle seed)
          (submission.checkForgery row.1)
          rounds (adversary.initial row.1 row.2.1)
          {hashCalls := 860161})] := by
  unfold organizerContinuation
  rw [interact_eq_services]

/-- Pointwise service refinements transport the whole programmed adaptive
game, with no change to the success bit or the charged call count. -/
theorem organizerContinuation_service_refinement
    (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes)
    (seed : SphincsSecurity.MasterSeed) (rounds : Nat)
    (inputs : Finset SigGolf.Query)
    (row : SigGolf.PublicKey × SigGolf.Cache × (inputs → BitVec 256))
    (sign : SigGolf.SigningRequest → OracleComp SigGolf.HashSpec
      (SigGolf.RunResult (SigGolf.Bytes submission.sizes.signature)))
    (check : SigGolf.Transcript submission.sizes →
      SigGolf.Forgery submission.sizes →
      OracleComp SigGolf.HashSpec SigGolf.AttackResult)
    (hsign : ∀ request, submission.signingOracle seed request = sign request)
    (hcheck : ∀ transcript candidate,
      submission.checkForgery row.1 transcript candidate =
        check transcript candidate) :
    organizerContinuation submission adversary seed rounds inputs row =
      𝒮[simulateQ (fixedOrganizerWorld (finiteHashAnswer ∅ inputs row.2.2))
        (interactWithServices adversary sign check
          rounds (adversary.initial row.1 row.2.1)
          {hashCalls := 860161})] := by
  rw [organizerContinuation_eq_services]
  rw [interactWithServices_congr adversary
    (submission.signingOracle seed) sign
    (submission.checkForgery row.1) check hsign hcheck]

/-- A joint trace with identical good-event outcomes transfers any predicate
on the complete organizer result, including a hash-call cutoff. -/
theorem coupled_good_event_le
    (joint : SPMF (SigGolf.AttackResult × SigGolf.AttackResult × Bool))
    (actual reference : SPMF SigGolf.AttackResult)
    (event : SigGolf.AttackResult → Prop)
    (hactual : (fun z => z.1) <$> joint = actual)
    (hreference : (fun z => z.2.1) <$> joint = reference)
    (hgood : ∀ z ∈ support joint, z.2.2 = false → z.1 = z.2.1) :
    Pr[event | actual] ≤
      Pr[event | reference] + Pr[fun z => z.2.2 = true | joint] := by
  have hstep : Pr[fun z => event z.1 | joint] ≤
      Pr[fun z => event z.2.1 ∨ z.2.2 = true | joint] := by
    apply probEvent_mono
    intro z hz hevent
    cases hflag : z.2.2 with
    | true => exact Or.inr rfl
    | false =>
        exact Or.inl (by simpa only [hgood z hz hflag] using hevent)
  calc
    Pr[event | actual] = Pr[fun z => event z.1 | joint] := by
      rw [← hactual, probEvent_map]
      rfl
    _ ≤ Pr[fun z => event z.2.1 ∨ z.2.2 = true | joint] := hstep
    _ ≤ Pr[fun z => event z.2.1 | joint] +
        Pr[fun z => z.2.2 = true | joint] := probEvent_or_le _ _ _
    _ = Pr[event | reference] +
        Pr[fun z => z.2.2 = true | joint] := by
          rw [← hreference, probEvent_map]
          rfl

/-- The existing 160-bit cache MAC first-hit price is below one 127-bit
security unit per charged query. -/
theorem mac_first_hit_rate_le_127 (Q : Nat) :
    (Q : ENNReal) * (Fintype.card SphincsSecurity.Digest : ENNReal)⁻¹ ≤
      (Q : ENNReal) / 2 ^ 127 := by
  have hcard : Fintype.card SphincsSecurity.Digest = 2 ^ 160 := by
    change Fintype.card (BitVec 160) = 2 ^ 160
    rw [Fintype.card_bitVec]
  rw [hcard]
  simp only [div_eq_mul_inv]
  gcongr
  norm_num

/-- Once a full-result coupling identifies bad traces with the existing
first-hit experiment, altered-cache hits add at most `Q / 2^127` to the
organizer win event. The two remaining obligations are precisely the missing
real-game trace coupling and the reference service refinement. -/
theorem coupled_good_event_mac_le
    (joint : SPMF (SigGolf.AttackResult × SigGolf.AttackResult × Bool))
    (actual reference : SPMF SigGolf.AttackResult) (Q : Nat)
    (hactual : (fun z => z.1) <$> joint = actual)
    (hreference : (fun z => z.2.1) <$> joint = reference)
    (hgood : ∀ z ∈ support joint, z.2.2 = false → z.1 = z.2.1)
    (hfirst : Pr[fun z => z.2.2 = true | joint] ≤
      (Q : ENNReal) * (Fintype.card SphincsSecurity.Digest : ENNReal)⁻¹) :
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ Q | actual] ≤
      Pr[fun result => result.won = true ∧ result.hashCalls ≤ Q | reference] +
        (Q : ENNReal) / 2 ^ 127 := by
  exact (coupled_good_event_le joint actual reference
    (fun result => result.won = true ∧ result.hashCalls ≤ Q)
    hactual hreference hgood).trans
    (add_le_add le_rfl (hfirst.trans (mac_first_hit_rate_le_127 Q)))

/-- Instantiate the good-event inequality with the proved adaptive
first-hit bound for the concrete cache-MAC test plan. The remaining `hflag`
obligation is the full-result coupling of the organizer interaction to that
stopped trace, not a probabilistic assumption about the MAC. -/
theorem coupled_good_event_plan_le
    (joint : SPMF (SigGolf.AttackResult × SigGolf.AttackResult × Bool))
    (actual reference : SPMF SigGolf.AttackResult)
    (adversary : SigGolf.Adversary SphincsSubmission.submission.sizes)
    (canonical : SigGolf.Cache)
    (nonalignedAnswer : SphincsAlignedQuery.NonalignedQuery → BitVec 256)
    (wire : SphincsSecurity.Signature →
      SigGolf.Bytes SphincsSubmission.submission.sizes.signature)
    (secretKey : SphincsSecurity.Seeded.SecretKey)
    (material : SphincsSecurity.Seeded.KeyMaterial)
    (seed : SphincsSecurity.MasterSeed)
    (pads : List (BitVec 32 × SphincsSecurity.HashOutput))
    (macAnswer : SphincsSecurity.HashOutput)
    (Q rounds : Nat) (state : adversary.State)
    (hactual : (fun z => z.1) <$> joint = actual)
    (hreference : (fun z => z.2.1) <$> joint = reference)
    (hgood : ∀ z ∈ support joint, z.2.2 = false → z.1 = z.2.1)
    (hflag : Pr[fun z => z.2.2 = true | joint] ≤
      Pr[fun result => result.2 = true |
        StateT.run' (simulateQ SphincsSecurity.romImpl
          (SphincsCacheMacCompiledGame.compiledFailureFlag secretKey
            (SphincsCacheMacCompiledGame.stopBeforeAttack seed
              (SphincsCacheMacTypedGame.encodeTyped material.1 seed
                (SphincsCacheRequestSplit.ciphertext canonical)
                (SphincsTypedInteractionPlan.plan adversary canonical
                  nonalignedAnswer wire Q rounds state 0)))))
          (SphincsMaskedCacheProgramming.maskedMaterialCache material seed pads
            (List.ofFn (SphincsCacheRequestSplit.ciphertext canonical))
            macAnswer)]) :
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ Q | actual] ≤
      Pr[fun result => result.won = true ∧ result.hashCalls ≤ Q | reference] +
        (Q : ENNReal) / 2 ^ 127 := by
  apply coupled_good_event_mac_le joint actual reference Q
    hactual hreference hgood
  exact hflag.trans (SphincsTypedInteractionPlan.plan_real_first_hit_le
    adversary canonical nonalignedAnswer wire secretKey material seed pads
    macAnswer Q rounds state)

/-- The concrete SPHINCS 128-bit reference bound leaves room for the
256-bit seed-programming loss and the 160-bit cache-MAC first-hit loss. -/
theorem seeded_reference_margin_with_seed_hit
    (Q : Nat) (hQ : 1 ≤ Q) (hsmall : Q < 2 ^ 127)
    (adversary : SphincsSecurity.Adversary)
    (hbound : SphincsSecurity.HasHashQueryBound
      SphincsSecurity.Seeded.scheme adversary Q) :
    SphincsSecurity.forgeAdvantage SphincsSecurity.Seeded.scheme adversary +
      (Q : ENNReal) / 2 ^ 160 +
      (Q : ENNReal) / 2 ^ 256 ≤ (Q : ENNReal) / 2 ^ 127 := by
  have hsmall256 : Q < 2 ^ 256 := hsmall.trans (by norm_num)
  have htable := SphincsSecurity.Seeded.tableBudget_from_deterministic
    adversary Q hsmall256 hbound
  have hindependent : SphincsSecurity.HasHashQueryBound
      SphincsSecurity.Concrete.scheme
      (SphincsSecurity.Seeded.memoAdversary adversary) (Q - 1) :=
    SphincsSecurity.Seeded.referenceBudget_from_table adversary (Q - 1)
      (SphincsSecurity.Seeded.tableBudget_memo adversary (Q - 1) htable)
  have hcomparison := SphincsSecurity.Seeded.forgeAdvantage_deterministic_le_reference
    adversary (Q - 1) htable
  have hcomparison' : SphincsSecurity.forgeAdvantage
      SphincsSecurity.Seeded.scheme adversary ≤
      SphincsSecurity.forgeAdvantage SphincsSecurity.Concrete.scheme
        (SphincsSecurity.Seeded.memoAdversary adversary) +
        ((Q - 1 : Nat) : ENNReal) / 2 ^ 256 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcomparison
  have hconcrete : SphincsSecurity.HasHashQueryBound
      SphincsSecurity.Concrete.scheme
      (SphincsSecurity.Seeded.memoAdversary adversary) Q := by
    rw [SphincsSecurity.hasHashQueryBound_iff] at hindependent ⊢
    exact hindependent.mono (Nat.sub_le Q 1)
  have href := SphincsSecurity.Concrete.security128_below_trivial_budget
    Q hQ hsmall.le (SphincsSecurity.Seeded.memoAdversary adversary) hconcrete
  have hseed : ((Q - 1 : Nat) : ENNReal) / 2 ^ 256 ≤
      (Q : ENNReal) / 2 ^ 256 := by
    apply ENNReal.div_le_div_right
    exact_mod_cast Nat.sub_le Q 1
  have hrate : (Q : ENNReal) / 2 ^ 128 +
      (Q : ENNReal) / 2 ^ 256 +
      (Q : ENNReal) / 2 ^ 160 +
      (Q : ENNReal) / 2 ^ 256 ≤
        (Q : ENNReal) / 2 ^ 127 := by
    simp only [div_eq_mul_inv]
    rw [← mul_add, ← mul_add, ← mul_add]
    gcongr
    have hnn : ((2 ^ 128 : NNReal)⁻¹ +
      (2 ^ 256 : NNReal)⁻¹ + (2 ^ 160 : NNReal)⁻¹ +
      (2 ^ 256 : NNReal)⁻¹) ≤
      (2 ^ 127 : NNReal)⁻¹ := by
      apply NNReal.coe_le_coe.mpr
      norm_num [div_le_div_iff₀]
    have henn := ENNReal.coe_le_coe.mpr hnn
    have hcast (n : Nat) : (↑((2 ^ n : NNReal)⁻¹) : ENNReal) =
        (2 ^ n : ENNReal)⁻¹ := by
      rw [ENNReal.coe_inv (by positivity), ENNReal.coe_pow]
      norm_num
    simpa only [ENNReal.coe_add, hcast] using henn
  calc
    _ ≤ ((SphincsSecurity.forgeAdvantage
        SphincsSecurity.Concrete.scheme
          (SphincsSecurity.Seeded.memoAdversary adversary) +
          ((Q - 1 : Nat) : ENNReal) / 2 ^ 256) +
            (Q : ENNReal) / 2 ^ 160) +
            (Q : ENNReal) / 2 ^ 256 :=
          add_le_add (add_le_add hcomparison' le_rfl) le_rfl
    _ ≤ ((Q : ENNReal) / 2 ^ 128 +
          (Q : ENNReal) / 2 ^ 256 +
            (Q : ENNReal) / 2 ^ 160) +
            (Q : ENNReal) / 2 ^ 256 := by
          apply add_le_add
          · apply add_le_add
            · exact add_le_add href hseed
            · exact le_rfl
          · exact le_rfl
    _ ≤ _ := hrate

/-- The 160-bit cache-MAC term alone also fits in the same margin. -/
theorem seeded_reference_margin
    (Q : Nat) (hQ : 1 ≤ Q) (hsmall : Q < 2 ^ 127)
    (adversary : SphincsSecurity.Adversary)
    (hbound : SphincsSecurity.HasHashQueryBound
      SphincsSecurity.Seeded.scheme adversary Q) :
    SphincsSecurity.forgeAdvantage SphincsSecurity.Seeded.scheme adversary +
      (Q : ENNReal) / 2 ^ 160 ≤ (Q : ENNReal) / 2 ^ 127 := by
  exact (le_add_right le_rfl).trans
    (seeded_reference_margin_with_seed_hit Q hQ hsmall adversary hbound)

/-- A complete trace with separate cache-MAC and direct-seed-hit flags
transfers the full win-and-cost event. Both bad events are charged once. -/
theorem coupled_two_bad_events_le
    (joint : SPMF (SigGolf.AttackResult × SigGolf.AttackResult × Bool × Bool))
    (actual reference : SPMF SigGolf.AttackResult)
    (event : SigGolf.AttackResult → Prop)
    (hactual : (fun z => z.1) <$> joint = actual)
    (hreference : (fun z => z.2.1) <$> joint = reference)
    (hgood : ∀ z ∈ support joint,
      z.2.2.1 = false → z.2.2.2 = false → z.1 = z.2.1) :
    Pr[event | actual] ≤ Pr[event | reference] +
      Pr[fun z => z.2.2.1 = true | joint] +
      Pr[fun z => z.2.2.2 = true | joint] := by
  have hstep : Pr[fun z => event z.1 | joint] ≤
      Pr[fun z => event z.2.1 ∨ z.2.2.1 = true ∨ z.2.2.2 = true | joint] := by
    apply probEvent_mono
    intro z hz hevent
    cases hm : z.2.2.1 with
    | true => exact Or.inr (Or.inl rfl)
    | false =>
        cases hs : z.2.2.2 with
        | true => exact Or.inr (Or.inr rfl)
        | false =>
            exact Or.inl (by simpa only [hgood z hz hm hs] using hevent)
  calc
    Pr[event | actual] = Pr[fun z => event z.1 | joint] := by
      rw [← hactual, probEvent_map]
      rfl
    _ ≤ Pr[fun z => event z.2.1 ∨ z.2.2.1 = true ∨
        z.2.2.2 = true | joint] := hstep
    _ ≤ Pr[fun z => event z.2.1 | joint] +
        Pr[fun z => z.2.2.1 = true ∨ z.2.2.2 = true | joint] :=
          probEvent_or_le _ _ _
    _ ≤ Pr[fun z => event z.2.1 | joint] +
        (Pr[fun z => z.2.2.1 = true | joint] +
          Pr[fun z => z.2.2.2 = true | joint]) :=
          add_le_add le_rfl (probEvent_or_le _ _ _)
    _ = _ := by rw [← hreference, probEvent_map, add_assoc]; rfl

/-- Given a full-result coupling and separately charged MAC and seed-hit
traces, the certified deterministic reference bound yields the required
127-bit organizer event bound. The hypotheses name precisely the interfaces
that still need to be related to the actual bytecode experiment. -/
theorem coupled_two_bad_security127
    (joint : SPMF (SigGolf.AttackResult × SigGolf.AttackResult × Bool × Bool))
    (actual reference : SPMF SigGolf.AttackResult)
    (Q : Nat) (hQ : 1 ≤ Q) (hsmall : Q < 2 ^ 127)
    (adversary : SphincsSecurity.Adversary)
    (hbound : SphincsSecurity.HasHashQueryBound
      SphincsSecurity.Seeded.scheme adversary Q)
    (hactual : (fun z => z.1) <$> joint = actual)
    (hreference : (fun z => z.2.1) <$> joint = reference)
    (hgood : ∀ z ∈ support joint,
      z.2.2.1 = false → z.2.2.2 = false → z.1 = z.2.1)
    (href : Pr[fun result => result.won = true ∧ result.hashCalls ≤ Q |
      reference] ≤
      SphincsSecurity.forgeAdvantage SphincsSecurity.Seeded.scheme adversary)
    (hmac : Pr[fun z => z.2.2.1 = true | joint] ≤
      (Q : ENNReal) / 2 ^ 160)
    (hseed : Pr[fun z => z.2.2.2 = true | joint] ≤
      (Q : ENNReal) / 2 ^ 256) :
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ Q | actual] ≤
      (Q : ENNReal) / 2 ^ 127 := by
  exact (coupled_two_bad_events_le joint actual reference
    (fun result => result.won = true ∧ result.hashCalls ≤ Q)
    hactual hreference hgood).trans
    ((add_le_add (add_le_add href hmac) hseed).trans
      (seeded_reference_margin_with_seed_hit Q hQ hsmall adversary hbound))

/-- At or above the 127-bit work scale, the organizer target is at least
one, so every win event meets it independently of the coupling. -/
theorem organizer_event_large_budget
    (actual : SPMF SigGolf.AttackResult) (Q : Nat)
    (hlarge : 2 ^ 127 ≤ Q) :
    Pr[fun result => result.won = true ∧ result.hashCalls ≤ Q | actual] ≤
      (Q : ENNReal) / 2 ^ 127 := by
  calc
    _ ≤ 1 := probEvent_le_one
    _ = ((2 ^ 127 : Nat) : ENNReal) / 2 ^ 127 := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        (ENNReal.div_self (by norm_num : (2 ^ 127 : ENNReal) ≠ 0)
          (by norm_num : (2 ^ 127 : ENNReal) ≠ ⊤)).symm
    _ ≤ _ := by
      apply ENNReal.div_le_div_right
      exact_mod_cast hlarge

/-- Select exactly the hash calls charged by the reference experiment;
private sampling does not spend the hash budget. -/
abbrev referenceHashCall (input : SphincsSecurity.OracleWorld.Domain) : Prop :=
  input matches .inr _

theorem referenceStop_queryBound (program : OracleComp SphincsSecurity.OracleWorld Bool)
    (Q : Nat) :
    (SphincsSecurity.QueryCap.run referenceHashCall program Q).IsQueryBoundP
      referenceHashCall Q :=
  SphincsSecurity.QueryCap.run_queryBound referenceHashCall program Q

theorem referenceStop_fixed_law (program : OracleComp SphincsSecurity.OracleWorld Bool)
    (Q : Nat) (impl : QueryImpl SphincsSecurity.OracleWorld PMF) :
    simulateQ impl (SphincsSecurity.QueryCap.run referenceHashCall program Q) =
      (SphincsSecurity.QueryCap.finish Q) <$>
        simulateQ impl (SphincsSecurity.QueryCap.counted referenceHashCall program) :=
  SphincsSecurity.QueryCap.run_eq_counted referenceHashCall impl program Q

attribute [local irreducible] SphincsSecurity.Seeded.scheme SphincsSecurity.gameCore

/-- A global cutoff around the complete reference game. It intercepts hash
queries from key generation, attacker actions, signing, and final verification. -/
noncomputable def stoppedReferenceGame
    (adversary : SphincsSecurity.Adversary) (Q : Nat) :
    OracleComp SphincsSecurity.OracleWorld (Option (Bool × Nat)) :=
  SphincsSecurity.QueryCap.run referenceHashCall
    (SphincsSecurity.gameCore SphincsSecurity.Seeded.scheme adversary) Q

/-- Every execution of the stopped complete game makes at most Q hash calls;
this structural bound is independent of the oracle implementation. -/
theorem stoppedReferenceGame_queryBound
    (adversary : SphincsSecurity.Adversary) (Q : Nat) :
    (stoppedReferenceGame adversary Q).IsQueryBoundP referenceHashCall Q := by
  change (SphincsSecurity.QueryCap.run referenceHashCall
    (SphincsSecurity.gameCore SphincsSecurity.Seeded.scheme adversary) Q).IsQueryBoundP
      referenceHashCall Q
  exact referenceStop_queryBound
    (SphincsSecurity.gameCore SphincsSecurity.Seeded.scheme adversary) Q

/-- Under any stateless reference oracle, the stopped game is exactly the
original complete game, including all costs, filtered at Q calls. -/
theorem stoppedReferenceGame_fixed_law
    (adversary : SphincsSecurity.Adversary) (Q : Nat)
    (impl : QueryImpl SphincsSecurity.OracleWorld PMF) :
    simulateQ impl (stoppedReferenceGame adversary Q) =
      (SphincsSecurity.QueryCap.finish Q) <$>
        simulateQ impl
          (SphincsSecurity.countHashQueries
            (SphincsSecurity.gameCore SphincsSecurity.Seeded.scheme adversary)) := by
  unfold stoppedReferenceGame SphincsSecurity.countHashQueries
  change simulateQ impl (SphincsSecurity.QueryCap.run referenceHashCall
    (SphincsSecurity.gameCore SphincsSecurity.Seeded.scheme adversary) Q) =
    (SphincsSecurity.QueryCap.finish Q) <$> simulateQ impl
      (SphincsSecurity.QueryCap.counted referenceHashCall
        (SphincsSecurity.gameCore SphincsSecurity.Seeded.scheme adversary))
  exact referenceStop_fixed_law
    (SphincsSecurity.gameCore SphincsSecurity.Seeded.scheme adversary) Q impl

/-- At a fixed oracle, a successful capped run is exactly an original
success with at most Q hash calls, including verifier calls. -/
theorem stoppedReferenceGame_fixed_budget_event
    (adversary : SphincsSecurity.Adversary) (Q : Nat)
    (impl : QueryImpl SphincsSecurity.OracleWorld PMF) :
    Pr[fun result => ∃ remaining, result = some (true, remaining) |
      simulateQ impl (stoppedReferenceGame adversary Q)] =
    Pr[fun result => result.1 = true ∧ result.2 ≤ Q |
      simulateQ impl
        (SphincsSecurity.countHashQueries
          (SphincsSecurity.gameCore SphincsSecurity.Seeded.scheme adversary))] := by
  rw [stoppedReferenceGame_fixed_law, probEvent_map]
  have hpred :
      ((fun result => ∃ remaining, result = some (true, remaining)) ∘
        SphincsSecurity.QueryCap.finish Q) =
      (fun result : Bool × Nat => result.1 = true ∧ result.2 ≤ Q) := by
    funext result
    apply propext
    simp only [Function.comp_def, SphincsSecurity.QueryCap.finish]
    split_ifs with hbudget
    · simp [hbudget]
    · simp [hbudget]
  rw [hpred]

/-- The entire stopped reference game, including signing and final verification,
issues at most `Q` hash calls on every oracle path. -/
theorem stoppedReferenceGame_hashQueryBound
    (adversary : SphincsSecurity.Adversary) (Q : Nat) :
    SphincsSecurity.HashQueryBound (stoppedReferenceGame adversary Q) ∅ Q := by
  intro result hresult
  exact SphincsSecurity.QueryCap.counted_le_of_queryBound referenceHashCall
    (stoppedReferenceGame adversary Q) Q
    (stoppedReferenceGame_queryBound adversary Q) result
    (OracleComp.support_simulateQ_run'_subset SphincsSecurity.romImpl
      (SphincsSecurity.countHashQueries (stoppedReferenceGame adversary Q)) ∅ hresult)


end SigGolfCandidate.SphincsSecurityPostKeygen

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.bind_fresh_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.bind_fresh_setup

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.exact_post_keygen_adaptive_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.exact_post_keygen_adaptive_coupling

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.fixedOrganizerWorld_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.fixedOrganizerWorld_lift_hash

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.fixedOrganizerWorld_setupAndInteract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.fixedOrganizerWorld_setupAndInteract

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.fixedOrganizerWorld_attack_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.fixedOrganizerWorld_attack_projection

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.finiteTableContinuation_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.finiteTableContinuation_at

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.organizer_full_fixed_seed_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.organizer_full_fixed_seed_project

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.bind_liftM_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.bind_liftM_map

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.organizer_full_fixed_seed_programmed_mac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.organizer_full_fixed_seed_programmed_mac

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.withRandomness_sample_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.withRandomness_sample_bind

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.securityExperiment_programmed_mac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.securityExperiment_programmed_mac

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.interact_eq_services' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.interact_eq_services

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.interactWithServices_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.interactWithServices_congr

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.organizerContinuation_service_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.organizerContinuation_service_refinement

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.coupled_good_event_mac_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.coupled_good_event_mac_le

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.coupled_good_event_plan_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.coupled_good_event_plan_le

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.seeded_reference_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.seeded_reference_margin

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.seeded_reference_margin_with_seed_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.seeded_reference_margin_with_seed_hit

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.coupled_two_bad_security127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.coupled_two_bad_security127

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.organizer_event_large_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.organizer_event_large_budget

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.stoppedReferenceGame_fixed_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.stoppedReferenceGame_fixed_law

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.stoppedReferenceGame_fixed_budget_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.stoppedReferenceGame_fixed_budget_event

/-- info: 'SigGolfCandidate.SphincsSecurityPostKeygen.stoppedReferenceGame_hashQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSecurityPostKeygen.stoppedReferenceGame_hashQueryBound
