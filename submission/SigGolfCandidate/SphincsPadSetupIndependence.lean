import SigGolfCandidate.SphincsFiniteTableMasking
import SigGolfCandidate.SphincsSecurity.Completeness.Fresh
import SigGolfCandidate.SphincsMaskedKeygenRefinement

/-! The plaintext keygen values never query tag-14 pad coordinates. -/

namespace SigGolfCandidate.SphincsPadSetupIndependence
open SigGolf OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheSecretDomains

theorem eval_eq_of_agree_on_path {α : Type} (computation : OracleComp SphincsSecurity.HashSpec α)
    (f g : QueryImpl SphincsSecurity.HashSpec Id)
    (hagree : ∀ input, input ∈ queriedInputs f computation → f input = g input) :
    evalWithAnswerFn f computation = evalWithAnswerFn g computation := by
  induction computation using OracleComp.inductionOn generalizing f g with
  | pure value => rfl
  | query_bind input next ih =>
      have hinput : f input = g input :=
        hagree input (by simp [queriedInputs_query_bind])
      have hf : evalWithAnswerFn f (liftM (SphincsSecurity.HashSpec.query input)) =
          f input := simulateQ_spec_query f input
      have hg : evalWithAnswerFn g (liftM (SphincsSecurity.HashSpec.query input)) =
          g input := simulateQ_spec_query g input
      simp only [evalWithAnswerFn_bind, hf, hg]
      rw [hinput]
      apply ih (g input) f g
      intro row hrow
      apply hagree row
      simp only [queriedInputs_query_bind]
      exact List.mem_cons_of_mem _ (hinput ▸ hrow)

def PadAgree (first second : SigGolf.Hash) (parameter : PublicParameter)
    (seed : MasterSeed) : Prop :=
  ∀ input : HashInput,
    (∀ i : Fin 4095, input ≠ padInput parameter seed (BitVec.ofNat 32 i.val)) →
    first (SphincsBridge.toQuery input) = second (SphincsBridge.toQuery input)

theorem eval_eq_of_avoids_pads {α : Type} (computation : OracleComp SphincsSecurity.HashSpec α)
    (first second : SigGolf.Hash) (parameter : PublicParameter)
    (seed : MasterSeed) (hagree : PadAgree first second parameter seed)
    (havoid : ∀ i : Fin 4095,
      SphincsSecurity.Completeness.Avoids (SphincsBridge.adaptOracle first)
        (padInput parameter seed (BitVec.ofNat 32 i.val)) computation) :
    evalWithAnswerFn (SphincsBridge.adaptOracle first) computation =
      evalWithAnswerFn (SphincsBridge.adaptOracle second) computation := by
  apply eval_eq_of_agree_on_path
  intro input hquery
  apply hagree input
  intro i heq
  exact havoid i (heq ▸ hquery)

theorem treeNode_avoids_pad (hash : SigGolf.Hash)
    (actualParameter padParameter : PublicParameter)
    (actualSeed padSeed : MasterSeed) (index : Fin 4095)
    (level node : Nat) :
    SphincsSecurity.Completeness.Avoids (SphincsBridge.adaptOracle hash)
      (padInput padParameter padSeed (BitVec.ofNat 32 index.val))
      (Seeded.treeNode actualParameter topLayer Concrete.rootTree actualSeed level node) := by
  apply SphincsSecurity.Completeness.Avoids.treeNode
  · intro leaf chain step payload
    exact (padInput_ne_tweakableHashInput padParameter actualParameter padSeed
      (BitVec.ofNat 32 index.val) (.chain topLayer Concrete.rootTree leaf chain step) payload).symm
  · intro leaf payload
    exact (padInput_ne_tweakableHashInput padParameter actualParameter padSeed
      (BitVec.ofNat 32 index.val) (.leaf topLayer Concrete.rootTree leaf) payload).symm
  · intro level node payload
    exact (padInput_ne_tweakableHashInput padParameter actualParameter padSeed
      (BitVec.ofNat 32 index.val) (.node topLayer Concrete.rootTree level node) payload).symm
  · intro leaf chain
    exact (padInput_ne_keygenHashInput padParameter actualParameter padSeed actualSeed
      (BitVec.ofNat 32 index.val) (.ots topLayer Concrete.rootTree leaf chain)).symm

theorem treeValue_eq_of_padAgree (first second : SigGolf.Hash)
    (actualParameter padParameter : PublicParameter)
    (actualSeed padSeed : MasterSeed)
    (hagree : PadAgree first second padParameter padSeed)
    (level node : Nat) :
    SphincsMaskedParentLevels.treeValue first actualParameter actualSeed level node =
      SphincsMaskedParentLevels.treeValue second actualParameter actualSeed level node := by
  unfold SphincsMaskedParentLevels.treeValue
  apply eval_eq_of_avoids_pads _ first second padParameter padSeed hagree
  intro index
  exact treeNode_avoids_pad first actualParameter padParameter actualSeed padSeed index level node

theorem parameter_eq_of_padAgree (first second : SigGolf.Hash)
    (padParameter : PublicParameter) (seed padSeed : MasterSeed)
    (hagree : PadAgree first second padParameter padSeed) :
    SphincsMaskedKeygenRefinement.parameter first seed =
      SphincsMaskedKeygenRefinement.parameter second seed := by
  unfold SphincsMaskedKeygenRefinement.parameter
  congr 1
  apply hagree
  intro index heq
  exact padInput_ne_keygenHashInput padParameter 0 padSeed seed
    (BitVec.ofNat 32 index.val) .parameter heq.symm

theorem root_eq_of_padAgree (first second : SigGolf.Hash)
    (padParameter : PublicParameter) (seed padSeed : MasterSeed)
    (hagree : PadAgree first second padParameter padSeed) :
    SphincsMaskedKeygenRefinement.root first seed =
      SphincsMaskedKeygenRefinement.root second seed := by
  have hparameter := parameter_eq_of_padAgree first second padParameter seed padSeed hagree
  calc
    SphincsMaskedKeygenRefinement.root first seed =
        SphincsMaskedParentLevels.treeValue first
          (SphincsMaskedKeygenRefinement.parameter first seed) seed
          (layerHeight topLayer) 0 := rfl
    _ = SphincsMaskedParentLevels.treeValue second
          (SphincsMaskedKeygenRefinement.parameter first seed) seed
          (layerHeight topLayer) 0 :=
      treeValue_eq_of_padAgree first second _ padParameter seed padSeed hagree _ _
    _ = SphincsMaskedKeygenRefinement.root second seed := by rw [hparameter]; rfl

theorem publicKey_eq_of_padAgree (first second : SigGolf.Hash)
    (padParameter : PublicParameter) (seed padSeed : MasterSeed)
    (hagree : PadAgree first second padParameter padSeed) :
    SphincsMaskedKeygenRefinement.publicKey first seed =
      SphincsMaskedKeygenRefinement.publicKey second seed := by
  have hparameter := parameter_eq_of_padAgree first second padParameter seed padSeed hagree
  have hroot := root_eq_of_padAgree first second padParameter seed padSeed hagree
  unfold SphincsMaskedKeygenRefinement.publicKey
  rw [hroot, hparameter]
  have hhash : first (SphincsBridge.toQuery (SphincsWire.commitmentInput
        ⟨SphincsMaskedKeygenRefinement.root second seed,
          SphincsMaskedKeygenRefinement.parameter second seed⟩)) =
      second (SphincsBridge.toQuery (SphincsWire.commitmentInput
        ⟨SphincsMaskedKeygenRefinement.root second seed,
          SphincsMaskedKeygenRefinement.parameter second seed⟩)) := by
    apply hagree
    intro index heq
    exact padInput_ne_commitmentInput padParameter padSeed
      (BitVec.ofNat 32 index.val)
      ⟨SphincsMaskedKeygenRefinement.root second seed,
        SphincsMaskedKeygenRefinement.parameter second seed⟩ heq.symm
  exact congrArg (fun output : BitVec 256 => output.extractLsb' 0 128) hhash

theorem finiteHashAnswer_padAgree (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (hmem : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (nodes : Fin 4095 → Digest) (table : inputs → BitVec 256) :
    PadAgree
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table)
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs
        (SphincsFiniteTableMasking.xorTable
          (SphincsFiniteTableMasking.nodeMask
            (SphincsFiniteTableMasking.padAddresses inputs parameter seed hmem) nodes) table))
      parameter seed := by
  intro input hnot
  by_cases hin : SphincsBridge.toQuery input ∈ inputs
  · rw [SphincsOrganizerFiniteHash.finiteHashAnswer_none ∅ inputs table _ hin (by rfl)]
    rw [SphincsOrganizerFiniteHash.finiteHashAnswer_none ∅ inputs _ _ hin (by rfl)]
    symm
    apply SphincsFiniteTableMasking.xorTable_away
    intro i heq
    have hhash := SphincsBridge.toQuery_injective (congrArg Subtype.val heq)
    exact hnot i hhash.symm
  · simp [SphincsOrganizerFiniteHash.finiteHashAnswer, hin]

noncomputable def plaintextSetup (inputs : Finset SigGolf.Query) (seed : MasterSeed)
    (table : inputs → BitVec 256) :
    Digest × SigGolf.PublicKey × (Nat → Nat → Digest) :=
  let hash := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table
  (SphincsMaskedKeygenRefinement.parameter hash seed,
    SphincsMaskedKeygenRefinement.publicKey hash seed,
    fun level node =>
      SphincsMaskedParentLevels.treeValue hash
        (SphincsMaskedKeygenRefinement.parameter hash seed) seed level node)

theorem plaintextSetup_stable (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (hmem : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (nodes : Fin 4095 → Digest) (table : inputs → BitVec 256) :
    plaintextSetup inputs seed
      (SphincsFiniteTableMasking.xorTable
        (SphincsFiniteTableMasking.nodeMask
          (SphincsFiniteTableMasking.padAddresses inputs parameter seed hmem) nodes) table) =
      plaintextSetup inputs seed table := by
  let first := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table
  let second := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs
    (SphincsFiniteTableMasking.xorTable
      (SphincsFiniteTableMasking.nodeMask
        (SphincsFiniteTableMasking.padAddresses inputs parameter seed hmem) nodes) table)
  have hagree : PadAgree first second parameter seed :=
    finiteHashAnswer_padAgree inputs parameter seed hmem nodes table
  have hparameter := parameter_eq_of_padAgree first second parameter seed seed hagree
  have hpublic := publicKey_eq_of_padAgree first second parameter seed seed hagree
  dsimp only [plaintextSetup]
  apply Prod.ext
  · exact hparameter.symm
  · apply Prod.ext
    · exact hpublic.symm
    · funext level node
      rw [hparameter]
      exact (treeValue_eq_of_padAgree first second
        (SphincsMaskedKeygenRefinement.parameter second seed)
        parameter seed seed hagree level node).symm

/-- The MAC address may be chosen from the ciphertext after the pad transform.
Its answer is retained because the address has a distinct tag from every pad. -/
theorem joint_setup_cipher_mac_table {State : Type} {n : Nat}
    {inputs : Finset SigGolf.Query} (addresses : Fin n → inputs)
    (hinj : Function.Injective addresses)
    (setup : (inputs → BitVec 256) → State)
    (nodes : State → Fin n → Digest)
    (hstable : ∀ table,
      setup (SphincsFiniteTableMasking.setupMaskTransform addresses setup nodes table) = setup table)
    (macAddress : (Fin n → Digest) → inputs)
    (hmac : ∀ cipher i, addresses i ≠ macAddress cipher) :
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table =>
        let cipher := fun i => truncateHash (table (addresses i)) ^^^ nodes (setup table) i
        (setup table, cipher, table (macAddress cipher), table)) =
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table =>
        let cipher := fun i => truncateHash (table (addresses i))
        (setup table, cipher, table (macAddress cipher),
          SphincsFiniteTableMasking.setupMaskTransform addresses setup nodes table)) := by
  let transform := SphincsFiniteTableMasking.setupMaskTransform addresses setup nodes
  let target := fun table : inputs → BitVec 256 =>
    let cipher := fun i => truncateHash (table (addresses i))
    (setup table, cipher, table (macAddress cipher), transform table)
  have hpoint : ∀ table : inputs → BitVec 256,
      (let cipher := fun i => truncateHash (table (addresses i)) ^^^ nodes (setup table) i
       (setup table, cipher, table (macAddress cipher), table)) =
      target (transform table) := by
    intro table
    have hcipher : (fun i => truncateHash (transform table (addresses i))) =
        (fun i => truncateHash (table (addresses i)) ^^^ nodes (setup table) i) := by
      funext i
      exact SphincsFiniteTableMasking.truncated_xorTable_at
        addresses (nodes (setup table)) hinj table i
    have hmacValue : transform table
        (macAddress (fun i => truncateHash (table (addresses i)) ^^^ nodes (setup table) i)) =
        table (macAddress (fun i => truncateHash (table (addresses i)) ^^^ nodes (setup table) i)) := by
      exact SphincsFiniteTableMasking.xorTable_away
        addresses (nodes (setup table)) table _
        (hmac _)
    dsimp only [target, transform]
    apply Prod.ext
    · exact (hstable table).symm
    · apply Prod.ext
      · exact hcipher.symm
      · apply Prod.ext
        · rw [hcipher]
          exact hmacValue.symm
        · exact (SphincsFiniteTableMasking.setupMaskTransform_involutive
            addresses setup nodes hstable table).symm
  calc
    _ = (PMF.uniformOfFintype (inputs → BitVec 256)).map
        (fun table => target (transform table)) := by
          congr 1
          funext table
          exact hpoint table
    _ = ((PMF.uniformOfFintype (inputs → BitVec 256)).map transform).map target := by
          rw [PMF.map_comp]
          rfl
    _ = _ := by
          rw [SphincsFiniteTableMasking.uniform_setupMaskTransform
            addresses setup nodes hstable]

def plaintextNodes (coordinates : Fin 4095 → Nat × Nat)
    (state : Digest × SigGolf.PublicKey × (Nat → Nat → Digest)) :
    Fin 4095 → Digest :=
  fun i => state.2.2 (coordinates i).1 (coordinates i).2

/-- Exact finite-table joint distribution for all 4095 encrypted tree nodes,
the dynamically selected tag-15 MAC answer, and the entire oracle table.
`encode` is the cache-prefix serialization; its exact machine encoding is a
separate refinement obligation. -/
theorem plaintext_cipher_mac_joint (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (hpad : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (coordinates : Fin 4095 → Nat × Nat)
    (encode : (Fin 4095 → Digest) → HashInput)
    (hmac : ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery (macInput parameter seed (encode cipher)) ∈ inputs) :
    let addresses := SphincsFiniteTableMasking.padAddresses inputs parameter seed hpad
    let setup := plaintextSetup inputs seed
    let nodes := plaintextNodes coordinates
    let macAddress := fun cipher : Fin 4095 → Digest =>
      (⟨SphincsBridge.toQuery (macInput parameter seed (encode cipher)), hmac cipher⟩ : inputs)
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table =>
        let cipher := fun i => truncateHash (table (addresses i)) ^^^ nodes (setup table) i
        (setup table, cipher, table (macAddress cipher), table)) =
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table =>
        let cipher := fun i => truncateHash (table (addresses i))
        (setup table, cipher, table (macAddress cipher),
          SphincsFiniteTableMasking.setupMaskTransform addresses setup nodes table)) := by
  let addresses := SphincsFiniteTableMasking.padAddresses inputs parameter seed hpad
  let setup := plaintextSetup inputs seed
  let nodes := plaintextNodes coordinates
  let macAddress := fun cipher : Fin 4095 → Digest =>
    (⟨SphincsBridge.toQuery (macInput parameter seed (encode cipher)), hmac cipher⟩ : inputs)
  have hinj : Function.Injective addresses :=
    SphincsFiniteTableMasking.padAddresses_injective inputs parameter seed hpad
  have hstable : ∀ table,
      setup (SphincsFiniteTableMasking.setupMaskTransform addresses setup nodes table) =
        setup table := by
    intro table
    exact plaintextSetup_stable inputs parameter seed hpad
      (nodes (setup table)) table
  have hdisjoint : ∀ cipher i, addresses i ≠ macAddress cipher := by
    intro cipher i
    exact SphincsFiniteTableMasking.padAddresses_ne_mac
      inputs parameter parameter seed seed (encode cipher) hpad (hmac cipher) i
  exact joint_setup_cipher_mac_table addresses hinj setup nodes hstable macAddress hdisjoint

def MacAgree (first second : SigGolf.Hash)
    (parameter : PublicParameter) (seed : MasterSeed)
    (ciphertext : HashInput) : Prop :=
  ∀ input : HashInput, input ≠ macInput parameter seed ciphertext →
    first (SphincsBridge.toQuery input) = second (SphincsBridge.toQuery input)

theorem eval_eq_of_avoids_mac {α : Type}
    (computation : OracleComp SphincsSecurity.HashSpec α)
    (first second : SigGolf.Hash) (parameter : PublicParameter)
    (seed : MasterSeed) (ciphertext : HashInput)
    (hagree : MacAgree first second parameter seed ciphertext)
    (havoid : SphincsSecurity.Completeness.Avoids
      (SphincsBridge.adaptOracle first) (macInput parameter seed ciphertext) computation) :
    evalWithAnswerFn (SphincsBridge.adaptOracle first) computation =
      evalWithAnswerFn (SphincsBridge.adaptOracle second) computation := by
  apply eval_eq_of_agree_on_path
  intro input hquery
  exact hagree input (fun heq => havoid (heq ▸ hquery))

theorem treeNode_avoids_mac (hash : SigGolf.Hash)
    (actualParameter macParameter : PublicParameter)
    (actualSeed macSeed : MasterSeed) (ciphertext : HashInput)
    (level node : Nat) :
    SphincsSecurity.Completeness.Avoids (SphincsBridge.adaptOracle hash)
      (macInput macParameter macSeed ciphertext)
      (Seeded.treeNode actualParameter topLayer Concrete.rootTree actualSeed level node) := by
  apply SphincsSecurity.Completeness.Avoids.treeNode
  · intro leaf chain step payload
    exact (macInput_ne_tweakableHashInput macParameter actualParameter macSeed
      ciphertext (.chain topLayer Concrete.rootTree leaf chain step) payload).symm
  · intro leaf payload
    exact (macInput_ne_tweakableHashInput macParameter actualParameter macSeed
      ciphertext (.leaf topLayer Concrete.rootTree leaf) payload).symm
  · intro level node payload
    exact (macInput_ne_tweakableHashInput macParameter actualParameter macSeed
      ciphertext (.node topLayer Concrete.rootTree level node) payload).symm
  · intro leaf chain
    exact (macInput_ne_keygenHashInput macParameter actualParameter macSeed actualSeed
      ciphertext (.ots topLayer Concrete.rootTree leaf chain)).symm

theorem treeValue_eq_of_macAgree (first second : SigGolf.Hash)
    (actualParameter macParameter : PublicParameter)
    (actualSeed macSeed : MasterSeed) (ciphertext : HashInput)
    (hagree : MacAgree first second macParameter macSeed ciphertext)
    (level node : Nat) :
    SphincsMaskedParentLevels.treeValue first actualParameter actualSeed level node =
      SphincsMaskedParentLevels.treeValue second actualParameter actualSeed level node := by
  unfold SphincsMaskedParentLevels.treeValue
  apply eval_eq_of_avoids_mac _ first second macParameter macSeed ciphertext hagree
  exact treeNode_avoids_mac first actualParameter macParameter actualSeed macSeed ciphertext level node

theorem parameter_eq_of_macAgree (first second : SigGolf.Hash)
    (macParameter : PublicParameter) (seed macSeed : MasterSeed)
    (ciphertext : HashInput)
    (hagree : MacAgree first second macParameter macSeed ciphertext) :
    SphincsMaskedKeygenRefinement.parameter first seed =
      SphincsMaskedKeygenRefinement.parameter second seed := by
  unfold SphincsMaskedKeygenRefinement.parameter
  congr 1
  apply hagree
  intro heq
  exact macInput_ne_keygenHashInput macParameter 0 macSeed seed
    ciphertext .parameter heq.symm

theorem root_eq_of_macAgree (first second : SigGolf.Hash)
    (macParameter : PublicParameter) (seed macSeed : MasterSeed)
    (ciphertext : HashInput)
    (hagree : MacAgree first second macParameter macSeed ciphertext) :
    SphincsMaskedKeygenRefinement.root first seed =
      SphincsMaskedKeygenRefinement.root second seed := by
  have hparameter := parameter_eq_of_macAgree first second macParameter seed macSeed ciphertext hagree
  calc
    SphincsMaskedKeygenRefinement.root first seed =
        SphincsMaskedParentLevels.treeValue first
          (SphincsMaskedKeygenRefinement.parameter first seed) seed
          (layerHeight topLayer) 0 := rfl
    _ = SphincsMaskedParentLevels.treeValue second
          (SphincsMaskedKeygenRefinement.parameter first seed) seed
          (layerHeight topLayer) 0 :=
      treeValue_eq_of_macAgree first second _ macParameter seed macSeed ciphertext hagree _ _
    _ = SphincsMaskedKeygenRefinement.root second seed := by rw [hparameter]; rfl

theorem publicKey_eq_of_macAgree (first second : SigGolf.Hash)
    (macParameter : PublicParameter) (seed macSeed : MasterSeed)
    (ciphertext : HashInput)
    (hagree : MacAgree first second macParameter macSeed ciphertext) :
    SphincsMaskedKeygenRefinement.publicKey first seed =
      SphincsMaskedKeygenRefinement.publicKey second seed := by
  have hparameter := parameter_eq_of_macAgree first second macParameter seed macSeed ciphertext hagree
  have hroot := root_eq_of_macAgree first second macParameter seed macSeed ciphertext hagree
  unfold SphincsMaskedKeygenRefinement.publicKey
  rw [hroot, hparameter]
  have hhash : first (SphincsBridge.toQuery (SphincsWire.commitmentInput
        ⟨SphincsMaskedKeygenRefinement.root second seed,
          SphincsMaskedKeygenRefinement.parameter second seed⟩)) =
      second (SphincsBridge.toQuery (SphincsWire.commitmentInput
        ⟨SphincsMaskedKeygenRefinement.root second seed,
          SphincsMaskedKeygenRefinement.parameter second seed⟩)) := by
    apply hagree
    intro heq
    exact macInput_ne_commitmentInput macParameter macSeed ciphertext
      ⟨SphincsMaskedKeygenRefinement.root second seed,
        SphincsMaskedKeygenRefinement.parameter second seed⟩ heq.symm
  exact congrArg (fun output : BitVec 256 => output.extractLsb' 0 128) hhash

theorem finiteHashAnswer_macAgree (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (ciphertext : HashInput)
    (hmac : SphincsBridge.toQuery (macInput parameter seed ciphertext) ∈ inputs)
    (table : inputs → BitVec 256) (answer : BitVec 256) :
    MacAgree
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table)
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs
        (Function.update table
          (⟨SphincsBridge.toQuery (macInput parameter seed ciphertext), hmac⟩ : inputs)
          answer)) parameter seed ciphertext := by
  intro input hneq
  by_cases hin : SphincsBridge.toQuery input ∈ inputs
  · rw [SphincsOrganizerFiniteHash.finiteHashAnswer_none ∅ inputs table _ hin (by rfl)]
    rw [SphincsOrganizerFiniteHash.finiteHashAnswer_none ∅ inputs _ _ hin (by rfl)]
    have hsub : (⟨SphincsBridge.toQuery input, hin⟩ : inputs) ≠
        ⟨SphincsBridge.toQuery (macInput parameter seed ciphertext), hmac⟩ := by
      intro heq
      exact hneq (SphincsBridge.toQuery_injective (congrArg Subtype.val heq))
    simp [hsub]
  · simp [SphincsOrganizerFiniteHash.finiteHashAnswer, hin]

theorem plaintextSetup_stable_mac_update (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (ciphertext : HashInput)
    (hmac : SphincsBridge.toQuery (macInput parameter seed ciphertext) ∈ inputs)
    (table : inputs → BitVec 256) (answer : BitVec 256) :
    plaintextSetup inputs seed
      (Function.update table
        (⟨SphincsBridge.toQuery (macInput parameter seed ciphertext), hmac⟩ : inputs)
        answer) = plaintextSetup inputs seed table := by
  let first := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table
  let second := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs
    (Function.update table
      (⟨SphincsBridge.toQuery (macInput parameter seed ciphertext), hmac⟩ : inputs)
      answer)
  have hagree : MacAgree first second parameter seed ciphertext :=
    finiteHashAnswer_macAgree inputs parameter seed ciphertext hmac table answer
  have hparameter := parameter_eq_of_macAgree first second parameter seed seed ciphertext hagree
  have hpublic := publicKey_eq_of_macAgree first second parameter seed seed ciphertext hagree
  dsimp only [plaintextSetup]
  apply Prod.ext
  · exact hparameter.symm
  · apply Prod.ext
    · exact hpublic.symm
    · funext level node
      rw [hparameter]
      exact (treeValue_eq_of_macAgree first second
        (SphincsMaskedKeygenRefinement.parameter second seed)
        parameter seed seed ciphertext hagree level node).symm

end SigGolfCandidate.SphincsPadSetupIndependence

/-- info: 'SigGolfCandidate.SphincsPadSetupIndependence.eval_eq_of_avoids_pads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsPadSetupIndependence.eval_eq_of_avoids_pads

/-- info: 'SigGolfCandidate.SphincsPadSetupIndependence.plaintextSetup_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsPadSetupIndependence.plaintextSetup_stable

/-- info: 'SigGolfCandidate.SphincsPadSetupIndependence.plaintext_cipher_mac_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsPadSetupIndependence.plaintext_cipher_mac_joint
