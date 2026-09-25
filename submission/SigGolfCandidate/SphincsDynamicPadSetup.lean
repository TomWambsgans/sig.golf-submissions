import SigGolfCandidate.SphincsCacheLayoutSurjection

/-! Reparameterize pad answers even when keygen chooses the public parameter. -/

namespace SigGolfCandidate.SphincsDynamicPadSetup
open SigGolf SphincsSecurity
set_option backward.isDefEq.respectTransparency false

noncomputable def dynamicPadTransform {n : Nat} {inputs : Finset SigGolf.Query}
    (addresses : (inputs → BitVec 256) → Fin n → inputs)
    (nodes : (inputs → BitVec 256) → Fin n → Digest)
    (table : inputs → BitVec 256) : inputs → BitVec 256 :=
  SphincsFiniteTableMasking.xorTable
    (SphincsFiniteTableMasking.nodeMask (addresses table) (nodes table)) table

theorem dynamicPadTransform_involutive {n : Nat} {inputs : Finset SigGolf.Query}
    (addresses : (inputs → BitVec 256) → Fin n → inputs)
    (nodes : (inputs → BitVec 256) → Fin n → Digest)
    (haddresses : ∀ table,
      addresses (dynamicPadTransform addresses nodes table) = addresses table)
    (hnodes : ∀ table,
      nodes (dynamicPadTransform addresses nodes table) = nodes table)
    (table : inputs → BitVec 256) :
    dynamicPadTransform addresses nodes (dynamicPadTransform addresses nodes table) = table := by
  have ha : addresses
      (SphincsFiniteTableMasking.xorTable
        (SphincsFiniteTableMasking.nodeMask (addresses table) (nodes table)) table) =
      addresses table := by simpa only [dynamicPadTransform] using haddresses table
  have hn : nodes
      (SphincsFiniteTableMasking.xorTable
        (SphincsFiniteTableMasking.nodeMask (addresses table) (nodes table)) table) =
      nodes table := by simpa only [dynamicPadTransform] using hnodes table
  unfold dynamicPadTransform
  rw [ha, hn]
  exact SphincsFiniteTableMasking.xorTable_involutive
    (SphincsFiniteTableMasking.nodeMask (addresses table) (nodes table)) table

theorem uniform_dynamicPadTransform {n : Nat} {inputs : Finset SigGolf.Query}
    (addresses : (inputs → BitVec 256) → Fin n → inputs)
    (nodes : (inputs → BitVec 256) → Fin n → Digest)
    (haddresses : ∀ table,
      addresses (dynamicPadTransform addresses nodes table) = addresses table)
    (hnodes : ∀ table,
      nodes (dynamicPadTransform addresses nodes table) = nodes table) :
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (dynamicPadTransform addresses nodes) =
        PMF.uniformOfFintype (inputs → BitVec 256) := by
  apply PMF.uniformOfFintype_map_of_bijective
  constructor
  · intro left right heq
    have := congrArg (dynamicPadTransform addresses nodes) heq
    simpa only [dynamicPadTransform_involutive addresses nodes haddresses hnodes] using this
  · intro table
    exact ⟨dynamicPadTransform addresses nodes table,
      dynamicPadTransform_involutive addresses nodes haddresses hnodes table⟩

theorem joint_dynamic_pad_mac {State : Type} {n : Nat}
    {inputs : Finset SigGolf.Query}
    (setup : (inputs → BitVec 256) → State)
    (addresses : (inputs → BitVec 256) → Fin n → inputs)
    (nodes : (inputs → BitVec 256) → Fin n → Digest)
    (macAddress : State → (Fin n → Digest) → inputs)
    (hinj : ∀ table, Function.Injective (addresses table))
    (hsetup : ∀ table,
      setup (dynamicPadTransform addresses nodes table) = setup table)
    (haddresses : ∀ table,
      addresses (dynamicPadTransform addresses nodes table) = addresses table)
    (hnodes : ∀ table,
      nodes (dynamicPadTransform addresses nodes table) = nodes table)
    (hmac : ∀ table cipher i,
      addresses table i ≠ macAddress (setup table) cipher) :
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table =>
        let cipher := fun i => truncateHash (table (addresses table i)) ^^^ nodes table i
        (setup table, cipher, table (macAddress (setup table) cipher), table)) =
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table =>
        let cipher := fun i => truncateHash (table (addresses table i))
        (setup table, cipher, table (macAddress (setup table) cipher),
          dynamicPadTransform addresses nodes table)) := by
  let transform := dynamicPadTransform addresses nodes
  let target := fun table : inputs → BitVec 256 =>
    let cipher := fun i => truncateHash (table (addresses table i))
    (setup table, cipher, table (macAddress (setup table) cipher), transform table)
  have hpoint : ∀ table : inputs → BitVec 256,
      (let cipher := fun i => truncateHash (table (addresses table i)) ^^^ nodes table i
       (setup table, cipher, table (macAddress (setup table) cipher), table)) =
      target (transform table) := by
    intro table
    have hcipher : (fun i => truncateHash (transform table (addresses (transform table) i))) =
        (fun i => truncateHash (table (addresses table i)) ^^^ nodes table i) := by
      funext i
      rw [haddresses table]
      exact SphincsFiniteTableMasking.truncated_xorTable_at
        (addresses table) (nodes table) (hinj table) table i
    have hmacValue : transform table
        (macAddress (setup table)
          (fun i => truncateHash (table (addresses table i)) ^^^ nodes table i)) =
        table (macAddress (setup table)
          (fun i => truncateHash (table (addresses table i)) ^^^ nodes table i)) := by
      exact SphincsFiniteTableMasking.xorTable_away
        (addresses table) (nodes table) table _ (hmac table _)
    dsimp only [target, transform]
    apply Prod.ext
    · exact (hsetup table).symm
    · apply Prod.ext
      · exact hcipher.symm
      · apply Prod.ext
        · rw [hsetup table, hcipher]
          exact hmacValue.symm
        · exact (dynamicPadTransform_involutive
            addresses nodes haddresses hnodes table).symm
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
          rw [uniform_dynamicPadTransform addresses nodes haddresses hnodes]

noncomputable def keygenPadAddresses (inputs : Finset SigGolf.Query)
    (seed : MasterSeed)
    (hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery
        (SphincsCacheSecretDomains.padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (table : inputs → BitVec 256) : Fin 4095 → inputs :=
  SphincsFiniteTableMasking.padAddresses inputs
    (SphincsPadSetupIndependence.plaintextSetup inputs seed table).1 seed
    (hpad _)

theorem padAddresses_congr_parameter (inputs : Finset SigGolf.Query)
    (seed : MasterSeed)
    (hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery
        (SphincsCacheSecretDomains.padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (first second : PublicParameter) (heq : first = second) :
    SphincsFiniteTableMasking.padAddresses inputs first seed (hpad first) =
      SphincsFiniteTableMasking.padAddresses inputs second seed (hpad second) := by
  cases heq
  rfl

noncomputable def keygenPadNodes (inputs : Finset SigGolf.Query)
    (seed : MasterSeed) (coordinates : Fin 4095 → Nat × Nat)
    (table : inputs → BitVec 256) : Fin 4095 → Digest :=
  SphincsPadSetupIndependence.plaintextNodes coordinates
    (SphincsPadSetupIndependence.plaintextSetup inputs seed table)

noncomputable def keygenMacAddress (inputs : Finset SigGolf.Query)
    (seed : MasterSeed) (encode : PublicParameter → (Fin 4095 → Digest) → HashInput)
    (hmac : ∀ parameter : PublicParameter, ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery
        (SphincsCacheSecretDomains.macInput parameter seed (encode parameter cipher)) ∈ inputs)
    (state : Digest × SigGolf.PublicKey × (Nat → Nat → Digest))
    (cipher : Fin 4095 → Digest) : inputs :=
  ⟨SphincsBridge.toQuery
    (SphincsCacheSecretDomains.macInput state.1 seed (encode state.1 cipher)), hmac _ _⟩

/-- The parameter may be chosen by keygen from the oracle: the entire
plaintext/ciphertext/MAC/table law remains exact without conditioning on it. -/
theorem actual_parameter_joint_pad_mac
    (inputs : Finset SigGolf.Query) (seed : MasterSeed)
    (hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery
        (SphincsCacheSecretDomains.padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (coordinates : Fin 4095 → Nat × Nat)
    (encode : PublicParameter → (Fin 4095 → Digest) → HashInput)
    (hmac : ∀ parameter : PublicParameter, ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery
        (SphincsCacheSecretDomains.macInput parameter seed (encode parameter cipher)) ∈ inputs) :
    let setup := SphincsPadSetupIndependence.plaintextSetup inputs seed
    let addresses := keygenPadAddresses inputs seed hpad
    let nodes := keygenPadNodes inputs seed coordinates
    let mac := keygenMacAddress inputs seed encode hmac
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table =>
        let cipher := fun i => truncateHash (table (addresses table i)) ^^^ nodes table i
        (setup table, cipher, table (mac (setup table) cipher), table)) =
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table =>
        let cipher := fun i => truncateHash (table (addresses table i))
        (setup table, cipher, table (mac (setup table) cipher),
          dynamicPadTransform addresses nodes table)) := by
  let setup := SphincsPadSetupIndependence.plaintextSetup inputs seed
  let addresses := keygenPadAddresses inputs seed hpad
  let nodes := keygenPadNodes inputs seed coordinates
  let mac := keygenMacAddress inputs seed encode hmac
  have hinj : ∀ table, Function.Injective (addresses table) := by
    intro table
    exact SphincsFiniteTableMasking.padAddresses_injective inputs
      (setup table).1 seed (hpad _)
  have hsetup : ∀ table, setup (dynamicPadTransform addresses nodes table) = setup table := by
    intro table
    exact SphincsPadSetupIndependence.plaintextSetup_stable inputs
      (setup table).1 seed (hpad _) (nodes table) table
  have haddr : ∀ table, addresses (dynamicPadTransform addresses nodes table) =
      addresses table := by
    intro table
    have hp := congrArg Prod.fst (hsetup table)
    exact padAddresses_congr_parameter inputs seed hpad _ _ hp
  have hnodes : ∀ table, nodes (dynamicPadTransform addresses nodes table) =
      nodes table := by
    intro table
    exact congrArg (SphincsPadSetupIndependence.plaintextNodes coordinates) (hsetup table)
  have hdisjoint : ∀ table cipher i,
      addresses table i ≠ mac (setup table) cipher := by
    intro table cipher i
    exact SphincsFiniteTableMasking.padAddresses_ne_mac inputs
      (setup table).1 (setup table).1 seed seed
      (encode (setup table).1 cipher) (hpad _) (hmac _ _) i
  exact joint_dynamic_pad_mac setup addresses nodes mac hinj hsetup haddr hnodes hdisjoint

end SigGolfCandidate.SphincsDynamicPadSetup

/-- info: 'SigGolfCandidate.SphincsDynamicPadSetup.joint_dynamic_pad_mac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsDynamicPadSetup.joint_dynamic_pad_mac

/-- info: 'SigGolfCandidate.SphincsDynamicPadSetup.actual_parameter_joint_pad_mac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsDynamicPadSetup.actual_parameter_joint_pad_mac
